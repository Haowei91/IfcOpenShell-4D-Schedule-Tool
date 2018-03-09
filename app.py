from __future__ import print_function

import os
import sys
import time
import datetime
import operator
import functools
import csv

import OCC.AIS

from collections import defaultdict, Iterable, OrderedDict

os.environ['QT_API'] = 'pyqt4'
try:
    from pyqode.qt import QtCore
except: pass

from PyQt4 import QtGui, QtCore

from code_editor_pane import code_edit

try: from OCC.Display.pyqt4Display import qtViewer3d
except:
    import OCC.Display

    try: import OCC.Display.backend
    except: pass

    try: OCC.Display.backend.get_backend("qt-pyqt4")
    except: OCC.Display.backend.load_backend("qt-pyqt4")

    from OCC.Display.qtDisplay import qtViewer3d


from main import settings, iterator
from occ_utils import display_shape

from ifcopenshell import open as open_ifc_file
from ifcopenshell import get_supertype
import ifcopenshell
import uuid
# Depending on Python version and what not there may or may not be a QString
try:
    from PyQt4.QtCore import QString
except ImportError:
    QString = str
models ={}
class snippet_save_dialogue(QtGui.QDialog):
    pass


class configuration(object):
    def __init__(self):
        try:
            import ConfigParser
            Cfg = ConfigParser.RawConfigParser
        except:
            import configparser
            Cfg = configparser.ConfigParser(interpolation=None)
            
        self.conf_file = os.path.expanduser(os.path.join("~", ".ifcopenshell", "app", "snippets.conf"))
        if self.conf_file.startswith("~"):
            conf_file = None
            return
            
        self.config_encode = lambda s: s.replace("\\", "\\\\").replace("\n", "\n|")
        self.config_decode = lambda s: s.replace("\n|", "\n").replace("\\\\", "\\")
            
        if not os.path.exists(os.path.dirname(self.conf_file)):
            os.makedirs(os.path.dirname(self.conf_file))
            
        if not os.path.exists(self.conf_file):
            self.config = Cfg()
            self.config.add_section("snippets")
            self.config.set("snippets", "print all wall ids", self.config_encode("""
###########################################################################
# A simple script that iterates over all walls in the current model       #
# and prints their Globally unique IDs (GUIDS) to the console window      #
###########################################################################

for wall in model.by_type("IfcWall"):
    print ("wall with global id: "+str(wall.GlobalId))
""".lstrip()))
            
            self.config.set("snippets", "print properties of current selection", self.config_encode("""
###########################################################################
# A simple script that iterates over all IfcPropertySets of the currently #
# selected object and prints them to the console                          #
###########################################################################

# check if something is selected
if selection:
    #get the IfcProduct that is stored in the global variable 'selection'
    obj = selection
    for relDefinesByProperties in obj.IsDefinedBy:
         print("[{0}]".format(relDefinesByProperties.RelatingPropertyDefinition.Name))
         for prop in relDefinesByProperties.RelatingPropertyDefinition.HasProperties:
             print ("{:<20} :{}".format(prop.Name,prop.NominalValue.wrappedValue))
         print ("\\n")
""".lstrip()))
        self.config = Cfg()
        self.config.read(self.conf_file)

    def save_configuration(self):

        with open(self.conf_file, 'w') as configfile:
            self.config.write(configfile)

    def set_snippets(self,snippets):
        pass

    def options(self, s):
        return OrderedDict([(k, self.config_decode(self.config.get(s, k))) for k in self.config.options(s)])
        

class application(QtGui.QApplication):

    """A pythonOCC, PyQt based IfcOpenShell application
    with two tree views and a graphical 3d view"""

    class abstract_treeview(QtGui.QTreeWidget):
    
        """Base class for the two treeview controls"""
        
        instanceSelected = QtCore.pyqtSignal([object])
        instanceVisibilityChanged = QtCore.pyqtSignal([object, int])
        instanceDisplayModeChanged = QtCore.pyqtSignal([object, int])
        
        def __init__(self):
            QtGui.QTreeView.__init__(self)
            self.setColumnCount(len(self.ATTRIBUTES))
            self.setHeaderLabels(self.ATTRIBUTES)
            self.children = defaultdict(list)
            
        def get_children(self, inst):
            c = [inst]
            i = 0
            while i < len(c):
                c.extend(self.children[c[i]])
                i += 1
            return c
            
        def contextMenuEvent(self, event):
            menu = QtGui.QMenu(self)
            visibility = [menu.addAction("Show"), menu.addAction("Hide")]
            displaymode = [menu.addAction("Solid"), menu.addAction("Wireframe")]
            action = menu.exec_(self.mapToGlobal(event.pos()))
            index = self.selectionModel().currentIndex()
            inst = index.data(QtCore.Qt.UserRole)
            if hasattr(inst, 'toPyObject'):
                inst = inst.toPyObject()
            if action in visibility:
                self.instanceVisibilityChanged.emit(inst, visibility.index(action))
            elif action in displaymode:
                self.instanceDisplayModeChanged.emit(inst, displaymode.index(action))
                    
        def clicked(self, index):
            inst = index.data(QtCore.Qt.UserRole)
            if hasattr(inst, 'toPyObject'):
                inst = inst.toPyObject()
            if inst:
                self.instanceSelected.emit(inst)
        
        def select(self, product):
            itm = self.product_to_item.get(product)
            if itm is None: return
            self.selectionModel().setCurrentIndex(itm, QtGui.QItemSelectionModel.SelectCurrent | QtGui.QItemSelectionModel.Rows);
        
    class decomposition_treeview(abstract_treeview):
    
        """Treeview with typical IFC decomposition relationships"""
    
        ATTRIBUTES = ['Entity', 'GlobalId', 'Name']
        
        def parent(self, instance):
            if instance.is_a("IfcOpeningElement"):
                return instance.VoidsElements[0].RelatingBuildingElement
            if instance.is_a("IfcElement"):
                fills = instance.FillsVoids
                if len(fills):
                    return fills[0].RelatingOpeningElement
                containments = instance.ContainedInStructure
                if len(containments):
                    return containments[0].RelatingStructure
            if instance.is_a("IfcObjectDefinition"):
                decompositions = instance.Decomposes
                if len(decompositions):
                    return decompositions[0].RelatingObject
                    
        def load_file(self, f, **kwargs):
            products = list(f.by_type("IfcProduct")) + list(f.by_type("IfcProject"))
            parents = list(map(self.parent, products))
            items = {}
            skipped = 0
            ATTRS = self.ATTRIBUTES
            while len(items) + skipped < len(products):
                for product, parent in zip(products, parents):
                    if parent is None and not product.is_a("IfcProject"):
                        skipped += 1
                        continue
                    if (parent is None or parent in items) and product not in items:
                        sl = []
                        for attr in ATTRS:
                            if attr == 'Entity':
                                sl.append(product.is_a())
                            else:
                                sl.append(getattr(product, attr) or '')
                        itm = items[product] = QtGui.QTreeWidgetItem(items.get(parent, self), sl)
                        itm.setData(0, QtCore.Qt.UserRole, product)
                        self.children[parent].append(product)
            self.product_to_item = dict(zip(items.keys(), map(self.indexFromItem, items.values())))
            self.connect(self, QtCore.SIGNAL("clicked(const QModelIndex &)"), self.clicked)
            self.expandAll()
                
    class type_treeview(abstract_treeview):
    
        """Treeview with typical IFC decomposition relationships"""
    
        ATTRIBUTES = ['Name']
                            
        def load_file(self, f, **kwargs):
            products = list(f.by_type("IfcProduct"))

            types = set(map(lambda i: i.is_a(), products))
            items = {}
            for t in types:
                def add(t):
                    s = get_supertype(t)
                    if s: add(s)
                    s2, t2 = map(QString, (s,t))
                    if t2 not in items:
                        itm = items[t2] = QtGui.QTreeWidgetItem(items.get(s2, self), [t2])
                        itm.setData(0, QtCore.Qt.UserRole, t2)
                        self.children[s2].append(t2)
                add(t)
            
            for p in products:
                t = QString(p.is_a())
                itm = items[p] = QtGui.QTreeWidgetItem(items.get(t, self), [p.Name or '<no name>'])
                itm.setData(0, QtCore.Qt.UserRole, t)
                self.children[t].append(p)
                
            self.product_to_item = dict(zip(items.keys(), map(self.indexFromItem, items.values())))
            self.connect(self, QtCore.SIGNAL("clicked(const QModelIndex &)"), self.clicked)
            self.expandAll()

    class property_table(QtGui.QWidget):

        def __init__(self):
            QtGui.QWidget.__init__(self)
            self.layout= QtGui.QVBoxLayout(self)
            self.setLayout(self.layout)
            self.scroll = QtGui.QScrollArea(self)
            self.layout.addWidget(self.scroll)
            self.scroll.setWidgetResizable(True)
            self.scrollContent = QtGui.QWidget(self.scroll)
            self.scrollLayout = QtGui.QVBoxLayout(self.scrollContent)
            self.scrollContent.setLayout(self.scrollLayout)
            self.scroll.setWidget(self.scrollContent)
            self.prop_dict = {}

        #triggered by selection event in either component of parent
        def select(self, product):
        
            # Clear the old contents if any
            while self.scrollLayout.count():
                child = self.scrollLayout.takeAt(0)
                if child is not None:
                    if child.widget() is not None:
                        child.widget().deleteLater()

            self.scroll = QtGui.QScrollArea()
            self.scroll.setWidgetResizable(True)

            prop_sets = self.prop_dict.get(str(product))
            
            if prop_sets is not None:
                for k,v in prop_sets:
                    group_box = QtGui.QGroupBox()

                    group_box.setTitle(k)
                    group_layout = QtGui.QVBoxLayout()
                    group_box.setLayout(group_layout)
                    
                    for name, value in v.items():
                        prop_name = str(name)
                        
                        value_str = value
                        if hasattr(value_str, "wrappedValue"):
                            value_str = value_str.wrappedValue
                            
                        if isinstance(value_str, unicode):
                            value_str = value_str.encode('utf-8')
                        else:
                            value_str = str(value_str)
                            
                        if hasattr(value, "is_a"):
                            type_str = " <i>(%s)</i>" % value.is_a()
                        else:
                            type_str = ""
                        label = QtGui.QLabel("<b>%s</b>: %s%s" % (prop_name, value_str, type_str))
                        group_layout.addWidget(label)
                        
                    group_layout.addStretch()
                    self.scrollLayout.addWidget(group_box)

                self.scrollLayout.addStretch()
            else:
                label = QtGui.QLabel("No IfcPropertySets asscociated with selected entity instance" )
                self.scrollLayout.addWidget(label)


        def load_file(self, f, **kwargs):
            for p in f.by_type("IfcProduct"):
                propsets = []
                
                def process_pset(prop_def):
                    if prop_def is not None:
                        prop_set_name = prop_def.Name
                        props = {}
                        if prop_def.is_a("IfcElementQuantity"):
                            for q in prop_def.Quantities:
                                if q.is_a("IfcPhysicalSimpleQuantity"):
                                    props[q.Name]=q[3]
                        elif prop_def.is_a("IfcPropertySet"):
                            for prop in prop_def.HasProperties:
                                if prop.is_a("IfcPropertySingleValue"):
                                    props[prop.Name]=prop.NominalValue
                        else:
                            # Entity introduced in IFC4
                            # prop_def.is_a("IfcPreDefinedPropertySet"):
                            for prop in range(4, len(prop_def)):
                                props[prop_def.attribute_name(prop)]=prop_def[prop]
                        return prop_set_name, props
                
                try:
                    for is_def_by in p.IsDefinedBy:
                        if is_def_by.is_a("IfcRelDefinesByProperties"):
                            propsets.append(process_pset(is_def_by.RelatingPropertyDefinition))
                        elif is_def_by.is_a("IfcRelDefinesByType"):
                            type_psets = is_def_by.RelatingType.HasPropertySets
                            if type_psets is None: continue
                            for propset in type_psets:
                                propsets.append(process_pset(propset))
                except Exception, e:
                    import traceback
                    print("failed to load properties: {}".format(e))
                    traceback.print_exc()
                    
                if len(propsets):
                    self.prop_dict[str(p)] = propsets
                
            print ("property set dictionary has {} entries".format(len(self.prop_dict)))
    ###---class for the scheduletime table
    class task_table(QtGui.QMainWindow):

        def __init__(self):
            QtGui.QWidget.__init__(self)
            self.test()
            self.toolbar()

        def toolbar (self):
            t_bar = self.addToolBar("")
            t_bar.setMovable(False)

            add_row_u = QtGui.QPushButton(self)
            add_row_u.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/add_rowu.png")))
            add_row_u.setIconSize(QtCore.QSize(40,20))
            add_row_u.setToolTip("Add new row below")
            add_row_u.clicked.connect(self.a_rowu)
            t_bar.addWidget(add_row_u)

            add_row_o = QtGui.QPushButton(self)
            add_row_o.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/add_rowo.png")))
            add_row_o.setIconSize(QtCore.QSize(40,20))
            add_row_o.setToolTip("Add new row above")
            add_row_o.clicked.connect(self.a_rowo)
            t_bar.addWidget(add_row_o)

            del_row = QtGui.QPushButton(self)
            del_row.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/del_row.png")))
            del_row.setIconSize(QtCore.QSize(40,20))
            del_row.setToolTip("Delete selected row")
            del_row.clicked.connect(self.d_row)
            t_bar.addWidget(del_row)

            assig = QtGui.QPushButton(self)
            assig.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/assign.png")))
            assig.setIconSize(QtCore.QSize(40,20))
            assig.setToolTip("Assigns selected object to task. 1: select the object on the canvas. 2: select the task-row to assign.")
            assig.clicked.connect(self.assign)
            t_bar.addWidget(assig)

            buttonSave = QtGui.QPushButton(self)
            buttonSave.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/save.png")))
            buttonSave.setIconSize(QtCore.QSize(40,20))
            buttonSave.setToolTip("Save the content into IFC model")
            buttonSave.clicked.connect(self.handleSave)
            t_bar.addWidget(buttonSave)


            buttonImport = QtGui.QPushButton(self)
            buttonImport.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/import.png")))
            buttonImport.setIconSize(QtCore.QSize(40,20))
            buttonImport.setToolTip("Import CSV file into the schedule")
            buttonImport.clicked.connect(self.handleImport)
            t_bar.addWidget(buttonImport)

            buttonExport = QtGui.QPushButton(self)
            buttonExport.setIcon(QtGui.QIcon(QtGui.QPixmap("pic/export.png")))
            buttonExport.setToolTip("Export CSV file from the schedule")
            buttonExport.setIconSize(QtCore.QSize(40,20))
            buttonExport.clicked.connect(self.handleExport)
            t_bar.addWidget(buttonExport)
        ###---function to get IfcTask component from modell
        def load_file(self, f, **kwargs):
            global transposed
            transposed =[]
            products = list(f.by_type("IfcRelAssignsTasks"))
            raw_task = []
            task = []
            task_id =[]
            for i in products:
                raw_task.append(i[4])
            for i in raw_task:
                task.append(i[0])
                task_id.append(i[0].id())
            ###---get the Name of each IfcTask
            name = []
            for i in task:
                name.append(i[2])
            ###---get the Desciption of each IfcTask
            descrip = []
            for i in task:
                descrip.append(i[3])
            ###---get the ID Number of each IfcTask
            idnumber = []
            for i in task:
                idnumber.append(i[5])
            ###---get the Methode of each IfcTask
            method = []
            for i in task:
                method.append(i[7])
            ###---get the Milestone of each IfcTask
            mile = []
            for i in task:
                mile.append(str(i[8]))
            ###---get the Control of each IfcTask
            control = []
            for i in products:
                control.append(i[7])
            raw_duration = []
            ###---get the Duration of each IfcTask
            duration = []
            for i in control:
                raw_duration.append(i[13])
            for i in range(len(raw_duration)):
                duration.append(str(raw_duration[i]))
            ###---formatting the actually StartTime of each IfcTask
            def a_start():
                global a_s_date
                global a_s_time
                raw_act_start = []
                raw_act_start_date = []
                raw_act_start_time = []
                act_start_date = []
                act_start_time = []
                content_1 = [act_start_date , act_start_time]
                content_2 = []
                act_start = []
                a_s_date = []
                a_s_time = []
                ###---get the actuelly Start DateTime
                for i in control:
                    raw_act_start.append(i[5])
                ###---get the actuelly Start Date
                for i in raw_act_start:
                    if i is None:
                        raw_act_start_date.append(None)
                    else:
                        raw_act_start_date.append(i[0])

                for i in raw_act_start_date:
                    if i is None:
                        act_start_date.append(None)
                    else:
                        a = []
                        a.append(i[2])
                        a.append(i[1])
                        a.append(i[0])
                        act_start_date.append(a)
                ###---get the actuelly Start Time
                for i in raw_act_start:
                    if i is None:
                        raw_act_start_time.append(None)
                    else:
                        raw_act_start_time.append(i[1])
                for i in raw_act_start_time:
                    if i is None:
                        act_start_time.append(None)
                    else:
                        b = []
                        b.append(i[0])
                        b.append(i[1])
                        b.append(i[2])
                        b.append(i[3])
                        b.append(i[4])
                        act_start_time.append(b)
                ###---sort the list in right order
                for i in range(len(act_start_date)):
                    content_2.append([row[i] for row in content_1])
                ###---put the date and time list togehter
                for i,j in content_2:
                    if j is not None:
                        act_start.append(i + j)
                    elif j is None:
                        act_start.append(i)
                ###---insert 9. "None" into the list for the date output
                j=0
                for i in act_start:
                    if i is not None:
                        act_start[j].insert(8,None)
                    j+=1
                ###---replace the "None" with "0"
                k=0
                for i in act_start:
                    if i is not None:
                        for j in range(len(act_start[k])):
                            if act_start[k][j] == None:
                                act_start[k][j] = 0
                    k+=1
                ###---create the Date
                for i in act_start:
                    if i is not None:
                        dztupel = time.strftime('%d.%m.%Y', i)
                        a_s_date.append(dztupel)
                    else:
                        a_s_date.append(None)
                ###---create the Time
                for i in act_start:
                    if i is not None:
                        dztupel = time.strftime('%H:%M', i)
                        a_s_time.append(dztupel)
                    else:
                        a_s_time.append(None)
            ###---formatting the planned StartTime of each IfcTask
            def p_start():
                global p_s_date
                global p_s_time
                raw_plan_start = []
                raw_plan_start_date = []
                raw_plan_start_time = []
                plan_start_date = []
                plan_start_time = []
                content_3 = [plan_start_date , plan_start_time]
                content_4 = []
                plan_start = []
                p_s_date = []
                p_s_time = []
                ###---get the planned Start DateTime
                for i in control:
                    raw_plan_start.append(i[8])
                ###---get the planned Start Date
                for i in raw_plan_start:
                    if i is None:
                        raw_plan_start_date.append(None)
                    else:
                        raw_plan_start_date.append(i[0])

                for i in raw_plan_start_date:
                    if i is None:
                        plan_start_date.append(None)
                    else:
                        a = []
                        a.append(i[2])
                        a.append(i[1])
                        a.append(i[0])
                        plan_start_date.append(a)
                ###---get the planned Start Time
                for i in raw_plan_start:
                    if i is None:
                        raw_plan_start_time.append(None)
                    else:
                        raw_plan_start_time.append(i[1])
                for i in raw_plan_start_time:
                    if i is None:
                        plan_start_time.append(None)
                    else:
                        b = []
                        b.append(i[0])
                        b.append(i[1])
                        b.append(i[2])
                        b.append(i[3])
                        b.append(i[4])
                        plan_start_time.append(b)
                ###---sort the list in right order
                for i in range(len(plan_start_date)):
                    content_4.append([row[i] for row in content_3])
                ###---put the date and time list together
                for i,j in content_4:
                    if j is not None:
                        plan_start.append(i + j)
                    elif j is None:
                        plan_start.append(i)
                ###---insert 9. "None" into the list for the date output
                j=0
                for i in plan_start:
                    if i is not None:
                        plan_start[j].insert(8,None)
                    j+=1
                ###---replace the "None" with "0"
                k=0
                for i in plan_start:
                    if i is not None:
                        for j in range(len(plan_start[k])):
                            if plan_start[k][j] == None:
                                plan_start[k][j] = 0
                    k+=1
                ###---create the Date
                for i in plan_start:
                    if i is not None:
                        dztupel = time.strftime('%d.%m.%Y', i)
                        p_s_date.append(dztupel)
                    else:
                        p_s_date.append(None)
                ###---create the Time
                for i in plan_start:
                    if i is not None:
                        dztupel = time.strftime('%H:%M', i)
                        p_s_time.append(dztupel)
                    else:
                        p_s_time.append(None)
            ###---formatting the actually EndTime of each IfcTask
            def a_end():
                global a_e_date
                global a_e_time
                raw_act_end = []
                raw_act_end_date = []
                raw_act_end_time = []
                act_end_date = []
                act_end_time = []
                content_5 = [act_end_date , act_end_time]
                content_6 = []
                act_end = []
                a_e_date = []
                a_e_time = []
                ###---get the actuelly End DateTime
                for i in control:
                    raw_act_end.append(i[9])
                ###---get the actuelly End Date
                for i in raw_act_end:
                    if i is None:
                        raw_act_end_date.append(None)
                    else:
                        raw_act_end_date.append(i[0])

                for i in raw_act_end_date:
                    if i is None:
                        act_end_date.append(None)
                    else:
                        a = []
                        a.append(i[2])
                        a.append(i[1])
                        a.append(i[0])
                        act_end_date.append(a)
                ###---get the actuelly End Time
                for i in raw_act_end:
                    if i is None:
                        raw_act_end_time.append(None)
                    else:
                        raw_act_end_time.append(i[1])
                for i in raw_act_end_time:
                    if i is None:
                        act_end_time.append(None)
                    else:
                        b = []
                        b.append(i[0])
                        b.append(i[1])
                        b.append(i[2])
                        b.append(i[3])
                        b.append(i[4])
                        act_end_time.append(b)
                ###---sort the list in right order
                for i in range(len(act_end_date)):
                    content_6.append([row[i] for row in content_5])
                ###---put the date and time list togehter
                for i,j in content_6:
                    if j is not None:
                        act_end.append(i + j)
                    elif j is None:
                        act_end.append(i)
                ###---insert 9. "None" into the list for the date output
                j=0
                for i in act_end:
                    if i is not None:
                        act_end[j].insert(8,None)
                    j+=1
                ###---replace the "None" with "0"
                k=0
                for i in act_end:
                    if i is not None:
                        for j in range(len(act_end[k])):
                            if act_end[k][j] == None:
                                act_end[k][j] = 0
                    k+=1
                ###---create the Date
                for i in act_end:
                    if i is not None:
                        dztupel = time.strftime('%d.%m.%Y', i)
                        a_e_date.append(dztupel)
                    else:
                        a_e_date.append(None)
                ###---create the Time
                for i in act_end:
                    if i is not None:
                        dztupel = time.strftime('%H:%M', i)
                        a_e_time.append(dztupel)
                    else:
                        a_e_time.append(None)
            ###---formatting the planned EndTime of each IfcTask
            def p_end():
                global p_e_date
                global p_e_time
                raw_plan_end = []
                raw_plan_end_date = []
                raw_plan_end_time = []
                plan_end_date = []
                plan_end_time = []
                content_7 = [plan_end_date , plan_end_time]
                content_8 = []
                plan_end = []
                p_e_date = []
                p_e_time = []
                ###---get the planned End DateTime
                for i in control:
                    raw_plan_end.append(i[12])
                ###---get the planned End Date
                for i in raw_plan_end:
                    if i is None:
                        raw_plan_end_date.append(None)
                    else:
                        raw_plan_end_date.append(i[0])

                for i in raw_plan_end_date:
                    if i is None:
                        plan_end_date.append(None)
                    else:
                        a = []
                        a.append(i[2])
                        a.append(i[1])
                        a.append(i[0])
                        plan_end_date.append(a)
                ###---get the planned End Time
                for i in raw_plan_end:
                    if i is None:
                        raw_plan_end_time.append(None)
                    else:
                        raw_plan_end_time.append(i[1])
                for i in raw_plan_end_time:
                    if i is None:
                        plan_end_time.append(None)
                    else:
                        b = []
                        b.append(i[0])
                        b.append(i[1])
                        b.append(i[2])
                        b.append(i[3])
                        b.append(i[4])
                        plan_end_time.append(b)
                ###---sort the list in right order
                for i in range(len(plan_end_date)):
                    content_8.append([row[i] for row in content_7])
                ###---put the date and time list togehter
                for i,j in content_8:
                    if j is not None:
                        plan_end.append(i + j)
                    elif j is None:
                        plan_end.append(i)
                ###---insert 9. "None" into the list for the date output
                j=0
                for i in plan_end:
                    if i is not None:
                        plan_end[j].insert(8,None)
                    j+=1
                ###---replace the "None" with "0"
                k=0
                for i in plan_end:
                    if i is not None:
                        for j in range(len(plan_end[k])):
                            if plan_end[k][j] == None:
                                plan_end[k][j] = 0
                    k+=1
                ###---create the Date
                for i in plan_end:
                    if i is not None:
                        dztupel = time.strftime('%d.%m.%Y', i)
                        p_e_date.append(dztupel)
                    else:
                        p_e_date.append(None)
                ###---create the Time
                for i in plan_end:
                    if i is not None:
                        dztupel = time.strftime('%H:%M', i)
                        p_e_time.append(dztupel)
                    else:
                        p_e_time.append(None)
            ###---each for Assigns to Process Objects between IfcTask and IfcBuildingElements
            process =list(f.by_type("IfcRelAssignsToProcess"))
            raw_assigns = []
            assigns = []
            has = False
            for i in task_id:
                for j in process:
                    if j[6].id() == i:
                        has = True
                    if has:
                        raw_assigns.append(j[4])
                        break
                if not has:
                    raw_assigns.append(None)
                has = False
            for i in raw_assigns:
                if i is not None:
                    if len(i) > 1:
                        adds =[]
                        for k in i:
                            adds.append(str(k.id()))
                        add = ", ".join(adds)
                        assigns.append(add)
                    else:
                        assigns.append(str(i[0].id()))
                else:
                    assigns.append(None)
            a_start()
            p_start()
            a_end()
            p_end()
            li = [descrip, idnumber, name, p_s_date, p_e_date, duration, mile ,a_s_date, a_e_date, method, assigns]
            ###---write the Schedule Information into the TableWidget
            for i in range(len(task)):
                transposed.append([row[i] for row in li])
            t.setRowCount(len(transposed))
            for n, key in enumerate (transposed):
                for i, item in enumerate(key):
                    t.setItem(n,i, QtGui.QTableWidgetItem(item))

        def assign(self):
            cel_r = t.currentRow()
            t.setItem(cel_r,10, QtGui.QTableWidgetItem(str(obj)))
        ###---function to get the ID of the selected Buildingelement. Also possible to take the "name" oder "guid".
        def select(self, product):
            global obj
            global col_obj
            obj = product.id()
            col_obj = product

        def handleSave(self):
            model = models[list(models)[0]]
            ###---write the table content in 2 dimensional list
            rowdata =[]
            for row in range(t.rowCount()):
                rowrow = []
                for column in range(t.columnCount()):
                    item = t.item(row, column)
                    if item is not None:
                        rowrow.append(
                            unicode(item.text()).encode('utf8'))
                    elif item is None:
                        rowrow.append("")
                rowdata.append(rowrow)
            ###---repalce the empty value with None
            k=0

            for i in rowdata:
                if i is not None:
                    for j in range(len(rowdata[k])):
                        if rowdata[k][j] == "":
                            rowdata[k][j] = None
                k+=1
            ###---change the date format
            for row in rowdata:
                if row[6] == "True":
                    row[6] = True
                else:
                    row[6] = False
                if row[3] is not None:
                    tempStr = row[3].split('.')
                    tempIntArr = [0,0,0]
                    for i in range(0, len(tempStr)):
                        tempIntArr[i] = int(tempStr[i])
                    row[3] = tempIntArr
                if row[4] is not None:
                    tempStr = row[4].split('.')
                    tempIntArr = [0,0,0]
                    for i in range(0, len(tempStr)):
                        tempIntArr[i] = int(tempStr[i])
                    row[4] = tempIntArr
                if row[7] is not None:
                    tempStr = row[7].split('.')
                    tempIntArr = [0,0,0]
                    for i in range(0, len(tempStr)):
                        tempIntArr[i] = int(tempStr[i])
                    row[7] = tempIntArr
                if row[8] is not None:
                    tempStr = row[8].split('.')
                    tempIntArr = [0,0,0]
                    for i in range(0, len(tempStr)):
                        tempIntArr[i] = int(tempStr[i])
                    row[8] = tempIntArr

            ###---save the list into ifc schema
            filename = QtGui.QFileDialog.getSaveFileName(self, 'Save File','',"Industry Foundation Classes (*.ifc)")
            if filename:
                filename_string=str(filename)

            owner = model.by_type("IfcOwnerHistory")
            plan= model.by_type("IfcWorkPlan")
            if len(plan) is 0:
                plan_set_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                schedule_set_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                rela_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                date_schedule_s = model.createIfcCalendarDate(01,02,2017)
                time_schedule_s = model.createIfcLocalTime(0, 0, None, None, None)
                calender_schedule_s = model.createIfcDateAndTime(date_schedule_s,time_schedule_s)
                schedule_set = model.createIfcWorkSchedule(schedule_set_guid, owner[0], "Name", None, None, "Ifcopenshell", calender_schedule_s, None, None, None, None, calender_schedule_s, None, None, None )
                plan_set = model.createIfcWorkPlan(plan_set_guid, owner[0], "Name", None, None, "Ifcopenshell", schedule_set, None, None, None, None, calender_schedule_s, None, None, None )
                model.createIfcRelAggregates(rela_guid, owner[0], None, None, plan_set, [schedule_set])
            else:
                plan_set = plan
                schedule_set = model.by_type("IfcWorkSchedule")
            j=0
            for i in rowdata:
                task_set_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                control_set_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                rel_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                task_set = model.createIfcTask(task_set_guid, owner[0], rowdata[j][2], rowdata[j][0], None, rowdata[j][1], None, None, rowdata[j][6], None)

                if rowdata[j][3] is not None:
                    date_plan_s = model.createIfcCalendarDate(rowdata[j][3][0],rowdata[j][3][1],rowdata[j][3][2])
                    time_plan_s = model.createIfcLocalTime(0, 0, None, None, None)
                    calender_plan_s = model.createIfcDateAndTime(date_plan_s,time_plan_s)
                else:
                    calender_plan_s = None
                if rowdata[j][4] is not None:
                    date_plan_e = model.createIfcCalendarDate(rowdata[j][4][0],rowdata[j][4][1],rowdata[j][4][2])
                    time_plan_e = model.createIfcLocalTime(0, 0, None, None, None)
                    calender_plan_e = model.createIfcDateAndTime(date_plan_e,time_plan_e)
                else:
                    calender_plan_e = None
                if rowdata[j][7] is not None:
                    date_act_s = model.createIfcCalendarDate(rowdata[j][7][0],rowdata[j][7][1],rowdata[j][7][2])
                    time_act_s = model.createIfcLocalTime(0, 0, None, None, None)
                    calender_act_s = model.createIfcDateAndTime(date_act_s,time_act_s)
                else:
                    calender_act_s = None
                if rowdata[j][8] is not None:
                    date_act_e = model.createIfcCalendarDate(rowdata[j][8][0],rowdata[j][8][1],rowdata[j][8][2])
                    time_act_e = model.createIfcLocalTime(0, 0, None, None, None)
                    calender_act_e = model.createIfcDateAndTime(date_act_e,time_act_e)
                else:
                    calender_act_e = None
                control_set = model.createIfcScheduleTimeControl(control_set_guid, owner[0], None, "hasdw", "asdw", calender_act_s, None, None, calender_plan_s, calender_act_e, None, None, calender_plan_e, float(rowdata[j][5]), None, None, None, None, None, None, None, None, None)
                if len(schedule_set) is 1:
                    what=model.createIfcRelAssignsTasks(rel_guid, owner[0], None, None, [task_set], None, schedule_set[0], control_set)
                else:
                    what=model.createIfcRelAssignsTasks(rel_guid, owner[0], None, None, [task_set], None, schedule_set, control_set)
                j+=1
                ###---create process from task to objekt
            k = 0
            task = model.by_type("IfcTask")
            for i in rowdata:
                process_set_guid = ifcopenshell.guid.compress(uuid.uuid1().hex)
                if rowdata[k][10]is not None:
                    test = rowdata[k][10].split(',')
                    #
                    if len(test) > 1:
                        obj = []
                        for l in test:
                            obj.append(model.by_id(int(l)))
                        sts=model.createIfcRelAssignsToProcess(process_set_guid, owner[0], None, None, obj, None, task[k], None)
                    else:
                        one_obj = model.by_id(int(rowdata[k][10]))
                        st=model.createIfcRelAssignsToProcess(process_set_guid, owner[0], None, None, [one_obj], None, task[k], None)
                k+=1
            model.write(filename_string)
            #print("writing down")

        def handleImport(self):
            path = QtGui.QFileDialog.getOpenFileName(
                self, 'Open File', '', 'CSV(*.csv)')
            with open(unicode(path), 'rb') as stream:
                t.setRowCount(0)
                t.setColumnCount(0)
                for rowdata in csv.reader(stream):
                    row = t.rowCount()
                    t.insertRow(row)
                    t.setColumnCount(len(rowdata))
                    for column, data in enumerate(rowdata):
                        item = QtGui.QTableWidgetItem(data.decode('utf8'))
                        t.setItem(row, column, item)

        def handleExport(self):
            path = QtGui.QFileDialog.getSaveFileName(
                    self, 'Save File', '', 'CSV(*.csv)')
            with open(unicode(path), 'wb') as stream:
                writer = csv.writer(stream)
                for row in range(t.rowCount()):
                    rowdata = []
                    for column in range(t.columnCount()):
                        item = t.item(row, column)
                        if item is not None:
                            rowdata.append(
                                unicode(item.text()).encode('utf8'))
                        else:
                            rowdata.append('')
                    writer.writerow(rowdata)

        def d_row(self):
            rowPosition = t.currentRow()
            t.removeRow(rowPosition)

        def a_rowo(self):
            rowPosition = t.currentRow()
            t.insertRow(rowPosition)

        def a_rowu(self):
            rowPosition =t.currentRow()
            t.insertRow(rowPosition+1)

        def test(self):
            global t
            header = ["ID", "Number", "Name", "Planned Start", "Planned End","Duration", "Milestone", "Actual Start", "Actual End", "Method","Assignment"]
            width = [40,60,200,100,100,60,60,100,100,100,200]
            t = QtGui.QTableWidget()
            rowlen = len(header)
            t.setColumnCount(rowlen)
            t.setRowCount(1)
            i = 0
            for a in width:
                t.setColumnWidth(i,a)
                i+= 1
            t.setHorizontalHeaderLabels(header)
            vert = t.verticalHeader()
            vert.hide()
            self.setCentralWidget(t)

    class viewer(qtViewer3d):

        instanceSelected = QtCore.pyqtSignal([object])
        print(instanceSelected)
        @staticmethod
        def ais_to_key(ais_handle):
            def yield_shapes():
                ais = ais_handle.GetObject()
                if hasattr(ais, 'Shape'):
                    yield ais.Shape()
                    return
                shp = OCC.AIS.Handle_AIS_Shape.DownCast(ais_handle)
                if not shp.IsNull(): yield shp.Shape()
                return
                mult = ais_handle
                if mult.IsNull():
                    shp = OCC.AIS.Handle_AIS_Shape.DownCast(ais_handle)
                    if not shp.IsNull(): yield shp
                else:
                    li = mult.GetObject().ConnectedTo()
                    for i in range(li.Length()):
                        shp = OCC.AIS.Handle_AIS_Shape.DownCast(li.Value(i+1))
                        if not shp.IsNull(): yield shp
            return tuple(shp.HashCode(1 << 24) for shp in yield_shapes())

        def __init__(self, widget):
            qtViewer3d.__init__(self, widget)
            self.ais_to_product = {}
            self.product_to_ais = {}
            self.counter = 0
            self.window = widget
            #self.color()

        def initialize(self):
            self.InitDriver()
            self._display.Select = self.HandleSelection

        def load_file(self, f, setting=None):

            if setting is None:
                setting = settings()
                setting.set(setting.USE_PYTHON_OPENCASCADE, True)

            v = self._display

            t = {0: time.time()}
            def update(dt = None):
                t1 = time.time()
                if t1 - t[0] > (dt or -1):
                    v.FitAll()
                    v.Repaint()
                    t[0] = t1

            terminate = [False]
            self.window.window_closed.connect(lambda *args: operator.setitem(terminate, 0, True))

            t0 = time.time()

            it = iterator(setting, f)
            if not it.initialize():
                return

            old_progress = -1
            while True:
                if terminate[0]: break
                shape = it.get()
                product = f[shape.data.id]
                ais = display_shape(shape, viewer_handle=v)
                ais.GetObject().SetSelectionPriority(self.counter)
                self.ais_to_product[self.counter] = product
                self.product_to_ais[product] = ais
                self.counter += 1
                QtGui.QApplication.processEvents()
                if product.is_a() in {'IfcSpace', 'IfcOpeningElement'}:
                    v.Context.Erase(ais, True)
                progress = it.progress() // 2
                if progress > old_progress:
                    print("\r[" + "#" * progress + " " * (50 - progress) + "]", end="")
                    old_progress = progress
                if not it.next():
                    break
                update(0.2)

            print("\rOpened file in %.2f seconds%s" % (time.time() - t0, " "*25))

            update()

        def select(self, product):
            ais = self.product_to_ais.get(product)
            if ais is None: return
            v = self._display.Context
            v.ClearSelected(False)
            v.SetSelected(ais, True)

        def set_color(self, product, red, green, blue):
            qclr = OCC.Quantity.Quantity_Color(red,green,blue, OCC.Quantity.Quantity_TOC_RGB)
            ais_shape = self.product_to_ais.get(product)
            ais = ais_shape.GetObject()
            ais.SetColor(qclr)
            self.update()

        def get_selection_set(self,model):
           selection_set =[]
           for p in model.by_type("IfcProduct"):
               ais = self.product_to_ais.get(p)
               if ais != None:
                   if self._display.Context.IsSelected(ais):
                       selection_set.append(p)
           # print(selection_set)
           return selection_set

        def set_transparency (self, product, transp):
            ais_shape = self.product_to_ais.get(product)
            ais = ais_shape.GetObject()
            ais.SetTransparency(transp)

        def toggle(self, product_or_products, fn):
            if not isinstance(product_or_products, Iterable):
                product_or_products = [product_or_products]
            aiss = list(filter(None, map(self.product_to_ais.get, product_or_products)))
            last = len(aiss) - 1
            for i, ais in enumerate(aiss):
                fn(ais, i == last)

        def toggle_visibility(self, product_or_products, flag):
            v = self._display.Context
            if flag:
                def visibility(ais, last):
                    v.Erase(ais, last)
            else:
                def visibility(ais, last):
                    v.Display(ais, last)
            self.toggle(product_or_products, visibility)

        def toggle_wireframe(self, product_or_products, flag):
            v = self._display.Context
            if flag:
                def wireframe(ais, last):
                    if v.IsDisplayed(ais):
                        v.SetDisplayMode(ais, 0, last)
            else:
                def wireframe(ais, last):
                    if v.IsDisplayed(ais):
                        v.SetDisplayMode(ais, 1, last)
            self.toggle(product_or_products, wireframe)

        def HandleSelection(self, X, Y):
            v = self._display.Context
            v.Select()
            v.InitSelected()
            if v.MoreSelected():
                ais = v.SelectedInteractive()
                inst = self.ais_to_product[ais.GetObject().SelectionPriority()]
                self.instanceSelected.emit(inst)

    class window(QtGui.QMainWindow):

        TITLE = "IfcOpenShell IFC viewer"

        window_closed = QtCore.pyqtSignal([])

        def __init__(self):
            QtGui.QMainWindow.__init__(self)
            self.setWindowTitle(self.TITLE)
            self.menu = self.menuBar()
            self.menus = {}

        def closeEvent(self, *args):
            self.window_closed.emit()

        def add_menu_item(self, menu, label, callback, icon=None, shortcut=None):
            m = self.menus.get(menu)
            if m is None:
                m = self.menu.addMenu(menu)
                self.menus[menu] = m

            if icon:
                a = QtGui.QAction(QtGui.QIcon(icon), label, self)
            else:
                a = QtGui.QAction(label, self)

            if shortcut:
                a.setShortcut(shortcut)

            a.triggered.connect(callback)
            m.addAction(a)

    def makeSelectionHandler(self, component):
        def handler(inst):
            for c in self.components:
                if c != component:
                    c.select(inst)
        return handler

    def __init__(self, settings=None):
        QtGui.QApplication.__init__(self, sys.argv)
        self.window = application.window()
        self.tree = application.decomposition_treeview()
        self.tree2 = application.type_treeview()
        self.propview = self.property_table()
        self.canvas = application.viewer(self.window)
        self.custom = self.task_table()
        self.tabs = QtGui.QTabWidget()
        self.window.resize(1280, 720)
        splitter = QtGui.QSplitter(QtCore.Qt.Horizontal)
        splitter.addWidget(self.tabs)
        self.tabs.addTab(self.tree, 'Decomposition')
        self.tabs.addTab(self.tree2, 'Types')
        self.tabs.addTab(self.propview, "Properties")
        self.tabs.addTab(self.custom, "Schedule")
        splitter2 = QtGui.QSplitter(QtCore.Qt.Horizontal)
        splitter2.addWidget(self.canvas)
        self.editor = code_edit(self.canvas, configuration())

        codeDockWidget = QtGui.QDockWidget("Script Code Editor")
        codeDockWidget.setObjectName("codeDockWidget")
        codeDockWidget.setWidget(self.editor)
        codeDockWidget.setAllowedAreas(QtCore.Qt.LeftDockWidgetArea
                                         | QtCore.Qt.RightDockWidgetArea
                                         | QtCore.Qt.BottomDockWidgetArea
                                         | QtCore.Qt.TopDockWidgetArea)
        self.window.addDockWidget(QtCore.Qt.RightDockWidgetArea, codeDockWidget)



        # splitter2.addWidget(self.editor)
        splitter.addWidget(splitter2)
        splitter.setSizes([300,600])
        splitter2.setSizes([400,200])
        self.window.setCentralWidget(splitter)
        self.canvas.initialize()
        self.components = [self.tree, self.tree2, self.canvas,self.custom, self.propview, self.editor]
        self.files = {}
        self.window.add_menu_item('File', '&Open', self.browse, shortcut='CTRL+O')
        self.window.add_menu_item('File', '&Schedule4D', self.schedule4D, shortcut='CTRL+t')
        self.window.add_menu_item('File', '&Close', self.clear, shortcut='CTRL+W')
        self.window.add_menu_item('File', '&Exit', self.window.close, shortcut='ALT+F4')

        self.tree.instanceSelected.connect(self.makeSelectionHandler(self.tree))
        self.tree2.instanceSelected.connect(self.makeSelectionHandler(self.tree2))
        self.canvas.instanceSelected.connect(self.makeSelectionHandler(self.canvas))
        for t in [self.tree, self.tree2]:
            t.instanceVisibilityChanged.connect(functools.partial(self.change_visibility, t))
            t.instanceDisplayModeChanged.connect(functools.partial(self.change_displaymode, t))
        # self.window.statusBar().showMessage('Ready')
        self.settings = settings

    def change_visibility(self, tree, inst, flag):
        insts = tree.get_children(inst)
        self.canvas.toggle_visibility(insts, flag)

    def change_displaymode(self, tree, inst, flag):
        insts = tree.get_children(inst)
        self.canvas.toggle_wireframe(insts, flag)

    def start(self):
        self.window.show()
        sys.exit(self.exec_())

    def browse(self):
        filename = QtGui.QFileDialog.getOpenFileName(self.window, 'Open file',".","Industry Foundation Classes (*.ifc)")
        self.load(filename)

    def schedule4D(self):
        model = models[list(models)[0]]
        viewer = self.canvas
        content = []
        conten =[]
        conte =[]
        cont =[]
        obs =[]
        for i in range(t.rowCount()):
            try: content.append(unicode(t.item(i,10).text()).encode("utf8"))
            except: continue
        for j in content:
            if j is not '':
                conten.append(j)
        for k in conten:
            conte.append(k.split(', '))
        for l in conte:
            if len(l) > 1:
                adds =[]
                for g in l:
                    adds.append(g)
                for str in adds:
                    cont.append(str)
            else:
                cont.append(l[0])
        for g in cont:
            obs.append(model.by_id(int(g)))
        for p in obs:
            viewer.set_color(p,0,0,1)

    def clear(self):
        self.canvas._display.Context.RemoveAll()
        self.tree.clear()
        self.tree2.clear()
        self.files.clear()
        
    def load(self, fn):
        if fn in self.files: return        
        f = open_ifc_file(str(fn))
        self.files[fn] = f
        global models
        models[fn] = f
        for c in self.components:
            c.load_file(f, setting=self.settings)

if __name__ == "__main__":
    application().start()
