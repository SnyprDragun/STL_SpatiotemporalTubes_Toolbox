#!/opt/homebrew/bin/python3.11
# This is an automatically generated Python script
from CombinedToolbox import *

stl_obj_1 = STL(1, SeqReachAvoidStay(10, 1, 0.5, 1))
obj = ALWAYS(1,2,EVENTUALLY(1,0,REACH(stl_obj_1.main, 0)))
obj.return_value = False
obj.call()
stl_obj_1.plotter()