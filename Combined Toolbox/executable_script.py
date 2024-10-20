#!/opt/homebrew/bin/python3.11
# This is an automatically generated Python script
from CombinedToolbox import *

stl_obj_1 = STL(1, SeqReachAvoidStay(6, 1, 0.4, 1))
# obj = AND(1,AND(1,OR(1,EVENTUALLY(1,0,1,REACH(stl_obj_1.main, 0, 1)),EVENTUALLY(1,1,2,REACH(stl_obj_1.main, 1, 2))),EVENTUALLY(1,2,3,REACH(stl_obj_1.main, 2, 3))),AND(1,ALWAYS(1,3,4,AVOID(stl_obj_1.main, 3, 4)),ALWAYS(1,4,5,AVOID(stl_obj_1.main, 4, 5)),ALWAYS(1,5,6,AVOID(stl_obj_1.main, 5, 6))))
obj = AND(1, EVENTUALLY(1, 0, 1, REACH(stl_obj_1.main, 0, 1)),
                ALWAYS(1, 5, 6, AVOID(stl_obj_1.main, 0, 2)),
            EVENTUALLY(1, 10, 11, REACH(stl_obj_1.main, 0, 1)),
                ALWAYS(1, 15, 16, AVOID(stl_obj_1.main, 0, 2)),
            EVENTUALLY(1, 20, 21, REACH(stl_obj_1.main, 0, 1)))
obj.return_value = False
obj.call()
stl_obj_1.plotter()