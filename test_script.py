#!/usr/bin/env python3
# This is an automatically generated Python script
from seq_reach_avoid_stay import *
from stl_main import *
from action_classes import *

print("Hello from the new Python file!")
x = 5
y = 10
print(f"The sum of {x} and {y} is: {x + y}")

stl_obj_1 = STL(1, SeqReachAvoidStay(10, 1, 0.5, 1))
obj = AND(1,AND(1,OR(1,EVENTUALLY(1,0,1,REACH(stl_obj_1.main, 0, 1)),EVENTUALLY(1,1,2,REACH(stl_obj_1.main, 1, 2))),EVENTUALLY(1,2,3,REACH(stl_obj_1.main, 2, 3))),AND(1,ALWAYS(1,3,4,AVOID(stl_obj_1.main, 3, 4)),ALWAYS(1,4,5,AVOID(stl_obj_1.main, 4, 5)),ALWAYS(1,5,6,AVOID(stl_obj_1.main, 5, 6))))
obj.return_value = False
obj.call()
stl_obj_1.plotter()