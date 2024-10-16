#!/usr/bin/env python3
# This is an automatically generated Python script
from solver import *
from stl_main import *
from text_to_stl import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

print("Hello from the new Python file!")
x = 5
y = 10
print(f"The sum of {x} and {y} is: {x + y}")

stl_obj_1 = STL(1, SeqReachAvoidStay(10, 1, 0.5, 1))
obj = AND(1,OR(1,OR(1,EVENTUALLY(1,((REACH(stl_obj_1, 1, 2)))),EVENTUALLY(1,((REACH(stl_obj_1, 2, 3))))),EVENTUALLY(1,((REACH(stl_obj_1, 3, 4))))),AND(1,ALWAYS(1,AVOID(stl_obj_1, 4, 5)),ALWAYS(1,AVOID(stl_obj_1, 5, 6)),ALWAYS(1,AVOID(stl_obj_1, 6, 7))))
obj.call()