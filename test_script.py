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
obj = AND(1,OR(1,OR(1,EVENTUALLY(1,((REACH(T1)))),EVENTUALLY(1,((REACH(T2))))),EVENTUALLY(1,((REACH(T3))))),AND(1,ALWAYS(1,AVOID(O1)),ALWAYS(1,AVOID(O2)),ALWAYS(1,AVOID(O3))))