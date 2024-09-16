#!/opt/homebrew/bin/python3.11
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
obj = AND(1, OR(1, EVENTUALLY(1, 0, 1, REACH([0])), EVENTUALLY(1, 0, 1, REACH([0]))), AND(1, ALWAYS(1, 2, 3, AVOID([0])), ALWAYS(1, 2, 3, AVOID([0]))))