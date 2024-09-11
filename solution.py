#!/opt/homebrew/bin/python3.11
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

stl2 = STL(1, SeqReachAvoidStay(2, 1, 0.05, 1))
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3, 2, 3)).call()).call()
obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3)).call()).call()
stl2.plotter()

# stl3 = STL(2, SeqReachAvoidStay(2, 1, 0.05, 1))
# obj3 = AND(2, stl3.EVENTUALLY(0, 1, REACH(stl3.main, 0, 1)), stl3.EVENTUALLY(4, 5, REACH(stl3.main, 2, 3)))
# obj3.call()
# stl3.plotter()




# degree 3
# add reach 2 min 20 sec
# solver 16 sec
