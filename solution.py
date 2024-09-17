#!/opt/homebrew/bin/python3.11
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

stl2 = STL(1, SeqReachAvoidStay(3, 2, 0.05, 1))
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3, 2, 3)).call()).call()
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3)).call()).call()
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3)).call()).call()


# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#             EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call(), 
#             ALWAYS(1, 7, 8, AVOID(stl2.main, 7, 8, 7, 8)).call()).call()


obj2 = OR(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
            EVENTUALLY(1, 8, 9, REACH(stl2.main, 8, 9, 8, 9))).call()
# obj3 = AND(1, EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call()
# obj4 = AND(1, EVENTUALLY(1, 1, 2, REACH(stl2.main, 1, 2, 1, 2)).call()).call()

stl2.plotter()

# need to add or constraints properly
# the call() method has to be timed correctly
# toolbox has zero error, i.e. all semantics must start from zero (plotting issue)
