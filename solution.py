#!/usr/bin/env python3
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

stl2 = STL(1, SeqReachAvoidStay(10, 2, 0.05, 1))
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3, 2, 3)).call()).call()
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3)).call()).call()
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3)).call()).call()


# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#             EVENTUALLY(1, 3, 4, REACH(stl2.main, 3, 4, 11, 12)).call(),
#             EVENTUALLY(1, 11, 12, REACH(stl2.main, 3, 12, 3, 4)).call(),
#             # EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call(), 
#                 # ALWAYS(1, 7, 8, AVOID(stl2.main, 7, 8, 7, 8)).call()
#                 ).call()

# constraints = [EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#                EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)).call(),
#                EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)).call(),
#                EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()]

# # print(constraints)

# for i in constraints:
#     # for j in i:
#     stl2.main.solver.add(i)

# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#                EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)).call(),
#                EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)).call(),
#                EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call()

## doesnt work
# OR(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
#         # EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)),
#         # EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)),
#         EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15))).call1()

## works
# obj2 = OR(1, EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)).call(), 
#         # EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)).call(),
#         # EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)).call(),
#         EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call2()


obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
               EVENTUALLY(1, 2, 3, REACH(stl2.main, 4, 5, 4, 5)).call(),
               EVENTUALLY(1, 5, 6, REACH(stl2.main, 7, 8, 7, 8)).call(),
               EVENTUALLY(1, 8, 9, REACH(stl2.main, 4, 5, 4, 5)).call(),
            #    EVENTUALLY(1, 11, 12, REACH(stl2.main, 7, 8, 7, 8)).call(),
               EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call()



# obj3 = AND(1, EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call()
# obj4 = AND(1, EVENTUALLY(1, 1, 2, REACH(stl2.main, 1, 2, 1, 2)).call()).call()
stl2.plotter()

# need to add or constraints properly
# the call() method has to be timed correctly
# toolbox has zero error, i.e. all semantics must start from zero (plotting issue)
# OR constraints are a mess, also need to handle for OR AND concatenation














    #####        #####       #####       #######
   ##   ##      ##   ##      ##  ##      ##  
  ##           ##     ##     ##   ##     #### 
  ##           ##     ##     ##   ##     ####
   ##   ##      ##   ##      ##  ##      ## 
    #####        #####       #####       #######

# RUNNING!!!!!!!
