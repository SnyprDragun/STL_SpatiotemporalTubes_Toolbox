#!/usr/bin/env python3
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

stl2 = STL(1, SeqReachAvoidStay(7, 2, 0.05, 1))
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

## doesnt work (actually works, just that zero error shit, the start is 14 for code, 
# but for plot it is 0, so thats all the crazyness, my code worksss 😭😭😭😭😭😭😭😭
# for OR case, always give a reference, and fix plotting issue, plot should be from start to end)
# OR(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
#          # EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)),
#          # EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)),
#          EVENTUALLY(1, 14, 15, REACH(stl2.main, 4, 5, 4, 5))).call()

# AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call()).call()

## works
# obj2 = OR(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#          # EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)).call(),
#          # EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)).call(),
#          EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call2()


obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
               EVENTUALLY(1, 4, 5, REACH(stl2.main, 7, 8, 11, 12)).call(),
               EVENTUALLY(1, 8, 9, REACH(stl2.main, 10, 11, 4, 5)).call(),
               EVENTUALLY(1, 12, 13, REACH(stl2.main, 7, 8, 11, 12)).call(),
            #    EVENTUALLY(1, 11, 12, REACH(stl2.main, 7, 8, 7, 8)).call(),
               EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()
            ).call()



# obj3 = AND(1, EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()).call()
# obj4 = AND(1, EVENTUALLY(1, 1, 2, REACH(stl2.main, 1, 2, 1, 2)).call()).call()
stl2.plotter()

# need to add or constraints properly
# the call() method has to be timed correctly
# toolbox has zero error, i.e. all semantics must start from zero (plotting issue)
# OR constraints are a mess, also need to handle for OR AND concatenation


# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1]]
# Time taken:  0 hours,  0 minutes,  0.27 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [2, 3, 5, 6, 2, 3]]
# Time taken:  0 hours,  0 minutes,  0.28 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [2, 3, 5, 6, 2, 3], [7, 8, 3, 4, 5, 6]]
# Time taken:  0 hours,  0 minutes,  0.27 seconds
# Solving...
# C0 = 0.707592343632889
# C1 = 0.761038811743221
# C2 = -4.405038532263898
# C3 = 6.157309126243847
# C4 = -3.2817707416761035
# C5 = 0.8239145240734465
# C6 = -0.09728601920283335
# C7 = 0.004340403636294661
# C8 = 0.5566546685411149
# C9 = -3.7217155856927864
# C10 = 3.8316751253847716
# C11 = 1.4778136458548294
# C12 = -1.8326770201310199
# C13 = 0.5500167969516585
# C14 = -0.06952943385770247
# C15 = 0.0032521334850075345
# C16 = 1.2387468072788392
# C17 = 0.38642563151983406
# C18 = -3.0669868489827157
# C19 = 5.033745682864649
# C20 = -2.7869326342408463
# C21 = 0.6973782281322062
# C22 = -0.0801925151804452
# C23 = 0.003419468575000197
# C24 = 1.087809132187065
# C25 = -4.096328765916173
# C26 = 5.1697268086659545
# C27 = 0.3542502024756307
# C28 = -1.3378389126957626
# C29 = 0.4234805010104182
# C30 = -0.05243592983531434
# C31 = 0.0023311984237130703

# 25 mins











                #####        #####       #####       #######
               ##   ##      ##   ##      ##  ##      ##  
              ##           ##     ##     ##   ##     #### 
              ##           ##     ##     ##   ##     ####
               ##   ##      ##   ##      ##  ##      ## 
                #####        #####       #####       #######

#####      ##     ##     ###    ##     ###    ##     ##     ###    ##     #####
##  ##     ##     ##     ####   ##     ####   ##     ##     ####   ##    ##
##  ##     ##     ##     ## ##  ##     ## ##  ##     ##     ## ##  ##   ##
## ##      ##     ##     ##  ## ##     ##  ## ##     ##     ##  ## ##   ##   ### 
##  ##      ##   ##      ##   ####     ##   ####     ##     ##   ####    ##   ##
##   ##      #####       ##    ###     ##    ###     ##     ##    ###     #####

