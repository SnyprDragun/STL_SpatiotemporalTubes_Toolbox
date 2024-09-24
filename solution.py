#!/usr/bin/env python3
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

stl2 = STL(1, SeqReachAvoidStay(5, 2, 0.05, 1))
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3, 2, 3)).call()).call()
# obj2 = AND(1, EVENTUALLY(1, 0,- 1, REACH(stl2.main, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3)).call()).call()
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

# ALWAYS EVENTUALLY EXAMPLE
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#                EVENTUALLY(1, 4, 5, REACH(stl2.main, 7, 8, 11, 12)).call(),
#                EVENTUALLY(1, 8, 9, REACH(stl2.main, 10, 11, 4, 5)).call(),
#                EVENTUALLY(1, 12, 13, REACH(stl2.main, 7, 8, 11, 12)).call(),
#             #    EVENTUALLY(1, 11, 12, REACH(stl2.main, 7, 8, 7, 8)).call(),
#                EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)).call()
#             ).call()

# OR CASE EXAMPLE
obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
               # EVENTUALLY(1, 4, 5, REACH(stl2.main, 4, 5, 5, 6)).call(),
               EVENTUALLY(1, 4, 5, REACH(stl2.main, 6, 7, 5, 6)).call(),
               EVENTUALLY(1, 10, 11, REACH(stl2.main, 9, 10, 9, 10)).call(),
               ALWAYS(1, 4, 6, AVOID(stl2.main, 5, 6, 2, 6)).call()
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



# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1]]
# Time taken:  0 hours,  0 minutes,  0.33 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 11, 12, 4, 5]]
# Time taken:  0 hours,  0 minutes,  0.33 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 11, 12, 4, 5], [10, 11, 4, 5, 8, 9]]
# Time taken:  0 hours,  0 minutes,  0.33 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 11, 12, 4, 5], [10, 11, 4, 5, 8, 9], [7, 8, 11, 12, 12, 13]]
# Time taken:  0 hours,  0 minutes,  0.32 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 11, 12, 4, 5], [10, 11, 4, 5, 8, 9], [7, 8, 11, 12, 12, 13], [14, 15, 14, 15, 14, 15]]
# Time taken:  0 hours,  0 minutes,  0.33 seconds
# Solving...
# No solution found.
# range:  301 
# start:  0 
# finish:  15 
# step:  0.05
# Time taken:  26 hours,  37 minutes,  21 seconds








# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1]]
# Time taken:  0 hours,  0 minutes,  0.22 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [4, 5, 5, 6, 4, 5]]
# Time taken:  0 hours,  0 minutes,  0.23 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [4, 5, 5, 6, 4, 5], [9, 10, 9, 10, 10, 11]]
# Time taken:  0 hours,  0 minutes,  0.22 seconds
# Added Avoid Constraints:  [[5, 6, 5, 6, 5, 6]]
# Time taken:  0 hours,  0 minutes,  0.22 seconds
# Solving...
# C0 = -0.49042954184063553
# C1 = 1.0372652849612387
# C2 = 0.021418455987188483
# C3 = -0.012748711136309862
# C4 = 0.002685073375052976
# C5 = -0.0001661976669242473
# C6 = -0.49179351223981954
# C7 = -0.03529816723066544
# C8 = 1.5792618027211525
# C9 = -0.5132629040204001
# C10 = 0.059713893661179795
# C11 = -0.0023153546963445818
# C12 = 0.49397700904924696
# C13 = 1.096665134875751
# C14 = -0.044209705248240645
# C15 = -0.009055315328576095
# C16 = 0.003770471282873895
# C17 = -0.00025198927628639924
# C18 = 0.49534097944843103
# C19 = 0.018128722739422096
# C20 = 1.512815679824099
# C21 = -0.5080551039997402
# C22 = 0.06048724206716131
# C23 = -0.0023835712567075607
# range:  221 
# start:  0 
# finish:  11 
# step:  0.05
# Time taken:  0 hours,  2 minutes,  10 seconds





## OR BLOCK 1
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1]]
# Time taken:  0 hours,  0 minutes,  0.23 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [4, 5, 5, 6, 4, 5]]
# Time taken:  0 hours,  0 minutes,  0.22 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [4, 5, 5, 6, 4, 5], [9, 10, 9, 10, 10, 11]]
# Time taken:  0 hours,  0 minutes,  0.22 seconds
# Added Avoid Constraints:  [[5, 6, 4, 6, 4, 6]]
# Time taken:  0 hours,  0 minutes,  0.44 seconds
# Solving...
# C0 = -0.4910798767118161
# C1 = 0.7355429643227853
# C2 = 0.4760698963391336
# C3 = -0.17407128893137622
# C4 = 0.022477900968591348
# C5 = -0.0009567339178525866
# C6 = 0.5048897675842339
# C7 = -3.923164002625066
# C8 = 4.599222822679576
# C9 = -1.3001491439433137
# C10 = 0.1394624380810051
# C11 = -0.005071678657393034
# C12 = 0.4937438346334281
# C13 = 0.7950485248855055
# C14 = 0.41032494027215394
# C15 = -0.17037132019011675
# C16 = 0.023565230499414083
# C17 = -0.0010426782058267135
# C18 = 1.4924462744941542
# C19 = -3.8696420317553026
# C20 = 4.532658449269559
# C21 = -1.2949320758871838
# C22 = 0.14023716277264062
# C23 = -0.005140016619019229
# range:  221 
# start:  0 
# finish:  11 
# step:  0.05
# Time taken:  0 hours,  27 minutes,  31 seconds


## OR BLOCK 2
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1]]
# Time taken:  0 hours,  0 minutes,  0.21 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [6, 7, 5, 6, 4, 5]]
# Time taken:  0 hours,  0 minutes,  0.21 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [6, 7, 5, 6, 4, 5], [9, 10, 9, 10, 10, 11]]
# Time taken:  0 hours,  0 minutes,  0.21 seconds
# Added Avoid Constraints:  [[5, 6, 2, 6, 4, 6]]
# Time taken:  0 hours,  0 minutes,  0.42 seconds
# Solving...
# C0 = 0.5084855517338179
# C1 = -4.176199055495358
# C2 = 4.994701766390769
# C3 = -1.3957072521525709
# C4 = 0.14743106541097284
# C5 = -0.005282895246749072
# C6 = -0.4972112866723671
# C7 = 0.19697078950054797
# C8 = 1.2146113677064614
# C9 = -0.3735145665185251
# C10 = 0.04232960733314398
# C11 = -0.0016322088336753185
# C12 = 1.4877961638293382
# C13 = -4.083439951904657
# C14 = 4.871789429857199
# C15 = -1.373564709623207
# C16 = 0.146477406951223
# C17 = -0.005295685301531963
# C18 = 0.500929571109211
# C19 = 0.19697078950054797
# C20 = 1.2146113677064614
# C21 = -0.3735145665185251
# C22 = 0.04232960733314398
# C23 = -0.0016322088336753185
# range:  221 
# start:  0 
# finish:  11 
# step:  0.05
# Time taken:  0 hours,  37 minutes,  35 seconds




                #####        #####       #####       #######
               ##   ##      ##   ##      ##  ##      ##  
              ##           ##     ##     ##   ##     #### 
              ##           ##     ##     ##   ##     ####
               ##   ##      ##   ##      ##  ##      ## 
                #####        #####       #####       #######

######      ##     ##     ###    ##     ###    ##     ##     ###    ##     #####
##   ##     ##     ##     ####   ##     ####   ##     ##     ####   ##    ##
##   ##     ##     ##     ## ##  ##     ## ##  ##     ##     ## ##  ##   ##
## ##       ##     ##     ##  ## ##     ##  ## ##     ##     ##  ## ##   ##   ### 
##  ##       ##   ##      ##   ####     ##   ####     ##     ##   ####    ##   ##
##   ##       #####       ##    ###     ##    ###     ##     ##    ###     #####

