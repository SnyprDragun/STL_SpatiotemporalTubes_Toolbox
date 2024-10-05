#!/usr/bin/env python3
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

stl2 = STL(1, SeqReachAvoidStay(12, 2, 0.1, 1))
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3, 2, 3))).call()
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3)).call()).call()
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3)).call()).call()

#------------ DRONE CASE------------#
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, -1, 2, -1, 2, 1, 4)), 
#             EVENTUALLY(1, 14, 15, REACH(stl2.main, 12, 15, 12, 15, 12, 15)),
#             OR(1, EVENTUALLY(1, 7, 8, REACH(stl2.main, 9, 12, 6, 9, 6, 9)), 
#                     EVENTUALLY(1, 7, 8, REACH(stl2.main, 3, 6, 6, 9, 6, 9))
#                 ),
#             ALWAYS(1, 0, 15, AVOID(stl2.main, 6, 9, 6, 11, 0, 15)),
#         ).call()
#-----------------------------------#

# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), 
#             # EVENTUALLY(1, 4, 5, REACH(stl2.main, 4, 5, 5, 6, 4, 5)).call(), 
#             EVENTUALLY(1, 6, 7, REACH(stl2.main, 6, 7, 5, 6, 4, 5)).call(), 
#             EVENTUALLY(1, 10, 11, REACH(stl2.main, 10, 11, 10, 11, 10, 11)).call(), 
#             ALWAYS(1, 2, 7, AVOID(stl2.main, 5, 6, 5, 6, 4, 5)).call()
#             ).call()



# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), 
#             EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8, 7, 8)).call(), 
#             # EVENTUALLY(1, 6, 7, REACH(stl2.main, 6, 7, 5, 6, 4, 5)).call(), 
#             EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 1, 2, 14, 15)).call(), 
#             # ALWAYS(1, 2, 7, AVOID(stl2.main, 5, 6, 5, 6, 4, 5)).call()
#             ).call()

# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
#             EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8)), 
#             # EVENTUALLY(1, 6, 7, REACH(stl2.main, 6, 7, 5, 6, 4, 5)), 
#             # EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15))
#             # ALWAYS(1, 2, 7, AVOID(stl2.main, 5, 6, 5, 6, 4, 5)).call()
#             ).call()


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

########## return the function call that is returmimg something😭😭😭😭
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
#         OR(1, EVENTUALLY(1, 2, 3, REACH(stl2.main, 2, 3, 2, 3)),
#                EVENTUALLY(1, 7, 8, REACH(stl2.main, 7, 8, 7, 8))
#             ),
#                EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15))) # 5min 31sec
# obj2.call()


# obj2 = AND(1, IMPLIES(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)),
#                         EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15)))) # 5min 31sec
# obj2.call()


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
obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
               EVENTUALLY(1, 3, 4, REACH(stl2.main, 7, 8, 11, 12)),
               EVENTUALLY(1, 6, 7, REACH(stl2.main, 10, 11, 7, 8)),
               EVENTUALLY(1, 9, 10, REACH(stl2.main, 7, 8, 11, 12)),
               EVENTUALLY(1, 12, 13, REACH(stl2.main, 11, 12, 7, 8)),
               EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15))
            ).call()

# OR CASE EXAMPLE
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)).call(), 
#                # EVENTUALLY(1, 4, 5, REACH(stl2.main, 4, 5, 5, 6)).call(),
#                EVENTUALLY(1, 4, 5, REACH(stl2.main, 6, 7, 5, 6)).call(),
#                EVENTUALLY(1, 10, 11, REACH(stl2.main, 9, 10, 9, 10)).call(),
#             #    ALWAYS(1, 4, 6, AVOID(stl2.main, 5, 6, 2, 6)).call()
#             ).call()


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


# STAY
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1]]
# Time taken:  0 days,  0 hours,  0 minutes,  0.26 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 7, 8, 7, 8]]
# Time taken:  0 days,  0 hours,  0 minutes,  0.53 seconds
# Added Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 7, 8, 7, 8], [14, 15, 14, 15, 12, 15]]
# Time taken:  0 days,  0 hours,  0 minutes,  1 seconds
# Solving...
# C0 = 0.4997518379140666
# C1 = -2.4712022077233744
# C2 = 3.4551157740834415
# C3 = -1.013238004066181
# C4 = 0.12718614259014793
# C5 = -0.007212079336623855
# C6 = 0.00015196252593303714
# C7 = 0.4997518379140666
# C8 = -2.4712022077233744
# C9 = 3.4551157740834415
# C10 = -1.013238004066181
# C11 = 0.12718614259014793
# C12 = -0.007212079336623855
# C13 = 0.00015196252593303714
# C14 = 0.9998759189570333
# C15 = -2.4712022077233744
# C16 = 3.4551157740834415
# C17 = -1.013238004066181
# C18 = 0.12718614259014793
# C19 = -0.007212079336623855
# C20 = 0.00015196252593303714
# C21 = 0.9998759189570333
# C22 = -2.4712022077233744
# C23 = 3.4551157740834415
# C24 = -1.013238004066181
# C25 = 0.12718614259014793
# C26 = -0.007212079336623855
# C27 = 0.00015196252593303714
# gamma_dot for x_upper max =  2.7278492633898637
# gamma_dot for x_lower max =  2.7278492633898637
# gamma_dot for y_upper max =  2.7278492633898637
# gamma_dot for y_lower max =  2.7278492633898637
# range:  301 
# start:  0 
# finish:  15 
# step:  0.05
# Time taken:  0 days,  3 hours,  2 minutes,  39 seconds




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
# # range:  221 
# start:  0 
# finish:  11 
# step:  0.05
# Time taken:  0 hours,  37 minutes,  35 seconds


# C_fin = [C0, C1, C2, C3, C4, C5,
#          C6, C7, C8, C9, C10, C11,
#          C12, C13, C14, C15, C16, C17,
#          C18, C19, C20, C21, C22, C23]
# stl2.main.setStart(0)
# stl2.main.setRange(220)
# stl2.main.setFinish(15)
# stl2.main.plot_for_2D(C_fin)

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






# -------------------------------------- ALWAYS-EVENTUALLY EXAMPLE -------------------------------------- #
# Reach Constraints:  [[0, 1, 0, 1, 0, 1], [7, 8, 11, 12, 3, 4], [10, 11, 7, 8, 6, 7], [7, 8, 11, 12, 9, 10], [11, 12, 7, 8, 12, 13], [14, 15, 14, 15, 14, 15]]
# C0 = 0.08333333333333333
# C1 = -5.817436030541716
# C2 = 18.42434361623948
# C3 = -13.95526959737941
# C4 = 5.298201103203326
# C5 = -1.1646603810073652
# C6 = 0.15232477853262447
# C7 = -0.010408960326033685
# C8 = 0.0
# C9 = 6.641565062178928e-05
# C10 = -5.7836284132781364e-06
# C11 = 2.2218992013231217e-07
# C12 = -3.3709706402282637e-09
# C13 = 0.08333333333333333
# C14 = -0.5644011695585874
# C15 = 1.4730509589736605
# C16 = 1.7656366115500863
# C17 = -0.9428363835173661
# C18 = 0.04409656710255154
# C19 = 0.057870859988860546
# C20 = -0.01664561149694609
# C21 = 0.002216675443836667
# C22 = -0.00016877638634275402
# C23 = 7.509226919078036e-06
# C24 = -1.8073326755822833e-07
# C25 = 1.797148064281541e-09
# C26 = 0.9166666666666666
# C27 = -8.03045020496731
# C28 = 23.8758114499262
# C29 = -19.114204479901467
# C30 = 7.866317700941796
# C31 = -1.9403011149956013
# C32 = 0.30536754431523905
# C33 = -0.03088014010876313
# C34 = 0.0018780373654999922
# C35 = -5.0357461614743235e-05
# C36 = -1.0682350059652324e-06
# C37 = 1.1039516193943358e-07
# C38 = -2.188198426960021e-09
# C39 = 0.6666666666666666
# C40 = -0.4762809678792631
# C41 = 1.088734647470142
# C42 = 2.3708487659866515
# C43 = -1.4121941399387143
# C44 = 0.25305617203885217
# C45 = 0.0
# C46 = -0.006254620144161909
# C47 = 0.000988294758218591
# C48 = -7.394827589892189e-05
# C49 = 2.911844965333087e-06
# C50 = -5.374330168041333e-08
# C51 = 2.730628516158349e-10

# -------------------------------------- DRONE EXAMPLE -------------------------------------- #

#------------------ DRONE OR CASE FIRST BLOCK ------------------#
# Reach Constraints:  [[-1, 2, -1, 2, 1, 4, 0, 1], [12, 15, 12, 15, 12, 15, 14, 15], [9, 12, 6, 9, 6, 9, 7, 8]]
# Avoid Constraints:  [[6, 9, 6, 11, 0, 15, 0, 15]]
# C0 = -0.5092201124440394
# C1 = -1.665740011109661
# C2 = 1.542484516723121
# C3 = -0.3243109601139466
# C4 = 0.026244366716944464
# C5 = -0.0007154516946045534
# C6 = -0.5092201124440394
# C7 = -0.9354351139789893
# C8 = 0.8798053580061804
# C9 = -0.15421328533867962
# C10 = 0.011825144550615181
# C11 = -0.00032995786104859844
# C12 = 1.4907798875559606
# C13 = -0.14819509743468093
# C14 = 0.32437796115886813
# C15 = -0.058556349964849215
# C16 = 0.0052465859553120706
# C17 = -0.0001699023672777245
# C18 = 1.9953899437779803
# C19 = -1.6883828104673564
# C20 = 1.5955854133448955
# C21 = -0.34080413875938786
# C22 = 0.02799927661790214
# C23 = -0.0007749401658234577
# C24 = 1.9953899437779803
# C25 = -0.9354351139789893
# C26 = 0.8798053580061804
# C27 = -0.15421328533867962
# C28 = 0.011825144550615181
# C29 = -0.00032995786104859844
# C30 = 3.99538994377798
# C31 = -0.14819509743468093
# C32 = 0.32437796115886813
# C33 = -0.058556349964849215
# C34 = 0.0052465859553120706
# C35 = -0.0001699023672777245


#------------------ DRONE OR CASE SECOND BLOCK ------------------#
# Reach Constraints:  [[-1, 2, -1, 2, 1, 4, 0, 1], [12, 15, 12, 15, 12, 15, 14, 15], [9, 12, 6, 9, 6, 9, 7, 8]]
# Avoid Constraints:  [[6, 9, 6, 9, 0, 15, 0, 15]]
# C0 = -0.9947193621508238
# C1 = 0.4277863285546202
# C2 = 1.2140297298487956
# C3 = -0.27679682188266586
# C4 = 0.02200792560735738
# C5 = -0.0005888928692527835
# C6 = -0.5105612756983524
# C7 = -1.4667281217292212
# C8 = 1.0843122115171406
# C9 = -0.18152804910001696
# C10 = 0.013280466284529367
# C11 = -0.0003552471176615102
# C12 = 1.4894387243016476
# C13 = -1.27618875247245
# C14 = 0.655150320834794
# C15 = -0.08099965733727106
# C16 = 0.004422992408222249
# C17 = -8.864906559813607e-05
# C18 = 1.5105612756983524
# C19 = 0.4277863285546202
# C20 = 1.2140297298487956
# C21 = -0.27679682188266586
# C22 = 0.02200792560735738
# C23 = -0.0005888928692527835
# C24 = 1.994719362150824
# C25 = -1.4667281217292212
# C26 = 1.0843122115171406
# C27 = -0.18152804910001696
# C28 = 0.013280466284529367
# C29 = -0.0003552471176615102
# C30 = 3.994719362150824
# C31 = -1.27618875247245
# C32 = 0.655150320834794
# C33 = -0.08099965733727106
# C34 = 0.004422992408222249
# C35 = -8.864906559813607e-05