#!/opt/homebrew/bin/python3.11
'''script to test STL specifications'''
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

# stl = STL()
# stl.AND(stl.EVENTUALLY(0, 1, REACH(stl.main, 0, 1)), stl.EVENTUALLY(4, 5, REACH(stl.main, 2, 3)))
# stl.AND(stl.EVENTUALLY(0, 1, REACH(stl.main, 0, 1, 0, 1)), stl.EVENTUALLY(4, 5, REACH(stl.main, 2, 3, 2, 3)))
# stl.AND(stl.EVENTUALLY(0, 1, REACH(stl.main, 0, 1, 0, 1, 0, 1)), stl.EVENTUALLY(4, 5, REACH(stl.main, 2, 3, 2, 3, 2, 3)))

# obj = AND(stl.EVENTUALLY(0, 1, REACH(stl.main, 0, 1)), stl.EVENTUALLY(4, 5, REACH(stl.main, 2, 3)))
# obj.call()

# stl.plotter()


# eventually1 = EVENTUALLY(REACH(0, 1))
# eventually2 = EVENTUALLY(REACH(2, 3))
# eventually1.EVENTUALLY()

# and1 = AND(eventually1.EVENTUALLY(), eventually2.EVENTUALLY())
# and2 = AND(eventually1.EVENTUALLY(), eventually2.EVENTUALLY())

# or1 = OR(and1.AND(), and2.AND())
# or1.OR()

# ########### in one line ###########
# semantic_constraints.return_value = False
# semantic_constraints = OR(AND(EVENTUALLY(REACH(0, 1)).EVENTUALLY(), EVENTUALLY(REACH(2, 3)).EVENTUALLY()), AND(EVENTUALLY(REACH(0, 1)).EVENTUALLY(), EVENTUALLY(REACH(2, 3)).EVENTUALLY()).AND)

# SOLVER(semantic_constraints.call())
# SOLVER.allSolutions()


stl2 = STL(1, SeqReachAvoidStay(2, 3, 0.05, 1))
obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3, 2, 3, 2, 3)).call()).call()
stl2.plotter()

# stl3 = STL(2, SeqReachAvoidStay(2, 1, 0.05, 1))
# obj3 = AND(2, stl3.EVENTUALLY(0, 1, REACH(stl3.main, 0, 1)), stl3.EVENTUALLY(4, 5, REACH(stl3.main, 2, 3)))
# obj3.call()
# stl3.plotter()




# degree 3
# add reach 2 min 20 sec
# solver 16 sec






# stl.AND(stl.EVENTUALLY(0, 0.3, REACH(-0.5, 0.5, -0.5, 0.5, stl.main)), stl.EVENTUALLY(4.8, 5, REACH(3.5, 5, 3.5, 5, stl.main)))#, stl.ALWAYS(2, 3, AVOID(2, 2.5, 2.3, 3, stl.main)))
# stl.OR(stl.EVENTUALLY(2, 3, REACH(1, 1.5, 2.3, 3)), stl.EVENTUALLY(2, 3, REACH(3, 3.5, 2.3, 3)))
# stl.AND(stl.EVENTUALLY(2, 3, REACH(1, 2, 2, 3, stl.main)))

########################################################## CASE 1 ##########################################################

#        x1     x2    y1     y2    t1    t2
# REACH( -0.5,  0.5,  -0.5,  0.5,  0  ,  0.3)
# REACH( 3.5 ,  5  ,  3.5 ,  5  ,  4.8,  5  )
# AVOID( 2   ,  2.5,  2.3 ,  3  ,  2  ,  3  )

# [-0.4831309     ,  1.84008097    ,  -0.17004049   ,  0.03373819    ,  1.84008097     , -0.17004049    ]
# [-0.4           ,  -0.1          ,  0.2           ,  0.10990099    ,  -0.1           , 0.2            ]
# [-0.48          ,  -0.07         ,  0.21          ,  0.42985775    ,  -0.1881053     , 0.21985775     ]
# [-0.47          ,  0.01          ,  0.17152778    ,  0.1197        ,  -0.0603        , 0.1997         ]
# [-0.41          ,  0.02          ,  0.16597661    ,  0.48989899    ,  -0.17010101    , 0.18989899     ]
# [-4.60000000e-01,  5.87382501e-02,  1.59932188e-01,  9.00000000e-02,  -6.78120980e-05,  1.79932188e-01]
# [-0.43302328    ,  0.09997672    ,  0.14997672    ,  0.37997672    ,  -0.05          , 0.16997672     ] 
# [-0.45          ,  0.26          ,  0.13366251    ,  0.05990099    ,  0.26           , 0.13366251     ]
# [-0.43          ,  -0.02         ,  0.18          ,  0.16          ,  0.18968496     , 0.14351336     ]
# [-0.42          ,  -0.03         ,  0.19          ,  0.14          ,  0.17987828     , 0.15135737     ]