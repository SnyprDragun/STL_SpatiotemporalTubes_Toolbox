# STL_STT_Toolbox (Developer's Branch)
This toolbox follows a data-driven approach for generating Spatiotemporal Tubes. Signal Temporal Logic specification is collected from user and z3 solver is used to solve for the constraints for reach-avoid-stay maintaining robustness and safety of trajectory.

## System Requirements
* Python 3.8 or greater
* Numpy, Matplotlib, PyTorch, Z3, Mpl_toolkits
* Windows/MacOS/Linux

## Start locally
* Clone the repo into your system.
* Download and install system requirements if you are missing any.

## Executable inputs
Structure:
Enter - i. STL semantics

Choose b/w - i. Single Agent
            ii. Multi Agent
           iii. Decomposition

Return Item - i. Robust Spatiotemporal Tubes

Know before running:
Dimension - 1D for x vs t                       (2 tubes)
            2D for x vs t and y vs t            (4 tubes)
            3D for x vs t and y vs t and z vs t (6 tubes)

Tube Thickness Lower Limit - 0.5
               Upper Limit - User Input

1D Output - i. x vs t
2D Output - i. x vs t
           ii. y vs t
          iii. x vs y
           iv. x vs y vs t
3D Output - i. x vs t
           ii. y vs t
          iii. z vs t

Decomposition:
              i. Obstacle must have integer level discretization
             ii. 
            iii. 

Multiagent:
              i. Identifier must be mentioned for each STL instance
             ii. Unique STL instance for each Bot
            iii.
## Contributors
* [Subhodeep Choudhury](https://github.com/snyprdragun)
* [Ratnangshu Das](https://github.com/RatnangshuD)
* [Pushpak Jagtap](https://github.com/Pushpak-IISc)

## Acknowledgement
This work is supported by [Formal Control and Autonomous Systems (FOCAS) Lab](https://www.focaslab.com/) and [Robert Bosch Centre for Cyber Physical Systems, Indian Institue of Science, Bangalore](https://cps.iisc.ac.in/).

## Related Publication
[S. Choudhury, R. Das, P. Jagtap, Data-driven Spatiotemporal Tubes to satisfy Signal Temporal Logic
Specifications for Unknown Systems]()

## Other Resources
For implementing this paper in simulation/hardware along with controller deployment for real world systems, visit [this repo](https://github.com/SnyprDragun/STL_STT_examples). Both `cpp` and `python` implementations on Mechanum Omnibot and Quadcopter are illustrated.

## Copyright Declaration
* Copyright (c) 2024 by FOCAS Lab, RBCCPS, IISc Blr.  All rights reserved.
* This version of the STL-STT library can be redistributed under CNRI's Python 1.6 license.  For any other use, please contact FOCAS Lab
----
