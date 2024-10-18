#!/usr/bin/env python3
'''script for Reach, Avoid and Stay classes'''
import z3
import time
import numpy as np

class TASK():
    depths = ["full", "partial", "minimum"]

    def __init__(self):
        self.eventually = False
        self.always = False
        self.implies = False
        self.start = time.time()
        self.depth = "partial"

class REACH(TASK):
    '''class for reach STL specification'''
    def __init__(self, main, x1, x2, y1 = None, y2 = None, z1 = None, z2 = None):
        super().__init__()
        if x1 is not None and x2 is not None:
            self.x1 = x1
            self.x2 = x2
            self.callable = 1
            self.local_setpoint = [self.x1, self.x2]
        elif x1 is not None and x2 is None:
            self.callable = 1.5

        if y1 is not None and y2 is not None:
            self.y1 = y1
            self.y2 = y2
            self.callable = 2
            self.local_setpoint = [self.x1, self.x2, self.y1, self.y2]
        elif y1 is not None and y2 is None:
            self.callable = 2.5

        if z1 is not None and z2 is not None:
            self.z1 = z1
            self.z2 = z2
            self.callable = 3
            self.local_setpoint = [self.x1, self.x2, self.y1, self.y2, self.z1, self.z2]
        elif z1 is not None and z2 is None:
            self.callable = 3.5

        self.t1 = 0
        self.t2 = 0
        self.main = main

        if self.main.getStart() > self.t1:
            self.main.setStart(self.t1)
        if self.main.getFinish() < self.t2:
            self.main.setFinish(self.t2)

    def call(self):
        if self.callable == 1:
            if self.depth == "minimum":
                return self.execute_reach_1D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_reach_1D_depth_partial()
            elif self.depth == "full":
                return self.execute_reach_1D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")
        
        elif self.callable == 2:
            if self.depth == "minimum":
                return self.execute_reach_2D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_reach_2D_depth_partial()
            elif self.depth == "full":
                return self.execute_reach_2D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")
        
        else:
            if self.depth == "minimum":
                return self.execute_reach_3D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_reach_3D_depth_partial()
            elif self.depth == "full":
                return self.execute_reach_3D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")

    def execute_reach_1D_depth_minimum(self):
        self.main.setpoints.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5
    
        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma1_U = self.main.gammas(t)[1]

            x_mid = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            constraint = z3.And(x_mid<self.x2, x_mid>self.x1)
            all_constraints.append(constraint)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_1D_depth_partial(self):
        self.main.setpoints.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma1_U = self.main.gammas(t)[1]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            constraint_low = z3.And(x_low<self.x2, x_low>self.x1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            constraint_high = z3.And(x_high<self.x2, x_high>self.x1)
            all_constraints.append(constraint_high)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_1D_depth_full(self):
        self.main.setpoints.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                gamma1_L = self.main.gammas(t)[0]
                gamma1_U = self.main.gammas(t)[1]

                x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                constraint = z3.And(x<self.x2, x>self.x1)
                all_constraints.append(constraint)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_2D_depth_minimum(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma1_U = self.main.gammas(t)[2]
            gamma2_U = self.main.gammas(t)[3]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            y = (lambda_ * gamma2_L + (1 - lambda_) * gamma2_U)
            constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1)
            all_constraints.append(constraint)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_2D_depth_partial(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma1_U = self.main.gammas(t)[2]
            gamma2_U = self.main.gammas(t)[3]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            y_low = (lambda_low * gamma2_L + (1 - lambda_low) * gamma2_U)
            constraint_low = z3.And(x_low<self.x2, x_low>self.x1, y_low<self.y2, y_low>self.y1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            y_high = (lambda_high * gamma2_L + (1 - lambda_high) * gamma2_U)
            constraint_high = z3.And(x_high<self.x2, x_high>self.x1, y_high<self.y2, y_high>self.y1)
            all_constraints.append(constraint_high)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_2D_depth_full(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                for lambda_2 in self.main.lambda_values:
                    gamma1_L = self.main.gammas(t)[0]
                    gamma2_L = self.main.gammas(t)[1]
                    gamma1_U = self.main.gammas(t)[2]
                    gamma2_U = self.main.gammas(t)[3]

                    x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                    y = (lambda_2 * gamma2_L + (1 - lambda_2) * gamma2_U)
                    constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1)
                    all_constraints.append(constraint)
        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_3D_depth_minimum(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5
        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma3_L = self.main.gammas(t)[2]
            gamma1_U = self.main.gammas(t)[3]
            gamma2_U = self.main.gammas(t)[4]
            gamma3_U = self.main.gammas(t)[5]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            y = (lambda_ * gamma2_L + (1 - lambda_) * gamma2_U)
            z = (lambda_ * gamma3_L + (1 - lambda_) * gamma3_U)
            constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1, z<self.z2, z>self.z1)
            all_constraints.append(constraint)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_3D_depth_partial(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1
        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma3_L = self.main.gammas(t)[2]
            gamma1_U = self.main.gammas(t)[3]
            gamma2_U = self.main.gammas(t)[4]
            gamma3_U = self.main.gammas(t)[5]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            y_low = (lambda_low * gamma2_L + (1 - lambda_low) * gamma2_U)
            z_low = (lambda_low * gamma3_L + (1 - lambda_low) * gamma3_U)
            constraint_low = z3.And(x_low<self.x2, x_low>self.x1, y_low<self.y2, y_low>self.y1, z_low<self.z2, z_low>self.z1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            y_high = (lambda_high * gamma2_L + (1 - lambda_high) * gamma2_U)
            z_high = (lambda_high * gamma3_L + (1 - lambda_high) * gamma3_U)
            constraint_high = z3.And(x_high<self.x2, x_high>self.x1, y_high<self.y2, y_high>self.y1, z_high<self.z2, z_high>self.z1)
            all_constraints.append(constraint_high)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_reach_3D_depth_full(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                for lambda_2 in self.main.lambda_values:
                    for lambda_3 in self.main.lambda_values:
                        gamma1_L = self.main.gammas(t)[0]
                        gamma2_L = self.main.gammas(t)[1]
                        gamma3_L = self.main.gammas(t)[2]
                        gamma1_U = self.main.gammas(t)[3]
                        gamma2_U = self.main.gammas(t)[4]
                        gamma3_U = self.main.gammas(t)[5]

                        x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                        y = (lambda_2 * gamma2_L + (1 - lambda_2) * gamma2_U)
                        z = (lambda_3 * gamma3_L + (1 - lambda_3) * gamma3_U)
                        constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1, z<self.z2, z>self.z1)
                        all_constraints.append(constraint)

        print("Added Reach Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints


class AVOID(TASK):
    '''class for avoid STL specification'''
    def __init__(self, main, x1, x2, y1 = None, y2 = None, z1 = None, z2 = None):
        super().__init__()
        if x1 is not None and x2 is not None:
            self.x1 = x1
            self.x2 = x2
            self.callable = 1
            self.local_obstacle = [self.x1, self.x2]
        elif x1 is not None and x2 is None:
            self.callable = 1.5

        if y1 is not None and y2 is not None:
            self.y1 = y1
            self.y2 = y2
            self.callable = 2
            self.local_obstacle = [self.x1, self.x2, self.y1, self.y2]
        elif y1 is not None and y2 is None:
            self.callable = 2.5

        if z1 is not None and z2 is not None:
            self.z1 = z1
            self.z2 = z2
            self.callable = 3
            self.local_obstacle = [self.x1, self.x2, self.y1, self.y2, self.z1, self.z2]
        elif z1 is not None and z2 is None:
            self.callable = 3.5

        self.t1 = 0
        self.t2 = 0
        self.main = main

        if self.main.getStart() > self.t1:
            self.main.setStart(self.t1)
        if self.main.getFinish() < self.t2:
            self.main.setFinish(self.t2)

    def call(self):
        if self.callable == 1:
            if self.depth == "minimum":
                return self.execute_avoid_1D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_avoid_1D_depth_partial()
            elif self.depth == "full":
                return self.execute_avoid_1D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")
        
        elif self.callable == 2:
            if self.depth == "minimum":
                return self.execute_avoid_2D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_avoid_2D_depth_partial()
            elif self.depth == "full":
                return self.execute_avoid_2D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")
        
        else:
            if self.depth == "minimum":
                return self.execute_avoid_3D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_avoid_3D_depth_partial()
            elif self.depth == "full":
                return self.execute_avoid_3D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")

    def execute_avoid_1D_depth_minimum(self):
        self.main.obstacles.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma1_U = self.main.gammas(t)[1]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            constraint = z3.Or(x>self.x2, x<self.x1)
            all_constraints.append(constraint)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_1D_depth_partial(self):
        self.main.obstacles.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma1_U = self.main.gammas(t)[1]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            constraint_low = z3.Or(x_low>self.x2, x_low<self.x1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            constraint_high = z3.Or(x_high>self.x2, x_high<self.x1)
            all_constraints.append(constraint_high)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_1D_depth_full(self):
        self.main.obstacles.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)

        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                gamma1_L = self.main.gammas(t)[0]
                gamma1_U = self.main.gammas(t)[1]

                x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                constraint = z3.Or(x>self.x2, x<self.x1)
                all_constraints.append(constraint)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_2D_depth_minimum(self):
        self.main.obstacles.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma1_U = self.main.gammas(t)[2]
            gamma2_U = self.main.gammas(t)[3]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            y = (lambda_ * gamma2_L + (1 - lambda_) * gamma2_U)
            constraint = z3.Or(z3.Or(x>self.x2, x<self.x1), z3.Or(y>self.y2, y<self.y1))
            all_constraints.append(constraint)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_2D_depth_partial(self):
        self.main.obstacles.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma1_U = self.main.gammas(t)[2]
            gamma2_U = self.main.gammas(t)[3]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            y_low = (lambda_low * gamma2_L + (1 - lambda_low) * gamma2_U)
            constraint_low = z3.Or(z3.Or(x_low>self.x2, x_low<self.x1), z3.Or(y_low>self.y2, y_low<self.y1))
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            y_high = (lambda_high * gamma2_L + (1 - lambda_high) * gamma2_U)
            constraint_high = z3.Or(z3.Or(x_high>self.x2, x_high<self.x1), z3.Or(y_high>self.y2, y_high<self.y1))
            all_constraints.append(constraint_high)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_2D_depth_full(self):
        self.main.obstacles.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)

        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                for lambda_2 in self.main.lambda_values:
                        gamma1_L = self.main.gammas(t)[0]
                        gamma2_L = self.main.gammas(t)[1]
                        gamma1_U = self.main.gammas(t)[2]
                        gamma2_U = self.main.gammas(t)[3]

                        x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                        y = (lambda_2 * gamma2_L + (1 - lambda_2) * gamma2_U)
                        constraint = z3.Or(z3.Or(x>self.x2, x<self.x1), z3.Or(y>self.y2, y<self.y1))
                        all_constraints.append(constraint)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_3D_depth_minimum(self):
        self.main.obstacles.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma3_L = self.main.gammas(t)[2]
            gamma1_U = self.main.gammas(t)[3]
            gamma2_U = self.main.gammas(t)[4]
            gamma3_U = self.main.gammas(t)[5]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            y = (lambda_ * gamma2_L + (1 - lambda_) * gamma2_U)
            z = (lambda_ * gamma3_L + (1 - lambda_) * gamma3_U)
            constraint = z3.Or(z3.Or(x>self.x2, x<self.x1), z3.Or(y>self.y2, y<self.y1), z3.Or(z>self.z2, z<self.z1))
            all_constraints.append(constraint)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_3D_depth_partial(self):
        self.main.obstacles.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma3_L = self.main.gammas(t)[2]
            gamma1_U = self.main.gammas(t)[3]
            gamma2_U = self.main.gammas(t)[4]
            gamma3_U = self.main.gammas(t)[5]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            y_low = (lambda_low * gamma2_L + (1 - lambda_low) * gamma2_U)
            z_low = (lambda_low * gamma3_L + (1 - lambda_low) * gamma3_U)
            constraint_low = z3.Or(z3.Or(x_low>self.x2, x_low<self.x1), z3.Or(y_low>self.y2, y_low<self.y1), z3.Or(z_low>self.z2, z_low<self.z1))
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            y_high = (lambda_high * gamma2_L + (1 - lambda_high) * gamma2_U)
            z_high = (lambda_high * gamma3_L + (1 - lambda_high) * gamma3_U)
            constraint_high = z3.Or(z3.Or(x_high>self.x2, x_high<self.x1), z3.Or(y_high>self.y2, y_high<self.y1), z3.Or(z_high>self.z2, z_high<self.z1))
            all_constraints.append(constraint_high)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_avoid_3D_depth_full(self):
        self.main.obstacles.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)

        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                for lambda_2 in self.main.lambda_values:
                    for lambda_3 in self.main.lambda_values:
                        gamma1_L = self.main.gammas(t)[0]
                        gamma2_L = self.main.gammas(t)[1]
                        gamma3_L = self.main.gammas(t)[2]
                        gamma1_U = self.main.gammas(t)[3]
                        gamma2_U = self.main.gammas(t)[4]
                        gamma3_U = self.main.gammas(t)[5]

                        x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                        y = (lambda_2 * gamma2_L + (1 - lambda_2) * gamma2_U)
                        z = (lambda_3 * gamma3_L + (1 - lambda_3) * gamma3_U)
                        constraint = z3.Or(z3.Or(x>self.x2, x<self.x1), z3.Or(y>self.y2, y<self.y1), z3.Or(z>self.z2, z<self.z1))
                        all_constraints.append(constraint)

        print("Added Avoid Constraints: ", self.main.obstacles)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints


class STAY(TASK):
    '''class for stay STL specification'''
    def __init__(self, main, x1, x2, y1 = None, y2 = None, z1 = None, z2 = None):
        super().__init__()
        if x1 is not None and x2 is not None:
            self.x1 = x1
            self.x2 = x2
            self.callable = 1
            self.local_setpoint = [self.x1, self.x2]
        elif x1 is not None and x2 is None:
            self.callable = 1.5

        if y1 is not None and y2 is not None:
            self.y1 = y1
            self.y2 = y2
            self.callable = 2
            self.local_setpoint = [self.x1, self.x2, self.y1, self.y2]
        elif y1 is not None and y2 is None:
            self.callable = 2.5

        if z1 is not None and z2 is not None:
            self.z1 = z1
            self.z2 = z2
            self.callable = 3
            self.local_setpoint = [self.x1, self.x2, self.y1, self.y2, self.z1, self.z2]
        elif z1 is not None and z2 is None:
            self.callable = 3.5

        self.t1 = 0
        self.t2 = 0
        self.main = main

        if self.main.getStart() > self.t1:
            self.main.setStart(self.t1)
        if self.main.getFinish() < self.t2:
            self.main.setFinish(self.t2)

    def call(self):
        if self.callable == 1:
            if self.depth == "minimum":
                return self.execute_stay_1D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_stay_1D_depth_partial()
            elif self.depth == "full":
                return self.execute_stay_1D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")
        
        elif self.callable == 2:
            if self.depth == "minimum":
                return self.execute_stay_2D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_stay_2D_depth_partial()
            elif self.depth == "full":
                return self.execute_stay_2D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")
        
        else:
            if self.depth == "minimum":
                return self.execute_stay_3D_depth_minimum()
            elif self.depth == "partial":
                return self.execute_stay_3D_depth_partial()
            elif self.depth == "full":
                return self.execute_stay_3D_depth_full()
            else:
                raise ValueError(f"Invalid depth value: {self.depth}. Must be one of {list(self.depths)}")

    def execute_stay_1D_depth_minimum(self):
        self.main.setpoints.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5
    
        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma1_U = self.main.gammas(t)[1]

            x_mid = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            constraint = z3.And(x_mid<self.x2, x_mid>self.x1)
            all_constraints.append(constraint)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_1D_depth_partial(self):
        self.main.setpoints.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma1_U = self.main.gammas(t)[1]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            constraint_low = z3.And(x_low<self.x2, x_low>self.x1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            constraint_high = z3.And(x_high<self.x2, x_high>self.x1)
            all_constraints.append(constraint_high)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_1D_depth_full(self):
        self.main.setpoints.append([self.x1, self.x2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                gamma1_L = self.main.gammas(t)[0]
                gamma1_U = self.main.gammas(t)[1]

                x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                constraint = z3.And(x<self.x2, x>self.x1)
                all_constraints.append(constraint)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_2D_depth_minimum(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma1_U = self.main.gammas(t)[2]
            gamma2_U = self.main.gammas(t)[3]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            y = (lambda_ * gamma2_L + (1 - lambda_) * gamma2_U)
            constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1)
            all_constraints.append(constraint)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_2D_depth_partial(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1

        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma1_U = self.main.gammas(t)[2]
            gamma2_U = self.main.gammas(t)[3]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            y_low = (lambda_low * gamma2_L + (1 - lambda_low) * gamma2_U)
            constraint_low = z3.And(x_low<self.x2, x_low>self.x1, y_low<self.y2, y_low>self.y1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            y_high = (lambda_high * gamma2_L + (1 - lambda_high) * gamma2_U)
            constraint_high = z3.And(x_high<self.x2, x_high>self.x1, y_high<self.y2, y_high>self.y1)
            all_constraints.append(constraint_high)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_2D_depth_full(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                for lambda_2 in self.main.lambda_values:
                    gamma1_L = self.main.gammas(t)[0]
                    gamma2_L = self.main.gammas(t)[1]
                    gamma1_U = self.main.gammas(t)[2]
                    gamma2_U = self.main.gammas(t)[3]

                    x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                    y = (lambda_2 * gamma2_L + (1 - lambda_2) * gamma2_U)
                    constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1)
                    all_constraints.append(constraint)
        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_3D_depth_minimum(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_ = 0.5
        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma3_L = self.main.gammas(t)[2]
            gamma1_U = self.main.gammas(t)[3]
            gamma2_U = self.main.gammas(t)[4]
            gamma3_U = self.main.gammas(t)[5]

            x = (lambda_ * gamma1_L + (1 - lambda_) * gamma1_U)
            y = (lambda_ * gamma2_L + (1 - lambda_) * gamma2_U)
            z = (lambda_ * gamma3_L + (1 - lambda_) * gamma3_U)
            constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1, z<self.z2, z>self.z1)
            all_constraints.append(constraint)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_3D_depth_partial(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        lambda_low = 0
        lambda_high = 1
        for t in t_values:
            gamma1_L = self.main.gammas(t)[0]
            gamma2_L = self.main.gammas(t)[1]
            gamma3_L = self.main.gammas(t)[2]
            gamma1_U = self.main.gammas(t)[3]
            gamma2_U = self.main.gammas(t)[4]
            gamma3_U = self.main.gammas(t)[5]

            x_low = (lambda_low * gamma1_L + (1 - lambda_low) * gamma1_U)
            y_low = (lambda_low * gamma2_L + (1 - lambda_low) * gamma2_U)
            z_low = (lambda_low * gamma3_L + (1 - lambda_low) * gamma3_U)
            constraint_low = z3.And(x_low<self.x2, x_low>self.x1, y_low<self.y2, y_low>self.y1, z_low<self.z2, z_low>self.z1)
            all_constraints.append(constraint_low)

            x_high = (lambda_high * gamma1_L + (1 - lambda_high) * gamma1_U)
            y_high = (lambda_high * gamma2_L + (1 - lambda_high) * gamma2_U)
            z_high = (lambda_high * gamma3_L + (1 - lambda_high) * gamma3_U)
            constraint_high = z3.And(x_high<self.x2, x_high>self.x1, y_high<self.y2, y_high>self.y1, z_high<self.z2, z_high>self.z1)
            all_constraints.append(constraint_high)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints

    def execute_stay_3D_depth_full(self):
        self.main.setpoints.append([self.x1, self.x2, self.y1, self.y2, self.z1, self.z2, self.t1, self.t2])
        all_constraints = []
        t_values = np.arange(self.t1, self.t2, self.main._step)
        for t in t_values:
            for lambda_1 in self.main.lambda_values:
                for lambda_2 in self.main.lambda_values:
                    for lambda_3 in self.main.lambda_values:
                        gamma1_L = self.main.gammas(t)[0]
                        gamma2_L = self.main.gammas(t)[1]
                        gamma3_L = self.main.gammas(t)[2]
                        gamma1_U = self.main.gammas(t)[3]
                        gamma2_U = self.main.gammas(t)[4]
                        gamma3_U = self.main.gammas(t)[5]

                        x = (lambda_1 * gamma1_L + (1 - lambda_1) * gamma1_U)
                        y = (lambda_2 * gamma2_L + (1 - lambda_2) * gamma2_U)
                        z = (lambda_3 * gamma3_L + (1 - lambda_3) * gamma3_U)
                        constraint = z3.And(x<self.x2, x>self.x1, y<self.y2, y>self.y1, z<self.z2, z>self.z1)
                        all_constraints.append(constraint)

        print("Added Stay Constraints: ", self.main.setpoints)
        end = time.time()
        self.main.displayTime(self.start, end)
        return all_constraints
