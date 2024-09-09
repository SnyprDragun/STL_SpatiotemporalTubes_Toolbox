#!/opt/homebrew/bin/python3.11
'''STL toolbox compined script'''
import z3
import time
import random
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

class SeqReachAvoidStay():
    '''class representing constraints on trajectory'''
    def __init__(self, degree, dimension, time_step, tube_thickness):
        self.setpoints = []
        self.obstacles = []
        self._start = 0
        self._finish = 0
        self._step = time_step
        self._range = 0
        self._x_start = 0
        self._x_finish = 0
        self._y_start = 0
        self._y_finish = 0
        self.tube_thickness = tube_thickness
        self.lambda_values = np.arange(0, 1.1, 0.1)
        self.degree = degree
        self.dimension = dimension
        self.solver = z3.Solver()
        z3.set_param("parallel.enable", True)
        self.C = [z3.Real(f'C{i}') for i in range((2 * self.dimension) * (self.degree + 1))]

    def gammas(self, t):
        '''method to calculate tube equations'''
        tubes = [z3.Real(f'e_{i}') for i in range(2 * self.dimension)]

        for i in range(2 * self.dimension):
            tubes[i] = 0
            power = 0
            for j in range(self.degree + 1):
                tubes[i] += ((self.C[j + i * (self.degree + 1)]) * (t ** power))
                power += 1
        return tubes

    def real_gammas(self, t, C_fin):
        '''method to calculate tube equations'''
        real_tubes = np.zeros(2 * self.dimension)

        for i in range(2 * self.dimension): #for 4 tube equations
            power = 0
            for j in range(self.degree + 1): #each tube eq has {degree+1} terms
                real_tubes[i] += ((C_fin[j + i * (self.degree + 1)]) * (t ** power))
                power += 1
        return real_tubes

    def general(self):
        '''method for general specifications'''
        temp_t_values = np.arange(self.getStart(), self.getFinish(), self._step)
        for t in temp_t_values:
            if self.dimension == 1:
                gamma1_L = self.gammas(t)[0]
                gamma1_U = self.gammas(t)[1]
                self.solver.add(z3.And((gamma1_U - gamma1_L) > 0.5, (gamma1_U - gamma1_L) < self.tube_thickness))
            if self.dimension == 2:
                gamma1_L = self.gammas(t)[0]
                gamma2_L = self.gammas(t)[1]
                gamma1_U = self.gammas(t)[2]
                gamma2_U = self.gammas(t)[3]
                self.solver.add(z3.And((gamma1_U - gamma1_L) > 0.5, (gamma1_U - gamma1_L) < self.tube_thickness))
                self.solver.add(z3.And((gamma2_U - gamma2_L) > 0.5, (gamma2_U - gamma2_L) < self.tube_thickness))
            if self.dimension == 3:
                gamma1_L = self.gammas(t)[0]
                gamma2_L = self.gammas(t)[1]
                gamma3_L = self.gammas(t)[2]
                gamma1_U = self.gammas(t)[3]
                gamma2_U = self.gammas(t)[4]
                gamma3_U = self.gammas(t)[5]
                self.solver.add(z3.And((gamma1_U - gamma1_L) > 0.5, (gamma1_U - gamma1_L) < self.tube_thickness))
                self.solver.add(z3.And((gamma2_U - gamma2_L) > 0.5, (gamma2_U - gamma2_L) < self.tube_thickness))
                self.solver.add(z3.And((gamma3_U - gamma3_L) > 0.5, (gamma3_U - gamma3_L) < self.tube_thickness))

    def plot_for_1D(self, C_fin):
        x_u = np.zeros(self.getRange())
        x_l = np.zeros(self.getRange())

        for i in range(self.getRange()):
            x_u[i] = self.real_gammas(i * self._step, C_fin)[1]
            x_l[i] = self.real_gammas(i * self._step, C_fin)[0]

        fig, axs = plt.subplots(1, 1, figsize=(8, 8), constrained_layout=True)
        ax = axs
        for i in self.setpoints:       # t1    x1     t2     t1    x2     x1
            square = patches.Rectangle((i[2], i[0]), i[3] - i[2], i[1] - i[0], edgecolor='green', facecolor='none')
            ax.add_patch(square)

        for i in self.obstacles:       # t1    x1     t2     t1    x2     x1
            square = patches.Rectangle((i[2], i[0]), i[3] - i[2], i[1] - i[0], edgecolor='red', facecolor='none')
            ax.add_patch(square)

        print("range: ", self.getRange(), "\nstart: ", self.getStart(), "\nfinish: ", self.getFinish(), "\nstep: ", self._step)
        t = np.linspace(self.getStart(), self.getFinish(), self.getRange())

        ax.plot(t, x_u)
        ax.plot(t, x_l)

    def plot_for_2D(self, C_fin):
        x_u = np.zeros(self.getRange())
        x_l = np.zeros(self.getRange())
        y_u = np.zeros(self.getRange())
        y_l = np.zeros(self.getRange())

        for i in range(self.getRange()):
            x_u[i] = self.real_gammas(i * self._step, C_fin)[2]
            x_l[i] = self.real_gammas(i * self._step, C_fin)[0]
            y_u[i] = self.real_gammas(i * self._step, C_fin)[3]
            y_l[i] = self.real_gammas(i * self._step, C_fin)[1]

        fig, axs = plt.subplots(2, 1, figsize=(8, 8), constrained_layout=True)
        ax, bx = axs
        for i in self.setpoints:        # t1    x1/y1   t2     t1   x2/y2  x1/y1
            square_x = patches.Rectangle((i[4], i[0]), i[5] - i[4], i[1] - i[0], edgecolor='green', facecolor='none')
            square_y = patches.Rectangle((i[4], i[2]), i[5] - i[4], i[3] - i[2], edgecolor='green', facecolor='none')
            ax.add_patch(square_x)
            bx.add_patch(square_y)

        for i in self.obstacles:        # t1    x1/y1   t2     t1   x2/y2  x1/y1
            square_x = patches.Rectangle((i[4], i[0]), i[5] - i[4], i[1] - i[0], edgecolor='red', facecolor='none')
            square_y = patches.Rectangle((i[4], i[2]), i[5] - i[4], i[3] - i[2], edgecolor='red', facecolor='none')
            ax.add_patch(square_x)
            bx.add_patch(square_y)

        t = np.linspace(self.getStart(), self.getFinish(), self.getRange())
        print("range: ", self.getRange(), "\nstart: ", self.getStart(), "\nfinish: ", self.getFinish(), "\nstep: ", self._step)

        ax.plot(t, x_u)
        ax.plot(t, x_l)
        bx.plot(t, y_u)
        bx.plot(t, y_l)

        fig2 = plt.figure(2)
        dx = fig2.add_subplot(111, projection='3d')
        dx.set_xlim(0, 5)
        dx.set_ylim(0, 5)
        dx.set_zlim(0, 5)
        dx.set_xlabel('X Axis')
        dx.set_ylabel('Y Axis')
        dx.set_zlabel('Time Axis')

        for i in range(self.getRange()):
            vertices = [[x_u[i], y_u[i], i * self._step], [x_l[i], y_u[i], i * self._step], [x_l[i], y_l[i], i * self._step], [x_u[i], y_l[i], i * self._step],
                        [x_u[i], y_u[i], i * self._step], [x_l[i], y_u[i], i * self._step], [x_l[i], y_l[i], i * self._step], [x_u[i], y_l[i], i * self._step]]

            faces = [   [vertices[0], vertices[1], vertices[2], vertices[3]],  # Bottom face
                [vertices[4], vertices[5], vertices[6], vertices[7]],  # Top face
                [vertices[0], vertices[1], vertices[5], vertices[4]],  # Front face
                [vertices[2], vertices[3], vertices[7], vertices[6]],  # Back face
                [vertices[1], vertices[2], vertices[6], vertices[5]],  # Right face
                [vertices[0], vertices[3], vertices[7], vertices[4]]]  # Left face

            dx.add_collection3d(Poly3DCollection(faces, facecolors='blue', edgecolors='blue', alpha=0.25))

        for i in self.obstacles:
            dx.add_collection3d(Poly3DCollection(self.faces(i), facecolors='red', edgecolors='r', alpha=0.25))

        for i in self.setpoints:
            dx.add_collection3d(Poly3DCollection(self.faces(i), facecolors='green', edgecolors='green', alpha=0.25))

        fig3 = plt.figure(3)
        plt.plot(x_u, y_u, marker='o', linestyle='-')
        plt.plot(x_l, y_l, marker='o', linestyle='-')
        plt.title("Plot of array1 vs array2")
        plt.xlabel("X-Axis")
        plt.ylabel("Y-Axis")

    def plot_for_3D(self, C_fin):
        x_u = np.zeros(self.getRange())
        x_l = np.zeros(self.getRange())
        y_u = np.zeros(self.getRange())
        y_l = np.zeros(self.getRange())
        z_u = np.zeros(self.getRange())
        z_l = np.zeros(self.getRange())

        for i in range(self.getRange()):
            x_u[i] = self.real_gammas(i * self._step, C_fin)[3]
            x_l[i] = self.real_gammas(i * self._step, C_fin)[0]
            y_u[i] = self.real_gammas(i * self._step, C_fin)[4]
            y_l[i] = self.real_gammas(i * self._step, C_fin)[1]
            z_u[i] = self.real_gammas(i * self._step, C_fin)[5]
            z_l[i] = self.real_gammas(i * self._step, C_fin)[2]

        fig, axs = plt.subplots(3, 1, figsize=(8, 8), constrained_layout=True)
        ax, bx, cx = axs
        for i in self.setpoints:        # t1  x1/y1/z1  t2    t1  x2/y2/z2  x1
            square_x = patches.Rectangle((i[6], i[0]), i[7] - i[6], i[1] - i[0], edgecolor='green', facecolor='none')
            square_y = patches.Rectangle((i[6], i[2]), i[7] - i[6], i[3] - i[2], edgecolor='green', facecolor='none')
            square_z = patches.Rectangle((i[6], i[4]), i[7] - i[6], i[5] - i[4], edgecolor='green', facecolor='none')
            ax.add_patch(square_x)
            bx.add_patch(square_y)
            cx.add_patch(square_z)

        for i in self.obstacles:        # t1  x1/y1/z1  t2    t1  x2/y2/z2  x1
            square_x = patches.Rectangle((i[6], i[0]), i[7] - i[6], i[1] - i[0], edgecolor='red', facecolor='none')
            square_y = patches.Rectangle((i[6], i[2]), i[7] - i[6], i[3] - i[2], edgecolor='red', facecolor='none')
            square_z = patches.Rectangle((i[6], i[4]), i[7] - i[6], i[5] - i[4], edgecolor='red', facecolor='none')
            ax.add_patch(square_x)
            bx.add_patch(square_y)
            cx.add_patch(square_z)

        t = np.linspace(self.getStart(), self.getFinish(), self.getRange())
        print("range: ", self.getRange(), "\nstart: ", self.getStart(), "\nfinish: ", self.getFinish(), "\nstep: ", self._step)

        ax.plot(t, x_u)
        ax.plot(t, x_l)
        bx.plot(t, y_u)
        bx.plot(t, y_l)
        cx.plot(t, z_u)
        cx.plot(t, z_l)
        ax.set_title("First Subplot")
        bx.set_title("Second Subplot")
        cx.set_title("Third Subplot")

    def find_solution(self):
        '''method to plot the tubes'''
        start = time.time()
        print("Solving...")

        self.setAll()
        self.general()

        if self.solver.check() == z3.sat:
            model = self.solver.model()
            xi = np.zeros((2 * self.dimension) * (self.degree + 1))
            Coeffs = []
            C_fin = np.zeros((2 * self.dimension) * (self.degree + 1))
            for i in range(len(self.C)):
                xi[i] = (float(model[self.C[i]].numerator().as_long()))/(float(model[self.C[i]].denominator().as_long()))
                print("{} = {}".format(self.C[i], xi[i]))
                Coeffs.append(xi[i])

            for i in range(len(Coeffs)):
                C_fin[i] = Coeffs[i]

            if self.dimension == 1:
                self.plot_for_1D(C_fin)
            elif self.dimension == 2:
                self.plot_for_2D(C_fin)
            else:
                self.plot_for_3D(C_fin)

            end = time.time()
            self.displayTime(start, end)
            plt.show(block=True)

        else:
            print("No solution found.")
            end = time.time()
            self.displayTime(start, end)

    def test_plot(self):
        '''method to plot the tubes'''
        start = time.time()
        print("Solving...")

        self.setAll()
        self.general()

        x_u = np.zeros(self.getRange())
        x_l = np.zeros(self.getRange())

        all_solutions = []
        count = 0
        while self.solver.check() == z3.sat:
            count += 1
            print("Model Number: ", count)
            model = self.solver.model()
            try:
                xi = np.zeros((2 * self.dimension) * (self.degree + 1))
                Coeffs = []
                C_fin = np.zeros((2 * self.dimension) * (self.degree + 1))
                for i in range(len(self.C)):
                    xi[i] = (float(model[self.C[i]].numerator().as_long()))/(float(model[self.C[i]].denominator().as_long()))
                    print("{} = {}".format(self.C[i], xi[i]))
                    Coeffs.append(xi[i])

                for i in range(len(Coeffs)):
                    C_fin[i] = Coeffs[i]

                print("Coefficients array: ", C_fin)
                all_solutions.append(C_fin)
                t = np.linspace(self.getStart(), self.getFinish(), self.getRange())
                print("range: ", self.getRange(), "\nstart: ", self.getStart(), "\nfinish: ", self.getFinish(), "\nstep: ", self._step)
                for i in range(self.getRange()):
                    x_u[i] = self.real_gammas(i * self._step, C_fin)[1]
                    x_l[i] = self.real_gammas(i * self._step, C_fin)[0]

                    plt.subplot(211)
                    plt.plot(t, x_u, color = 'orange')
                    plt.plot(t, x_l, color = 'orange')

                self.plot_setpoints()
                self.plot_obstacles()

            except OverflowError:
                print("OverflowError")
                break

            end = time.time()
            k = int(end - start)
            hrs = k // 3600
            mins = (k // 60) - (hrs * 60)
            if end - start < 1:
                secs = (((end - start) * 10000) // 100) / 100
            else:
                secs = k - (mins * 60) - (hrs * 60 * 60)
            print("Time taken: ", hrs , "hours, ", mins, "minutes, ", secs, "seconds")

            for i in range(len(self.C)):
                a = self.C[i]
                b = model[self.C[i]]
                second_decimal_of_a = z3.ToInt((a * 10000) / 100) % 10
                second_decimal_of_b = z3.ToInt((b * 10000) / 100) % 10
                self.solver.add(second_decimal_of_a != second_decimal_of_b)
        print("All Solutions: ", all_solutions)
        plt.show(block = True)

    def faces(self, i):
        vertices = [[i[0], i[2], i[4]], [i[1], i[2], i[4]], [i[1], i[3], i[4]], [i[0], i[3], i[4]],  # Bottom face
                    [i[0], i[2], i[5]], [i[1], i[2], i[5]], [i[1], i[3], i[5]], [i[0], i[3], i[5]]]   # Top face

        # Define the 6 faces of the cube using the vertices
        faces = [   [vertices[0], vertices[1], vertices[2], vertices[3]],  # Bottom face
                    [vertices[4], vertices[5], vertices[6], vertices[7]],  # Top face
                    [vertices[0], vertices[1], vertices[5], vertices[4]],  # Front face
                    [vertices[2], vertices[3], vertices[7], vertices[6]],  # Back face
                    [vertices[1], vertices[2], vertices[6], vertices[5]],  # Right face
                    [vertices[0], vertices[3], vertices[7], vertices[4]]]  # Left face
        return faces

    def setAll(self):
        all_points = self.setpoints + self.obstacles
        x1, x2, y1, y2, z1, z2, t1, t2 = [], [], [], [], [], [], [], []
        for i in all_points:
            tab = 0
            if self.dimension == 1:
                x1.append(i[0])
                x2.append(i[1])
                t1.append(i[2])
                t2.append(i[3])
            if self.dimension == 2:
                x1.append(i[0])
                x2.append(i[1])
                y1.append(i[2])
                y2.append(i[3])
                t1.append(i[4])
                t2.append(i[5])
            if self.dimension == 3:
                x1.append(i[0])
                x2.append(i[1])
                y1.append(i[2])
                y2.append(i[3])
                z1.append(i[4])
                z2.append(i[5])
                t1.append(i[6])
                t2.append(i[7])

        self.setStart(min(t1))
        self.setFinish(max(t2))
        self.set_x_start(min(x1))
        self.set_x_finish(max(x2))

        if self.dimension >= 2:
            self.set_y_start(min(y1))
            self.set_y_finish(max(y2))

        if self.dimension >= 3:
            self.set_z_start(min(z1))
            self.set_z_finish(max(z2))

        self.setRange(int((self.getFinish() - self.getStart() + self._step) / self._step))

    def displayTime(self, start, end):
        k = int(end - start)
        hrs = k // 3600
        mins = (k // 60) - (hrs * 60)
        if end - start < 1:
            secs = (((end - start) * 10000) // 100) / 100
        else:
            secs = k - (mins * 60) - (hrs * 60 * 60)
        print("Time taken: ", hrs , "hours, ", mins, "minutes, ", secs, "seconds")

    def getStart(self):
        return self._start

    def setStart(self, start_value):
        self._start = start_value

    def getFinish(self):
        return self._finish

    def setFinish(self, finish_value):
        self._finish = finish_value

    def getRange(self):
        return self._range

    def setRange(self, value):
        self._range = value

    def get_x_start(self):
        return self._x_start

    def set_x_start(self, value):
        self._x_start = value

    def get_x_finish(self):
        return self._x_finish

    def set_x_finish(self, value):
        self._x_finish = value

    def get_y_start(self):
        return self._y_start

    def set_y_start(self, value):
        self._y_start = value

    def get_y_finish(self):
        return self._y_finish

    def set_y_finish(self, value):
        self._y_finish = value

    def get_z_start(self):
        return self._z_start

    def set_z_start(self, value):
        self._z_start = value

    def get_z_finish(self):
        return self._z_finish

    def set_z_finish(self, value):
        self._z_finish = value

    def get_degree(self):
        return self.degree

    def set_degree(self, value):
        self.degree = value

    def get_dimension(self):
        return self.dimension

    def set_dimension(self, value):
        self.dimension = value


class TASK():
    def __init__(self, eventually, always, implies):
        self.eventually = False
        self.always = False
        self.implies = False

class REACH(TASK):
    '''class for reach STL specification'''
    def __init__(self, main, x1, x2, y1 = None, y2 = None, z1 = None, z2 = None):
        if x1 is not None and x2 is not None:
            self.x1 = x1
            self.x2 = x2
            self.callable = 1
        elif x1 is not None and x2 is None:
            self.callable = 1.5

        if y1 is not None and y2 is not None:
            self.y1 = y1
            self.y2 = y2
            self.callable = 2
        elif y1 is not None and y2 is None:
            self.callable = 2.5

        if z1 is not None and z2 is not None:
            self.z1 = z1
            self.z2 = z2
            self.callable = 3
        elif z1 is not None and z2 is None:
            self.callable = 3.5

        self.t1 = 0
        self.t2 = 0
        self.main = main

        if self.main.getStart() > self.t1:
            self.main.setStart(self.t1)
        if self.main.getFinish() < self.t2:
            self.main.setFinish(self.t2)

    def checkCallableAndCallExecute(self):
        match self.callable:
            case 1:
                return self.execute_reach_1D()
            case 1.5:
                print("Error: Must enter both values for X")
            case 2:
                return self.execute_reach_2D()
            case 2.5:
                print("Error: Must enter both values for Y")
            case 3:
                return self.execute_reach_3D()
            case 3.5:
                print("Error: Must enter both values for Z")
            case default:
                print("Error: Must enter ", 2 * self.main.dimension, "values for degree ", self.main.dimension, 
                    ". Currently have mismatch.")

    def execute_reach_1D(self):
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
        return all_constraints

    def execute_reach_2D(self):
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
        return all_constraints

    def execute_reach_3D(self):
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
        return all_constraints

class AVOID(TASK):
    '''class for avoid STL specification'''
    def __init__(self, main, x1, x2, y1 = None, y2 = None, z1 = None, z2 = None):
        if x1 is not None and x2 is not None:
            self.x1 = x1
            self.x2 = x2
            self.callable = 1
        elif x1 is not None and x2 is None:
            self.callable = 1.5

        if y1 is not None and y2 is not None:
            self.y1 = y1
            self.y2 = y2
            self.callable = 2
        elif y1 is not None and y2 is None:
            self.callable = 2.5

        if z1 is not None and z2 is not None:
            self.z1 = z1
            self.z2 = z2
            self.callable = 3
        elif z1 is not None and z2 is None:
            self.callable = 3.5

        self.t1 = 0
        self.t2 = 0
        self.main = main

        if self.main.getStart() > self.t1:
            self.main.setStart(self.t1)
        if self.main.getFinish() < self.t2:
            self.main.setFinish(self.t2)

    def checkCallableAndCallExecute(self):
        match self.callable:
            case 1:
                return self.execute_avoid_1D()
            case 1.5:
                print("Error: Must enter both values for X")
            case 2:
                return self.execute_avoid_2D()
            case 2.5:
                print("Error: Must enter both values for Y")
            case 3:
                return self.execute_avoid_3D()
            case 3.5:
                print("Error: Must enter both values for Z")
            case default:
                print("Error: Must enter proper values")

    def execute_avoid_1D(self):
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
        return all_constraints

    def execute_avoid_2D(self):
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
        return all_constraints

    def execute_avoid_3D(self):
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
        return all_constraints

class STAY(TASK):
    '''class for stay STL specification'''
    def __init__(self, main, x1, x2, y1 = None, y2 = None, z1 = None, z2 = None):
        if x1 is not None and x2 is not None:
            self.x1 = x1
            self.x2 = x2
            self.callable = 1
        elif x1 is not None and x2 is None:
            self.callable = 1.5

        if y1 is not None and y2 is not None:
            self.y1 = y1
            self.y2 = y2
            self.callable = 2
        elif y1 is not None and y2 is None:
            self.callable = 2.5

        if z1 is not None and z2 is not None:
            self.z1 = z1
            self.z2 = z2
            self.callable = 3
        elif z1 is not None and z2 is None:
            self.callable = 3.5

        self.t1 = 0
        self.t2 = 0
        self.main = main

        if self.main.getStart() > self.t1:
            self.main.setStart(self.t1)
        if self.main.getFinish() < self.t2:
            self.main.setFinish(self.t2)

    def checkCallableAndCallExecute(self):
        match self.callable:
            case 1:
                return self.execute_stay_1D()
            case 1.5:
                print("Error: Must enter both values for X")
            case 2:
                return self.execute_stay_2D()
            case 2.5:
                print("Error: Must enter both values for Y")
            case 3:
                return self.execute_stay_3D()
            case 3.5:
                print("Error: Must enter both values for Z")
            case default:
                print("Error: Must enter proper values")

    def execute_stay_1D(self):
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
        return all_constraints

    def execute_stay_2D(self):
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
        return all_constraints

    def execute_stay_3D(self):
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
        return all_constraints


class STL():
    '''class to solve STL specifications'''
    _instances = {}

    def __init__(self, identifier, main):
        self.main = main
        STL._instances[identifier] = self

    @classmethod
    def get_instance(cls, identifier):
        return cls._instances.get(identifier)

    def plotter(self):
        self.main.find_solution()

class AND(STL):
    def __init__(self, identifier, *instances):
        self.instances = instances
        self.return_value = False
        self.always = False
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def add_resultant(self):
        '''adds constraints'''
        if self.always == True:
            for constraints in self.instances:
                for constraint in constraints:
                    self.main.solver.add(constraint)
        else:
            for constraints in self.instances:
                self.main.solver.add(constraints)

    def return_resultant(self):
        '''returns constraints'''
        return self.instances

    def call(self):
        if self.return_value == True:
            self.return_resultant()
        else:
            self.add_resultant()

class OR(STL):
    def __init__(self, identifier, *instances):
        self.instances = instances
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def add_resultant(self):
        '''adds constraints'''
        for constraints in self.instances:
            choice = random.randint(0, len(constraints) - 1)
            self.main.solver.add(constraints[choice])

    def return_resultant(self):
        '''returns constraints'''
        for constraints in self.instances:
            choice = random.randint(0, len(constraints) - 1)
            self.main.solver.add(constraints[choice])

    def call(self):
        if self.return_value == True:
            self.return_resultant()
        else:
            self.add_resultant()

class NOT(STL):
    def __init__(self, identifier, *instances):
        self.instances = instances
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def add_resultant(self):
        '''adds constraints'''
        for constraints in self.instances:
            for constraint in constraints:
                self.main.solver.add(z3.Not(constraint))

    def return_resultant(self):
        '''returns constraints'''
        return z3.Not(self.instances)

    def call(self):
        if self.return_value == True:
            self.return_resultant()
        else:
            self.add_resultant()

class EVENTUALLY(STL):
    def __init__(self, identifier, t1, t2, task):
        task.eventually = True
        task.t1 = t1
        task.t2 = t2
        self.task = task
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def call(self):
        all_constraints = self.task.checkCallableAndCallExecute()
        if self.return_value == True:
            return z3.AtLeast(*all_constraints, 3)
            # return all_constraints[random.randint(1, len(all_constraints) - 1)]
        else:
            self.main.solver.add(z3.AtLeast(*all_constraints, 3))

class ALWAYS(STL):
    def __init__(self, identifier, t1, t2, task):
        task.always = True
        task.t1 = t1
        task.t2 = t2
        self.task = task
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def call(self):
        all_constraints = self.task.checkCallableAndCallExecute()
        if self.return_value == True:
            return all_constraints
        else:
            self.main.solver.add(all_constraints)

class UNTIL(STL):
    def __init__(self):
        pass

class IMPLIES(STL):
    def __init__(self) -> None:
        pass

    def loop(self):
        pass

    def normal(self):
        pass


class SOLVER():
    def __init__(self, degree, dimension):
        self.degree = degree
        self.dimension = dimension
        self.solver = z3.Solver()
        z3.set_param("parallel.enable", True)

    def Solution(self):
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            xi = np.zeros((2 * self.dimension) * (self.degree + 1))
            Coeffs = []
            C_fin = np.zeros((2 * self.dimension) * (self.degree + 1))
            for i in range(len(self.C)):
                xi[i] = (float(model[self.C[i]].numerator().as_long()))/(float(model[self.C[i]].denominator().as_long()))
                print("{} = {}".format(self.C[i], xi[i]))
                Coeffs.append(xi[i])

            for i in range(len(Coeffs)):
                C_fin[i] = Coeffs[i]

        return C_fin

    def allSolutions(self):
        pass


class Error():
    def __init__(self) -> None:
        pass

    def valueError():
        # try:
        #     x
        # except valueError:
        #     throw exception
        pass


stl2 = STL(1, SeqReachAvoidStay(2, 1, 0.05, 1))
obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1)).call(), EVENTUALLY(1, 4, 5, REACH(stl2.main, 2, 3)).call()).call()
stl2.plotter()