#!/usr/bin/env python3
'''script for robust sequential reach-avoid-stay STL specifications'''
import z3
import time
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches

from solver import *
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

        self.reach_solver = SOLVER(2, 3)
        self.avoid_solver = SOLVER(2, 3)

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

        for i in range(2 * self.dimension):
            power = 0
            for j in range(self.degree + 1): #each tube eq has {degree+1} terms
                real_tubes[i] += ((C_fin[j + i * (self.degree + 1)]) * (t ** power))
                power += 1
        return real_tubes

    def gamma_dot(self, t):
        '''method to calculate tube equations'''
        tubes = [z3.Real(f'g_{i}') for i in range(2 * self.dimension)]

        for i in range(2 * self.dimension):
            tubes[i] = 0
            power = 0
            for j in range(self.degree + 1):
                if power < 1:
                    tubes[i] += 0
                    power += 1
                else:
                    tubes[i] += power * ((self.C[j + i * (self.degree + 1)]) * (t ** (power - 1)))
                    power += 1
        return tubes

    def general(self):
        '''method for general specifications'''
        temp_t_values = np.arange(self.getStart(), self.getFinish(), self._step)
        for t in temp_t_values:
            if self.dimension == 1:
                gamma1_L = self.gammas(t)[0]
                gamma1_U = self.gammas(t)[1]
                constraint_x = z3.And((gamma1_U - gamma1_L) > 0.5, (gamma1_U - gamma1_L) < self.tube_thickness)
                self.solver.add(constraint_x)
                
                x_gamma_dot = (self.gamma_dot(t)[0] + self.gamma_dot(t)[1]) / 2
                self.solver.add(x_gamma_dot < 10000000)

            if self.dimension == 2:
                gamma1_L = self.gammas(t)[0]
                gamma2_L = self.gammas(t)[1]
                gamma1_U = self.gammas(t)[2]
                gamma2_U = self.gammas(t)[3]
                constraint_x = z3.And((gamma1_U - gamma1_L) > 0.5, (gamma1_U - gamma1_L) < self.tube_thickness)
                constraint_y = z3.And((gamma2_U - gamma2_L) > 0.5, (gamma2_U - gamma2_L) < self.tube_thickness)
                self.solver.add(constraint_x)
                self.solver.add(constraint_y)
            if self.dimension == 3:
                gamma1_L = self.gammas(t)[0]
                gamma2_L = self.gammas(t)[1]
                gamma3_L = self.gammas(t)[2]
                gamma1_U = self.gammas(t)[3]
                gamma2_U = self.gammas(t)[4]
                gamma3_U = self.gammas(t)[5]
                constraint_x = z3.And((gamma1_U - gamma1_L) > 0.5, (gamma1_U - gamma1_L) < self.tube_thickness)
                constraint_y = z3.And((gamma2_U - gamma2_L) > 0.5, (gamma2_U - gamma2_L) < self.tube_thickness)
                constraint_z = z3.And((gamma3_U - gamma3_L) > 0.5, (gamma3_U - gamma3_L) < self.tube_thickness)
                self.solver.add(constraint_x)
                self.solver.add(constraint_y)
                self.solver.add(constraint_z)

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
        dx.set_xlim(0, 15) ## dx.set_xlim(self.get_x_start(), self.get_x_finish())
        dx.set_ylim(0, 15) ## dx.set_ylim(self.get_y_start(), self.get_y_finish())
        dx.set_zlim(0, 15) ## dx.set_zlim(self.getStart(), self.getFinish())
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

        fig1, axs = plt.subplots(3, 1, figsize=(8, 8), constrained_layout=True)
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
        ax.set_title("t vs x")
        bx.set_title("t vs y")
        cx.set_title("t vs z")

        # --------------------------------------------------- 3D PLOT --------------------------------------------------- #
        fig2 = plt.figure(2, figsize=(10, 8))
        dx = fig2.add_subplot(111, projection='3d')
        dx.set_xlim(0, 15) ## dx.set_xlim(self.get_x_start(), self.get_x_finish())
        dx.set_ylim(0, 15) ## dx.set_ylim(self.get_y_start(), self.get_y_finish())
        dx.set_zlim(0, 15) ## dx.set_zlim(self.getStart(), self.getFinish())
        dx.set_xlabel('X Axis')
        dx.set_ylabel('Y Axis')
        dx.set_zlabel('Z Axis')

        for i in range(self.getRange()):
            vertices = [[x_u[i], y_u[i], z_u[i]], [x_l[i], y_u[i], z_u[i]], [x_l[i], y_l[i], z_u[i]], [x_u[i], y_l[i], z_u[i]],
                        [x_u[i], y_u[i], z_l[i]], [x_l[i], y_u[i], z_l[i]], [x_l[i], y_l[i], z_l[i]], [x_u[i], y_l[i], z_l[i]]]

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

        print("x_u: ", x_u)
        print("x_l: ", x_l)
        print("y_u: ", y_u)
        print("y_l: ", y_l)
        print("z_u: ", z_u)
        print("z_l: ", z_l)

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
                xi[i] = (np.float128(model[self.C[i]].numerator().as_long()))/(np.float128(model[self.C[i]].denominator().as_long()))
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
            print("range: ", self.getRange(), "\nstart: ", self.getStart(), "\nfinish: ", self.getFinish(), "\nstep: ", self._step)
            end = time.time()
            self.displayTime(start, end)

    def parallel_solvers(self):
        SOLVER.commonSolution(self.reach_solver.solver, self.avoid_solver.solver)

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

    def min_distance_element(self, target_array, goal):
        min_distance = float('inf')
        closest_element = None
        for element in target_array:
            distance = np.linalg.norm(np.array(element) - np.array(goal))
            if distance < min_distance:
                min_distance = distance
                closest_element = element
        return closest_element

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
