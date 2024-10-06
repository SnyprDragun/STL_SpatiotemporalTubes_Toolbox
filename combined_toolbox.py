#!/opt/homebrew/bin/python3.11
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
        self.goal = []
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
        tubes = [z3.Real(f'g_{i}') for i in range(2 * self.dimension)]

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
        tubes = [z3.Real(f'gd_{i}') for i in range(2 * self.dimension)]

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

    def real_gamma_dot(self, t, C_fin):
        '''method to calculate tube equations'''
        real_tubes = np.zeros(2 * self.dimension)

        for i in range(2 * self.dimension):
            power = 0
            for j in range(self.degree + 1):
                if power < 1:
                    real_tubes[i] += 0
                    power += 1
                else:
                    real_tubes[i] += power * ((C_fin[j + i * (self.degree + 1)]) * (t ** (power - 1)))
                    power += 1
        return real_tubes

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
                # self.solver.add(x_gamma_dot < 10000000)

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
                constraint_x = z3.And((gamma1_U - gamma1_L) > 2.5, (gamma1_U - gamma1_L) < self.tube_thickness)
                constraint_y = z3.And((gamma2_U - gamma2_L) > 2.5, (gamma2_U - gamma2_L) < self.tube_thickness)
                constraint_z = z3.And((gamma3_U - gamma3_L) > 2.5, (gamma3_U - gamma3_L) < self.tube_thickness)
                self.solver.add(constraint_x)
                self.solver.add(constraint_y)
                self.solver.add(constraint_z)

    def plot_for_1D(self, C_fin):
        x_u = np.zeros(self.getRange())
        x_l = np.zeros(self.getRange())

        gd_xu = np.zeros(self.getRange())
        gd_xl = np.zeros(self.getRange())

        for i in range(self.getRange()):
            x_u[i] = self.real_gammas(i * self._step, C_fin)[1]
            x_l[i] = self.real_gammas(i * self._step, C_fin)[0]

            gd_xu[i] = self.real_gamma_dot(i * self._step, C_fin)[1]
            gd_xl[i] = self.real_gamma_dot(i * self._step, C_fin)[0]
        
        print("gamma_dot for x_upper max = ", max(gd_xu))
        print("gamma_dot for x_lower max = ", max(gd_xl))

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

        gd_xu = np.zeros(self.getRange())
        gd_xl = np.zeros(self.getRange())
        gd_yu = np.zeros(self.getRange())
        gd_yl = np.zeros(self.getRange())

        for i in range(self.getRange()):
            x_u[i] = self.real_gammas(i * self._step, C_fin)[2]
            x_l[i] = self.real_gammas(i * self._step, C_fin)[0]
            y_u[i] = self.real_gammas(i * self._step, C_fin)[3]
            y_l[i] = self.real_gammas(i * self._step, C_fin)[1]

            gd_xu[i] = self.real_gamma_dot(i * self._step, C_fin)[2]
            gd_xl[i] = self.real_gamma_dot(i * self._step, C_fin)[0]
            gd_yu[i] = self.real_gamma_dot(i * self._step, C_fin)[3]
            gd_yl[i] = self.real_gamma_dot(i * self._step, C_fin)[1]

        print("gamma_dot for x_upper max = ", gd_xu, max(gd_xu))
        print("gamma_dot for x_lower max = ", gd_xl, max(gd_xl))
        print("gamma_dot for y_upper max = ", gd_yu, max(gd_yu))
        print("gamma_dot for y_lower max = ", gd_yl, max(gd_yl))

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

        gd_xu = np.zeros(self.getRange())
        gd_xl = np.zeros(self.getRange())
        gd_yu = np.zeros(self.getRange())
        gd_yl = np.zeros(self.getRange())
        gd_zu = np.zeros(self.getRange())
        gd_zl = np.zeros(self.getRange())

        for i in range(self.getRange()):
            x_u[i] = self.real_gammas(i * self._step, C_fin)[3]
            x_l[i] = self.real_gammas(i * self._step, C_fin)[0]
            y_u[i] = self.real_gammas(i * self._step, C_fin)[4]
            y_l[i] = self.real_gammas(i * self._step, C_fin)[1]
            z_u[i] = self.real_gammas(i * self._step, C_fin)[5]
            z_l[i] = self.real_gammas(i * self._step, C_fin)[2]

            gd_xu[i] = self.real_gamma_dot(i * self._step, C_fin)[3]
            gd_xl[i] = self.real_gamma_dot(i * self._step, C_fin)[0]
            gd_yu[i] = self.real_gamma_dot(i * self._step, C_fin)[4]
            gd_yl[i] = self.real_gamma_dot(i * self._step, C_fin)[1]
            gd_zu[i] = self.real_gamma_dot(i * self._step, C_fin)[5]
            gd_zl[i] = self.real_gamma_dot(i * self._step, C_fin)[2]

        print("x_u: ", x_u)
        print("x_l: ", x_l)
        print("y_u: ", y_u)
        print("y_l: ", y_l)
        print("z_u: ", z_u)
        print("z_l: ", z_l)

        print("gamma_dot for x_upper max = ", max(gd_xu))
        print("gamma_dot for x_lower max = ", max(gd_xl))
        print("gamma_dot for y_upper max = ", max(gd_yu))
        print("gamma_dot for y_lower max = ", max(gd_yl))
        print("gamma_dot for z_upper max = ", max(gd_zu))
        print("gamma_dot for z_lower max = ", max(gd_zl))

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

        # --------------------------------------------------- 3D PLOT {X vs Y vs Z} --------------------------------------------------- #
        fig2 = plt.figure(2, figsize = (10, 8))
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

        # --------------------------------------------------- 3D PLOT {X vs Y vs T} --------------------------------------------------- #
        fig3 = plt.figure(3, figsize = (10, 8))
        dx = fig3.add_subplot(311, projection='3d')
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

        # --------------------------------------------------- 3D PLOT {Y vs Z vs T} --------------------------------------------------- #
        dx = fig3.add_subplot(312, projection='3d')
        dx.set_xlim(0, 15) ## dx.set_xlim(self.get_x_start(), self.get_x_finish())
        dx.set_ylim(0, 15) ## dx.set_ylim(self.get_y_start(), self.get_y_finish())
        dx.set_zlim(0, 15) ## dx.set_zlim(self.getStart(), self.getFinish())
        dx.set_xlabel('X Axis')
        dx.set_ylabel('Y Axis')
        dx.set_zlabel('Time Axis')

        for i in range(self.getRange()):
            vertices = [[z_u[i], y_u[i], i * self._step], [z_l[i], y_u[i], i * self._step], [z_l[i], y_l[i], i * self._step], [z_u[i], y_l[i], i * self._step],
                        [z_u[i], y_u[i], i * self._step], [z_l[i], y_u[i], i * self._step], [z_l[i], y_l[i], i * self._step], [z_u[i], y_l[i], i * self._step]]

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

        # --------------------------------------------------- 3D PLOT {X vs Z vs T} --------------------------------------------------- #
        dx = fig3.add_subplot(313, projection='3d')
        dx.set_xlim(0, 15) ## dx.set_xlim(self.get_x_start(), self.get_x_finish())
        dx.set_ylim(0, 15) ## dx.set_ylim(self.get_y_start(), self.get_y_finish())
        dx.set_zlim(0, 15) ## dx.set_zlim(self.getStart(), self.getFinish())
        dx.set_xlabel('X Axis')
        dx.set_ylabel('Y Axis')
        dx.set_zlabel('Time Axis')

        for i in range(self.getRange()):
            vertices = [[z_u[i], z_u[i], i * self._step], [z_l[i], z_u[i], i * self._step], [z_l[i], z_l[i], i * self._step], [z_u[i], z_l[i], i * self._step],
                        [z_u[i], z_u[i], i * self._step], [z_l[i], z_u[i], i * self._step], [z_l[i], z_l[i], i * self._step], [z_u[i], z_l[i], i * self._step]]

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
        days = k // (3600 * 24)
        hrs = (k // 3600) - (days * 24)
        mins = (k // 60) - (hrs * 60)
        if end - start < 1:
            secs = (((end - start) * 10000) // 100) / 100
        else:
            secs = k - (mins * 60) - (hrs * 3600) - (days * 24 * 3600)
        print("Time taken: ", days, "days, ", hrs , "hours, ", mins, "minutes, ", secs, "seconds")

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

    def get_goal(self):
        return self.goal

    def set_goal(self, value):
        self.goal = value


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

    def checkCallableAndCallExecute(self):
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

    def checkCallableAndCallExecute(self):
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

    def checkCallableAndCallExecute(self):
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
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def add_resultant(self):
        '''adds constraints'''
        for instance in self.instances:
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS) or isinstance(instance, AND) or isinstance(instance, IMPLIES):
                instance.return_value = True
                constraints = instance.call()
                for constraint in constraints:
                    self.main.solver.add(constraint)
            elif isinstance(instance, OR):
                constraints = instance.call()
                self.main.solver.add(constraints)
            else:
                print("Unknown Instance")

    def return_resultant(self):
        '''returns constraints'''
        all_constraints =[]
        for instance in self.instances:
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS) or isinstance(instance, AND):
                instance.return_value = True
                constraints = instance.call()
                for constraint in constraints:
                    all_constraints.append(constraint)
            elif isinstance(instance, OR):
                constraints = instance.call()
                all_constraints.append(constraints)
            else:
                print("Unknown Instance")
        return all_constraints

    def call(self):
        if self.return_value == True:
            return self.return_resultant()
        else:
            self.add_resultant()


class OR(STL):
    def __init__(self, identifier, *instances):
        self.choice = None
        self.instances = instances
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")
        
        self.reach_or_targets = []
        self.avoid_or_targets = []
        self.stay_or_targets = []
        
        for instance in self.instances:
            if isinstance(instance.task, REACH):
                self.reach_or_targets.append(instance.task.local_setpoint)
            if isinstance(instance.task, AVOID):
                self.avoid_or_targets.append(instance.task.local_obstacle)
            if isinstance(instance.task, STAY):
                self.stay_or_targets.append(instance.task.local_setpoint)
    
        self.all_or_targets = self.reach_or_targets + self.avoid_or_targets + self.stay_or_targets
        self.goal = [3, 4, 3, 4, 3, 4]

    def add_resultant(self):
        if self.reach_or_targets != []:
            print("OR reach-target options: ", self.reach_or_targets)
            self.choice = self.reach_or_targets.index(self.main.min_distance_element(self.reach_or_targets, self.goal))
            print("choice: ", self.choice)
            constraints = self.instances[self.choice].call()
            self.main.solver.add(constraints)

        elif self.avoid_or_targets != []:
            print("OR avoid-target options: ", self.avoid_or_targets)
            self.choice = self.avoid_or_targets.index(self.main.min_distance_element(self.avoid_or_targets, self.goal))
            print("choice: ", self.choice)
            constraints = self.instances[self.choice].call()
            self.main.solver.add(constraints)

        elif self.reach_or_targets != [] and self.avoid_or_targets != []:
            print("All OR target options: ", self.all_or_targets)
            self.choice = self.all_or_targets.index(self.main.min_distance_element(self.all_or_targets, self.goal))
            print("choice: ", self.choice)
            constraints = self.instances[self.choice].call()
            self.main.solver.add(constraints)

        else:
            raise ValueError("No options in 'OR' block!")

    def return_resultant(self):
        if self.reach_or_targets != [] and self.avoid_or_targets == []:
            print("OR reach-target options: ", self.reach_or_targets)
            self.choice = self.reach_or_targets.index(self.main.min_distance_element(self.reach_or_targets, self.goal))
            print("choice: ", self.choice)
            constraints = self.instances[self.choice].call()
            return constraints

        elif self.avoid_or_targets != [] and self.reach_or_targets == []:
            print("OR avoid-target options: ", self.avoid_or_targets)
            self.choice = self.avoid_or_targets.index(self.main.min_distance_element(self.avoid_or_targets, self.goal))
            print("choice: ", self.choice)
            constraints = self.instances[self.choice].call()
            return constraints
        
        elif self.reach_or_targets != [] and self.avoid_or_targets != []:
            print("All OR target options: ", self.all_or_targets)
            self.choice = self.all_or_targets.index(self.main.min_distance_element(self.all_or_targets, self.goal))
            print("choice: ", self.choice)
            constraints = self.instances[self.choice].call()
            return constraints
        
        else:
            raise ValueError("No options in 'OR' block!")

    def call(self):
        if self.return_value == True:
            return self.return_resultant()
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
        for instance in self.instances:
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS) or isinstance(instance, AND):
                instance.return_value = True
                constraints = instance.call()
                for constraint in constraints:
                    self.main.solver.add(z3.Not(constraint))
            elif isinstance(instance, OR):
                constraints = instance.call()
                self.main.solver.add(z3.Not(constraints))
            else:
                print("Unknown Instance")

    def return_resultant(self):
        '''returns constraints'''
        all_constraints =[]
        for instance in self.instances:
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS) or isinstance(instance, AND):
                instance.return_value = True
                constraints = instance.call()
                for constraint in constraints:
                    all_constraints.append(z3.Not(constraint))
            elif isinstance(instance, OR):
                constraints = instance.call()
                all_constraints.append(z3.Not(constraints))
            else:
                print("Unknown Instance")
        return all_constraints

    def call(self):
        if self.return_value == True:
            return self.return_resultant()
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
            return all_constraints
        else:
            self.main.solver.add(all_constraints)


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
    def __init__(self, identifier, instance_a, instance_b):
        self.instance_a = instance_a
        self.instance_b = instance_b
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def add_resultant(self):
        '''adds constraints'''
        pass

    def return_resultant(self):
        '''returns constraints'''
        pass

    def call(self):
        if self.return_value == True:
            return self.return_resultant()
        else:
            self.add_resultant()


class IMPLIES(STL):
    def __init__(self, identifier, instance_a, instance_b):
        self.instance_a = instance_a
        self.instance_b = instance_b
        self.return_value = True
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def call(self):
        all_constraints_a = []
        all_constraints_b = []
        implies_constraint = []

        if isinstance(self.instance_a, EVENTUALLY) or isinstance(self.instance_a, ALWAYS):
            constraints = self.instance_a.call()
            for constraint in constraints:
                all_constraints_a.append(constraint)
        elif isinstance(self.instance_a, AND):
            self.instance_a.return_value = True
            constraints = self.instance_a.call()
            for constraint in constraints:
                all_constraints_a.append(constraint)
        elif isinstance(self.instance_a, OR):
            constraints = self.instance_a.call()
            all_constraints_a.append(constraints)
        else:
            print("Unknown Instance")

        if isinstance(self.instance_b, EVENTUALLY) or isinstance(self.instance_b, ALWAYS):
            constraints = self.instance_b.call()
            for constraint in constraints:
                all_constraints_b.append(constraint)
        elif isinstance(self.instance_b, AND):
            self.instance_b.return_value = True
            constraints = self.instance_b.call()
            for constraint in constraints:
                all_constraints_b.append(constraint)
        elif isinstance(self.instance_b, OR):
            constraints = self.instance_b.call()
            all_constraints_b.append(constraints)
        else:
            print("Unknown Instance")

        for i in range(len(all_constraints_a)):
            for j in range(len(all_constraints_b)):
                implies_constraint.append(z3.Or(z3.Not(all_constraints_a[i]), all_constraints_b[j]))

        if self.return_value == True:
            return implies_constraint
        else:
            for i in implies_constraint:
                self.main.solver.add(i)


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


#------ ALWAYS EVENTUALLY CASE -----#
# obj2 = AND(1, EVENTUALLY(1, 0, 1, REACH(stl2.main, 0, 1, 0, 1)), 
#                EVENTUALLY(1, 3, 4, REACH(stl2.main, 7, 8, 11, 12)),
#                EVENTUALLY(1, 6, 7, REACH(stl2.main, 10, 11, 7, 8)),
#                EVENTUALLY(1, 9, 10, REACH(stl2.main, 7, 8, 11, 12)),
#                EVENTUALLY(1, 12, 13, REACH(stl2.main, 11, 12, 7, 8)),
#                EVENTUALLY(1, 14, 15, REACH(stl2.main, 14, 15, 14, 15))
#             ).call()
#-----------------------------------#

stl2.plotter()



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