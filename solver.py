#!/opt/homebrew/bin/python3.11
'''script for Z3 Solver'''
import z3
import numpy as np

class SOLVER():
    def __init__(self, degree = None, dimension = None):
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
            except OverflowError:
                    print("OverflowError")
                    break

            for i in range(len(self.C)):
                a = self.C[i]
                b = model[self.C[i]]
                second_decimal_of_a = z3.ToInt((a * 10000) / 100) % 10
                second_decimal_of_b = z3.ToInt((b * 10000) / 100) % 10
                self.solver.add(second_decimal_of_a != second_decimal_of_b)
        print("All Solutions: ", all_solutions)
        return all_solutions

    def commonSolution(self, *solvers):
        pass