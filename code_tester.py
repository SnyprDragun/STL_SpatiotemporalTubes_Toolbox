#!/opt/homebrew/bin/python3.11
'''script to try out various code snippets'''

########################################## to print all z3 solutions ##########################################
# import z3

# a = z3.Int('a')
# b = z3.Int('b')

# s = z3.Solver()
# s.add(1 <= a)
# s.add(a <= 20)
# s.add(1 <= b)
# s.add(b <= 20)
# s.add(a >= 2*b)

# while s.check() == z3.sat:
#     print(s.model())
#     s.add(z3.Or(a != s.model()[a], b != s.model()[b])) # prevent next model from using the same assignment as a previous model

########################################## to continuously print on one graph ##########################################
# import matplotlib.pyplot as plt
# import numpy as np

# # Initialize the figure and axis
# fig, ax = plt.subplots()

# # Example loop to plot multiple curves
# for i in range(5):
#     x = np.linspace(0, 2 * np.pi, 100)
#     y = np.sin(x + i)  # Create a new curve in each iteration
    
#     ax.plot(x, y, label=f'Curve {i+1}')  # Plot the curve with a label
    
#     ax.legend()  # Update legend with the new curve
    
#     # Manually update the figure canvas
#     fig.canvas.draw()
    
#     plt.pause(1)  # Pause to see the new curve being added

# # Keep the plot open at the end
# plt.show()


########################################## to add array to array ##########################################
# # Initialize an empty array
# arr1 = []

# # Create arr2 and arr3
# arr2 = [1, 2, 3]
# arr3 = [4, 5, 6]

# # Add arr2 to arr1
# arr1.append(arr2)
# print(arr1)  # Output will be [[1, 2, 3]]

# # Add arr3 to arr1
# arr1.append(arr3)
# print(arr1)  # Output will be [[1, 2, 3], [4, 5, 6]]
# import numpy as np

# # Initialize an empty list
# arr1 = []

# # Create arr2 and arr3 as numpy arrays
# arr2 = np.array([1, 2, 3])
# arr3 = np.array([4, 5, 6])

# # Add arr2 to arr1
# arr1.append(arr2)
# print(arr1)  # Output will be [array([1, 2, 3])]

# # Add arr3 to arr1
# arr1.append(arr3)
# print(arr1)  # Output will be [array([1, 2, 3]), array([4, 5, 6])]
# import numpy as np

# # Create arr2 and arr3 as numpy arrays
# arr2 = np.array([1, 2, 3])
# arr3 = np.array([4, 5, 6])

# # Initialize arr1 as an empty numpy array with the correct shape
# arr1 = np.array([arr2])  # Start with arr2 as the first element

# print(arr1)
# # Output: [[1 2 3]]

# # Add arr3 to arr1 using vstack
# arr1 = np.vstack([arr1, arr3])
# print(arr1)
# # Output: [[1 2 3]
# #          [4 5 6]]


# import matplotlib.pyplot as plt

# # Create a figure and three subplots arranged vertically
# fig, axs = plt.subplots(3, 1, figsize=(8, 12), constrained_layout=True)

# # Unpack the subplots
# ax, bx, cx = axs

# # Add simple content to each subplot to confirm layout
# ax.plot([1, 2, 3], [1, 4, 9])
# bx.plot([1, 2, 3], [1, 2, 3])
# cx.plot([1, 2, 3], [9, 4, 1])

# # Set titles for clarity (optional)
# ax.set_title("First Subplot")
# bx.set_title("Second Subplot")
# cx.set_title("Third Subplot")

# # Display the figure with all three subplots
# plt.show()

# import matplotlib.pyplot as plt
# import matplotlib.patches as patches
# setpoints = [[0, 1, 0, 1, 0, 1, 0, 1], [2, 3, 2, 3, 2, 3, 4, 5]]
# # Create a figure and three subplots arranged vertically
# fig, axs = plt.subplots(3, 1, figsize=(8, 12), constrained_layout=True)

# # Unpack the subplots
# ax, bx, cx = axs

# # Adjust the spacing between the subplots using `constrained_layout`
# # `constrained_layout=True` automatically adjusts subplot parameters to give specified padding.

# # Example: Add square patches to the first and second subplots
# for i in setpoints:  # t1  x1/y1  t2   t1   x2/y2  x1/y1
#     square_x = patches.Rectangle((i[4], i[0]), i[5] - i[4], i[1] - i[0], edgecolor='green', facecolor='none')
#     square_y = patches.Rectangle((i[4], i[2]), i[5] - i[4], i[3] - i[2], edgecolor='green', facecolor='none')

#     ax.add_patch(square_x)  # Add patch to the first subplot
#     bx.add_patch(square_y)  # Add patch to the second subplot

# # Set titles for clarity (optional)
# ax.set_title("First Subplot")
# bx.set_title("Second Subplot")
# cx.set_title("Third Subplot")

# # Display the figure with all three subplots
# plt.show()

# import matplotlib.pyplot as plt
# import matplotlib.patches as patches

# # Create a figure and three subplots arranged vertically
# fig, axs = plt.subplots(3, 1, figsize=(8, 12), constrained_layout=True)

# # Unpack the subplots
# ax, bx, cx = axs

# # Example data for setpoints (replace this with your actual data)
# setpoints = [[0.1, 0.2, 0.3, 0.4, 0.1, 0.3]]  # Modify as needed

# # Add patches to the first and second subplots
# for i in setpoints:
#     square_x = patches.Rectangle((i[4], i[0]), i[5] - i[4], i[1] - i[0], edgecolor='green', facecolor='none')
#     square_y = patches.Rectangle((i[4], i[2]), i[5] - i[4], i[3] - i[2], edgecolor='green', facecolor='none')

#     ax.add_patch(square_x)
#     bx.add_patch(square_y)

# # Set the axes limits to ensure patches are visible
# ax.set_xlim(0, 1)
# ax.set_ylim(0, 1)
# bx.set_xlim(0, 1)
# bx.set_ylim(0, 1)

# # Add a simple plot to the third subplot for comparison
# cx.plot([1, 2, 3], [9, 4, 1])

# # Set titles for clarity (optional)
# ax.set_title("First Subplot")
# bx.set_title("Second Subplot")
# cx.set_title("Third Subplot")

# # Display the figure with all three subplots
# plt.show()


# class A():
#     def __init__(self):
#         self.main = D()

# class B(A):
#     def __init__(self):
#         pass

# class C(B):
#     def __init__(self):
#         pass

#     def task(self):
#         self.main.execute()

# class D():
#     def execute(self):
#         print("Hi")

# obj = C()
# obj.task()

# class A():
#     def __init__(self):
#         self.main = D()

# class B(A):
#     def __init__(self):
#         super().__init__()

# class C(B):
#     def __init__(self):
#         super().__init__()
        
#     def task(self):
#         self.main.execute()

# class D():
#     def execute(self):
#         print("Hi")

# # Create an object of class C and call the task method
# c_object = C()
# c_object.task()


# class G():
#     def __init__(self):
#         self.solver = 5

# class STL():
#     '''class to solve STL specifications'''
#     def __init__(self):
#         self.main = G()

#     def AND(self, *args1):
#         print("A", self.main.solver, len(args1), args1)
#         obj3 = AND(args1)
#         obj3.AND()

# class AND(STL):
#     def __init__(self, *args2):
#         super().__init__()
#         self.args2 = args2

#     def AND(self):
#         print("B", self.main.solver, len(self.args2), self.args2)

#         # for constraints in self.args2:
#         #     for constraint in constraints:
#         #             print(constraint)

# obj1 = STL()
# obj1.AND(4, 4, 4, 4)

# obj2 = AND(3, 3, 3)
# obj2.AND()
# import random

# class A():
#     num = random.randint(0, 5)
#     def __init__(self):
#         pass

# class B():
#     def __init__(self):
#         self.main = A()
#         print(self.main.num)

# class C(B):
#     def __init__(self):
#         super().__init__()
#         self.fn()

#     def fn(self):
#         print(self.main.num)

# obj1 = B()
# obj2 = C()
# import random
# print(random.randint(0,3))


# class A:
#     _instances = {}  # Registry for storing instances

#     def __init__(self, identifier, num):
#         # Store num and register the instance
#         self.num = num
#         A._instances[identifier] = self

#     @classmethod
#     def get_instance(cls, identifier):
#         # Fetch the instance from the registry by identifier
#         return cls._instances.get(identifier)


# class B:
#     def __init__(self, identifier):
#         # Automatically get the appropriate instance of A by identifier
#         self.main = A.get_instance(identifier)
#         if self.main:
#             print(self.main.num)
#         else:
#             print(f"No instance of A found for identifier '{identifier}'")

# class C(B):
#     def __init__(self, identifier):
#         # Call the parent constructor with the identifier
#         super().__init__(identifier)
#         print(self.main.num)

# # Create multiple instances of A with different identifiers
# A('a1', 3)
# A('a2', 5)

# # Create objects of B and C using the identifiers without passing A instances
# obj1 = C('a1')  # This will print 3
# obj2 = C('a2')  # This will print 5 twice

# import torch
# import z3
# import time

# start = time.time()
# x1 = 0
# x2 = 1

# def gammas(self, t_values):
#     ''' Vectorized version for computing tube equations, keeping symbolic coefficients '''
#     num_t_values = len(t_values)
    
#     # Prepare the tubes array to hold symbolic expressions
#     tubes = [[z3.Real(f'e_{i}_{j}') for j in range(num_t_values)] for i in range(2 * 3)]
    
#     # Compute powers of t_values using Torch for parallelism
#     powers = torch.stack([t_values ** i for i in range(2 + 1)], dim=-1)  # Shape: (len(t_values), degree+1)
    
#     # Now iterate over dimensions and construct symbolic tubes with Z3
#     for i in range(2 * 3):
#         for j in range(num_t_values):
#             tubes[i][j] = 0
#             for k in range(2 + 1):
#                 tubes[i][j] += self.C[k + i * (2 + 1)] * powers[j, k].item()  # `.item()` extracts the value from the tensor
            
#     return tubes

# # Create torch tensors for t_values and lambda_values
# t_values = torch.linspace(0, 1, steps=11)
# lambda_values = torch.linspace(0, 1, steps=11)

# # Call the gammas function with t_values
# gammas_at_all_t = gammas(t_values)

# all_constraints = []
# for i, t in enumerate(t_values):
#     gamma1_L, gamma1_U = gammas_at_all_t[0][i], gammas_at_all_t[1][i]  # Extract symbolic gammas for each t
    
#     # Compute constraints as symbolic Z3 expressions
#     for lambda_1 in lambda_values:
#         x = lambda_1.item() * gamma1_L + (1 - lambda_1.item()) * gamma1_U
#         constraint = z3.And(x < x2, x > x1)
#         all_constraints.append(constraint)

# print("Time: ", time.time() - start)


# import z3

# def find_common_solution(*solvers):
#     models = []
    
#     # Solve each solver and get its model
#     for solver in solvers:
#         if solver.check() == z3.sat:
#             model = solver.model()
#             models.append(model)
#         else:
#             print("One of the solvers is unsatisfiable")
#             return None  # If one is unsatisfiable, there is no common solution
    
#     if not models:
#         print("No models found")
#         return None

#     # Create a dictionary to store the common values of the variables
#     common_values = {}
    
#     # Get variables from the first model
#     for v in models[0]:
#         # Extract the value from the model and store it
#         common_values[v] = models[0][v].as_long()
    
#     # Compare with subsequent models
#     for model in models[1:]:
#         for v in common_values:
#             # Extract the value from the current model
#             value = model[v].as_long()
#             # Compare values
#             if common_values[v] != value:
#                 print("No common solution found among models")
#                 return None
    
#     return common_values

# # Usage example:
# # Define some Z3 solvers
# solver1 = z3.Solver()
# solver2 = z3.Solver()

# # Define some Z3 variables
# x = z3.Int('x')
# y = z3.Int('y')

# # Add constraints to the solvers
# solver1.add(x > 5, y == 10)
# solver2.add(x < 10, y == 10)

# # Find common solution
# common_solution = find_common_solution(solver1, solver2)

# # Print the solution if it exists
# if common_solution:
#     print("Common solution:", common_solution)
# else:
#     print("No common solution")


# class STL:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
# class REACH:
#     def __init__(self, stl, target):
#         self.stl = stl
#         self.target = target
    
#     def call(self):
#         return f"REACH({self.target})"

# class AVOID:
#     def __init__(self, stl, obstacle):
#         self.stl = stl
#         self.obstacle = obstacle
    
#     def call(self):
#         return f"AVOID({self.obstacle})"

# class EVENTUALLY:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
#     def call(self):
#         return f"EVENTUALLY({self.operation})"

# class ALWAYS:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
#     def call(self):
#         return f"ALWAYS({self.operation})"

# class AND:
#     def __init__(self, level, *operations):
#         self.level = level
#         self.operations = operations
    
#     def call(self):
#         return f"AND({', '.join(self.operations)})"

# class OR:
#     def __init__(self, level, *operations):
#         self.level = level
#         self.operations = operations
    
#     def call(self):
#         return f"OR({', '.join(self.operations)})"

# def transform_formula(T1, T2, O1, O2):
#     # Create an STL object instance with SeqReachAvoidStay
#     stl = STL(1, "SeqReachAvoidStay")
    
#     # Build the semantic representation step by step
#     eventually_T1 = EVENTUALLY(1, REACH(stl, T1).call()).call()
#     eventually_T2 = EVENTUALLY(1, REACH(stl, T2).call()).call()
#     avoid_O1 = ALWAYS(1, AVOID(stl, O1).call()).call()
#     avoid_O2 = ALWAYS(1, AVOID(stl, O2).call()).call()
    
#     # Combine using OR for the targets and AND for the overall formula
#     or_targets = OR(1, eventually_T1, eventually_T2).call()
#     and_obstacles = AND(1, avoid_O1, avoid_O2).call()
    
#     # Final formula using AND
#     formula = AND(1, or_targets, and_obstacles).call()
    
#     return formula

# # Example usage
# T1 = "T1"
# T2 = "T2"
# O1 = "O1"
# O2 = "O2"

# result = transform_formula(T1, T2, O1, O2)
# print(result)


# import re

# class STL:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation

# class REACH:
#     def __init__(self, stl, target):
#         self.stl = stl
#         self.target = target
    
#     def call(self):
#         return f"REACH({self.target})"

# class AVOID:
#     def __init__(self, stl, obstacle):
#         self.stl = stl
#         self.obstacle = obstacle
    
#     def call(self):
#         return f"AVOID({self.obstacle})"

# class EVENTUALLY:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
#     def call(self):
#         return f"EVENTUALLY({self.operation})"

# class ALWAYS:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
#     def call(self):
#         return f"ALWAYS({self.operation})"

# class AND:
#     def __init__(self, level, *operations):
#         self.level = level
#         self.operations = operations
    
#     def call(self):
#         return f"AND({', '.join(self.operations)})"

# class OR:
#     def __init__(self, level, *operations):
#         self.level = level
#         self.operations = operations
    
#     def call(self):
#         return f"OR({', '.join(self.operations)})"

# # Map LTL symbols to STL functions
# ltl_to_stl_mapping = {
#     '◊': EVENTUALLY,
#     '□': ALWAYS,
#     '∧': AND,
#     '∨': OR,
#     '¬': AVOID  # Negation treated as avoiding the obstacle
# }

# # Parsing the formula and dynamically building the STL expression
# def parse_formula(stl, formula):
#     tokens = re.split(r'(\s|◊|□|∧|∨|¬|\(|\))', formula)
#     tokens = [token for token in tokens if token.strip()]  # Remove empty tokens
    
#     stack = []
    
#     for token in tokens:
#         if token == '(':
#             stack.append(token)  # Push '(' onto the stack
#         elif token in ('T1', 'T2'):
#             stack.append(REACH(stl, token).call())
#         elif token in ('O1', 'O2'):
#             stack.append(AVOID(stl, token).call())
#         elif token in ltl_to_stl_mapping:
#             stack.append(token)  # Push operator
#         elif token == ')':
#             # Pop the expression to evaluate, applying the STL operator
#             args = []
#             while stack and stack[-1] != '(':
#                 args.insert(0, stack.pop())
#             if stack and stack[-1] == '(':
#                 stack.pop()  # Remove '('
            
#             if len(stack) > 0 and stack[-1] in ltl_to_stl_mapping:
#                 operator = stack.pop()  # Get operator
#                 if operator == '¬':  # Negation only applies to one operand
#                     stl_operator = ltl_to_stl_mapping[operator](stl, args[0]).call()
#                 else:
#                     stl_operator = ltl_to_stl_mapping[operator](1, *args).call()
#                 stack.append(stl_operator)
#             else:
#                 raise ValueError("Mismatched parentheses or missing operator.")
#         else:
#             raise ValueError(f"Unexpected token: {token}")
    
#     if len(stack) != 1:
#         raise ValueError("Formula parsing error: incomplete or invalid formula.")
    
#     return stack[0]

# # General function to convert LTL formula to STL
# def transform_formula(stl, formula):
#     return parse_formula(stl, formula)

# # Example usage
# stl = STL(1, "SeqReachAvoidStay")
# formula = "(◊ T1 ∨ ◊ T2) ∧ (□ ¬(O1 ∧ O2))"  # Input formula
# semantic = transform_formula(stl, formula)
# print(semantic)


# import re

# class STL:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation

# class REACH:
#     def __init__(self, stl, target):
#         self.stl = stl
#         self.target = target
    
#     def call(self):
#         return f"REACH({self.target})"

# class AVOID:
#     def __init__(self, stl, obstacle):
#         self.stl = stl
#         self.obstacle = obstacle
    
#     def call(self):
#         return f"AVOID({self.obstacle})"

# class EVENTUALLY:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
#     def call(self):
#         return f"EVENTUALLY({self.operation})"

# class ALWAYS:
#     def __init__(self, level, operation):
#         self.level = level
#         self.operation = operation
    
#     def call(self):
#         return f"ALWAYS({self.operation})"

# class AND:
#     def __init__(self, level, *operations):
#         self.level = level
#         self.operations = operations
    
#     def call(self):
#         return f"AND({', '.join(self.operations)})"

# class OR:
#     def __init__(self, level, *operations):
#         self.level = level
#         self.operations = operations
    
#     def call(self):
#         return f"OR({', '.join(self.operations)})"

# # Map LTL symbols to STL functions
# ltl_to_stl_mapping = {
#     '◊': EVENTUALLY,
#     '□': ALWAYS,
#     '∧': AND,
#     '∨': OR,
#     '¬': AVOID  # Negation for avoid
# }

# # Parsing the formula and dynamically building the STL expression
# def parse_formula(stl, formula):
#     tokens = re.split(r'(\s|◊|□|∧|∨|¬|\(|\))', formula)
#     tokens = [token for token in tokens if token.strip()]  # Remove empty tokens
    
#     stack = []
    
#     for token in tokens:
#         if token == '(':
#             stack.append(token)  # Push '(' onto the stack
#         elif token in ('T1', 'T2'):
#             stack.append(REACH(stl, token).call())
#         elif token in ('O1', 'O2'):
#             stack.append(AVOID(stl, token).call())
#         elif token in ltl_to_stl_mapping:
#             stack.append(token)  # Push operator
#         elif token == ')':
#             # Pop the expression to evaluate, applying the STL operator
#             args = []
#             while stack and stack[-1] != '(':
#                 args.insert(0, stack.pop())
#             if stack and stack[-1] == '(':
#                 stack.pop()  # Remove '('
            
#             if len(stack) > 0 and stack[-1] in ltl_to_stl_mapping:
#                 operator = stack.pop()  # Get operator
#                 if operator == '¬':  # Negation only applies to one operand
#                     stl_operator = ltl_to_stl_mapping[operator](stl, args[0]).call()
#                 else:
#                     stl_operator = ltl_to_stl_mapping[operator](1, *args).call()
#                 stack.append(stl_operator)
#             else:
#                 raise ValueError("Mismatched parentheses or missing operator.")
#         else:
#             raise ValueError(f"Unexpected token: {token}")
    
#     if len(stack) != 1:
#         raise ValueError("Formula parsing error: incomplete or invalid formula.")
    
#     return stack[0]

# # General function to convert LTL formula to STL
# def transform_formula(stl, formula):
#     open_parens = formula.count('(')
#     close_parens = formula.count(')')
    
#     # Check if parentheses are balanced
#     if open_parens != close_parens:
#         raise ValueError(f"Unbalanced parentheses: {open_parens} opening and {close_parens} closing.")
    
#     return parse_formula(stl, formula)

# # Example usage
# stl = STL(1, "SeqReachAvoidStay")
# formula = "(◊ T1 ∨ ◊ T2) ∧ (□ ¬(O1 ∧ O2))"  # Input formula
# semantic = transform_formula(stl, formula)
# print(semantic)


import re

class STL:
    def __init__(self, level, operation):
        self.level = level
        self.operation = operation

class REACH:
    def __init__(self, stl, target):
        self.stl = stl
        self.target = target
    
    def call(self):
        return f"REACH({self.target})"

class AVOID:
    def __init__(self, stl, obstacle):
        self.stl = stl
        self.obstacle = obstacle
    
    def call(self):
        return f"AVOID({self.obstacle})"

class EVENTUALLY:
    def __init__(self, level, operation):
        self.level = level
        self.operation = operation
    
    def call(self):
        return f"EVENTUALLY({self.operation})"

class ALWAYS:
    def __init__(self, level, operation):
        self.level = level
        self.operation = operation
    
    def call(self):
        return f"ALWAYS({self.operation})"

class AND:
    def __init__(self, level, left, right):
        self.level = level
        self.left = left
        self.right = right
    
    def call(self):
        return f"AND({self.left}, {self.right})"

class OR:
    def __init__(self, level, left, right):
        self.level = level
        self.left = left
        self.right = right
    
    def call(self):
        return f"OR({self.left}, {self.right})"

# Map LTL symbols to STL functions
ltl_to_stl_mapping = {
    '◊': EVENTUALLY,
    '□': ALWAYS,
    '∧': AND,
    '∨': OR,
    '¬': AVOID  # Negation treated as avoiding the obstacle
}

# Improved tokenization function
def tokenize(formula):
    # Split formula by operators, parentheses, and atomic propositions
    tokens = re.findall(r'(\w+|[◊□¬∧∨()])', formula)
    return tokens

# Parsing the formula and dynamically building the STL expression
def parse_formula(stl, formula):
    tokens = tokenize(formula)
    
    stack = []
    operator_stack = []
    
    for token in tokens:
        if token in ('T1', 'T2'):
            stack.append(REACH(stl, token).call())
        elif token in ('O1', 'O2'):
            stack.append(AVOID(stl, token).call())
        elif token in ltl_to_stl_mapping:
            operator_stack.append(token)  # Push operator
        elif token == '(':
            operator_stack.append(token)  # Push '('
        elif token == ')':
            # Apply operators until '('
            while operator_stack and operator_stack[-1] != '(':
                operator = operator_stack.pop()
                if operator == '¬':
                    operand = stack.pop()
                    stack.append(ltl_to_stl_mapping[operator](stl, operand).call())
                else:
                    right = stack.pop()
                    left = stack.pop()
                    stack.append(ltl_to_stl_mapping[operator](1, left, right).call())
            operator_stack.pop()  # Pop '('
        else:
            raise ValueError(f"Unexpected token: {token}")

    # If any operators are left after the loop
    while operator_stack:
        operator = operator_stack.pop()
        if operator == '¬':
            operand = stack.pop()
            stack.append(ltl_to_stl_mapping[operator](stl, operand).call())
        else:
            right = stack.pop()
            left = stack.pop()
            stack.append(ltl_to_stl_mapping[operator](1, left, right).call())

    if len(stack) != 1:
        raise ValueError("Formula parsing error: incomplete or invalid formula.")
    
    return stack[0]

# General function to convert LTL formula to STL
def transform_formula(stl, formula):
    return parse_formula(stl, formula)

# Example usage
stl = STL(1, "SeqReachAvoidStay")
formula = "(◊ T1 ∨ ◊ T2) ∧ (□ ¬(O1 ∧ O2))"  # Input formula
semantic = transform_formula(stl, formula)
print(semantic)
