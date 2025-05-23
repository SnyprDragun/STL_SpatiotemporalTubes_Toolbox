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
#     def __init__(self, level, left, right):
#         self.level = level
#         self.left = left
#         self.right = right
    
#     def call(self):
#         return f"AND({self.left}, {self.right})"

# class OR:
#     def __init__(self, level, left, right):
#         self.level = level
#         self.left = left
#         self.right = right
    
#     def call(self):
#         return f"OR({self.left}, {self.right})"

# # Map LTL symbols to STL functions
# ltl_to_stl_mapping = {
#     '◊': EVENTUALLY,
#     '□': ALWAYS,
#     '∧': AND,
#     '∨': OR,
#     '¬': AVOID  # Negation treated as avoiding the obstacle
# }

# # Improved tokenization function
# def tokenize(formula):
#     # Split formula by operators, parentheses, and atomic propositions
#     tokens = re.findall(r'(\w+|[◊□¬∧∨()])', formula)
#     return tokens

# # Parsing the formula and dynamically building the STL expression
# def parse_formula(stl, formula):
#     tokens = tokenize(formula)
    
#     stack = []
#     operator_stack = []
    
#     for token in tokens:
#         if token in ('T1', 'T2'):
#             stack.append(REACH(stl, token).call())
#         elif token in ('O1', 'O2'):
#             stack.append(AVOID(stl, token).call())
#         elif token in ltl_to_stl_mapping:
#             operator_stack.append(token)  # Push operator
#         elif token == '(':
#             operator_stack.append(token)  # Push '('
#         elif token == ')':
#             # Apply operators until '('
#             while operator_stack and operator_stack[-1] != '(':
#                 operator = operator_stack.pop()
#                 if operator == '¬':
#                     operand = stack.pop()
#                     stack.append(ltl_to_stl_mapping[operator](stl, operand).call())
#                 else:
#                     right = stack.pop()
#                     left = stack.pop()
#                     stack.append(ltl_to_stl_mapping[operator](1, left, right).call())
#             operator_stack.pop()  # Pop '('
#         else:
#             raise ValueError(f"Unexpected token: {token}")

#     # If any operators are left after the loop
#     while operator_stack:
#         operator = operator_stack.pop()
#         if operator == '¬':
#             operand = stack.pop()
#             stack.append(ltl_to_stl_mapping[operator](stl, operand).call())
#         else:
#             right = stack.pop()
#             left = stack.pop()
#             stack.append(ltl_to_stl_mapping[operator](1, left, right).call())

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
# from typing import Dict, Callable

# # Define the STL classes and functions (placeholders)
# class STL:
#     def __init__(self, level, func):
#         self.level = level
#         self.func = func

# class SeqReachAvoidStay:
#     def call(self):
#         # Placeholder function
#         return "SeqReachAvoidStay"

# class AND:
#     def __init__(self, level, *args):
#         self.level = level
#         self.args = args
#     def call(self):
#         # Placeholder function
#         return "AND"

# class OR:
#     def __init__(self, level, *args):
#         self.level = level
#         self.args = args
#     def call(self):
#         # Placeholder function
#         return "OR"

# class EVENTUALLY:
#     def __init__(self, level, condition):
#         self.level = level
#         self.condition = condition
#     def call(self):
#         # Placeholder function
#         return "EVENTUALLY"

# class ALWAYS:
#     def __init__(self, level, condition):
#         self.level = level
#         self.condition = condition
#     def call(self):
#         # Placeholder function
#         return "ALWAYS"

# class REACH:
#     def __init__(self, stl, condition):
#         self.stl = stl
#         self.condition = condition
#     def call(self):
#         # Placeholder function
#         return "REACH"

# class AVOID:
#     def __init__(self, stl, condition):
#         self.stl = stl
#         self.condition = condition
#     def call(self):
#         # Placeholder function
#         return "AVOID"

# # Function to parse and convert list-like brackets
# def parse_bracket_contents(contents: str):
#     # Remove any surrounding brackets and split by commas
#     contents = contents.strip('[]').strip()
#     return list(map(float, contents.split(',')))

# def parse_formula(stl, formula: str):
#     operators = {'∧': AND, '∨': OR}
#     temporal_operators = {'♦': EVENTUALLY, '□': ALWAYS}
#     ltl_to_stl_mapping = {'REACH': REACH, 'AVOID': AVOID}

#     tokens = re.split(r'(\s*∧\s*|\s*∨\s*|\s*♦\s*|\s*□\s*)', formula)
#     stack = []
    
#     i = 0
#     while i < len(tokens):
#         token = tokens[i].strip()
#         if not token:
#             i += 1
#             continue
        
#         if token in operators:
#             right = stack.pop()
#             left = stack.pop()
#             stack.append(operators[token](1, left, right).call())
        
#         elif token in temporal_operators:
#             i += 1
#             next_token = tokens[i].strip()
#             if not next_token:
#                 raise ValueError("Missing temporal operator condition.")
#             if next_token.startswith('[') and next_token.endswith(']'):
#                 condition = parse_bracket_contents(next_token)
#                 stack.append(temporal_operators[token](1, condition).call())
#             else:
#                 raise ValueError(f"Unexpected token: {next_token}")
        
#         elif token.startswith('¬'):
#             i += 1
#             next_token = tokens[i].strip()
#             if next_token.startswith('[') and next_token.endswith(']'):
#                 condition = parse_bracket_contents(next_token)
#                 stack.append(ALWAYS(1, AVOID(stl, condition)).call())
#             else:
#                 raise ValueError(f"Unexpected token: {next_token}")
        
#         else:
#             if token.startswith('[') and token.endswith(']'):
#                 condition = parse_bracket_contents(token)
#                 stack.append(condition)
#             else:
#                 raise ValueError(f"Unexpected token: {token}")
        
#         i += 1

#     if len(stack) != 1:
#         raise ValueError("Mismatched parentheses or missing operator.")

#     return stack[0]

# def transform_formula(stl, formula: str):
#     try:
#         return parse_formula(stl, formula)
#     except ValueError as e:
#         print(f"Error processing formula: {formula}")
#         print(f"Error message: {e}")
#         return None

# # Example usage
# formula = "♦[T1 [10, 10, -5, 5]] ∧ □ ¬[O1 [−10, 3, 8, 10]]"
# stl = STL(1, SeqReachAvoidStay())
# semantic = transform_formula(stl, formula)
# print(semantic)



# import re
# from typing import List, Union, Tuple

# # Helper functions
# def parse_bracket_contents(contents: str) -> List[float]:
#     # Remove brackets and split by commas
#     contents = contents.strip()[1:-1]  # Remove brackets
#     contents = contents.replace('−', '-')  # Replace '−' with '-'
#     return [float(x) for x in contents.split(',')]

# def tokenize_formula(formula: str) -> List[Tuple[str, str]]:
#     token_patterns = [
#         (r'□|♦|∧|∨|¬', 'OPERATOR'),
#         (r'\[.*?\]', 'BRACKETS'),
#         (r'[^\s\[\]∧∨□♦¬]+', 'VARIABLE')
#     ]
    
#     combined_pattern = '|'.join(f'(?P<{name}>{pattern})' for pattern, name in token_patterns)
#     regex = re.compile(combined_pattern)
    
#     tokens = []
#     for match in regex.finditer(formula):
#         token_type = match.lastgroup
#         token_value = match.group(token_type)
#         tokens.append((token_type, token_value))
    
#     return tokens

# def parse_formula(formula: str) -> Union[str, None]:
#     operators = {'∧': 'AND', '∨': 'OR'}
#     temporal_operators = {'♦': 'EVENTUALLY', '□': 'ALWAYS'}
#     negation = '¬'
    
#     tokens = tokenize_formula(formula)
#     stack = []
#     i = 0
    
#     while i < len(tokens):
#         token_type, token_value = tokens[i]
        
#         if token_type == 'OPERATOR':
#             if token_value in operators:
#                 right = stack.pop()
#                 left = stack.pop()
#                 stack.append(f"{operators[token_value]}({left}, {right})")
#             elif token_value in temporal_operators:
#                 i += 1
#                 token_type, next_token = tokens[i]
#                 if token_type == 'BRACKETS':
#                     condition = parse_bracket_contents(next_token)
#                     stack.append(f"{temporal_operators[token_value]}({condition})")
#                 else:
#                     return f"Unexpected token: {next_token}"
#             elif token_value == negation:
#                 i += 1
#                 token_type, next_token = tokens[i]
#                 if token_type == 'BRACKETS':
#                     condition = parse_bracket_contents(next_token)
#                     stack.append(f"NOT({condition})")
#                 else:
#                     return f"Unexpected token: {next_token}"
#             else:
#                 return f"Unexpected token: {token_value}"
        
#         elif token_type == 'BRACKETS':
#             condition = parse_bracket_contents(token_value)
#             stack.append(condition)
        
#         elif token_type == 'VARIABLE':
#             if i + 1 < len(tokens) and tokens[i + 1][0] == 'BRACKETS':
#                 next_token = tokens[i + 1][1]
#                 condition = parse_bracket_contents(next_token)
#                 if token_value.startswith('♦'):
#                     stack.append(f"EVENTUALLY({condition})")
#                 elif token_value.startswith('□'):
#                     stack.append(f"ALWAYS({condition})")
#                 i += 1
                
#         i += 1
    
#     if len(stack) != 1:
#         return "Mismatched parentheses or missing operator."
    
#     return stack[0]

# def transform_formula(formula: str) -> Union[str, None]:
#     try:
#         return parse_formula(formula)
#     except Exception as e:
#         return f"Error processing formula: {e}"

# # Example usage
# formulas = [
#     "♦[T1 [10, 10, -5, 5]] ∧ □ ¬[O1 [−10, 3, 8, 10]]",
#     "□ ¬[O1 [0, 0, 0, 0]]",
#     "♦[T1 [5, 10, −10, 10]] ∧ ♦[T2 [−10, 10, −10, 7]] ∧ ♦[T3 [3, 3, 3, 3]]",
#     "♦[T1 [5, 10, −10, 10]] ∧ □ ¬[O1 [−10, 1, 2, 10]]",
#     "□ ¬[O1 [−10, 2, 7, 10]] ∧ ♦[T1 [10, 10, 10, 10]]",
#     "□[♦[T1 [8, 8, 8, 8]]]",
#     "□ ¬[O1 [−10, 3, −10, 3]] ∧ ♦[T1 [7, 10, 7, 10]]",
#     "□ ¬[O1 [−10, 4, −10, 4]] ∧ ♦[T1 [8, 10, 8, 10]]",
#     "♦[T1 [6, 10, 6, 10]] ∧ □ ¬[O1 [6, 10, 6, 10]]",
#     "□[♦[T1 [5, 10, −10, 10]] ∧ ♦[T2 [−10, 10, 7, 10]]]"
# ]

# for formula in formulas:
#     result = transform_formula(formula)
#     print(f"Formula: {formula}")
#     print(f"Result: {result}\n")


# def slice_after_symbols(formula: str):
#     # List to store the results
#     results = []
#     # Symbols to check
#     symbols = ['◊', '□']
    
#     # Iterate through the formula string
#     i = 0
#     while i < len(formula):
#         # If a symbol is found, slice the string
#         if formula[i] in symbols:
#             start = i + 1  # Start slicing after the symbol
#             end = formula.find(']', start)  # Find the first closing bracket
#             if end != -1:
#                 # Append the sliced part to the results list
#                 results.append(formula[start:end+1])
#                 i = end + 1  # Continue searching after this slice
#             else:
#                 break  # Exit if no closing bracket found
#         else:
#             i += 1  # Continue to next character

#     return results

# # Test cases
# formula1 = "◊[T1 [10, 10, -5, 5]] ∧ □¬[O1 [−10, 3, 8, 10]]"
# formula2 = "□[◊[T1 [5, 10, −10, 10]] ∧ ◊[T2 [−10, 10, −10, 7]] ∧ ◊[T3 [3, 3, 3, 3]]]"

# print(slice_after_symbols(formula1))  # Output: ['[T1 [10, 10, -5, 5]]', '[O1 [−10, 3, 8, 10]]']
# print(slice_after_symbols(formula2))  # Output: ['[T1 [5, 10, −10, 10]]', '[T2 [−10, 10


# import re

# class STL:
#     def __init__(self, id, sequence):
#         self.id = id
#         self.sequence = sequence

# class SeqReachAvoidStay:
#     pass

# class REACH:
#     def __init__(self, stl, target):
#         self.stl = stl
#         self.target = target
    
#     def call(self):
#         return f"REACH({self.stl}, {self.target})"

# class AVOID:
#     def __init__(self, stl, obstacle):
#         self.stl = stl
#         self.obstacle = obstacle
    
#     def call(self):
#         return f"AVOID({self.stl}, {self.obstacle})"

# class EVENTUALLY:
#     def __init__(self, id, reach_expr):
#         self.id = id
#         self.reach_expr = reach_expr
    
#     def call(self):
#         return f"EVENTUALLY({self.id}, {self.reach_expr})"

# class ALWAYS:
#     def __init__(self, id, avoid_expr):
#         self.id = id
#         self.avoid_expr = avoid_expr
    
#     def call(self):
#         return f"ALWAYS({self.id}, {self.avoid_expr})"

# class AND:
#     def __init__(self, id, expr1, expr2):
#         self.id = id
#         self.expr1 = expr1
#         self.expr2 = expr2
    
#     def call(self):
#         return f"AND({self.id}, {self.expr1}, {self.expr2})"

# class OR:
#     def __init__(self, id, expr1, expr2):
#         self.id = id
#         self.expr1 = expr1
#         self.expr2 = expr2
    
#     def call(self):
#         return f"OR({self.id}, {self.expr1}, {self.expr2})"


# # Generalized function to parse and simplify the formula
# def parse_formula(formula):
#     # Replace the LTL operators with their corresponding STL functions
#     def replace_operators(match):
#         # Extract the inner targets or obstacles (T1, T2, O1, O2)
#         operator = match.group(1)
#         target = match.group(2)

#         if operator == '◊':  # Eventually
#             return f"EVENTUALLY(1, REACH(stl, {target}).call())"
#         elif operator == '□':  # Always
#             return f"ALWAYS(1, AVOID(stl, {target}).call())"
#         else:
#             return match.group(0)  # No replacement

#     # Initialize STL object and sequences
#     stl = STL(1, SeqReachAvoidStay())

#     # Parse formula step 1: Replace ◊ and □ operators with corresponding calls
#     parsed_formula = re.sub(r'(◊|□)\s*(T\d+|O\d+)', replace_operators, formula)

#     # Parse formula step 2: Simplify the AND and OR combinations
#     parsed_formula = re.sub(r'◊ T(\d+)\s*∨\s*◊ T(\d+)', r"OR(1, EVENTUALLY(1, REACH(stl, T\1)).call(), EVENTUALLY(1, REACH(stl, T\2)).call())", parsed_formula)
#     parsed_formula = re.sub(r'□ ¬ O(\d+)\s*∧\s*□ ¬ O(\d+)', r"AND(1, ALWAYS(1, AVOID(stl, O\1)).call(), ALWAYS(1, AVOID(stl, O\2)).call())", parsed_formula)

#     # Parse formula step 3: Add the AND condition at the outer level
#     parsed_formula = f"AND(1, {parsed_formula})"

#     return parsed_formula


# # Example usage
# ltl_formula = "((◊ T₁ ∨ ◊ T₂) ∧ □ ¬ (O₁ ∧ O₂))"
# simplified_formula = parse_formula(ltl_formula)

# print("Simplified formula:")
# print(simplified_formula)


# import re

# class STL:
#     def __init__(self, id, sequence):
#         self.id = id
#         self.sequence = sequence

# class SeqReachAvoidStay:
#     pass

# class REACH:
#     def __init__(self, stl, target):
#         self.stl = stl
#         self.target = target
    
#     def call(self):
#         return f"REACH({self.stl}, {self.target})"

# class AVOID:
#     def __init__(self, stl, obstacle):
#         self.stl = stl
#         this.obstacle = obstacle
    
#     def call(self):
#         return f"AVOID({self.stl}, {self.obstacle})"

# class EVENTUALLY:
#     def __init__(self, id, reach_expr):
#         self.id = id
#         self.reach_expr = reach_expr
    
#     def call(self):
#         return f"EVENTUALLY({self.id}, {self.reach_expr})"

# class ALWAYS:
#     def __init__(self, id, avoid_expr):
#         self.id = id
#         self.avoid_expr = avoid_expr
    
#     def call(self):
#         return f"ALWAYS({self.id}, {self.avoid_expr})"

# class AND:
#     def __init__(self, id, expr1, expr2):
#         self.id = id
#         self.expr1 = expr1
#         self.expr2 = expr2
    
#     def call(self):
#         return f"AND({self.id}, {self.expr1}, {self.expr2})"

# class OR:
#     def __init__(self, id, expr1, expr2):
#         self.id = id
#         self.expr1 = expr1
#         self.expr2 = expr2
    
#     def call(self):
#         return f"OR({self.id}, {self.expr1}, {self.expr2})"


# # Generalized function to parse and simplify the formula
# def parse_formula(formula):
#     stl = STL(1, SeqReachAvoidStay())  # Initialize the STL object

#     # Step 1: Replace ◊ (eventually) and □ (always) with corresponding STL expressions
#     formula = re.sub(r'◊\s*(T\d+)', lambda m: f"EVENTUALLY(1, REACH(stl, {m.group(1)}).call())", formula)
#     formula = re.sub(r'□\s*¬\s*(O\d+)', lambda m: f"ALWAYS(1, AVOID(stl, {m.group(1)}).call())", formula)

#     # Step 2: Replace ∨ (or) and ∧ (and) with OR and AND operations
#     formula = re.sub(r'\s*∨\s*', lambda m: ' OR(1, ', formula)
#     formula = re.sub(r'\s*∧\s*', lambda m: ' AND(1, ', formula)

#     # Add the closing parentheses where appropriate for OR/AND
#     # For simplification, we'll assume a basic structure for now
#     # You'll need to refine the parentheses depending on how nested the formula is
#     formula = re.sub(r'OR\(1, ([^\)]*)\)', r'OR(1, \1)', formula)
#     formula = re.sub(r'AND\(1, ([^\)]*)\)', r'AND(1, \1)', formula)

#     # Wrap everything in an outer AND call
#     return f"AND(1, {formula})"


# # Example usage
# ltl_formula = "((◊ T₁ ∨ ◊ T₂) ∧ □ ¬ (O₁ ∧ O₂))"
# simplified_formula = parse_formula(ltl_formula)

# print("Simplified formula:")
# print(simplified_formula)

# import re

# class STL:
#     def __init__(self, id, sequence):
#         self.id = id
#         self.sequence = sequence

# class SeqReachAvoidStay:
#     pass

# # Parsing functions to wrap operations
# class REACH:
#     def __init__(self, stl, target):
#         self.stl = stl
#         self.target = target
    
#     def call(self):
#         return f"◊ {self.target}"

# class AVOID:
#     def __init__(self, stl, obstacle):
#         self.stl = stl
#         self.obstacle = obstacle
    
#     def call(self):
#         return f"□ ¬ {self.obstacle}"

# class AND:
#     def __init__(self, id, expr1, expr2):
#         self.id = id
#         self.expr1 = expr1
#         self.expr2 = expr2
    
#     def call(self):
#         return f"AND({self.id}, {self.expr1}, {self.expr2})"

# class OR:
#     def __init__(self, id, expr1, expr2):
#         self.id = id
#         self.expr1 = expr1
#         self.expr2 = expr2
    
#     def call(self):
#         return f"OR({self.id}, {self.expr1}, {self.expr2})"

# # Generalized function to parse and simplify the formula
# def parse_formula(formula):
#     stl = STL(1, SeqReachAvoidStay())  # Initialize the STL object

#     # Step 1: Replace ◊ (eventually) and □ (always) with corresponding STL expressions
#     formula = re.sub(r'◊\s*(T\d+)', lambda m: f"◊ {m.group(1)}", formula)
#     formula = re.sub(r'□\s*¬\s*(O\d+)', lambda m: f"□ ¬ {m.group(1)}", formula)

#     # Step 2: Recursively handle nested logical operations for AND and OR

#     def handle_and_or(expr):
#         # Handle OR first to keep proper order
#         if '∨' in expr:
#             parts = [handle_and_or(part.strip()) for part in expr.split('∨')]
#             return f"OR(1, ({', '.join(expr)}))"
#         # Handle AND after OR to ensure proper nesting
#         if '∧' in expr:
#             parts = [handle_and_or(part.strip()) for part in expr.split('∧')]
#             return f"AND(1, ({', '.join(expr)}))"
#         return expr  # Return the unchanged part if no AND/OR is present

#     # Apply the AND/OR handler on the entire formula
#     formula = handle_and_or(formula)

#     return f"AND(1, {formula})"

# # Example usage
# ltl_formula = "((◊ T₁ ∨ ◊ T₂) ∧ □ ¬ (O₁ ∧ O₂))"
# simplified_formula = parse_formula(ltl_formula)

# print("Simplified formula:")
# print(simplified_formula)


###############################
# def check_parentheses(s):
#     stack = []
#     for char in s:
#         if char == '(':
#             stack.append(char)
#         elif char == ')':
#             if not stack:
#                 return False
#             stack.pop()
#     return len(stack) == 0

# def expression_within_bracket(exp):
#     open_count = 0
#     close_count = 0
#     count = 0
#     i_pos = 0
#     for i in exp:
#         if i == '(':
#             open = i_pos
#             j_pos = i_pos
#             for j in exp[(i_pos+1):]:
#                 if j == '(':
#                     count += 1
#                     open_count += 1
#                 if j == ')':
#                     count -= 1
#                     close_count += 1
#                 if j == ')' and count == -1:
#                     close = j_pos
#                     if exp[open] == '(' and exp[close + 1] == ')':
#                         if check_parentheses(exp[open + 1 : close + 1]):
#                             print("check: ", exp[open + 1 : close + 1])
#                 j_pos += 1
#         count = 0
#         i_pos += 1

# exp1 = '(see you (tomorrow), (bye), (tata(lmao)))'
# exp2 = 'mera (name) toh (pata(hi(hoga)))'
# expression_within_bracket(exp1)
# expression_within_bracket(exp2)



# print(bracket_closure(exp))
# print(exp[4:])
# for i in exp[4:]:
#     print(i)


# input: '(hi)(nita)'
# output: hi
#         nita


# input: '(see you (tomorrow), (bye), (tata(lmao)))'
# output: see you (tomorrow), (bye), (tata(lmao))
#         tomorrow
#         bye
#         tata(lmao)
#         lmao

# input: 'mera (name) toh (pata(hi(hoga)))'
# output: name
#         pata(hi(hoga))
#         hi(hoga)
#         hoga
####################################


# def expression_within_bracket(exp):
#     open_indices = []
#     i_pos = 0
    
#     while i_pos < len(exp):
#         if exp[i_pos] == '(':
#             open_indices.append(i_pos)
#         elif exp[i_pos] == ')' and open_indices:
#             open = open_indices.pop()
#             if check_parentheses(exp[open:i_pos+1]):
#                 print("check: ", exp[open:i_pos+1])
#                 convert(exp[open:i_pos+1])
#         i_pos += 1

# def check_parentheses(s):
#     stack = []
#     for char in s:
#         if char == '(':
#             stack.append(char)
#         elif char == ')':
#             if not stack:
#                 return False
#             stack.pop()
#     return len(stack) == 0

# def convert(exp):
#     for i in exp:
#         pass

# expression_within_bracket('(see you (tomorrow), (bye), (tata(lmao)))')

#########################################


# def final(temp):
#     exp = temp
#     stack = []
#     for i in range(len(exp)):
#         for j in range (len(exp)):
#             if exp[i] == '(' and exp[j] == ')' and '(' not in exp[i+1:j] and ')' not in exp[i+1:j] and exp[i+1:j] != '':
#                 stack.append(exp[i:j+1])
#     for item in stack:
#         temp = temp.replace(item, 'x', 1)
#     print(temp)
#     if temp != 'x':
#         final(temp)

# final('(see you (tomorrow), (bye), (tata(lmao)))')

#########################################

# def declassify(semantic):
#     i_pos = 0
#     count = 0
#     for i in semantic:
#         if i == '∧':
#             semantic = semantic.replace(i, ',')
#             semantic = 'AND[' + semantic[1:len(semantic) - 1] + ']'
#         if i == '∨':
#             semantic = semantic.replace(i, ',')
#             semantic = 'OR[' + semantic[1:len(semantic) - 1] + ']'
#         if i == '◊':
#             semantic = semantic.replace(i, 'EVENTUALLY')
#         if i == '□':
#             semantic = semantic.replace(i, 'ALWAYS')
#         if i == '¬':
#             semantic = semantic.replace(i, 'AVOID')
#     return semantic


# # print(declassify('((◊ T₁ ∨ ◊ T₂) ∧ □ ¬ (O₁ ∧ O₂))'))
# # print(declassify('(O₁ ∧ O₂)'))
# # print(declassify('(◊ T₁ ∨ ◊ T₂)'))


# def final(temp):
#     exp = temp
#     stack = []
#     for i in range(len(exp)):
#         for j in range (len(exp)):
#             if exp[i] == '(' and exp[j] == ')' and '(' not in exp[i+1:j] and ')' not in exp[i+1:j] and exp[i+1:j] != '':
#                 stack.append(exp[i:j+1])
#     # print(stack)
#     for item in stack:
#         temp = temp.replace(item, declassify(item), 1)
#     print(temp)
#     if '∧' not in temp:
#         print(temp)
#         final_str = temp
#     else:
#         final(temp)
#     return final_str

# final('((◊ T₁ ∨ ◊ T₂) ∧ (□ ¬ O₁ ∧ □ ¬ O₂))')

# final('see you (tomorrow), (bye)')
# final('(tomorrow ∧ bye ∧ see)')

#########################################

# import re

# # Define the classes (same as before)
# class REACH:
#     def __init__(self, id, start, end, setpoints):
#         self.id = id
#         self.start = start
#         self.end = end
#         self.setpoints = setpoints

#     def call(self):
#         return f"REACH([{', '.join(map(str, self.setpoints))}])"


# class AVOID:
#     def __init__(self, id, start, end, setpoints):
#         self.id = id
#         self.start = start
#         self.end = end
#         self.setpoints = setpoints

#     def call(self):
#         return f"AVOID([{', '.join(map(str, self.setpoints))}])"


# class EVENTUALLY:
#     def __init__(self, id, start, end, operation):
#         self.id = id
#         self.start = start
#         self.end = end
#         self.operation = operation

#     def call(self):
#         return f"EVENTUALLY({self.id}, {self.start},{self.end} {self.operation})"


# class ALWAYS:
#     def __init__(self, id, start, end, operation):
#         self.id = id
#         self.start = start
#         self.end = end
#         self.operation = operation

#     def call(self):
#         return f"ALWAYS({self.id}, {self.start},{self.end} {self.operation})"


# class OR:
#     def __init__(self, id, *operations):
#         self.id = id
#         self.operations = operations

#     def call(self):
#         return f"OR({self.id}, {', '.join(op.call() for op in self.operations)})"


# class AND:
#     def __init__(self, id, *operations):
#         self.id = id
#         self.operations = operations

#     def call(self):
#         return f"AND({self.id}, {', '.join(op.call() for op in self.operations)})"


# # Map variables like T₁, O₁ to setpoints (index ranges)
# variable_map = {
#     'T₁': [0, 1],
#     'T₂': [2, 3],
#     'O₁': [5, 6],
#     'O₂': [0, 1]
# }

# # Helper function to parse and convert the string
# def parse_expression(expression, id=1):
#     # Remove whitespaces around brackets for cleaner parsing
#     expression = re.sub(r'\s*,\s*', ',', expression)  # Normalize commas
#     expression = re.sub(r'\s*\[\s*', '[', expression)  # Normalize brackets

#     def extract_arguments(inner_expr):
#         """Extracts arguments within brackets and returns them as a list."""
#         stack = []
#         result = []
#         temp = ""
#         for char in inner_expr:
#             if char == ',' and not stack:
#                 result.append(temp.strip())
#                 temp = ""
#             else:
#                 temp += char
#                 if char == '[':
#                     stack.append('[')
#                 elif char == ']':
#                     stack.pop()
#         if temp:
#             result.append(temp.strip())
#         return result

#     # Recursively build the expression tree
#     def build_expression(expr, id):
#         # Match different operations
#         if expr.startswith("AND["):
#             args = extract_arguments(expr[4:-1])
#             return AND(id, *[build_expression(arg, id) for arg in args])
#         elif expr.startswith("OR["):
#             args = extract_arguments(expr[3:-1])
#             return OR(id, *[build_expression(arg, id) for arg in args])
#         elif expr.startswith("ALWAYS AVOID"):
#             args = extract_arguments(expr[12:-1])
#             start, end = 2, 3  # Set default or inferred values
#             setpoints = variable_map.get(args[0], [0])  # Map the argument to setpoints
#             return ALWAYS(id, start, end, AVOID(id, start, end, setpoints).call())
#         elif expr.startswith("EVENTUALLY"):
#             args = extract_arguments(expr[11:-1])
#             start, end = 0, 1  # Set default or inferred values
#             setpoints = variable_map.get(args[0], [0])  # Map the argument to setpoints
#             return EVENTUALLY(id, start, end, REACH(id, start, end, setpoints).call())
#         else:
#             raise ValueError(f"Unknown expression format: {expr}")

#     return build_expression(expression, id).call()


# # Example usage
# expression = 'AND[OR[EVENTUALLY T₁ , EVENTUALLY T₂] , AND[ALWAYS AVOID O₁ , ALWAYS AVOID O₂]]'
# parsed_output = parse_expression(expression)
# # print(parsed_output)

# import os
# import subprocess

# def create_and_run_python_file(file_name, content):
#     # Step 1: Create the Python file and write the content to it
#     with open(file_name, 'w') as f:
#         f.write(content)

#     print(f"{file_name} created successfully!")

#     # Step 2: Run the newly created Python file
#     try:
#         # For Windows: use 'python' instead of 'python3'
#         result = subprocess.run(['python3', file_name], capture_output=True, text=True)
#         print("Output of the script:")
#         print(result.stdout)
#         if result.stderr:
#             print("Errors:")
#             print(result.stderr)
#     except Exception as e:
#         print(f"Failed to run the script: {e}")

# # Example usage
# file_name = 'test_script.py'
# content = '''#!/opt/homebrew/bin/python3.11
# # This is an automatically generated Python script
# print("Hello from the new Python file!")
# x = 5
# y = 10
# print(f"The sum of {x} and {y} is: {x + y}")
# '''

# create_and_run_python_file(file_name, content)





# * = and
# # = or
# ^ = eventually
# ! = always
# @ = reach
# & = avoid

# input string: (x * y * z) -> output string: OR(x, y, z)
# input string: (x * y) -> output string: OR(x, y)
# do this for n arguments

# import re

# def convert_to_or(expression):
#     if not re.fullmatch(r'[\w\s\+\*\(\)]+', expression):
#         return "enter valid exp"
    
#     def replace_and_with_or(match):
#         variables = match.group(1)
#         return f"OR({variables.replace('*', ',')})"
    
#     expression = re.sub(r'\(([\w\*]+)\)', replace_and_with_or, expression)

#     if re.search(r'\(\w+\*\w+', expression):
#         return "enter valid bro"
    
#     return expression

# expr = '(x * y * z)'
# print(convert_to_or(expr))

# import re

# def convert_to_logic_expression(input_string):
#     # Step 1: Remove parentheses and spaces
#     cleaned_string = input_string.strip().replace('(', '').replace(')', '').replace(' ', '')

#     # Step 2: Check the operator in the string and split accordingly
#     if '∨' in cleaned_string:
#         # If the operator is '*', split by '*' and use OR
#         variables = cleaned_string.split('∨')
#         return f"OR({', '.join(variables)})"
#     elif '∧' in cleaned_string:
#         # If the operator is '$', split by '$' and use AND
#         variables = cleaned_string.split('∧')
#         return f"AND({', '.join(variables)})"
#     else:
#         # If neither operator is found, return the input as-is or raise an error
#         return "Invalid input: No valid operator found (* or $)"

# # Example usage
# input_string_1 = "(◊ T₁ ∨ ◊ T₂ ∨ ◊ T₃)"
# input_string_2 = "(x ∧ y)"

# output_1 = convert_to_logic_expression(input_string_1)
# output_2 = convert_to_logic_expression(input_string_2)

# # print(f"Input: {input_string_1} -> Output: {output_1}")
# # print(f"Input: {input_string_2} -> Output: {output_2}")

# import numpy as np

# def min_distance_element(arr, target):
#     min_distance = float('inf')
#     closest_element = None
#     for element in arr:
#         distance = np.linalg.norm(np.array(element) - target)
#         if distance < min_distance:
#             min_distance = distance
#             closest_element = element
#     return closest_element

# array = [[3, 4], [7, 8], [5, 10], [4, 3], [6, 10]]
# target = [5, 5]
# result = min_distance_element(array, target)
# # print(f"Element closest to (5, 5): {result}")
# # print(array[0:-2])

# import random

# class reach():
#     def r(self):
#         k = random.randint(10, 100)
#         print("reach: ", k)
#         return k
    
#     def call(self):
#         return self.r()

# class even():
#     def __init__(self, task):
#         self.task = task

# class Or():
#     def __init__(self, *args):
#         self.args = args
        
#     def decide(self):
#         choice = random.randint(0, len(self.args) - 1)
#         print("choice: ", choice)
#         # Create an instance of the task class before calling the method
#         instance = self.args[choice].task.call() # Create an instance of `reach`
#         print(instance)
#         return instance  # Call the method on the instance
    
# Create the Or object and decide
# j = Or(even(reach()), even(reach()), even(reach()), even(reach())).decide()
# print("j = ", j)



# class A():
#     def ret(self):
#         return 5

# a = A()
# b = a.ret()
# print(type(b))
# import numpy as np

# ############## AND AND issue ##############
# class EVENTUALLY():
#     pass
# class ALWAYS():
#     pass
# class AND():
#     def __init__(self, *instances):
#         self.instances = instances
#         self.return_value = False
#     def add_resultant(self):
#         '''adds constraints'''
#         print("total: ", len(self.instances), self.instances)
#         for instance in self.instances:
#             print("add constraint block")
#             if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS):
#                 print("eventually/always encountered")
#             elif isinstance(instance, AND):
#                 print("AND encountered")
#                 instance.return_value = True
#                 constraints = instance.call()
#                 if constraints == None:
#                     print("red: ", instance, instance.return_value)
#                 print(constraints)
#             else:
#                 print("Unknown Instance")

#     def return_resultant(self):
#         '''returns constraints'''
#         all_constraints =[]
#         for instance in self.instances:
#             print("redirected to return block")
#             if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS):
#                 print("eventually/always in return block")
#                 all_constraints.append(6)
#             elif isinstance(instance, AND):
#                 instance.return_value = True
#                 constraints = instance.call()
#                 all_constraints.append(constraints)
#             else:
#                 print("Unknown Instance")
#         print("constraints: ", all_constraints)
#         return all_constraints

#     def call(self):
#         if self.return_value == True:
#             return self.return_resultant()
#         else:
#             self.add_resultant()

# obj2 = AND(EVENTUALLY(), 
#             AND(ALWAYS()),
#             EVENTUALLY())

# obj2.call()

# l1 = [[1,2]]
# l2 = [[3,4]]
# print(l1+l2)


# import re

# def remove_brackets_and_print_words(input_str):
#     stages = [input_str]
    
#     while '(' in stages[-1] or ')' in stages[-1]:
#         # Find all innermost bracketed content
#         innermost_content = re.findall(r'\(([^()]+)\)', stages[-1])
#         print("Words inside the innermost brackets:", ', '.join(innermost_content))
        
#         # Replace innermost brackets with their content
#         new_stage = re.sub(r'\(([^()]+)\)', r'\1', stages[-1])
#         stages.append(new_stage)
    
#     return stages

# # Test the function
# input_str = "(some (english) word (is (written)) here)"
# stages = remove_brackets_and_print_words(input_str)
# for i, stage in enumerate(stages, 1):
#     print(f"Stage {i}: {stage}")


# import re

# def evaluate(phrase):
#     # Check for '*' and replace with AND[...] if found
#     if '*' in phrase:
#         parts = phrase.split('*')
#         # Strip and join the parts into the desired format
#         evaluated = f"AND[{', '.join(part.strip() for part in parts)}]"
#         return evaluated
#     return phrase

# def remove_brackets_and_evaluate(input_str):
#     stages = [input_str]
    
#     while '(' in stages[-1] or ')' in stages[-1]:
#         # Find all innermost bracketed content
#         innermost_content = re.findall(r'\(([^()]+)\)', stages[-1])
#         evaluated_content = [evaluate(content) for content in innermost_content]
        
#         # Print evaluated contents
#         print("Evaluated content:", ', '.join(evaluated_content))
        
#         # Replace innermost brackets with evaluated content
#         new_stage = stages[-1]
#         for original, evaluated in zip(innermost_content, evaluated_content):
#             new_stage = new_stage.replace(f"({original})", evaluated, 1)
            
#         stages.append(new_stage)
    
#     return stages

# # Test the function
# input_str = "(good ((examples * are) * (rare)))"
# stages = remove_brackets_and_evaluate(input_str)
# for i, stage in enumerate(stages, 1):
#     print(f"Stage {i}: {stage}")


# import re

# def evaluate(phrase):
#     # Check for each symbol and replace accordingly
#     if '∧' in phrase:
#         parts = phrase.split('∧')
#         evaluated = f"AND[{', '.join(part.strip() for part in parts)}]"
#     elif '∨' in phrase:
#         parts = phrase.split('∨')
#         evaluated = f"OR[{', '.join(part.strip() for part in parts)}]"
#     else:
#         evaluated = phrase  # No special symbol found, return as is
    
#     return evaluated

# def remove_brackets_and_evaluate(input_str):
#     stages = [input_str]
    
#     while '(' in stages[-1] or ')' in stages[-1]:
#         # Find all innermost bracketed content
#         innermost_content = re.findall(r'\(([^()]+)\)', stages[-1])
#         evaluated_content = [evaluate(content) for content in innermost_content]
        
#         # Print evaluated contents
#         print("Evaluated content:", ', '.join(evaluated_content))
        
#         # Replace innermost brackets with evaluated content
#         new_stage = stages[-1]
#         for original, evaluated in zip(innermost_content, evaluated_content):
#             new_stage = new_stage.replace(f"({original})", evaluated, 1)
            
#         stages.append(new_stage)
    
#     return stages

# # Test the function
# # input_str = "(good (examples % are taken) (to $ find) (for # all) (and @ reach) (but & avoid) rare)"
# input_str = "((◊ T₁ ∨ ◊ T₂ ∨ ◊ T₃) ∧ (□ ¬ O₁ ∧ □ ¬ O₂ ∧ □ ¬ O₃))"
# stages = remove_brackets_and_evaluate(input_str)
# for i, stage in enumerate(stages, 1):
#     print(f"Stage {i}: {stage}")


# import re

# def evaluate(phrase):
#     # Handle the EVENTUALLY, ALWAYS, and AVOID symbols
#     phrase = phrase.replace('◊', 'EVENTUALLY')
#     phrase = phrase.replace('□', 'ALWAYS')
    
#     # Handle negations, wrapping ¬ Oₓ as [AVOID[Oₓ]]
#     phrase = re.sub(r'¬\s*(O\d+)', r'[AVOID[\1]]', phrase)
    
#     # Replace T_x terms with REACH[T_x] only if not already wrapped in REACH[]
#     phrase = re.sub(r'\b(T\d+)\b(?!\])', r'REACH[\1]', phrase)

#     # Wrap REACH[Tₓ] with [REACH[Tₓ]]
#     phrase = re.sub(r'REACH\[(T\d+)\]', r'[REACH[\1]]', phrase)

#     # Check for each symbol and replace accordingly
#     if '∧' in phrase:
#         parts = phrase.split('∧')
#         evaluated = f"AND[{', '.join(part.strip() for part in parts)}]"
#     elif '∨' in phrase:
#         parts = phrase.split('∨')
#         evaluated = f"OR[{', '.join(part.strip() for part in parts)}]"
#     else:
#         evaluated = phrase  # No special symbol found, return as is
    
#     return evaluated

# def remove_brackets_and_evaluate(input_str):
#     stages = [input_str]
    
#     while '(' in stages[-1] or ')' in stages[-1]:
#         # Find all innermost bracketed content
#         innermost_content = re.findall(r'\(([^()]+)\)', stages[-1])
#         evaluated_content = [evaluate(content) for content in innermost_content]
        
#         # Print evaluated contents
#         print("Evaluated content:", ', '.join(evaluated_content))
        
#         # Replace innermost brackets with evaluated content
#         new_stage = stages[-1]
#         for original, evaluated in zip(innermost_content, evaluated_content):
#             new_stage = new_stage.replace(f"({original})", evaluated, 1)
            
#         stages.append(new_stage)
    
#     return stages

# def replace_brackets(input_str):
#     # Replace [ with ( and ] with )
#     output_str = input_str.replace('[', '(').replace(']', ')')
#     return output_str

# # Test the function
# # test_str = "AND[OR[EVENTUALLY [REACH[T1]], EVENTUALLY [REACH[T2]], EVENTUALLY [REACH[T3]]], AND[ALWAYS [AVOID[O1]], ALWAYS [AVOID[O2]], ALWAYS [AVOID[O3]]]]"
# # result = replace_brackets(test_str)
# # print(result)

# def replace_symbols_with_counter(input_str, num):
#     # Replace AND[ with AND[num,
#     output_str = input_str.replace('AND[', f'AND[{num},')
#     # Replace OR[ with OR[num,
#     output_str = output_str.replace('OR[', f'OR[{num},')
#     # Replace EVENTUALLY[ with EVENTUALLY[num,
#     output_str = output_str.replace('EVENTUALLY[', f'EVENTUALLY[{num},')
#     # Replace ALWAYS[ with ALWAYS[num,
#     output_str = output_str.replace('ALWAYS[', f'ALWAYS[{num},')
    
#     return output_str


# def remove_spaces(input_str):
#     # Remove all spaces from the string
#     return input_str.replace(' ', '')


# # Test the function
# test_str = "AND[OR[EVENTUALLY [REACH[T1]], EVENTUALLY [REACH[T2]], EVENTUALLY [REACH[T3]]], AND[ALWAYS [AVOID[O1]], ALWAYS [AVOID[O2]], ALWAYS [AVOID[O3]]]]"
# num_choice = 5  # Example: replace with number 5
# result = replace_symbols_with_counter(remove_spaces(test_str), num_choice)
# print(result)




# Test the function
# test_str = "AND[ OR[ EVENTUALLY [ REACH[ T1 ] ], EVENTUALLY [ REACH[ T2 ] ], EVENTUALLY [ REACH[ T3 ] ] ], AND[ ALWAYS [ AVOID[ O1 ] ], ALWAYS [ AVOID[ O2 ] ], ALWAYS [ AVOID[ O3 ] ] ] ]"
# result = remove_spaces(test_str)
# # print(result)

# # Test the function
# # test_str = "AND[OR[EVENTUALLY [REACH[T1]], EVENTUALLY [REACH[T2]], EVENTUALLY [REACH[T3]]], AND[ALWAYS [AVOID[O1]], ALWAYS [AVOID[O2]], ALWAYS [AVOID[O3]]]]"
# result = replace_symbols_with_counter(result)
# print(result)


# # Test the function
# input_str = "(((◊ T1 ∨ ◊ T2) ∨ (◊ T3)) ∧ (□ ¬ O1 ∧ □ ¬ O2 ∧ □ ¬ O3))"
# stages = remove_brackets_and_evaluate(input_str)
# for i, stage in enumerate(stages, 1):
#     print(f"Stage {i}: {stage}")


# c = 5
# print(c if not None else None)

# class REACH:
#     def __init__(self, stl_main, start, end):
#         self.stl_main = stl_main
#         self.start_time = start
#         self.end_time = end

# class EVENTUALLY:
#     def __init__(self, priority, start, end, inner_formula):
#         self.priority = priority
#         self.start_time = start
#         self.end_time = end
#         self.inner_formula = inner_formula

#     def __repr__(self):
#         return f"EVENTUALLY({self.priority}, {self.start_time}, {self.end_time}, {self.inner_formula})"

# class ALWAYS:
#     def __init__(self, priority, start, end, inner_formula):
#         self.priority = priority
#         self.start_time = start
#         self.end_time = end
#         self.inner_formula = inner_formula

#     def __repr__(self):
#         return f"ALWAYS({self.priority}, {self.start_time}, {self.end_time}, {self.inner_formula})"

# def expand_always_eventually(obj):
#     # Extract time intervals from ALWAYS and EVENTUALLY
#     always_start = obj.start_time  # 0
#     always_end = obj.end_time      # 10
#     eventually_duration = obj.inner_formula.end_time - obj.inner_formula.start_time  # 2 - 0 = 2
    
#     expanded_eventually = []
    
#     # Loop through the ALWAYS time frame, incrementing by eventually_duration
#     current_time = always_start
#     while current_time < always_end:
#         next_time = min(current_time + eventually_duration, always_end)
        
#         # Create new EVENTUALLY objects for each time slice
#         new_eventually = EVENTUALLY(
#             obj.inner_formula.priority,
#             current_time, next_time, obj.inner_formula.inner_formula
#         )
#         expanded_eventually.append(new_eventually)
        
#         current_time = next_time
    
#     return expanded_eventually

# # Usage
# # Create the inner REACH object
# reach_formula = REACH("stl.main", 0, 1)

# # Create the EVENTUALLY object inside ALWAYS
# eventually_formula = EVENTUALLY(1, 0, 2, reach_formula)

# # Create the ALWAYS object that contains the EVENTUALLY
# always_obj = ALWAYS(1, 0, 10, eventually_formula)

# # Run the function
# expanded_obj = expand_always_eventually(always_obj)

# # Print the output
# for obj in expanded_obj:
#     print(type(obj))
