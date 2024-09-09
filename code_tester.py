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


class A:
    _instances = {}  # Registry for storing instances

    def __init__(self, identifier, num):
        # Store num and register the instance
        self.num = num
        A._instances[identifier] = self

    @classmethod
    def get_instance(cls, identifier):
        # Fetch the instance from the registry by identifier
        return cls._instances.get(identifier)


class B:
    def __init__(self, identifier):
        # Automatically get the appropriate instance of A by identifier
        self.main = A.get_instance(identifier)
        if self.main:
            print(self.main.num)
        else:
            print(f"No instance of A found for identifier '{identifier}'")

class C(B):
    def __init__(self, identifier):
        # Call the parent constructor with the identifier
        super().__init__(identifier)
        print(self.main.num)

# Create multiple instances of A with different identifiers
A('a1', 3)
A('a2', 5)

# Create objects of B and C using the identifiers without passing A instances
obj1 = C('a1')  # This will print 3
obj2 = C('a2')  # This will print 5 twice
