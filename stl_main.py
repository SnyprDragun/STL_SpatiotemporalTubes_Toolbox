#!/opt/homebrew/bin/python3.11
'''script for STL specifications'''
import z3
import random
from action_classes import *
from seq_reach_avoid_stay import *

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
