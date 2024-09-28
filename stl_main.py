#!/usr/bin/env python3
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
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")

    def add_resultant(self):
        '''adds constraints'''
        for instance in self.instances:
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS):
                constraints = instance.call()
                for constraint in constraints:
                    self.main.solver.add(constraint)
            elif isinstance(instance, AND):
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
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS):
                constraints = instance.call()
                for constraint in constraints:
                    all_constraints.append(constraint)
            elif isinstance(instance, AND):
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
        self.goal = [13, 14, 13, 14]

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
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS):
                constraints = instance.call()
                for constraint in constraints:
                    self.main.solver.add(z3.Not(constraint))
            elif isinstance(instance, AND):
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
            if isinstance(instance, EVENTUALLY) or isinstance(instance, ALWAYS):
                constraints = instance.call()
                for constraint in constraints:
                    all_constraints.append(z3.Not(constraint))
            elif isinstance(instance, AND):
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
    def __init__(self):
        pass


class IMPLIES(STL):
    def __init__(self) -> None:
        pass

    def loop(self):
        pass

    def normal(self):
        pass
