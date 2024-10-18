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
        self.return_value = True
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
        self.goal = [3, 4]

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
        self.identifier = identifier
        a_instance = STL.get_instance(identifier)
        if a_instance:
            self.main = a_instance.main
        else:
            raise ValueError(f"No instance of A found for identifier '{identifier}'")
    
    def add_resultant(self):
        '''adds constraints'''
        if isinstance(self.task, REACH) or isinstance(self.task, AVOID) or isinstance(self.task, STAY):
            constraints = self.task.call()
            for constraint in constraints:
                self.main.solver.add(constraint)
        elif isinstance(self.task, ALWAYS):
            always = self.task
            if self.main.dimension == 1:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2)).call()
            elif self.main.dimension == 2:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2)).call()
            else:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2, always.task.z1, always.task.z2)).call()
            
            for constraint in constraints:
                self.main.solver.add(constraint)
        elif isinstance(self.task, EVENTUALLY) or isinstance(self.task, IMPLIES) or isinstance(self.task, UNTIL) or isinstance(self.task, NOT):
            print(self.task.__class__.__name__, "not handeled for EVENTUALLY")
        else:
            print("Unknown Instance")

    def return_resultant(self):
        '''returns constraints'''
        all_constraints =[]

        if isinstance(self.task, REACH) or isinstance(self.task, AVOID) or isinstance(self.task, STAY):
            constraints = self.task.call()
            for constraint in constraints:
                all_constraints.append(constraint)
        elif isinstance(self.task, ALWAYS):
            always = self.task
            if self.main.dimension == 1:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2)).call()
            elif self.main.dimension == 2:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2)).call()
            else:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2, always.task.z1, always.task.z2)).call()
            
            for constraint in constraints:
                all_constraints.append(constraint)
        elif isinstance(self.task, EVENTUALLY) or isinstance(self.task, IMPLIES) or isinstance(self.task, UNTIL) or isinstance(self.task, NOT):
            print(self.task.__class__.__name__, "not handeled for EVENTUALLY")
        else:
            print("Unknown Instance")
        return all_constraints

    def call(self):
        if self.return_value == True:
            return self.return_resultant()
        else:
            self.add_resultant()


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

    def add_resultant(self):
        '''adds constraints'''
        if isinstance(self.task, REACH) or isinstance(self.task, AVOID) or isinstance(self.task, STAY):
            constraints = self.task.call()
            for constraint in constraints:
                self.main.solver.add(constraint)
        elif isinstance(self.task, ALWAYS):
            always = self.task
            if self.main.dimension == 1:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2)).call()
            elif self.main.dimension == 2:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2)).call()
            else:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2, always.task.z1, always.task.z2)).call()
            
            for constraint in constraints:
                self.main.solver.add(constraint)
        elif isinstance(self.task, EVENTUALLY) or isinstance(self.task, IMPLIES) or isinstance(self.task, UNTIL) or isinstance(self.task, NOT):
            print(self.task.__class__.__name__, "not handeled for EVENTUALLY")
        else:
            print("Unknown Instance")

    def return_resultant(self):
        '''returns constraints'''
        all_constraints =[]

        if isinstance(self.task, REACH) or isinstance(self.task, AVOID) or isinstance(self.task, STAY):
            constraints = self.task.call()
            for constraint in constraints:
                all_constraints.append(constraint)
        elif isinstance(self.task, ALWAYS):
            always = self.task
            if self.main.dimension == 1:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2)).call()
            elif self.main.dimension == 2:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2)).call()
            else:
                constraints = EVENTUALLY(self.identifier, always.t1, always.t2, STAY(always.task.main, always.task.x1, always.task.x2, always.task.y1, always.task.y2, always.task.z1, always.task.z2)).call()
            
            for constraint in constraints:
                all_constraints.append(constraint)
        elif isinstance(self.task, EVENTUALLY) or isinstance(self.task, IMPLIES) or isinstance(self.task, UNTIL) or isinstance(self.task, NOT):
            print(self.task.__class__.__name__, "not handeled for EVENTUALLY")
        else:
            print("Unknown Instance")
        return all_constraints

    def call(self):
        if self.return_value == True:
            return self.return_resultant()
        else:
            self.add_resultant()


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
