#!/usr/bin/env python3
'''script to convert stl semantic to executable form'''
import os
import re
import subprocess
# from solver import *
# from stl_main import *
# from action_classes import *
# from error_handling import *
# from seq_reach_avoid_stay import *


# Define the classes (same as before)
class REACH:
    def __init__(self, id, start, end, setpoints):
        self.id = id
        self.start = start
        self.end = end
        self.setpoints = setpoints

    def call(self):
        return f"REACH([{', '.join(map(str, self.setpoints))}])"


class AVOID:
    def __init__(self, id, start, end, setpoints):
        self.id = id
        self.start = start
        self.end = end
        self.setpoints = setpoints

    def call(self):
        return f"AVOID([{', '.join(map(str, self.setpoints))}])"


class EVENTUALLY:
    def __init__(self, id, start, end, operation):
        self.id = id
        self.start = start
        self.end = end
        self.operation = operation

    def call(self):
        return f"EVENTUALLY({self.id}, {self.start}, {self.end}, {self.operation})"


class ALWAYS:
    def __init__(self, id, start, end, operation):
        self.id = id
        self.start = start
        self.end = end
        self.operation = operation

    def call(self):
        return f"ALWAYS({self.id}, {self.start}, {self.end}, {self.operation})"


class OR:
    def __init__(self, id, *operations):
        self.id = id
        self.operations = operations

    def call(self):
        return f"OR({self.id}, {', '.join(op.call() for op in self.operations)})"


class AND:
    def __init__(self, id, *operations):
        self.id = id
        self.operations = operations

    def call(self):
        return f"AND({self.id}, {', '.join(op.call() for op in self.operations)})"



class TextToSTL():
    def __init__(self, text):
        self.text = text
        self.final_str = ''
        self.variable_map = {
                                'T₁': [0, 1],
                                'T₂': [2, 3],
                                'O₁': [5, 6],
                                'O₂': [0, 1]
                            }

    def declassify(self, semantic):
        # Step 1: Remove parentheses and spaces
        cleaned_string = semantic.strip().replace('(', '').replace(')', '').replace(' ', '')

        # Step 2: Check the operator in the string and split accordingly
        if '∨' in cleaned_string:
            # If the operator is '*', split by '*' and use OR
            variables = cleaned_string.split('∨')
            return f"OR({', '.join(variables)})"
        elif '∧' in cleaned_string:
            # If the operator is '$', split by '$' and use AND
            variables = cleaned_string.split('∧')
            return f"AND({', '.join(variables)})"
        else:
            # If neither operator is found, return the input as-is or raise an error
            return "Invalid input: No valid operator found (* or $)"

    def final(self, temp):
        exp = temp
        stack = []
        for i in range(len(exp)):
            for j in range (len(exp)):
                if exp[i] == '(' and exp[j] == ')' and '(' not in exp[i+1:j] and ')' not in exp[i+1:j] and exp[i+1:j] != '':
                    stack.append(exp[i:j+1])
        for item in stack:
            temp = temp.replace(item, self.declassify(item), 1)
        if '∧' not in temp and '∨' not in temp and '◊' not in temp and '□' not in temp and temp != None:
            self.final_str = temp
            print(self.final_str)
        elif temp == None:
            print("Done")
        else:
            self.final(temp)
        return self.final_str

    # Helper function to parse and convert the string
    def parse_expression(self, expression, id=1):
        # Remove whitespaces around brackets for cleaner parsing
        expression = re.sub(r'\s*,\s*', ',', expression)  # Normalize commas
        expression = re.sub(r'\s*\[\s*', '[', expression)  # Normalize brackets

        def extract_arguments(inner_expr):
            """Extracts arguments within brackets and returns them as a list."""
            stack = []
            result = []
            temp = ""
            for char in inner_expr:
                if char == ',' and not stack:
                    result.append(temp.strip())
                    temp = ""
                else:
                    temp += char
                    if char == '[':
                        stack.append('[')
                    elif char == ']':
                        stack.pop()
            if temp:
                result.append(temp.strip())
            return result

        # Recursively build the expression tree
        def build_expression(expr, id):
            # Match different operations
            if expr.startswith("AND["):
                args = extract_arguments(expr[4:-1])
                return AND(id, *[build_expression(arg, id) for arg in args])
            elif expr.startswith("OR["):
                args = extract_arguments(expr[3:-1])
                return OR(id, *[build_expression(arg, id) for arg in args])
            elif expr.startswith("ALWAYS AVOID"):
                args = extract_arguments(expr[12:-1])
                start, end = 2, 3  # Set default or inferred values
                setpoints = self.variable_map.get(args[0], [0])  # Map the argument to setpoints
                return ALWAYS(id, start, end, AVOID(id, start, end, setpoints).call())
            elif expr.startswith("EVENTUALLY"):
                args = extract_arguments(expr[11:-1])
                start, end = 0, 1  # Set default or inferred values
                setpoints = self.variable_map.get(args[0], [0])  # Map the argument to setpoints
                return EVENTUALLY(id, start, end, REACH(id, start, end, setpoints).call())
            else:
                raise ValueError(f"Unknown expression format: {expr}")

        return build_expression(expression, id).call()

    def create_and_run_python_file(self, file_name, content):
        # Step 1: Create the Python file and write the content to it
        with open(file_name, 'w') as f:
            f.write(content)

        print(f"{file_name} created successfully!")

        # Step 2: Run the newly created Python file
        try:
            # For Windows: use 'python' instead of 'python3'
            result = subprocess.run(['python3', file_name], capture_output=True, text=True)
            print("Output of the script:")
            print(result.stdout)
            if result.stderr:
                print("Errors:")
                print(result.stderr)
        except Exception as e:
            print(f"Failed to run the script: {e}")

    def execute(self):
        parsed_output = self.parse_expression(self.final(self.text))
        # print(parsed_output)

        # Example usage
        file_name = 'test_script.py'
        content = '''#!/usr/bin/env python3
# This is an automatically generated Python script
from solver import *
from stl_main import *
from text_to_stl import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *
print("Hello from the new Python file!")
x = 5
y = 10
print(f"The sum of {x} and {y} is: {x + y}")
obj = ''' + parsed_output

        self.create_and_run_python_file(file_name, content)

x = TextToSTL('((◊ T₁ ∨ ◊ T₂ ∨ ◊ T₃) ∧ (□ ¬ O₁ ∧ □ ¬ O₂ ∧ □ ¬ O₃))')

x1 = x.final(x.text)
print(x1)
# parsed_output = x.parse_expression(x1)
# print(parsed_output)
# x.execute()

# final('((◊ T₁ ∨ ◊ T₂) ∧ (□ ¬ O₁ ∧ □ ¬ O₂))')



############################ tasks:
# 1. Handle always eventually (loop eventually in always time frame)
# 2. Handle eventually always (stay, might circle around in same position or like climb up with time)
# 3. Handle global [goal] for OR cases