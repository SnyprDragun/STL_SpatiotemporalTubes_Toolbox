#!/usr/bin/env python3
'''script to convert stl semantic to executable form'''
import os
import re
import subprocess

class TextToSTL():
    def __init__(self, semantic):
        self.semantic = semantic
        self.class_phrase = None

    def evaluate(self, phrase):
        phrase = phrase.replace('◊', 'EVENTUALLY')
        phrase = phrase.replace('□', 'ALWAYS')

        # Handle negations, wrapping ¬ Oₓ as [AVOID[Oₓ]]
        phrase = re.sub(r'¬\s*(O\d+)', r'[AVOID[\1]]', phrase)
        
        # Replace T_x terms with REACH[T_x] only if not already wrapped in REACH[]
        phrase = re.sub(r'\b(T\d+)\b(?!\])', r'REACH[\1]', phrase)

        # Wrap REACH[Tₓ] with [REACH[Tₓ]]
        phrase = re.sub(r'REACH\[(T\d+)\]', r'[REACH[\1]]', phrase)

        if '∧' in phrase:
            parts = phrase.split('∧')
            evaluated = f"AND[{', '.join(part.strip() for part in parts)}]"
        elif '∨' in phrase:
            parts = phrase.split('∨')
            evaluated = f"OR[{', '.join(part.strip() for part in parts)}]"
        else:
            evaluated = phrase

        return evaluated

    def remove_brackets_and_evaluate(self, input_str):
        stages = [input_str]

        while '(' in stages[-1] or ')' in stages[-1]:
            innermost_content = re.findall(r'\(([^()]+)\)', stages[-1])
            evaluated_content = [self.evaluate(content) for content in innermost_content]

            # print("Evaluated content:", ', '.join(evaluated_content))

            new_stage = stages[-1]
            for original, evaluated in zip(innermost_content, evaluated_content):
                new_stage = new_stage.replace(f"({original})", evaluated, 1)
                
            stages.append(new_stage)

        return stages

    def remove_spaces(self, input_str):
        return input_str.replace(' ', '')

    def replace_symbols_with_counter(self, input_str, num):
        output_str = input_str.replace('AND[', f'AND[{num},')
        output_str = output_str.replace('OR[', f'OR[{num},')
        output_str = output_str.replace('EVENTUALLY[', f'EVENTUALLY[{num},')
        output_str = output_str.replace('ALWAYS[', f'ALWAYS[{num},')

        return output_str

    def replace_brackets(self, input_str):
        output_str = input_str.replace('[', '(').replace(']', ')')
        return output_str

    def count_and_map_T_O(self, input_str):
        T_matches = sorted(set(re.findall(r'\bT\d+\b', input_str)))
        O_matches = sorted(set(re.findall(r'\bO\d+\b', input_str)))
        T_dict = {}
        O_dict = {}
        print("Please provide values for each Tx and Ox term (enter comma-separated integers):")

        for T in T_matches:
            values = input(f"Enter values for {T}: ")
            T_dict[T] = list(map(int, values.split(',')))

        for O in O_matches:
            values = input(f"Enter values for {O}: ")
            O_dict[O] = list(map(int, values.split(',')))

        return T_dict, O_dict

    def replace_T_O_with_values(self, input_str, T_dict, O_dict):
        for T, values in T_dict.items():
            value_str = str(values)
            input_str = re.sub(rf'\({T}\)', value_str, input_str)

        for O, values in O_dict.items():
            value_str = str(values)
            input_str = re.sub(rf'\({O}\)', value_str, input_str)

        return input_str

    def create_and_run_python_file(self, file_name, content):
        with open(file_name, 'w') as f:
            f.write(content)
        print(f"{file_name} created successfully!")

        try:
            result = subprocess.run(['python3', file_name], capture_output=True, text=True)
            print("Output of the script:")
            print(result.stdout)
            if result.stderr:
                print("Errors:")
                print(result.stderr)
        except Exception as e:
            print(f"Failed to run the script: {e}")

    def execute(self):
        print(self.class_phrase)
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
obj = ''' + self.class_phrase + '''obj.call()'''

        self.create_and_run_python_file(file_name, content)

    def call(self):
        stages = self.remove_brackets_and_evaluate(self.semantic)
        # for i, stage in enumerate(stages, 1):
        #     print(f"Stage {i}: {stage}")

        self.class_phrase = self.replace_brackets(self.replace_symbols_with_counter(self.remove_spaces(stages[-1]), 1))

        T_dict, O_dict = self.count_and_map_T_O(self.class_phrase)
        self.class_phrase = self.replace_brackets(self.replace_T_O_with_values(self.class_phrase, T_dict, O_dict))
        

        print("T_dict:", T_dict)
        print("O_dict:", O_dict)
        print(self.class_phrase)

        self.execute()

semantic = "(((◊ T1 ∨ ◊ T2) ∨ (◊ T3)) ∧ (□ ¬ O1 ∧ □ ¬ O2 ∧ □ ¬ O3))"
x = TextToSTL(semantic)
x.call()

############################ tasks:
# 1. Handle always eventually (loop eventually in always time frame)
# 2. Handle eventually always (stay, might circle around in same position or like climb up with time)
# 3. Handle global [goal] for OR cases
