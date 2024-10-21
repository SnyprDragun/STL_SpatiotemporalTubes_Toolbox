#!/opt/homebrew/bin/python3.11
import re
import subprocess
from CombinedToolbox import *


class TextToSTL():
    def __init__(self, semantic, degree, dimension, step, thickness):
        self.semantic = semantic
        self.degree = degree
        self.dimension = dimension
        self.step = step
        self.thickness = thickness
        self.class_phrase = None
        self.object_identifier = 1
        self.eventually_always_dict = None
        self.T_dict = {}
        self.O_dict = {}

    def evaluate(self, phrase):
        phrase = phrase.replace('◊', 'EVENTUALLY')
        phrase = phrase.replace('□', 'ALWAYS')

        phrase = re.sub(r'¬\s*(O\d+)', r'[AVOID[\1]]', phrase)
        phrase = re.sub(r'\bT(\d+)\b(?![^\[]*\])', r'[REACH[T\1]]', phrase)

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
            new_stage = stages[-1]

            for original, evaluated in zip(innermost_content, evaluated_content):
                new_stage = new_stage.replace(f"({original})", evaluated, 1)
            stages.append(new_stage)

        return stages[-1]

    def remove_spaces(self, input_str):
        return input_str.replace(' ', '')

    def replace_symbols_with_counter(self, input_str):
        output_str = input_str.replace('AND[', f'AND[{self.object_identifier},')
        output_str = output_str.replace('OR[', f'OR[{self.object_identifier},')

        output_str = output_str.replace('EVENTUALLY[', f'EVENTUALLY[{self.object_identifier},')
        output_str = output_str.replace('ALWAYS[', f'ALWAYS[{self.object_identifier},')

        output_str = output_str.replace('REACH[', f'REACH[stl_obj_{self.object_identifier}.main, ')
        output_str = output_str.replace('AVOID[', f'AVOID[stl_obj_{self.object_identifier}.main, ')

        return output_str

    def replace_brackets(self, input_str):
        output_str = input_str.replace('[', '(').replace(']', ')')
        return output_str

    def count_and_map_T_O(self, input_str):
        T_matches = sorted(set(re.findall(r'\bT\d+\b', input_str)))
        O_matches = sorted(set(re.findall(r'\bO\d+\b', input_str)))

        print("Please provide values for each Tx and Ox term (enter comma-separated integers):")

        for T in T_matches:
            values = input(f"Enter values for {T}: ")
            self.T_dict[T] = list(map(int, values.split(',')))

        for O in O_matches:
            values = input(f"Enter values for {O}: ")
            self.O_dict[O] = list(map(int, values.split(',')))

    def replace_T_O_with_values(self, input_str):
        for T, values in self.T_dict.items():
            value_str = str(values)
            input_str = re.sub(rf'{T}\)', f'{value_str[1:]}', input_str)

        for O, values in self.O_dict.items():
            value_str = str(values)
            input_str = re.sub(rf'{O}\)', f'{value_str[1:]}', input_str)

        return input_str

    def count_eventually_always(self, text):
        eventually_matches = re.findall(r'EVENTUALLY', text)
        always_matches = re.findall(r'ALWAYS', text)

        self.eventually_always_dict = {}

        for i, _ in enumerate(eventually_matches, start=1):
            value = input(f"Enter a value for EVENTUALLY[{i}]: ")
            self.eventually_always_dict[f'EVENTUALLY[{i}]'] = value

        for i, _ in enumerate(always_matches, start=1):
            value = input(f"Enter a value for ALWAYS[{i}]: ")
            self.eventually_always_dict[f'ALWAYS[{i}]'] = value

    def replace_eventually_always_with_brackets(self, input_str):
        output = re.sub(r'ALWAYSEVENTUALLY\[(.*?)\]', r'ALWAYS[EVENTUALLY[\1]]', input_str)
        return re.sub(r'EVENTUALLYALWAYS\[(.*?)\]', r'EVENTUALLY[ALWAYS[\1]]', output)

    def replace_eventually_always_with_values(self, input_str):
        eventually_count = 0
        always_count = 0

        def replace_eventually_match(match):
            nonlocal eventually_count
            eventually_count += 1
            key = f'EVENTUALLY[{eventually_count}]'
            value = self.eventually_always_dict.get(key, "")
            return f'EVENTUALLY[{value},'
        input_str = re.sub(r'EVENTUALLY\[', replace_eventually_match, input_str)

        def replace_always_match(match):
            nonlocal always_count
            always_count += 1
            key = f'ALWAYS[{always_count}]'
            value = self.eventually_always_dict.get(key, "")
            return f'ALWAYS[{value},'
        result = re.sub(r'ALWAYS\[', replace_always_match, input_str)

        return result

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
        file_name = 'Combined Toolbox/executable_script.py'
        content = '#!/opt/homebrew/bin/python3.11\n' \
        + '# This is an automatically generated Python script\n' \
        + 'from CombinedToolbox import *\n\n' \
        + 'stl_obj_' + str(self.object_identifier) + ' = STL(' + str(self.object_identifier) + ', SeqReachAvoidStay(' + str(self.degree) + ', ' + str(self.dimension) + ', ' + str(self.step) + ', ' + str(self.thickness) + '))\n' \
        + 'obj = ' + self.class_phrase + '\n' \
        + 'obj.return_value = False\n' \
        + 'obj.call()\n' \
        + 'stl_obj_' + str(self.object_identifier) + '.plotter()'

        self.create_and_run_python_file(file_name, content)

    def call(self):
        self.class_phrase = self.remove_spaces(self.remove_brackets_and_evaluate(self.semantic))
        self.count_eventually_always(self.class_phrase)
        self.class_phrase = self.replace_brackets(self.replace_symbols_with_counter(self.remove_spaces(self.replace_eventually_always_with_values(self.replace_eventually_always_with_brackets(self.class_phrase)))))
        self.count_and_map_T_O(self.class_phrase)
        self.class_phrase = self.replace_brackets(self.replace_T_O_with_values(self.class_phrase))        
        print(self.class_phrase)
        self.execute()

# semantic = "(((◊ T1 ∨ ◊ T2) ∧ (◊ T3)) ∧ (□ ¬ O1 ∧ □ ¬ O2 ∧ □ ¬ O3))"
# semantic = "((◊ (□ T1)) ∧ (◊ T2))"
semantic = "(□ (◊ T1))"
TextToSTL(semantic, 10, 1, 0.5, 1).call()

############################ tasks:
# 1. Handle always eventually (loop eventually in always time frame)                                    -> DONE
# 2. Handle eventually always (stay, might circle around in same position or like climb up with time)   -> DONE
# 3. Handle global [goal] for OR cases                                                                  -> PENDING
# 4. Handle OR-OR cascade in stl_main                                                                   -> DONE
# 5. Handle always-eventually and eventually-always bracket closure                                     -> DONE
