#!/usr/bin/env python3
'''script to convert stl semantic to executable form'''
import os
import re
import subprocess

class TextToSTL():
    def __init__(self, semantic):
        self.semantic = semantic

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

            print("Evaluated content:", ', '.join(evaluated_content))

            new_stage = stages[-1]
            for original, evaluated in zip(innermost_content, evaluated_content):
                new_stage = new_stage.replace(f"({original})", evaluated, 1)
                
            stages.append(new_stage)

        return stages

    def replace_brackets(self, input_str):
        output_str = input_str.replace('[', '(').replace(']', ')')
        return output_str

    def replace_symbols_with_counter(self, input_str, num):
        output_str = input_str.replace('AND[', f'AND[{num},')
        output_str = output_str.replace('OR[', f'OR[{num},')
        output_str = output_str.replace('EVENTUALLY[', f'EVENTUALLY[{num},')
        output_str = output_str.replace('ALWAYS[', f'ALWAYS[{num},')

        return output_str

    def remove_spaces(self, input_str):
        return input_str.replace(' ', '')

    def call(self):
        stages = self.remove_brackets_and_evaluate(self.semantic)
        for i, stage in enumerate(stages, 1):
            print(f"Stage {i}: {stage}")

        print(self.replace_brackets(self.replace_symbols_with_counter(self.remove_spaces(stages[-1]), 1)))


semantic = "(((◊ T1 ∨ ◊ T2) ∨ (◊ T3)) ∧ (□ ¬ O1 ∧ □ ¬ O2 ∧ □ ¬ O3))"
x = TextToSTL(semantic)
x.call()

############################ tasks:
# 1. Handle always eventually (loop eventually in always time frame)
# 2. Handle eventually always (stay, might circle around in same position or like climb up with time)
# 3. Handle global [goal] for OR cases