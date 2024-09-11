#!/opt/homebrew/bin/python3.11
'''script to convert stl semantic to executable form'''
import re
from solver import *
from stl_main import *
from action_classes import *
from error_handling import *
from seq_reach_avoid_stay import *

class TextToSTL():
    ltl_to_stl_mapping = {
        '◊': EVENTUALLY,
        '□': ALWAYS,
        '∧': AND,
        '∨': OR,
        '¬': AVOID
    }

    def __init__(self, text):
        self.text = text

    def tokenize(self, formula):
        '''Split formula by operators, parentheses, and atomic propositions'''
        tokens = re.findall(r'(\w+|[◊□¬∧∨()])', formula)
        return tokens

    def parse_formula(self, stl, formula):
        tokens = self.tokenize(formula)
        
        stack = []
        operator_stack = []
        
        for token in tokens:
            if token in ('T'):
                stack.append(REACH(stl, token))
            elif token in ('O'):
                stack.append(AVOID(stl, token))
            elif token in self.ltl_to_stl_mapping:
                operator_stack.append(token)  # Push operator
            elif token == '(':
                operator_stack.append(token)  # Push '('
            elif token == ')':
                # Apply operators until '('
                while operator_stack and operator_stack[-1] != '(':
                    operator = operator_stack.pop()
                    if operator == '¬':
                        operand = stack.pop()
                        stack.append(self.ltl_to_stl_mapping[operator](stl, operand).call())
                    else:
                        right = stack.pop()
                        left = stack.pop()
                        stack.append(self.ltl_to_stl_mapping[operator](1, left, right).call())
                operator_stack.pop()  # Pop '('
            else:
                raise ValueError(f"Unexpected token: {token}")

        # If any operators are left after the loop
        while operator_stack:
            operator = operator_stack.pop()
            if operator == '¬':
                operand = stack.pop()
                stack.append(self.ltl_to_stl_mapping[operator](stl, operand).call())
            else:
                right = stack.pop()
                left = stack.pop()
                stack.append(self.ltl_to_stl_mapping[operator](1, left, right).call())

        if len(stack) != 1:
            raise ValueError("Formula parsing error: incomplete or invalid formula.")
        
        return stack[0]




# (eventually reach [] and always avoid [(t1 and t2)]) or (eventually reach t1 and eventually reach t2)
# ((◊ T₁ ∨ ◊ T₂) ∧ □ ¬ (O₁ ∧ O₂))

# Simplify level 1: 
# ((◊ T₁ ∨ ◊ T₂) ∧ (□ ¬ O₁ ∧ □ ¬ O₂))

# Simplify level 2: 
# ((eventually reach T1 or eventually reach T2) and (always avoid O1 and always avoid O2))

# Simplify level 3:
# stl = STL(1, SeqReachAvoidStay())
# semantic = AND(1, OR(1, EVENTUALLY(1, REACH(stl, T1)).call(), EVENTUALLY(1, REACH(stl, T2)).call()).call(),
#                     AND(1, ALWAYS(1, AVOID(stl, O1)).call(), ALWAYS(1, AVOID(stl, O2)).call()).call())