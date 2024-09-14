eses(s):
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