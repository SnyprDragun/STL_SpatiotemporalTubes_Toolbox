#!/opt/homebrew/bin/python3.11

class TextToSTL():
    def __init__(self, text):
        self.text = text

    def identify_semantics(self):
        index = 0
        mark_mid = []
        open_brackets = 0
        close_brackets = 0
        for ch in self.text:
            if ch == "(":
                open_brackets += 1
                mark_mid.append(index)
            index += 1

        for ch in len(self.text):
            pass




# (eventually reach [] and always avoid [(t1 and t2)]) or (eventually reach t1 and eventually reach t2)