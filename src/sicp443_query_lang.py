from typing import Callable, Dict, List
from sicp414_evaluator import TokenCombo


class QPattern:
    '''
    the base class for all patterns, use class for easier static type checking
    pattern is very similar to SchemeVal, the difference is that:
    it supports variable, but not procedure and primitve

    I will not store token inside pattern, because I can not find an elegant way to do that
    after all, it's strange that two equal patterns have different tokens
    besides, the calculation exposed to user is very easy, and where the bug occurs can be easily spotted
    '''
    pass

class StringPat(QPattern):
    def __init__(self, value: str):
        self.value = value

class NumberPat(QPattern):
    def __init__(self, value: float):
        self.value = value

class BooleanPat(QPattern):
    def __init__(self, value: bool):
        self.value = value

class NilPat(QPattern):
    pass

class PairPat(QPattern):
    def __init__(self, left: QPattern, right: QPattern):
        self.left = left
        self.right = right

class SymbolPat(QPattern):
    def __init__(self, name: str):
        self.name = name

class VarPat(QPattern):
    def __init__(self, name: str, version: int):
        self.name = name
        self.version = version

def parse_simple_pattern(combo: TokenCombo):
    pass

def parse_pattern(combo: TokenCombo):
    pass

def update_pattern_rules(rules: Dict[str, Callable[[TokenCombo], QPattern]]):
    pass

def check_assertion(pat: QPattern):
    pass

def parse_assertions(combos: List[TokenCombo]):
    pass

class AndPat(QPattern):
    pass

def parse_and_pattern(combo: TokenCombo):
    pass

class OrPat(QPattern):
    pass

def parse_or_pattern(combo: TokenCombo):
    pass

class NotPat(QPattern):
    pass

def parse_not_pattern(combo: TokenCombo):
    pass

class PredPat(QPattern):
    pass

def parse_pred_pattern(combo: TokenCombo):
    pass