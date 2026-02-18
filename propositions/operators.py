# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_variable(formula.root):
        return Formula(formula.root)

    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))

    if is_binary(formula.root):
        first = to_not_and_or(formula.first)
        second = to_not_and_or(formula.second)
        if formula.root == '&':
            return Formula('&', first, second)
        elif formula.root == '|':
            return Formula('|', first, second)
        elif formula.root == '->':
            return Formula('|', Formula('~', first), second)
        elif formula.root == '+':
            left = Formula('&', first, Formula('~', second))
            right = Formula('&', Formula('~', first), second)
            return Formula('|', left, right)
        elif formula.root == '<->': 
            left = Formula('|', Formula('~', first), second)
            right = Formula('|', first, Formula('~', second))
            return Formula('&', left, right)
        elif formula.root == '-&': 
            return Formula('~', Formula('&', first, second))
        elif formula.root == '-|': 
            return Formula('~', Formula('|', first, second))
    
    if formula.root == 'T':
        return Formula('|', Formula('p'), Formula('~', Formula('p')))
    
    if formula.root == 'F':
        return Formula('&', Formula('p'), Formula('~', Formula('p')))
    
    return formula
    # Task 3.5

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    if is_variable(formula.root):
        return Formula(formula.root)
    
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('~', Formula('&', Formula('p'), Formula('~', Formula('p'))))
        else:
            return Formula('&', Formula('p'), Formula('~', Formula('p')))
    
    if is_unary(formula.root):
        inner = to_not_and(formula.first)
        return Formula('~', inner)
    
    if is_binary(formula.root):
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        
        if formula.root == '&':
            return Formula('&', first, second)
        elif formula.root == '|':
            return Formula('~', Formula('&', Formula('~', first), Formula('~', second)))
        elif formula.root == '->':
            return Formula('~', Formula('&', first, Formula('~', second)))
        elif formula.root == '+':
            left = Formula('&', first, Formula('~', second))
            right = Formula('&', Formula('~', first), second)
            return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))
        elif formula.root == '<->':
            left = Formula('&', first, second)
            right = Formula('&', Formula('~', first), Formula('~', second))
            return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))
        elif formula.root == '-&':
            return Formula('~', Formula('&', first, second))
        elif formula.root == '-|':
            return Formula('~', Formula('~', Formula('&', Formula('~', first), Formula('~', second))))
    
    return formula
    # Task 3.6a

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    a = to_not_and(formula)
    
    if is_variable(a.root):
        return Formula(a.root)
    
    if is_constant(a.root):
        if a.root == 'T':
            return Formula('-&', Formula('p'), Formula('-&', Formula('p'), Formula('p')))
        else:
            b = Formula('-&', Formula('p'), Formula('-&', Formula('p'), Formula('p')))
            return Formula('-&', b, b)
    
    if is_unary(a.root):
        b = to_nand(a.first)
        return Formula('-&', b, b)
    
    if is_binary(a.root):
        b = to_nand(a.first)
        c = to_nand(a.second)
        
        if a.root == '&':
            d = Formula('-&', b, c)
            return Formula('-&', d, d)
        elif a.root == '|':
            d = Formula('-&', b, b)
            e = Formula('-&', c, c)
            f = Formula('-&', d, e)
            return Formula('-&', f, f)
        elif a.root == '->':
            d = Formula('-&', b, c)
            return Formula('-&', b, Formula('-&', d, d))
        elif a.root == '+':
            d = Formula('-&', b, c)
            e = Formula('-&', b, d)
            f = Formula('-&', c, d)
            return Formula('-&', e, f)
        elif a.root == '<->':
            d = Formula('-&', b, c)
            e = Formula('-&', d, d)
            return e
        elif a.root == '-&':
            return Formula('-&', b, c)
        elif a.root == '-|':
            d = Formula('-&', b, b)
            e = Formula('-&', c, c)
            f = Formula('-&', d, e)
            return f
    
    return a
    # Task 3.6b

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    a = to_nand(formula)
    
    if a.root == '-&':
        b = Formula('p')
        c = Formula('q')
        d = Formula('->', b, Formula('~', c))
        return a.substitute_operators({'-&': d})
    
    return a

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    a = to_implies_not(formula)

    mapp = {'~': Formula.parse('(p->F)')}

    return a.substitute_operators(mapp)
    # Task 3.6d
