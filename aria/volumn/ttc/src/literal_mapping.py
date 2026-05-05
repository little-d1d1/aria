from lark import Lark, Transformer
from lark.tree import Tree
from .utils import log
from .global_storage import gbl
import pandas as pd

# TODO what happens for free literals

grammar = r"""
    ?start: inequality

    inequality: "(" ">=" sum number ")"

    sum: "(" "+" product+ ")" | product

    product: "(" "*" number identifier ")" | identifier

    identifier: VAR | QUOTED_VAR

    VAR: /[a-zA-Z._~#@][a-zA-Z0-9._~#@]*/
    QUOTED_VAR: "|" /[^|]+/ "|"

    number: signed_number | unsigned_number | fraction
    signed_number: "(" "-" UNSIGNED_NUMBER ")"
    unsigned_number: UNSIGNED_NUMBER
    fraction: "(" "/" number number ")"

    %import common.SIGNED_NUMBER
    %import common.INT -> UNSIGNED_NUMBER
    %import common.WS
    %ignore WS
"""



class VariableCreator(Transformer):
    def __init__(self):
        self.variables = set()

    def inequality(self, *items):
        return {
            "type": "inequality",
            "operator": ">=",
            "left": items[0][0],
            "right": items[0][1]
        }

    def sum(self, *items):
        return {
            "type": "sum",
            "terms": list(items)
        }

    def product(self, *items):
        # Check if it's a standalone variable
        if len(items[0]) == 1 and isinstance(items[0][0], str):
            coefficient = 1
            variable = items[0][0]
            self.variables.add(variable)
        else:  # Otherwise, it's a product term like (* number VAR)
            coefficient = items[0][0]
            variable = self.identifier([items[0][1]])
            self.variables.add(variable)
        return {
            "type": "product",
            "coefficient": coefficient,
            "variable": variable
        }

    def signed_number(self, items):
        # items is a lidst containing one token, e.g., [Token('SIGNED_NUMBER', '-2')]
        token = items[0]
        value = int(token.value)
        return -1 * value

    def fraction(self, items):
        numerator = items[0].children[0]
        denominator = items[1].children[0]
        return numerator / denominator

    def unsigned_number(self, items):
        # items is a list containing one token, e.g., [Token('SIGNED_NUMBER', '-2')]
        token = items[0]
        value = int(token.value)
        sign = -1 if value < 0 else 1
        return sign * value

    def VAR(self, item):
        return str(item)

    def QUOTED_VAR(self, item):
        return str(item)

    def identifier(self, items):
        return items[0]



class ExpressionTransformer(Transformer, list):
    def __init__(self, variables):
        self.variables = variables
        self.constraints = pd.DataFrame(0,
                                        columns=variables, index=range(1))
        self.variable_datatype = float
        if gbl.logic == "lia":
            self.variable_datatype = int

    def fraction(self, items):
        numerator = items[0].children[0]
        denominator = items[1].children[0]
        return numerator / denominator

    def inequality(self, *items):
        number = - items[0][1].children[0]
        if isinstance(number, Tree) and number.data == "fraction":
            number = self.fraction(number.children)
            print(f"number: {number}")
        if isinstance(number, Tree):
            number = self.fraction(number.children)
        self.constraints["const"] = self.constraints["const"].astype(
            self.variable_datatype)
        self.constraints.loc[0, "const"] = self.variable_datatype(number)
        # self.constraints = pd.DataFrame(
        #     0, columns=self.variables, index=range(1))
        # # print(items)
        self.constraints.loc[0, "const"] = - items[0][1].children[0]
        return self.constraints

    def sum(self, *items):
        return {
            "type": "sum",
            "terms": list(items)
        }

    def product(self, *items):
        # Check if it's a standalone variable
        if len(items[0]) == 1 and isinstance(items[0][0], str):
            coefficient = 1
            variable = items[0]
            self.constraints.loc[0, variable] = coefficient
        else:  # Otherwise, it's a product term like (* number VAR)
            coefficient = items[0][0]
            variable = items[0][1]
            self.constraints[variable] = self.constraints[variable].astype(
                self.variable_datatype)
            self.constraints.loc[0, variable] = coefficient.children[0]

        return {
            "type": "product",
            "coefficient": coefficient,
            "variable": variable
        }

    def signed_number(self, items):
        token = items[0]
        value = int(token.value)
        return -1 * value

    def unsigned_number(self, items):
        token = items[0]
        value = int(token.value)
        return value

    def VAR(self, item):
        return str(item)

    def identifier(self, items):
        return items[0]

    def QUOTED_VAR(self, item):
        return str(item)



class LiteralMapping:
    def __init__(self):
        self.variables = set()
        # create empty dataframe for constraints
        self.constraint_matrix = pd.DataFrame()
        self.variable_creator_parser = Lark(grammar, parser='lalr',
                                            transformer=VariableCreator())
        self.parser = None  # will be initialized after we know all variables
        self.num_constraints_added = 0

    def get_variables(self, tree):
        variables = set()

        def traverse(node):
            if isinstance(node, dict):
                if 'variable' in node:
                    variables.add(node['variable'])
                if 'left' in node:
                    traverse(node['left'])
                if 'right' in node:
                    traverse(node['right'])
                if 'terms' in node:
                    for term in node['terms']:
                        if isinstance(term, list):
                            for subterm in term:
                                traverse(subterm)
                        else:
                            traverse(term)
            elif isinstance(node, Tree):
                for child in node.children:
                    traverse(child)

        traverse(tree)
        return variables

    def add_variable_in_constraint_matrix(self, ineq):
        parsed_tree = self.variable_creator_parser.parse(ineq)
        self.variables = self.variables.union(self.get_variables(parsed_tree))

    def finalize_variable_matrix(self):
        self.variables = ["const"] + list(self.variables)
        self.constraint_matrix = pd.DataFrame(
            columns=self.variables, index=range(0))
        log(
            f"created constraint matrix of size {self.constraint_matrix.shape}", 3)
        gbl.dimension = len(self.variables) - 1
        log(f"variables: {self.variables}", 4)
        one_constraint = pd.DataFrame(
            columns=self.variables, index=range(1))

    def negate_constraint(self, constraint_line):
        # negate the constraint line
        df = constraint_line.copy()
        df['const'] = -df['const']
        if gbl.logic == "lia":
            df['const'] = df['const'] - 1
        df.loc[:, df.columns != 'const'] = -df.loc[:, df.columns != 'const']
        return df

    def copy_constraint_matrix(self, constraint_line, literal):
        constraint_line.index = [literal]
        self.constraint_matrix.loc[literal] = constraint_line.iloc[0]

    def add_mapping(self, literal, inequality):
        if literal in [0, 1]:
            return
        self.parser = Lark(grammar, parser='lalr',
                           transformer=ExpressionTransformer(self.variables))
        inequality_line = self.parser.parse(inequality)
        neg_inequality_line = self.negate_constraint(inequality_line)
        self.copy_constraint_matrix(inequality_line, literal)
        self.copy_constraint_matrix(neg_inequality_line, -literal)

    def get_inequalities(self, literals):
        inequalities = []
        for lit in literals:
            if lit in [0, 1]:
                continue
            inequality = self.constraint_matrix.loc(lit)
            if inequality:
                inequalities.append(inequality)
        log(f"inequalities: {inequalities}", 3)
        return inequalities

    def __str__(self):
        return str(self.constraint_matrix)
