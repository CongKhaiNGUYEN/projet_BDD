from dataclasses import dataclass
from itertools import product
from turtle import right
from myDBtables import *

@dataclass
class Table:
    name: object #name of the table
    data: object #contents of the table


@dataclass
class Value:
    pass


@dataclass
class Attribute(Value):
    tab: object #name of the table
    name: object #name of the attribute


@dataclass
class Constant(Value):
    c: object


@dataclass
class Func:
    symb: object #symbol for printing
    f: object #function itself


@dataclass
class Test:
    func: Func #binary function of the test
    op1: Value #first operand, attribute or constant
    op2: Value #first operand, attribute or constant


@dataclass
class UnOp:
    mid: object #child of the unry operator


@dataclass
class Project(UnOp):
    symb = "Project"
    list: object #list of attributes we want to project on


@dataclass
class Restrict(UnOp):
    symb = "Restrict"
    test: object #test we want to restrict on


@dataclass
class BinOp:
    left: object #left child of the unry operator
    right: object #right child of the unry operator

@dataclass
class Product(BinOp):
    symb = "Product"

@dataclass
class Join(BinOp):
    symb = "Join"
    op1: Attribute(object,object)
    op2: Attribute(object,object)

class Times(BinOp):
    symb = "Times"


###Tree functions###


# copy_tree makes a copy of the tree t.
# like in lists, writing s=t then modifying s would modify t
# when you want to give to a variable the same value as t, use copy_tree(t)
def copy_tree(t):
    match t:
        case Table(name, data):
            return Table(name, data)
        case Constant(c):
            return Constant(c)
        case Attribute(name, att):
            return Attribute(name, att)
        case Func(symb, f):
            return Func(symb, f)
        case Test(f, op1, op2):
            return Test(copy_tree(f), copy_tree(op1), copy_tree(op2))
        case Restrict(mid,test):
            return Restrict(copy_tree(mid),copy_tree(test))
        case Project(mid,l):
            return Restrict(copy_tree(mid),l.copy())
        case Times(left, right):
            return Times(copy_tree(left),copy_tree(right))
        case Join(left,right,op1,op2):
            return Join(left,right,op1,op2)
        case _:
            print(f'\n\n\nin copy_tree {t}\n\n\n')
            return "XXX"


# string_tree generates a well-bracketed expression corresponding to a tree
def string_tree(t):
    match t:
        # To print a table: index:name
        case Table(name, d):
            return f"{name}"
        # To print a constant, print its value
        case Constant(c=val):
            return f"{val}"
        # To print an attribute: index.name, with the table's index
        case Attribute(tab, name):
            return f"{tab}.{name}"
        # To print a function: print its symbol
        case Func(symb):
            return f"{symb}"
        # To print a test: f(op1,op2)
        #   f the binary test function
        #   op1 the test's first operand
        #   op2 the test's second operand
        case Test(f, op1, op2):
            return f"{string_tree(f)}({string_tree(op1)},{string_tree(op2)})"
        # To print a restriction: Restr[test](child)
        case Restrict(mid, test):
            return f"{t.symb}[{string_tree(test)}]({string_tree(mid)})"
        # To print a list (that we assume to be a list of attributes for Project, for instance)
        # Print every attribute, separated by ", "
        case list():
            res = map(string_tree, iter(t))
            return ", ".join(res)
        # To print a projection: Restr[list of attributes](child)
        case Project(mid, l):
            return f"{t.symb}[{string_tree(l)}]({string_tree(mid)})"
        # To print a product: Times(left,right)
        #   childL and childR are the left and right children of the node
        case Times(l,r):
            return f"{t.symb}({string_tree(l)},{string_tree(r)})"
        #Join[leftChild.colmn==rightChild.column](leftChild,rightChild)
        case Join(left,right,op1,op2):
            return f"{t.symb}[{string_tree(op1)},{string_tree(op2)}]({string_tree(left),string_tree(right)})"
        case _:
            print(f'\n\n\nin string_tree {t}\n\n\n')
            return "XXX"

def implem_tree(t):
    match t:
        case Table(name, data):
            return Table(name,data)
        case Project(mid,l):
            match mid:
                case Times(left,right):
                    tLeft = prefixed_table(left.data, left.name)
                    tRight = prefixed_table(right.data, right.name)
                    prodt = product_table(tLeft,tRight)
                    affiche = project_table(prodt, l)
                    return affiche
                case _:
                    newMid = implem_tree(mid)
                    affiche = project_table(newMid, l)
                    return affiche
        case Restrict(mid,test):
            match mid:
                case Times(left,right):
                    tLeft = prefixed_table(left.data, left.name)
                    tRight = prefixed_table(right.data, right.name)
                    prodt = product_table(tLeft,tRight)
                    affiche = restrict_table(prodt,test)
                    affiche.pop(string_tree(test.op2))
                    return affiche
                case _:
                    newMid = implem_tree(mid)
                    affiche = restrict_table(newMid,test)
                    return affiche

        case Product(left,right):
            return product_table(left, right)
        case Join(jleft,jright,jop1,jop2):
            def eq(a, b):
                return a == b
            funceq = myAlgebra.Func(symb="Equal", f=eq)
            testJoin = myAlgebra.Test(func=funceq, op1=jop1, op2=jop2)
            tJoin = myAlgebra.Restrict(
                test = testJoin,
                mid = myAlgebra.Times(
                    left = jleft,
                    right = jright
                )
            )
            return implem_tree(tJoin)


def impl_tree(t):
    print(string_table(implem_tree(t)))


def is_in(t,s):
    return s in string_tree(t)

def on_table(v):
    match v:
        case Attribute(tab,name):
            return name
        case Constant(c):
            return None

def insert_restrict(t,tst):
    if len(product_table(t.mid.left.data,t.mid.right.data).values()) ==  len(set(map(tuple,product_table(t.mid.left.data,t.mid.right.data).values()))):
        # print("----------------------if----insert--------------------------------------------------")
        return  Restrict(test = copy_tree(tst),mid = copy_tree(t))
    else:
        # print("---------------------else---insert--------------------------------------------------")
        keys = []
        for k1,v1 in t.mid.left.data.items():
            for k2,v2 in t.mid.right.data.items():
                if v1==v2:
                    keys.append(k1)
                    keys.append(k2)

        return Restrict(test = copy_tree(tst),mid = Join(left = t.mid.left, right = t.mid.right, op1 = Attribute(t.mid.left.name,k1),op2=Attribute(t.mid.right.name,k2)))

def make_query_tree(lSelect,lFrom,lWhere):

    tCondition = Restrict(
        test = lWhere[0],
        mid = Times(
            left = lFrom[0],
            right = lFrom[1]
        )
    )
    for condi in lWhere:
        if condi == lWhere[0]:
            continue
        tCondition = insert_restrict(tCondition,condi)
    tFinal = Project(
        list = lSelect,
        mid = copy_tree(tCondition)
    )
    return implem_tree(tFinal)   

