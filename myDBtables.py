import myDBalgebra as myAlgebra

###Table manipulation functions###

#table_length checks that all attributes of d have the same number of entries, and returns that number
def table_length(d):
    #empty table of size zero
    if d == {}:
        return 0

    #for non empty tables, first element gives the length
    myIter = (iter(d))
    n = len(d[next(myIter)])

    #this loop tests consistency
    for att in myIter:
        assert n == len(d[att]), f"Table with inconsistent lengths! {att} is {len(d[att])} instead of {n}"

    #if all is well, return the length
    return n


#get_entry gets the ith entry of d
def get_entry(d,i):
    res={}
    for att in d:
        res[att]=d[att][i]
    return res


#add_entry adds an entry e at the end of d. If an attribute is unspecified, it's None.
def add_entry(d, e):
    #checking we don't add undue attributes
    for att in e:
        assert att in d, f"Adding attribute {att}, not in receiving table"

    #adding the right value at the end of every d[att]
    for att in d:
        if att in e:
            d[att].append(e[att])
        else:
            d[att].append(None)


#pop_entry deletes the ith entry of d
def pop_entry(d, i):
    assert i <= table_length(d), f"Error: there is no entry of that index {i}"
    for att in d:
        d[att].pop(i)


#test_entry gets a single entry and checks if it validates a test
def test_entry(e, test):
    #fetch first operand
    match test.op1:
        case myAlgebra.Attribute(): d1 = e[myAlgebra.string_tree(test.op1)]
        case myAlgebra.Constant(c): d1 = c
        case _: assert False, "Error in the test: invalid op1"

    #fetch second operand
    match test.op2:
        case myAlgebra.Attribute(): d2 = e[myAlgebra.string_tree(test.op2)]
        case myAlgebra.Constant(c): d2 = c
        case _: assert False, "Error in the test: invalid op2"

    #fetch function
    match test.func:
        case myAlgebra.Func(f=fun): g=fun
        case _: assert False, "Error in the test: invalid function"

    #apply function to operands
    return g(d1,d2)


###Database Operators###


# project_table only keeps the attributes of dictionary of lists d that appear in list of Attributes l
# warning: the dataclass Attribute is not hashable and thus cannot be a key
# we use string_tree() of myDBalgebra to turn Attributes into strings
def project_table(d,l):
    res = {}
    lstring=list(map(myAlgebra.string_tree,l))
    # checking we don't project on nonexisting attributes
    for att in lstring:
        assert att in d, f"Projecting on attribute {att}, not in receiving table"

    # every attribute we see in l gets copied without alterations. others are lost
    for att in d:
        if att in lstring:
            res[att] = d[att].copy() #copy to avoid modifications crawling back up in the original tables
    return res


# prefixed_table creates a copy of dictionary d where every attribute att is changed for s.att
# necessary since attributes are not hashable
def prefixed_table(d,s):
    res = {}
    for att in d:  #for att in d.keys()
        temp=myAlgebra.string_tree(myAlgebra.Attribute(s,att))
        res[temp]=d[att].copy()
    return res


# restrict_table only keeps the lines of d that satisfy test
def restrict_table(d,test):
    res = {}
    #initializing res
    for att in d:
        res[att] = []

    n=table_length(d)
    #loop that goes through entries of d and only add them if they satisfy test
    for i in range(n):
        e = get_entry(d,i)
        if test_entry(e,test):
            add_entry(res,e)
    return res




# product_table makes the cartesian product between two tables WITH NO COMMON ATTRIBUTE
def product_table(d1,d2):
    # res starts as an empty table with the attribute of both tables
    res = {}
    # NO COMMON ATTRIBUTE or this doesn't work right
    for att in d1:
        res[att] = []
    for att in d2:
        res[att] = []
    n1 = table_length(d1)
    n2 = table_length(d2)
    # double loop to add all combinations
    # NO COMMON ATTRIBUTE or this doesn't work right
    for i in range(n1):
        for j in range(n2):
            # these two lines compute the combination of the ith entry of d1 and the jth entry of d2
            e = get_entry(d1,i)
            # NO COMMON ATTRIBUTE or this doesn't work right
            e.update(get_entry(d2, j))
            # then we push
            add_entry(res,e)
    return res


###Table printing functions###


# prints a value in width exactly lim
# not pretty but not broken. touch at your own risk
def string_val(x, lim=20):
    s = f"{x}"
    if len(s) > lim:
        return s[:7] + "..."
    else:
        return f"{s: >{lim}}"


# prints the values of the entry i of d in the order ord (by default the order of d) with a width of lim.
# not pretty but not broken. touch at your own risk
def string_line(d, i, ord=None, lim=20):
    if ord is None:
        ord = d
    s = "|"
    for att in ord:
        s = s + string_val(d[att][i], lim) + "|"
    return s


# prints the titles of d in the order ord (by default the order of d) with a width of lim. Adds decorations.
# not pretty but not broken. touch at your own risk
def string_title(d, ord=None, lim=20):
    if ord is None:
        ord = d
    s = "|"
    for att in ord:
        s = s + string_val(att, lim) + "|"
    s = s + "\n" + "+"
    for att in ord:
        s = s + "-" * (lim) + "+"
    return s


# prints d with the order ord (by default the order of d) with a width of lim.
# not pretty but not broken. touch at your own risk
def string_table(d, ord=None, lim=20):
    if ord is None:
        ord = d
    s = string_title(d, ord, lim) + "\n"
    n = table_length(d)
    for i in range(n):
        s = s + string_line(d, i, ord, lim) + "\n"
    return s
