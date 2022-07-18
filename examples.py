import myDBalgebra as myAlgebra
import myDBtables as myTrees

###A few examples###

# Functions
def eq(a, b):
    return a == b


def geq(a, b):
    return a >= b


def leq(a, b):
    return a <= b


# Tables
dict_teach = {"id": [45, 32], "lastname": ["boiret", "hugot"], "firstname": ["adrien", "vincent"]}
dict_course = {"id": [70, 80, 90], "title": ["python", "bdd", "verif"], "teacher": [32, 45, 32]}

dict_test = {"id": [70, 80, 90], "title": ["python", "bdd", "verif"], "teacher": [32, 45, 32],"tea": [32, 45, 32]}


# Table leaves in algebra trees
tab1 = myAlgebra.Table("Teacher",dict_teach)
tab2 = myAlgebra.Table("Course",dict_course)
tab3 = myAlgebra.Table("Course",dict_test)

# A few useful binary functions
funceq = myAlgebra.Func(symb="Equal", f=eq)
funcgeq = myAlgebra.Func(symb="Greater", f=geq)
funcleq = myAlgebra.Func(symb="Less than", f=leq)

# A few tests

# Teacher.id=Course.teacher
testJoinTeach = myAlgebra.Test(func=funceq, op1=myAlgebra.Attribute("Teacher", "id"), op2=(myAlgebra.Attribute("Course", "teacher")))
# Course.id>80
testBigID = myAlgebra.Test(func=funcgeq, op1=myAlgebra.Attribute("Course", "id"), op2=myAlgebra.Constant(80))

# A join of Teacher and Course on the attributes Teacher.id and Course.teacher
tJoin = myAlgebra.Restrict(
    test = testJoinTeach,
    mid = myAlgebra.Times(
        left = tab1,
        right = tab2
    )
)

# A join of Teacher and Course on the attributes Teacher.id and Course.teacher
tJoinVrai = myAlgebra.Join(
    left = tab1,
    right = tab2,
    op1 = myAlgebra.Attribute("Teacher", "id"),
    op2 = myAlgebra.Attribute("Course", "teacher")
)

#projection for test
tProject = myAlgebra.Project(
    list = [myAlgebra.Attribute("Course", "title"), myAlgebra.Attribute("Teacher", "lastname")],
    mid = myAlgebra.Times(
        left = tab1,
        right = tab2
    )
)

# Then we only keep courses of Course.id > 80
tBigID = myAlgebra.Restrict(
    test = testBigID,
    mid = myAlgebra.copy_tree(tJoin)
)

# Then we only keep the Course.title of the course and the Teacher.lastname of the teacher
tFinal = myAlgebra.Project(
    list = [myAlgebra.Attribute("Course", "title"), myAlgebra.Attribute("Teacher", "lastname")],
    mid = myAlgebra.copy_tree(tBigID)
)

# Here are the SELECT FROM WHERE lists that should give an optimized version of this tree

# SELECT
lS=[myAlgebra.Attribute("Course", "id"), myAlgebra.Attribute("Teacher", "lastname")]
# FROM
lF=[tab1,tab2]
# WHERE
lW=[testJoinTeach, testBigID]



lS2=[myAlgebra.Attribute("Course", "id"), myAlgebra.Attribute("Teacher", "lastname")]
lF2 = [tab1,tab3]
lW2=[testJoinTeach]
print(myAlgebra.string_table(myAlgebra.make_query_tree(lS2,lF2,lW2)))