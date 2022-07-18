# Enter here

if __name__ == '__main__':
    import myDBalgebra as a
    import myDBtables as t
    import examples as e

    print("Examples")
    print("Table \"Teacher\"")
    print(t.string_table(e.dict_teach))
    print("Table \"Course\"")
    print(t.string_table(e.dict_course))

    dprefixed=t.prefixed_table(e.dict_teach,"Teacher")
    print("Teacher after renaming")
    print(t.string_table(dprefixed))
    dproj=t.project_table(dprefixed,[a.Attribute("Teacher","lastname")])
    print("Projection of Teacher on lastname")
    print(t.string_table(dproj))

    print("Expression of the example request")
    print(a.string_tree(e.tFinal))