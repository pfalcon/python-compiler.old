def fun():
    x = 123
    y = 456

    for y in range(2):
        z = 5
        for x in range(5):
            def fun2():
                print(y, x)
            fun2()
            last_x = x
    print("old:", x, y)
    print("last x:", last_x)
    print("z:", z)

fun()
