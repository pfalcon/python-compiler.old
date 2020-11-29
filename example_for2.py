def fun():
    x = 123
    for x in range(5):
        def subfun():
            print(x)
        subfun()
    print("old x:", x)

fun()
