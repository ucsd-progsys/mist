let x = 10,
    z = let x1 = add1(add1(x)),
            y  = add1(x1)
        in
            y
in
    add1(z)
