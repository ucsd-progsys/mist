let x = 10, 
    z = let x = add1(add1(x)), 
            y = add1(x)
        in 
            y
in 
    add1(z)
