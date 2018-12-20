let compose = (lambda(f, g): (lambda (x): f(g(x)))),
    incr    = (lambda(x): x + 1)
in
    compose(incr, incr)(100)
