let f = (lambda(x): let tmp = x + 1 in
                    (lambda(y): y + tmp))
  , g = f(1)
  , h = f(10)
in
    (g(0), h(0))
