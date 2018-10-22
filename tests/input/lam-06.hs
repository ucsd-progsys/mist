def compose(f, g):
  lambda (x): f(g(x))
in
def incr(x):
  x + 1
in
  compose(incr, incr)(200)
