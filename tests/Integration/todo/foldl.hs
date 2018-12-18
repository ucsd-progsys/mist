def null() as forall a. () => List[a]:
  false
in

def link(h, t) as forall a. (a, List[a]) => List[a]:
  (h, t)
in

def head(l) as forall a. (List[a]) => a:
  l[0]
in

def tail(l) as forall a. (List[a]) => List[a]:
  l[1]
in

def isNull(l) as forall a. (List[a]) => Bool:
  l == null()
in

def range(i, j):
  if (i < j):
    link(i, range(i+1, j))
  else:
    null()
in

def foldl(f, acc, xs):
  if isNull(xs):
    acc
  else:
    foldl(f, f(acc, head(xs)), tail(xs))
in

def fac(n):
  foldl((lambda (x, y): x * y), 1, range(1, n+1))
in

(fac(3) + fac(4) + fac(5))
