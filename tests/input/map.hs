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

def map(f, xs):
  if isNull(xs):
    null()
  else:
    let h = head(xs)
      , t = tail(xs)
    in
       link(f(h), map(f, t))
in

let l0 = range(0, 5)
in
    map((lambda (x): x * 10), l0)
