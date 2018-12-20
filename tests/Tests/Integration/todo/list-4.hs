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

def append(l1, l2):
  if isNull(l1):
    l2
  else:
    let h1 = head(l1),
        t1 = tail(l1)
    in
        link(h1, append(t1, l2))
in

def range(i, j):
  if (i < j):
    link(i, range(i+1, j))
  else:
    null()
in

let l0 = range(0, 3),
    l1 = range(3, 6)
in
    append(l0, l1)
