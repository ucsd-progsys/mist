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

def length(l):
  if isNull(l):
    0
  else:
    1 + length(tail(l))
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

def reverseHelper(acc, l):
  if isNull(l):
    acc
  else:
    let h = head(l),
        t = tail(l)
    in
        reverseHelper(link(h, acc), t)
in

def reverse(l):
  reverseHelper(null(), l)
in

let l0 = link(0, link(1, link(2, link(3, link(4, link(5, null()))))))
in
    reverse(l0)
