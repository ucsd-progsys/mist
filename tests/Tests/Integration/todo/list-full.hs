def link(h, t):
  (h, t)
in

def head(l):
  l[0]
in

def tail(l):
  l[1]
in

def isNull(l):
  l == false
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
  reverseHelper(false, l)
in

let l0 = link(0, link(1, link(2, link(3, link(4, link(5, false)))))),
    r0 = print(length(l0)),
    r1 = print(reverse(l0)),
    r2 = print(append(l0, l0))
in
    0
