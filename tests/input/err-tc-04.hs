def null() as forall a. () => Fist[a]:
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

def sumList(xs):
  if (xs == null()): 
    null()
  else: 
    head(xs) + sumList(tail(xs))
in

let zing = link(1, link(2, link(3, null()))) 

in

sumList(zing)

