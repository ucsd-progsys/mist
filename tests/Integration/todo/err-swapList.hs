def null() as forall a. () => List[a]:
  false
in

def link(h, t) as forall a. (a, List[a]) => List[a]:
  (h, t)
in

def swapList(p) :: forall a.((List[a], List[b])) => (List[b], List[a]) :
  (p[1], p[0])
in

let l0 = 1
  , l1 = link(true, null())
in
  swapList((l0, l1))
