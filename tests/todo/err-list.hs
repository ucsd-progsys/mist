def null() as forall a. () => List[a]:
  false
in

def link(h, t) as forall a. (a, List[a]) => List[a]:
  (h, t)
in

link(1, link(true, null())) 
