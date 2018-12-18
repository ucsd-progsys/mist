def swap(p) :: forall a, b. ((a, b)) => (b, a):
  (p[1], p[0])
in
  swap((10, 15))
