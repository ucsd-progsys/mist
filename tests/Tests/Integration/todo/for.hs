for as rforall a, b.
  s:Set ~>
  (x:a ->
  SetST
    <{v:Set | setSubset s v}
    >{v:Set | setSubset s v}
    >b) ->
  List >a ->
  SetST
    <{v:Set | v == s}
    >{v:Set | setSubset s v}
    >b
-- We can implement for using Lists (see append.hs)
for = 0

f as forall a. fs:Set ~> x:a -> SetST <{v:Set | v == fs} >{v:Set | setSubset fs v} >Int
f = 0

foo :: foos:Set ~> acts:(List >Int) -> SetST <{v:Set | v == foos} >{v:Set | setSubset foos v} >Int
foo = \acts -> for f acts
