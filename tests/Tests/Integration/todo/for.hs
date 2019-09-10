for as rforall a, b.
  s:(Set >Int) ~>
  (set:{v:Set >Int | setSubset s v} ~>
   x:a ->
   SetST
   <{v:Set >Int | v == set}
   >{v:Set >Int | setSubset set v}
   >b) ->
  List >a ->
  SetST
    <{v:Set >Int | v == s}
    >{v:Set >Int | setSubset s v}
    >b
-- We can implement for using Lists (see append.hs)
for = 0

f as forall a. fs:(Set >Int) ~> x:a -> SetST <{v:Set >Int | v == fs} >{v:Set >Int | setSubset fs v} >Int
f = 0

foo :: foos:(Set >Int) ~> acts:(List >Int) -> SetST <{v:Set >Int | v == foos} >{v:Set >Int | setSubset foos v} >Int
foo = \acts -> for f acts

pure as rforall a. x:a -> List >a
pure = 0

baz :: s:(Set >Int) ~> Int -> SetST <{v:Set >Int | v == s} >{v:Set >Int | setSubset s v} >Int
baz = \i -> for baz (pure i)

bar :: se:(Set >Int) ~> cur:{v:Int | v ∈ se} -> SetST <{v:Set >Int | v == se} >{v:Set >Int | setSubset se v} >Int
bar = \i -> for bar (pure i)

barg :: se:(Set >Int) ~> ({v:Int | v ∈ se} -> Bool) -> cur:{v:Int | v ∈ se} -> SetST <{v:Set >Int | v == se} >{v:Set >Int | setSubset se v} >Int 
barg = \f -> \i -> let g :: se2:{v:Set >Int | setSubset se v} ~> cur:{v:Int | v ∈ se2} -> SetST <{v:Set >Int | v == se2} >{v:Set >Int | setSubset se2 v} >Int
                          = barg f
                    in for g (pure i)
