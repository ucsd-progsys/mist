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

pure as rforall a. x:a -> List >a
pure = 0

barg
  :: se:(Set >Int)
  ~> ({v1:Int | v1 ∈ se} -> Bool)
  -> cur:{v2:Int | v2 ∈ se}
  -> SetST <{v3:Set >Int | v3 == se} >{v4:Set >Int | setSubset se v4} >Int
barg = \se ~> \f -> \i -> let g :: se2:{v5:Set >Int | setSubset se v5} ~> cur:{v6:Int | v6 ∈ se2} -> SetST <{v7:Set >Int | v7 == se2} >{v8:Set >Int | setSubset se2 v8} >Int
                          = barg f
                    in for g (pure i)
