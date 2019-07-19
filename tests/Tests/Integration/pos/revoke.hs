pure as forall a. acl:Set ~> x:a -> Perm <{v:Set | v == acl} >{v:Set | v == acl} >{v:a | v == x}
pure = 0

bind as rforall a, b. acl1:Set ~> acl2:Set ~> acl3:Set ~> (Perm <{v:Set | v == acl1} >{v:Set | v == acl2} >a) -> (x:a -> Perm <{v:Set | v == acl2} >{v:Set | v == acl3} >b) -> Perm <{v:Set | v == acl1} >{v:Set | v == acl3} >b
bind = 0

thenn as rforall a, b. acl1:Set ~> acl2:Set ~> acl3:Set ~> (Perm <{v:Set|v==acl1} >{v:Set|v==acl2} >a)
  -> (Perm <{v:Set|v==acl2} >{v:Set|v==acl3} >b)
  -> Perm <{v:Set|v==acl1} >{v:Set|v==acl3} >b
thenn = (0)

canRead as acl:Set ~> f:Int -> Perm <{v:Set | v == acl}  >{v:Set | v == acl} >{v:Bool | v == f ∈ acl}
canRead = 0

grant as aclGrant:Set ~> f:Int -> Perm <{v:Set | v == aclGrant} >{v:Set | v == setPlus aclGrant f} >Unit
grant = 0

revoke as acl:Set ~> f:Int -> Perm <{v:Set | v == acl} >{v:Set | v == setMinus acl f} >Unit
revoke = 0

read as aclRead:Set ~> {v:Int | v ∈ aclRead} -> Perm <{v:Set | v == aclRead} >{v:Set | v == aclRead} >String
read = 0

runPerm as rforall a. acl:Set -> (Perm <{v:Set | v == acl} >{v:Set | True} >a) -> a
runPerm = 0

-- TODO: should use theory emptyset, but failing that we should actually
-- make this assume work.
-- emptySet as {v: Set | 0 == 0}
-- emptySet = 0

foo :: start:Set ~> f:Int -> Perm <{v:Set | v == start} >{v:Set | 0 == 0} >String
foo = \f -> (bind (grant f) (\asdf -> (bind (read f) (\contents -> (bind (revoke f) (\asdf -> pure contents))))))

-- foo :: start:Set ~> f:Int -> Perm <{v:Set | v == start} >{v:Set | f ∈ v} >Unit
-- foo = \f -> (grant f)

-- foo :: acl:Set -> Int -> Perm <{v:Set | v == acl} >{v:Set | v == acl} >String
-- foo = \acl -> (\f -> (bind (grant f) (\asdf -> bind (read f) (\contents -> bind (revoke f) (\asdf -> pure contents)))))
