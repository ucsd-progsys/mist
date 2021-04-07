pure as forall a. acl:(Set >Int) ~>
  x:a -> Perm <{v:Set >Int | v == acl} >{v:Set >Int | v == acl} >{v:a | v == x}
pure = 0

bind as rforall a, b. acl1:(Set >Int) ~> acl2:(Set >Int) ~> acl3:(Set >Int) ~>
  Perm <{v:Set >Int | v == acl1} >{v:Set >Int | v == acl2} >a ->
  (x:a -> Perm <{v:Set >Int | v == acl2} >{v:Set >Int | v == acl3} >b) ->
  Perm <{v:Set >Int | v == acl1} >{v:Set >Int | v == acl3} >b
bind = 0

thenn as rforall a, b. acl1:(Set >Int) ~> acl2:(Set >Int) ~> acl3:(Set >Int) ~>
  Perm <{v:Set|v==acl1} >{v:Set|v==acl2} >a
  -> Perm <{v:Set|v==acl2} >{v:Set|v==acl3} >b
  -> Perm <{v:Set|v==acl1} >{v:Set|v==acl3} >b
thenn = (0)

canRead as acl:(Set >Int) ~>
  f:Int -> Perm <{v:Set >Int | v == acl}  >{v:Set >Int | v == acl} >{v:Bool | v == f ∈ acl}
canRead = 0

grant as aclGrant:(Set >Int) ~>
  f:Int -> Perm <{v:Set >Int | v == aclGrant} >{v:Set >Int | v == setPlus aclGrant f} >Unit
grant = 0

revoke as acl:(Set >Int) ~>
  f:Int -> Perm <{v:Set >Int | v == acl} >{v:Set >Int | v == setMinus acl f} >Unit
revoke = 0

read as aclRead:(Set >Int) ~>
  {v:Int | v ∈ aclRead} -> Perm <{v:Set >Int | v == aclRead} >{v:Set >Int | v == aclRead} >String
read = 0

runPerm as rforall a. acl:(Set >Int) ->
  Perm <{v:Set >Int | v == acl} >{v:Set >Int | True} >a -> a
runPerm = 0

-- TODO: should use theory emptyset, but failing that we should actually
-- make this assume work.
-- emptySet as {v: Set >Int | 0 == 0}
-- emptySet = 0

foo :: start:(Set >Int) ~> f:Int -> Perm <{v:Set >Int | v == start} >{v:Set >Int | 0 == 0} >String
foo = \f -> (bind (grant f) (\asdf -> (bind (read f) (\contents -> (bind (revoke f) (\asdf -> pure contents))))))

-- foo :: start:(Set >Int) ~> f:Int -> Perm <{v:Set >Int | v == start} >{v:Set >Int | f ∈ v} >Unit
-- foo = \f -> (grant f)

-- foo :: acl:Set -> Int -> Perm <{v:Set >Int | v == acl} >{v:Set >Int | v == acl} >String
-- foo = \acl -> (\f -> (bind (grant f) (\asdf -> bind (read f) (\contents -> bind (revoke f) (\asdf -> pure contents)))))
