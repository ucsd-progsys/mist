{-

Perm acl1 acl2 a = Perm a

pure as forall a. acl ~> x:a -> Perm acl acl {v | v = x}

(>>=) as forall a, b. ac1 ~> acl2 ~> acl3
  ~> Perm acl1 acl2 a
  -> (a -> Perm acl2 acl3 b)
  -> Perm acl1 acl3

canRead as acl ~> f:File -> Perm acl acl {v | v = f ∈ acl}

grant as acl ~> f:File -> Perm acl {v | v = acl + f} ()

revoke as acl ~> f:File -> SST acl (acl - f) ()

read as acl ~> {v:File | v ∈ acl} -> Perm acl acl String

runPerm : forall a. acl -> Perm acl {v | True} a -> a

foo :: file:File -> String
foo f = runPerm [] (grant f >> read f >>= (\contents -> revoke f >> pure contents))


type File = Int
-}

