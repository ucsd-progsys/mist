{-

type Acl = Set String
type AST ac1 acl2 Acl a = HST acl1 acl2 Acl a

pure :: acl ~> a -> AST acl acl a
(>>=) :: acl1 acl2 acl3 ~> AST acl1 acl2 a -> (a -> AST acl2 acl3 b) -> AST acl3 b

canRead :: acl ~> f:File -> AST acl acl {v | v = f ∈ acl}
canRead f = State (\acl -> (acl, member f acl))

grant :: acl ~> f:File -> AST acl {v | v = acl ∪ singleton f} ()
grant f = State (\acl -> (insert f acl, ()))

revoke :: acl ~> f:File -> AST acl {v | v = acl - singleton f} ()
revoke f = State (\acl -> (delete f acl, ()))

read :: acl ~> {f:File | f ∈ acl} -> AST acl acl String
read f = State (\acl -> (acl, "file contents"))

safeRead :: acl ~> f:File -> AST acl acl (Maybe String)
safeRead f = do
  allowed <- canRead
  if allowed
    then read >>= (\c -> Just c)
    else Nothing

main :: String
main = runST empty
  (do
    grant "f.txt"
    c <- read "f.txt"
    revoke "f.txt"
    pure contents)
-}

pure as forall a. acl:Set ~> x:a -> Perm <{v:Set | v == acl} >{v:Set | v == acl} >{v:a | v == x}
pure = 0

bind as forall a, b. acl1:Set ~> acl2:Set ~> acl3:Set ~> (Perm <{v:Set | v == acl1} >{v:Set | v == acl2} >a) -> (x:a -> Perm <{v:Set | v == acl2} >{v:Set | v == acl3} >b) -> Perm <{v:Set | v == acl2} >{v:Set | v == acl3} >b
bind = 0

canRead as acl:Set ~> f:Int -> Perm <{v:Set | v == acl}  >{v:Set | v == acl} >{v:Bool | v == f ∈  acl}
canRead = 0

grant as acl:Set ~> f:Int -> Perm <{v:Set | v == acl} >{v:Set | v == setPlus acl f} >Unit
grant = 0

revoke as acl:Set ~> f:Int -> Perm <{v:Set | v == acl} >{v:Set | v == setMinus acl f} >Unit
revoke = 0

read as acl:Set ~> {v:Int | v ∈  acl} -> Perm <{v:Set | v == acl} >{v:Set | v == acl} >String
read = 0

runPerm as forall a. acl:Set -> (Perm <{v:Set | v == acl} >{v:Set | True} >a) -> a
runPerm = 0

-- TODO: should use theory emptyset, but failing that we should actually
-- make this assume work.
-- emptySet as {v: Set | 0 == 0}
-- emptySet = 0

-- foo :: Int -> Perm <{v:Set | v == v} >{v:Set | v == v} >String
-- foo = \f -> (bind (grant f) (\asdf -> (read f)))

foo :: Set -> Int -> Perm <{v:Set | v == acl} >{v:Set | v == acl} >String
foo = \acl -> (\f -> (bind (grant f) (\asdf -> bind (read f) (\contents -> bind (revoke f) (\asdf -> pure contents)))))
