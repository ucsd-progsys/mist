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

