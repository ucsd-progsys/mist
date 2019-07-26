-- module State where

-- rjhala [10:45 AM]
-- The idris people have a bunch of nice STATE examples here:https://github.com/idris-lang/Idris-dev/tree/master/samples/STFor a start, how about [login.idr](https://github.com/idris-lang/Idris-dev/blob/master/samples/ST/Login.idr)
-- except in a way where you can clearly tell what’s going on…
--
-- rjhala [11:43 AM]
-- here’s a super simple example: can you get it to work with suitable annotations?

-----------------------------------------------------------------------------
-- | Library ----------------------------------------------------------------
-----------------------------------------------------------------------------
pure as forall a. acl:(Map <Int >Int) ~>
  x:a -> Perm <{v:Map <Int >Int | v == acl} >{v:Map <Int >Int | v == acl} >{v:a | v == x}
pure = 0

bind as rforall a, b. acl1:(Map <Int >Int) ~> acl2:(Map <Int >Int) ~> acl3:(Map <Int >Int) ~>
  Perm <{v:Map <Int >Int | v == acl1} >{v:Map <Int >Int | v == acl2} >a ->
  (x:a -> Perm <{v:Map <Int >Int | v == acl2} >{v:Map <Int >Int | v == acl3} >b) ->
  Perm <{v:Map <Int >Int | v == acl1} >{v:Map <Int >Int | v == acl3} >b
bind = 0

thenn as rforall a, b. acl1:(Map <Int >Int) ~> acl2:(Map <Int >Int) ~> acl3:(Map <Int >Int) ~>
  Perm <{v:Map <Int >Int|v==acl1} >{v:Map <Int >Int|v==acl2} >a
  -> Perm <{v:Map <Int >Int|v==acl2} >{v:Map <Int >Int|v==acl3} >b
  -> Perm <{v:Map <Int >Int|v==acl1} >{v:Map <Int >Int|v==acl3} >b
thenn = (0)

-- | Some opaque implementation of pointers to `Int` ------------------------
-- type Int = ()

undefined as forall a. a
undefined = 0

-- | Allocating a fresh `Int` with value `0`
new as rforall a. ST <a >a >Int
new = undefined

-- | Read a `Int`
get as hg:(Map <Int >Int) ~> p:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
get = undefined

-- | Write a `Int`
set as h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
set = undefined

-----------------------------------------------------------------------------
-- decr :: r:Int -> ST ()
-- decr r = do
--    n <- get r
--    set r (n - 1)
--    return ()
-- 
-- init :: n:Int -> ST Int
-- init n = do
--    r <- new
--    set r n
--    return r
-- 
-- zero :: r:Int -> ST ()
-- zero r = do
--    n <- get
--    if (n <= 0)
--        then return ()
--        else decr r >> zero r
-- 
-- test :: Nat -> Nat -> ST ()
-- test n1 n2 = do
--    r1 <- init n1
--    r2 <- init n2
--    zero r1
--    zero r2
--    v1 <- get r1
--    v2 <- get r2
--    assert (v1 == 0 && v2 == 0)
--    return ()
-----------------------------------------------------------------------------

simple :: h:(Map<Int >Int) ~> p:Int -> n:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h p n == v} >Unit
simple = \p -> \n -> set p n
