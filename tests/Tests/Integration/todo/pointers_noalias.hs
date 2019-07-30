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
-- pure as forall a. acl:(Map <Int >Int) ~>
--   x:a -> ST <{v:Map <Int >Int | v == acl} >{v:Map <Int >Int | v == acl} >{v:a | v == x}
-- pure = 0

-- bind as rforall a, b. forall s. acl1:(s) ~> acl2:(s) ~> acl3:(s) ~>
--   ST <{v:s | v == acl1} >{v:s | v == acl2} >a ->
--   (x:a -> ST <{v:s | v == acl2} >{v:s | v == acl3} >b) ->
--   ST <{v:s | v == acl1} >{v:s | v == acl3} >b
-- bind = 0
-- 
-- thenn as rforall a, b. tcl1:(Map <Int >Int) ~> tcl2:(Map <Int >Int) ~> tcl3:(Map <Int >Int) ~>
--   ST <{v:Map <Int >Int|v==tcl1} >{v:Map <Int >Int|v==tcl2} >a
--   -> ST <{v:Map <Int >Int|v==tcl2} >{v:Map <Int >Int|v==tcl3} >b
--   -> ST <{v:Map <Int >Int|v==tcl1} >{v:Map <Int >Int|v==tcl3} >b
-- thenn = (0)
--
-- debugging bind as rforall a, b, p, q, r.
-- debugging   ST <p >q >a ->
-- debugging   (x:a -> ST <q >r >b) ->
-- debugging   ST <p >r >b
-- debugging bind = 0
-- debugging 
-- debugging thenn as rforall a, b, p, q, r.
-- debugging   ST <p >q >a
-- debugging   -> ST <q >r >b
-- debugging   -> ST <p >r >b
-- debugging thenn = (0)
-- debugging 
-- debugging pure as rforall a, p, q.  x:a -> ST <p >q >a
-- debugging pure = 0
-- debugging 
-- debugging -- | Some opaque implementation of pointers to `Int` ------------------------
-- debugging -- type Int = ()
-- debugging 
undefined as forall a. a
undefined = 0
-- debugging 
-- debugging -- | Allocating a fresh `Int` with value `0`
-- debugging new as rforall a. ST <a >a >Int
-- debugging new = undefined
-- debugging 
-- debugging -- | Read a `Int`
-- debugging get as hg:(Map <Int >Int) ~> p:Int -> ST <{h:Map <Int >Int | h == hg} >{h:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
-- debugging get = undefined
-- debugging 
-- | Write a `Int`
set as h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
set = undefined


-----------------------------------------------------------------------------
--- what's wrong here?
-- setprime :: forall a. h:(Map <Int >Int) ~> p:Int -> v:Int -> (z:a -> a) -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
-- setprime = \p -> \n -> \f -> set p n

setprime :: h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
setprime = \p -> \n -> set p n

-- works:
-- decr :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h r ((select h r)-1) == v} >Unit
-- decr = \r -> bind (get r) (\n -> set r (n-1))

-- should work
-- init :: rforall p, q, a. hinit:(Map<Int >Int) ~> n:Int -> (r:Int ~> (ST <{v:Map <Int >Int | v == hinit} >{v:Map <Int >Int| store hinit r n == v} >{v:Int | v == r}) -> ST <p >q >a ) -> ST <p >q >a
-- init = \n -> \f -> (bind (new) (\ptr -> f (thenn (set ptr n) (pure ptr))))


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

-- simple :: h:(Map<Int >Int) ~> p:Int -> n:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h p n == v} >{v:Int | v == n}
-- simple = \p -> \n -> thenn (set p n) (get p)
