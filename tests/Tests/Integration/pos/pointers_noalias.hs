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

bind as rforall a, b, p, q, r.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = 0

thenn as rforall a, b, p, q, r.
  ST <p >q >a
  -> ST <q >r >b
  -> ST <p >r >b
thenn = (0)

pure as rforall a, p, q.  x:a -> ST <p >q >a
pure = 0

-- | Some opaque implementation of pointers to `Int` ------------------------
-- type Int = ()

undefined as forall a. a
undefined = 0

-- | Allocating a fresh `Int` with value `0`
new as rforall a. ST <a >a >Int
new = undefined

-- | Read a `Int`
get as hg:(Map <Int >Int) ~> p:Int -> ST <{h:Map <Int >Int | h == hg} >{h:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
get = undefined

-- | Write a `Int`
set as h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
set = undefined

-----------------------------------------------------------------------------
decr :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h r ((select h r)-1) == v} >Unit
decr = \r -> bind (get r) (\n -> set r (n-1))

-- TODO should work, blocked on tests/Tests/Integration/todo/tabs_with_ifun.hs
-- init :: rforall p, q, a. hinit:(Map<Int >Int) ~> n:Int -> (r:Int ~> (ST <{v:Map <Int >Int | v == hinit} >{v:Map <Int >Int| store hinit r n == v} >{v:Int | v == r}) -> ST <p >q >a ) -> ST <p >q >a
-- init = \n -> \f -> (bind (new) (\ptr -> f (thenn (set ptr n) (pure ptr))))


-- zero :: r:Int -> ST ()
-- zero r = do
--    n <- get
--    if (n <= 0)
--        then return ()
--        else decr r >> zero r

-- TODO implement `min`
-- zero :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| v == store h r (min 0 (select h r))} >{v:Int | v == 0}
-- zero = \r -> bind (get r) (\n -> if n <= 0 then pure 0 else (thenn (decr r) (zero r)))

zero :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h /\ (0 <= select h r) } >{v:Map <Int >Int| v == store h r 0} >{v:Int | v == 0}
zero = \r -> bind (get r) (\n -> if n <= 0 then pure 0 else (thenn (decr r) (zero r)))

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
assert as {v:Bool | v} -> Unit
assert = 0

test :: h:(Map<Int >Int) ~> n1:{v:Int | 0 <= v} -> n2:{v: Int | 0 <= v} -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| 0 == 0} >Unit
test = \n1 -> \n2 -> bind new (\r1 ->
      (thenn (set r1 n1)
      (bind new (\r2 ->
      (thenn (set r2 n2)
      (thenn (zero r1)
      (thenn (zero r2)
      (bind (get r1) (\v1 ->
      (bind (get r2) (\v2 ->
      (pure (assert ((v1 == 0) /\ (v2 == 0)))))))))))))))
-----------------------------------------------------------------------------

simple :: h:(Map<Int >Int) ~> p:Int -> n:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h p n == v} >{v:Int | v == n}
simple = \p -> \n -> thenn (set p n) (get p)
