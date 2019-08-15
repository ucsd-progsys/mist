-- module State where

-- rjhala [10:45 AM]
-- The idris people have a bunch of nice STATE examples here:https://github.com/idris-lang/Idris-dev/tree/master/samples/ST
-- For a start, how about [login.idr](https://github.com/idris-lang/Idris-dev/blob/master/samples/ST/Login.idr)
-- except in a way where you can clearly tell what’s going on…
--
-- rjhala [11:43 AM]
-- here’s a super simple example: can you get it to work with suitable annotations?

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Unit
assert = \tru -> Unit
-----------------------------------------------------------------------------
-- | Library ----------------------------------------------------------------
-----------------------------------------------------------------------------
bind :: rforall a, b, p, q, r.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

thenn :: rforall a, b, p, q, r.
  ST <p >q >a
  -> ST <q >r >b
  -> ST <p >r >b
thenn = undefined

pure :: rforall a, p, q.  x:a -> ST <p >q >a
pure = undefined

-- | Some opaque implementation of pointers to `Int` ------------------------

-- | Allocating a fresh `Int` with value `0`
new :: rforall a. ST <a >a >Int
new = undefined

-- | Read a `Int`
get :: hg:(Map <Int >Int) ~> p:Int -> ST <{h:Map <Int >Int | h == hg} >{h:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
get = undefined

-- | Write a `Int`
set :: h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
set = undefined

-----------------------------------------------------------------------------
decr :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h r ((select h r)-1) == v} >Unit
decr = \r -> bind (get r) (\n -> set r (n-1))

init :: rforall p, q, a. hinit:(Map<Int >Int) ~> n:Int -> (r:Int ~> (ST <{v:Map <Int >Int | v == hinit} >{v:Map <Int >Int| store hinit r n == v} >{v:Int | v == r}) -> ST <p >q >a ) -> ST <p >q >a
init = \n -> \f -> (bind (new) (\ptr -> f (thenn (set ptr n) (pure ptr))))


-- zero :: r:Int -> ST ()
-- zero r = do
--    n <- get
--    if (n <= 0)
--        then return ()
--        else decr r >> zero r

-- TODO implement aliaes, so I can write this nicely with `min`
zero :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| v == store h r (if (select h r) < 0 then select h r else 0)} >Unit
zero = \r -> bind (get r) (\n -> if n <= 0 then pure Unit else (thenn (decr r) (zero r)))

-- zero :: h:(Map<Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h /\ (0 <= select h r) } >{v:Map <Int >Int| v == store h r 0} >Unit
-- zero = \r -> bind (get r) (\n -> if n <= 0 then pure Unit else (thenn (decr r) (zero r)))

-- test :: Nat -> Nat -> ST ()
-- test n1 n2 =
--    init n1 $ \r1 ->
--    init n2 $ \r2 -> do
--    zero <$> r1
--    zero <$> r2
--    v1 <- get <$> r1
--    v2 <- get <$> r2
--    pure (assert (v1 == 0 && v2 == 0))

test :: h:(Map<Int >Int) ~> n1:{v:Int | 0 <= v} -> n2:{v: Int | 0 <= v} -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| 0 == 0} >Unit
test = \n1 -> \n2 ->
      init n1 (\str -> bind str (\r1 ->
      (init n2 (\str -> bind str (\r2 ->
      (thenn (zero r1)
      (thenn (zero r2)
      (bind (get r1) (\v1 ->
      (bind (get r2) (\v2 ->
      (pure (assert ((v1 == 0) /\ (v2 == 0)))))))))))))))
