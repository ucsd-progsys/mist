-- https://github.com/idris-lang/Idris-dev/blob/master/samples/ST/Intro.idr

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
-- crashes if this is Int instead of Int
new :: rforall a. ST <a >a >Int
new = undefined

-- | Read a `Int`
read :: hg:(Map <Int >Int) ~> p:Int -> ST <{h:Map <Int >Int | h == hg} >{h:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
read = undefined

-- | Write a `Int`
write :: h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
write = undefined

-----------------------------------------------------------------------------
increment :: h:(Map <Int >Int) ~> r:Int -> ST <{v:Map <Int >Int | v == h} >{v:Map <Int >Int| store h r ((select h r)+1) == v} >Unit
increment = \r -> bind (read r) (\n -> write r (n+1))

