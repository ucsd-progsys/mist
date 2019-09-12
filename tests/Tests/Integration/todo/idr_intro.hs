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
-- crashes if this is Ptr instead of Int
new :: rforall a. ST <a >a >Ptr
new = undefined

-- | Read a `Int`
read :: hg:(Map <Ptr >Int) ~> p:Ptr -> ST <{h:Map <Ptr >Int | h == hg} >{h:Map <Ptr >Int | h == hg} >{v:Int| v == select hg p}
read = undefined

-- | Write a `Int`
write :: h:(Map <Ptr >Int) ~> p:Ptr -> v:Int -> ST <{hg:Map <Ptr >Int | h == hg} >{hg:Map <Ptr >Int | store h p v == hg} >Unit
write = undefined

-----------------------------------------------------------------------------
increment :: h:(Map <Ptr >Int) ~> r:Ptr -> ST <{v:Map <Ptr >Int | v == h} >{v:Map <Ptr >Int| store h r ((select h r)+1) == v} >Unit
increment = \r -> bind (read r) (\n -> write r (n+1))

