-- tick and tock with session types in Mist

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Unit
assert = \tru -> Unit

-----------------------------------------------------------------------------
-- | The ST Monad -----------------------------------------------------------
-----------------------------------------------------------------------------
bind :: rforall a, b, p, q, r.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

pure :: rforall a, p, q. x:a -> ST <p >q >a
pure = undefined

thenn :: rforall a, b, p, q, r.
  ST <p >q >a
  -> ST <q >r >b
  -> ST <p >r >b
thenn = \f g -> bind f (\underscore -> g)

fmap :: rforall a, b, p, q.
  (underscore:a -> b) ->
  ST <p >q >a ->
  ST <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))

-----------------------------------------------------------------------------
-- | Primitive Connection Interface
-----------------------------------------------------------------------------
new as forall a. init:(Map <Int >Int) ~>
  underscore:Int ->
  (exists channel:Int.
    ST <{v:Map <Int >Int | v = init}
       >{v:Map <Int >Int | v = init}
       >{v:Int | v = channel})
new = undefined

read as hg:(Map <Int >Int) ~> p:Int -> ST <{h:Map <Int >Int | h == hg} >{h:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
read = undefined

write as h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
write = undefined

-----------------------------------------------------------------------------
-- | State Space
-----------------------------------------------------------------------------
ticked as Int
ticked = 0
tocked as Int
tocked = 0

-----------------------------------------------------------------------------
-- | Sessions
-----------------------------------------------------------------------------
channelStart :: {v:Int| v == tocked}
channelStart = tocked

startChannel :: init:(Map <Int >Int) ~>
  underscore:Int ->
  (exists channel:Int.
    ST <{v:Map <Int >Int | v == init}
       >{v:Map <Int >Int | v == store init channel channelStart}
       >{v:Int | v == channel})
startChannel = \underscore ->
  bind (new 0) (\v -> (thenn (write v channelStart) (pure v)))

-----------------------------------------------------------------------------
-- | Typed Session Wrappers
-----------------------------------------------------------------------------
tick ::
  m : (Map <Int >Int) ~>
  channel : {v: Int | select m v == tocked} ->
    (ST <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v = store m channel ticked}
       >{v:Int | v = channel})
tick = \c -> thenn (write c tocked) (pure c)

tock ::
  m : (Map <Int >Int) ~>
  channel : {v: Int | select m v == ticked} ->
    (ST <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v = store m channel tocked}
       >{v:Int | v = channel})
tock = \c -> thenn (write c ticked) (pure c)

-----------------------------------------------------------------------------
-- pos
main :: empty:(Map <Int >Int) ~> ST <{v:Map <Int >Int| v == empty} >(Map <Int >Int) >Int
main = bind (startChannel 0) (\c ->
       bind (tick c) (\c ->
       tock c))
-- neg
-- main = withChannel (\c -> bind c (\c -> tick c (\c -> bind c (\c -> tock c (\c -> c)))))


