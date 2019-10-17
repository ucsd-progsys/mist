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
new :: rforall a. ST <a >a >Int
new = undefined

read :: hg:(Map <Int >Int) ~> p:Int -> ST <{h:Map <Int >Int | h == hg} >{h:Map <Int >Int | h == hg} >{v:Int| v == select hg p}
read = undefined

write :: h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
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

withChannel :: rforall p, q, a.
  init:(Map <Int >Int) ~>
    (channel:Int ~>
    (ST <{v:Map <Int >Int | v == init}
        >{v:Map <Int >Int | v == store init channel channelStart}
        >{v:Int | v == channel}) ->
     ST <p >q >a) ->
  ST <p >q >a
withChannel = \f -> (bind new (\v -> f (thenn (write v channelStart) (pure v))))

-----------------------------------------------------------------------------
-- | Typed Session Wrappers
-----------------------------------------------------------------------------
tick :: rforall p,q,a.
  m : (Map <Int >Int) ~>
  channel : {v: Int | select m v == tocked} ->
    ((ST <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v = store m channel ticked}
       >{v:Int | v = channel}) ->
    ST <p >q >a)
   -> ST <p >q >a
tick = \ c f -> f (thenn (write c tocked) (pure c))

tock :: rforall p,q,a.
  m : (Map <Int >Int) ~>
  channel : {v: Int | select m v == ticked} ->
    ((ST <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v = store m channel tocked}
       >{v:Int | v = channel}) ->
    ST <p >q >a)
   -> ST <p >q >a
tock = \ c f -> f (thenn (write c ticked) (pure c))

-----------------------------------------------------------------------------
-- pos
main :: empty:(Map <Int >Int) ~> ST <{v:Map <Int >Int| v == empty} >(Map <Int >Int) >Int
main = withChannel (\c -> bind c (\c -> tick c (\c -> bind c (\c -> tock c (\c -> c)))))
-- neg
-- main = withChannel (\c -> bind c (\c -> tick c (\c -> bind c (\c -> tock c (\c -> c)))))


