-- pagination with session types in Mist

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
-- | Sessions
-----------------------------------------------------------------------------
channelStart :: {v:Int| v == 0}
channelStart = 0

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
nextPage :: rforall p,q,a.
  m : (Map <Int >Int) ~>
  n : Int ~>
  channel : {v: Int | select m v == n} ->
    ((ST <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v = store m channel (n+1)}
       >{v:Int | v = channel}) ->
    ST <p >q >a)
   -> ST <p >q >a
nextPage = \ c f -> f (bind (read c) (\n -> thenn (write c (n+1)) (pure c)))

-----------------------------------------------------------------------------
main :: empty:(Map <Int >Int) ~> ST <{v:Map <Int >Int| v == empty} >(Map <Int >Int) >{v:Int | v == 2}
main = withChannel (\c -> bind c (\c -> nextPage c (\c -> bind c (\c -> nextPage c (\c -> bind c read)))))


