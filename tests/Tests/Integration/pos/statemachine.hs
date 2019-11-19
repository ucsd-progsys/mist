-- tick and tock with session types in Mist

-- Message -> State -> State
measure update :: Int -> Int -> Int

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Unit
assert = \tru -> Unit

-----------------------------------------------------------------------------
-- | The ST Monad -----------------------------------------------------------
-----------------------------------------------------------------------------
bind :: rforall a, b, p, q, r, s, t, u.
  ST <s >t <p >q >a ->
  (x:a -> ST <t >u <q >r >b) ->
  ST <s >u <p >r >b
bind = undefined

pure :: rforall a, p, q, s, t. x:a -> ST <s >t <p >q >a
pure = undefined

thenn :: rforall a, b, p, q, r, s, t, u.
  n:Int ~> m:Int ~>
  ST <s >t <p >q >a ->
  ST <t >u <q >r >b ->
  ST <s >u <p >r >b
thenn = \f g -> bind f (\underscore -> g)

fmap :: rforall a, b, p, q, s, t.
  n:Int ~>
  (underscore:a -> b) ->
  ST <s >t <p >q >a ->
  ST <s >t <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))

-----------------------------------------------------------------------------
-- | State Space --- This is where we write the spec
-----------------------------------------------------------------------------
-- poor man's enums
error :: {v : Int | v == 0}
error = 0
ticked :: {v : Int | v == 1}
ticked = 1
tocked :: {v : Int | v == 2}
tocked = 2
initial :: {v : Int | v == 3}
initial = 3

tick :: Int
tick = 0
tock :: Int
tock = 1

-- really this should be a reflected function / map, but we don't implement
-- those yet
statemachine as {v: Int |
                          (update tick initial = ticked)
                      /\  (update tock initial = tocked)
                      /\  (update tick tocked = ticked)
                      /\  (update tock ticked = tocked)
                }
statemachine = 0

-----------------------------------------------------------------------------
-- | API for Channels, and sending things
-----------------------------------------------------------------------------
chan ::
  n:Int ~>
  m : (Map <Int >Int) ~>
  ST <{v:Int | v == n}
     >{v:Int | v == n+1}
     <{v:Map <Int >Int | v == m}
     >{v:Map <Int >Int | v == store m n initial}
     >{v:Int | v == n}
chan = undefined

send as
  m : (Map <Int >Int) ~>
  n: Int ~>
  channel : Int ->
  message : {v : Int | (update v (select m channel) /= error)} ->
  -- should be a fresh channel, not just a different channel.
  -- technically this is a conservative approximation, so we're fine
  (exists newchan:{v: Int | v /= channel}.
    ST <{v:Int | v = n} >{v:Int | v = n}
       <{v:Map <Int >Int | v = m}
       >{v:Map <Int >Int | v = store (store m newchan (update message (select m channel))) channel error}
       >{v:Int | v == newchan})
send = undefined

-----------------------------------------------------------------------------
-- | The Client
main ::
  empty:(Map <Int >Int) ~>
  ST <{v:Int| v == 0} >Int <{v:Map <Int >Int| v == empty} >(Map <Int >Int) >Int
main = bind chan (\c -> send c tick)
       -- unpack (gc1, mc1) = send c tick in
       -- bind mc1 (\c ->
       -- unpack (gc2, mc2) = send c tock in
       -- mc2))


