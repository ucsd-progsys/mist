-- tick and tock with session types in Mist

-- Message -> State -> State
measure update :: Int -> Int -> Int

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Int
assert = \tru -> 0

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

-- blocking
par :: rforall p, q, r, s, t, u, a, b.
  ST <s >t <p >q >a ->
  ST <t >u <p >q >b ->
  ST <s >u <p >q >(Pair >a >b)
par = undefined

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
stale :: {v : Int | v == 4}
stale = 4

tick :: Int
tick = 0
tock :: Int
tock = 1

-- really this should be a reflected function / map, but we don't implement
-- those yet
statemachine as {v: Int |
                          (update tick initial = ticked)
                      /\  (update tock initial = error)
                      /\  (update tick tocked = ticked)
                      /\  (update tock ticked = tocked)
                      /\  (update tock tocked = error)
                      /\  (update tick ticked = error)
                }
statemachine = 0

-----------------------------------------------------------------------------
-- | API for Channels, and sending things
-----------------------------------------------------------------------------
chan :: rforall a.
  n:Int ~>
  m : (Map <Int >Int) ~>
  ST <{v:Int | v == n}
     >{v:Int | v == n+1}
     <{v:Map <Int >Int | v == m}
     >{v:Map <Int >Int | v == store m n initial}
     >{v:Int | v == n}
chan = undefined

fail :: rforall a, r, s.
  m : (Map <Int >Int) ~>
  c : Int ->
  ST <r
     >s
     <{v:Map <Int >Int | v == m}
     >{v:Map <Int >Int | v == store m c error}
     >{v:Int | v == c}
fail = undefined

send as rforall p,q,a,s,t,u.
  m : (Map <Int >Int) ~>
  channel : Int ->
  message : {v : Int | (update v (select m channel) /= error)} ->
  -- should be a fresh channel, not just a different channel.
  -- technically this is a conservative approximation, so we're fine
    ( newchan : {v : Int  | v /= channel } ~>
      (ST <t >u
       <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v == store (store m newchan (update message (select m channel))) channel stale}
       >{v:Int | v == newchan}) ->
    ST <t >s <p >q >a)
   -> ST <t >s <p >q >a
send = undefined

recv as rforall p,q,a,s,t,u.
  m : (Map <Int >Int) ~>
  channel : Int ->
    ( newchan : {v : Int  | v /= channel } ~>
      message : { v: Int  | (update v (select m channel) /= error) 
                          -- again, poor man's enums
                          /\( (v == tock) \/ (v == tick) )}->
      (ST <t >u
       <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v == store (store m newchan (update message (select m channel))) channel stale}
       >{v:Int | v == newchan}) ->
    ST <t >s <p >q >a)
   -> ST <t >s <p >q >a
recv = undefined

-----------------------------------------------------------------------------
-- | The Clients

ticker ::
  start:(Map <Int >Int) ~>
  ch : {v : Int | select start v == initial } ->
  ST <Int >Int <{v:Map <Int >Int| v == start} >(Map <Int >Int) >Int
ticker = (\c ->
         send c tick (\c ->
         bind c (\c ->
         recv c (\msg c ->
                if msg == tock then c else pure (assert False)))))
tocker ::
  start:(Map <Int >Int) ~>
  ch : {v : Int | select start v == initial } ->
  ST <Int >Int <{v:Map <Int >Int| v == start} >(Map <Int >Int) >Int
tocker = (\c ->
         recv c (\msg c ->
                if msg == tick then
         bind c (\c ->
         send c tock (\c -> c))
         -- proves that this state is unreachable as long as all
         -- connections to the channel obey the state machine
                else pure (assert False)))

-- proves that these are consistent with a shared channel, but not that
-- they fully determine it
main :: m:(Map <Int >Int) ~> ST <{v:Int | v == 0} >Int <{v: Map <Int >Int | v == m} >(Map <Int >Int) >(Pair >Int >Int)
main = bind chan (\c -> par (ticker c) (tocker c))
