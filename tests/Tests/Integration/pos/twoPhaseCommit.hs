-- tick and tock with session types in Mist

-- Message -> State -> State
measure updateRecv :: Int -> Int -> Int
measure updateSend :: Int -> Int -> Int

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Unit
assert = \tru -> Unit

fail :: forall s,t,p,q. Int -> ST <s >t <p >q >Int
fail = undefined

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
preparePhase :: {v : Int | v == 1}
preparePhase = 1
commitPhase :: {v : Int | v == 2}
commitPhase = 2
prepareDone :: {v:Int | v == 4}
prepareDone = 4
initial :: {v : Int | v == 3}
initial = 3

prepare :: Int
prepare = 0
prepared :: Int
prepared = 1
commit :: Int
commit = 2
done :: Int
done = 3

-- really this should be a reflected function / map, but we don't implement
-- those yet
statemachine as {v: Int |
                          (updateRecv prepare initial = preparePhase)
                      /\  (updateSend prepared preparePhase = prepareDone)
                      /\  (updateRecv commit prepareDone = commitPhase)
                      /\  (updateSend done commitPhase = initial)
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

send as rforall p,q,a,s,t,u.
  m : (Map <Int >Int) ~>
  channel : Int ->
  message : {v : Int | (updateSend v (select m channel) /= error)} ->
  -- should be a fresh channel, not just a different channel.
  -- technically this is a conservative approximation, so we're fine
    ( newchan : {v : Int  | v /= channel } ~>
      (ST <t >u
       <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v == store (store m newchan (updateSend message (select m channel))) channel error}
       >{v:Int | v == newchan}) ->
    ST <t >s <p >q >a)
   -> ST <t >s <p >q >a
send = undefined

recv as rforall p,q,a,s,t,u.
  m : (Map <Int >Int) ~>
  channel : Int ->
    ( newchan : {v : Int  | v /= channel } ~>
      message : Int ->
      (ST <t >u
       <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v == store (store m newchan (updateRecv message (select m channel))) channel error}
       >{v:Int | v == newchan}) ->
    ST <t >s <p >q >a)
   -> ST <t >s <p >q >a
recv = undefined

-----------------------------------------------------------------------------
-- | The Client
main ::
  empty:(Map <Int >Int) ~>
  ST <{v:Int| v == 0} >Int <{v:Map <Int >Int| v == empty} >(Map <Int >Int) >Int
main = bind chan (\c ->
       recv c (\msg c ->
              if msg == prepare then
                 bind c (\c ->
                 send c prepared (\c ->
                 bind c (\c ->
                 recv c (\msg c ->
                        if msg == commit then
                           bind c (\c ->
                           send c done (\c -> c))
                        else fail 1))))
              else fail 0))


