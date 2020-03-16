-- tick and tock with session types in Mist

-- Message -> State -> State
measure updateRecv :: Int -> Int -> Int
measure updateSend :: Int -> Int -> Int

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Unit
assert = \tru -> Unit

unreachable :: forall s,t,p,q. {v:Int | False} -> ST <s >t <p >q >Int
unreachable = undefined

-- unreachable :: forall s,t,p,q. Int -> ST <s >t <p >q >Int
-- unreachable = undefined

----------------------------------------------------------------------------
-- | The ST Monad ----------------------------------------------------------
----------------------------------------------------------------------------
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

----------------------------------------------------------------------------
-- | State Space --- This is where we write the spec
----------------------------------------------------------------------------
-- poor man's enums
open    :: { v : Int | v = 1 }
open    =  1
syn     :: { v : Int | v = 2 }
syn     =  2
ack     :: { v : Int | v = 3 }
ack     =  3
fin     :: { v : Int | v = 4 }
fin     =  4
close   :: { v : Int | v = 5 }
close   =  5
timeout :: { v : Int | v = 6 }
timeout =  6

closed      :: { v : Int | v = 1 }
closed      =  1
listen      :: { v : Int | v = 2 }
listen      =  2
synSent     :: { v : Int | v = 3 }
synSent     =  3
synReceived :: { v : Int | v = 4 }
synReceived =  4
established :: { v : Int | v = 5 }
established =  5
finWaitI    :: { v : Int | v = 6 }
finWaitI    =  6
finWaitII   :: { v : Int | v = 7 }
finWaitII   =  7
closeWait   :: { v : Int | v = 8 }
closeWait   =  8
closing     :: { v : Int | v = 9 }
closing     =  9
lastAck     :: { v : Int | v = 10 }
lastAck     =  10
timeWait    :: { v : Int | v = 11 }
timeWait    =  11
stale       :: { v : Int | v = 12 }
stale       =  12
error       :: { v : Int | v = 13 }
error       =  13

-- in lieu of reft refl, I got sed to generate the full transition relation
-- updateSend open closed = synSent
-- updateSend syn listen = synSent
-- updateSend fin established = finWaitI
-- updateSend _ = id
-- 
-- updateRecv open closed = listen
-- updateRecv syn listen = synReceived
-- updateRecv close synSent = closed
-- updateRecv syn synSent = synReceived
-- updateRecv ack synReceived = established
-- updateRecv close synReceived = finWaitI
-- updateRecv ack finWaitI = finWaitII
-- updateRecv fin finWaitII = timeWait
-- updateRecv timeout timeWait = closed
-- updateRecv fin finWaitI = closing
-- updateRecv ack closing = timeWait
-- updateRecv fin established = closeWait
-- updateRecv close established = finWaitI
-- updateRecv close closeWait = lastAck
-- updateRecv ack lastAck = closeWait
-- updateRecv _ _ = error

statemachine as {v: Int |
       (updateSend open closed = synSent)
    /\ (updateSend syn listen = synSent)
    /\ (updateSend fin established = finWaitI)
    /\ (updateSend open listen = listen)
    /\ (updateSend open synSent = synSent)
    /\ (updateSend open synReceived = synReceived)
    /\ (updateSend open established = established)
    /\ (updateSend open finWaitI = finWaitI)
    /\ (updateSend open finWaitII = finWaitII)
    /\ (updateSend open closeWait = closeWait)
    /\ (updateSend open closing = closing)
    /\ (updateSend open lastAck = lastAck)
    /\ (updateSend open timeWait = timeWait)
    /\ (updateSend syn closed = closed)
    /\ (updateSend syn synSent = synSent)
    /\ (updateSend syn synReceived = synReceived)
    /\ (updateSend syn established = established)
    /\ (updateSend syn finWaitI = finWaitI)
    /\ (updateSend syn finWaitII = finWaitII)
    /\ (updateSend syn closeWait = closeWait)
    /\ (updateSend syn closing = closing)
    /\ (updateSend syn lastAck = lastAck)
    /\ (updateSend syn timeWait = timeWait)
    /\ (updateSend ack closed = closed)
    /\ (updateSend ack listen = listen)
    /\ (updateSend ack synSent = synSent)
    /\ (updateSend ack synReceived = synReceived)
    /\ (updateSend ack established = established)
    /\ (updateSend ack finWaitI = finWaitI)
    /\ (updateSend ack finWaitII = finWaitII)
    /\ (updateSend ack closeWait = closeWait)
    /\ (updateSend ack closing = closing)
    /\ (updateSend ack lastAck = lastAck)
    /\ (updateSend ack timeWait = timeWait)
    /\ (updateSend fin closed = closed)
    /\ (updateSend fin listen = listen)
    /\ (updateSend fin synSent = synSent)
    /\ (updateSend fin synReceived = synReceived)
    /\ (updateSend fin established = established)
    /\ (updateSend fin finWaitI = finWaitI)
    /\ (updateSend fin finWaitII = finWaitII)
    /\ (updateSend fin closeWait = closeWait)
    /\ (updateSend fin closing = closing)
    /\ (updateSend fin lastAck = lastAck)
    /\ (updateSend fin timeWait = timeWait)
    /\ (updateSend close closed = closed)
    /\ (updateSend close listen = listen)
    /\ (updateSend close synSent = synSent)
    /\ (updateSend close synReceived = synReceived)
    /\ (updateSend close established = established)
    /\ (updateSend close finWaitI = finWaitI)
    /\ (updateSend close finWaitII = finWaitII)
    /\ (updateSend close closeWait = closeWait)
    /\ (updateSend close closing = closing)
    /\ (updateSend close lastAck = lastAck)
    /\ (updateSend close timeWait = timeWait)
    /\ (updateSend timeout closed = closed)
    /\ (updateSend timeout listen = listen)
    /\ (updateSend timeout synSent = synSent)
    /\ (updateSend timeout synReceived = synReceived)
    /\ (updateSend timeout established = established)
    /\ (updateSend timeout finWaitI = finWaitI)
    /\ (updateSend timeout finWaitII = finWaitII)
    /\ (updateSend timeout closeWait = closeWait)
    /\ (updateSend timeout closing = closing)
    /\ (updateSend timeout lastAck = lastAck)
    /\ (updateSend timeout timeWait = timeWait)
    /\ (updateRecv open closed = listen)
    /\ (updateRecv syn listen = synReceived)
    /\ (updateRecv close synSent = closed)
    /\ (updateRecv syn synSent = synReceived)
    /\ (updateRecv ack synReceived = established)
    /\ (updateRecv close synReceived = finWaitI)
    /\ (updateRecv ack finWaitI = finWaitII)
    /\ (updateRecv fin finWaitII = timeWait)
    /\ (updateRecv timeout timeWait = closed)
    /\ (updateRecv fin finWaitI = closing)
    /\ (updateRecv ack closing = timeWait)
    /\ (updateRecv fin established = closeWait)
    /\ (updateRecv close established = finWaitI)
    /\ (updateRecv close closeWait = lastAck)
    /\ (updateRecv ack lastAck = closeWait)
    /\ (updateRecv open listen = error)
    /\ (updateRecv open synSent = error)
    /\ (updateRecv open synReceived = error)
    /\ (updateRecv open established = error)
    /\ (updateRecv open finWaitI = error)
    /\ (updateRecv open finWaitII = error)
    /\ (updateRecv open closeWait = error)
    /\ (updateRecv open closing = error)
    /\ (updateRecv open lastAck = error)
    /\ (updateRecv open timeWait = error)
    /\ (updateRecv syn closed = error)
    /\ (updateRecv syn synReceived = error)
    /\ (updateRecv syn established = error)
    /\ (updateRecv syn finWaitI = error)
    /\ (updateRecv syn finWaitII = error)
    /\ (updateRecv syn closeWait = error)
    /\ (updateRecv syn closing = error)
    /\ (updateRecv syn lastAck = error)
    /\ (updateRecv syn timeWait = error)
    /\ (updateRecv ack closed = error)
    /\ (updateRecv ack listen = error)
    /\ (updateRecv ack synSent = error)
    /\ (updateRecv ack established = error)
    /\ (updateRecv ack finWaitII = error)
    /\ (updateRecv ack closeWait = error)
    /\ (updateRecv ack timeWait = error)
    /\ (updateRecv fin closed = error)
    /\ (updateRecv fin listen = error)
    /\ (updateRecv fin synSent = error)
    /\ (updateRecv fin synReceived = error)
    /\ (updateRecv fin closeWait = error)
    /\ (updateRecv fin closing = error)
    /\ (updateRecv fin lastAck = error)
    /\ (updateRecv fin timeWait = error)
    /\ (updateRecv close closed = error)
    /\ (updateRecv close listen = error)
    /\ (updateRecv close finWaitI = error)
    /\ (updateRecv close finWaitII = error)
    /\ (updateRecv close closing = error)
    /\ (updateRecv close lastAck = error)
    /\ (updateRecv close timeWait = error)
    /\ (updateRecv timeout closed = error)
    /\ (updateRecv timeout listen = error)
    /\ (updateRecv timeout synSent = error)
    /\ (updateRecv timeout synReceived = error)
    /\ (updateRecv timeout established = error)
    /\ (updateRecv timeout finWaitI = error)
    /\ (updateRecv timeout finWaitII = error)
    /\ (updateRecv timeout closeWait = error)
    /\ (updateRecv timeout closing = error)
    /\ (updateRecv timeout lastAck = error)
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
     >{v:Map <Int >Int | v == store m n closed}
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
       >{v:Map <Int >Int | v == store (store m newchan (updateSend message (select m channel))) channel stale}
       >{v:Int | v == newchan}) ->
    ST <t >s <p >q >a)
   -> ST <t >s <p >q >a
send = undefined

recv as rforall p,q,a,s,t,u.
  m : (Map <Int >Int) ~>
  channel : Int ->
    ( newchan : {v : Int  | v /= channel } ~>
      message : { v: Int  | (updateRecv v (select m channel) /= error) 
                          -- again, poor man's enums
                          /\(
 (v == open   )
 \/ (v == syn    )
 \/ (v == ack    )
 \/ (v == fin    )
 \/ (v == close  )
 \/ (v == timeout)
  )}->
      (ST <t >u
       <{v:Map <Int >Int | v == m}
       >{v:Map <Int >Int | v == store (store m newchan (updateRecv message (select m channel))) channel stale}
       >{v:Int | v == newchan}) ->
    ST <t >s <p >q >a)
   -> ST <t >s <p >q >a
recv = undefined

----------------------------------------------------------------------------
-- | TCP client and server
client ::
   empty:(Map <Int >Int) ~>
   ST <{v:Int| v == 0} >Int <{v:Map <Int >Int| v == empty} >(Map <Int >Int) >Int
client = bind chan (\c ->
         send c open (\c ->
         bind c (\c ->
         send c syn (\c ->
         bind c (\c ->
         recv c (\msg c ->
                if msg == syn
                  then bind c (\c ->
                       recv c (\msg c ->
                       if msg == ack
                         then bind c (\c ->
                              send c ack (\c ->
                              bind c (\c ->
                              send c fin (\c ->
                              bind c (\c ->
                              recv c (\msg c ->
                                if msg == ack
                                  then bind c (\c ->
                                       recv c (\msg c ->
                                         if msg == close
                                           then bind c (\c ->
                                                send c fin (\c ->
                                                bind c (\c ->
                                                recv c (\msg c ->
                                                  if msg == timeout then c else unreachable 4))))
                                           else unreachable 2))
                                   else unreachable 5))))))
                         else unreachable 1))
                  else if msg == close then pure 0 else unreachable 0))))))
