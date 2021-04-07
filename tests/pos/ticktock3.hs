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
bind as rforall a, b, p, q, r.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

pure :: rforall a, p, q. x:a -> ST <p >q >a
pure = undefined

thenn as rforall a, b, p, q, r.
  ST <p >q >a ->
  ST <q >r >b ->
  ST <p >r >b
thenn = \f g -> bind f (\underscore -> g)

-- blocking
par :: rforall p, q, r, a, b.
  ST <p >q >a ->
  ST <p >q >b ->
  ST <p >q >(Pair >a >b)
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

tick :: Int
tick = 0
tock :: Int
tock = 1

-- really this should be a reflected function / map, but we don't implement
-- those yet
statemachine as {v: Int |
                          (update tick tocked = ticked)
                      /\  (update tock ticked = tocked)
                      /\  (update tock tocked = error)
                      /\  (update tick ticked = error)
                }
statemachine = 0

-----------------------------------------------------------------------------
-- | API for Channels, and sending things
-----------------------------------------------------------------------------
chan as rforall p, q. ST <p >q >Int
chan = undefined

send as
  gs : Int ~>
  channel : Int ->
  message : {v : Int | (update v gs) /= error} ->
  (exists gs2:{v:Int | v = update message gs}.
    ST <{v: Int | v = gs}
       >{v: Int | v = gs2}
       >Int)
send = undefined

recv as
  gs : Int ~>
  channel : Int ->
  (exists message:{v: Int | (update v gs /= error) /\ ((v = tock) \/ (v = tick))}.
    ST <{v: Int | v = gs}
       >{v: Int | v = (update message gs)}
       >{v: Int | v = message})
recv = undefined

-----------------------------------------------------------------------------
-- | The Clients

ticker ::
  gs:{v:Int | v = tocked} ~>
  c:Int ->
  ST <{v:Int| v == gs} >Int >Int
ticker = \c ->
  thenn (send c tick)
        (bind (recv c) (\msg -> if msg == tock then pure 0 else pure (assert False)))

tocker ::
  gs:{v:Int | v = tocked} ~>
  c:Int ->
  ST <{v:Int| v == gs} >Int >Int
tocker = \c ->
  bind (recv c) (\msg ->
    if msg = tick
    then send c tock
    else pure (assert False))

-- proves that these are consistent with a shared channel, but not that
-- they fully determine it
main :: gs:Int ~> ST <{v: Int | v = gs} >Int >(Pair >Int >Int)
main = bind chan (\c -> par (ticker c) (tocker c))
