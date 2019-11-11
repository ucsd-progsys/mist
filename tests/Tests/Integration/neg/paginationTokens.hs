undefined as rforall a. a
undefined = 0

done as Int
done = undefined

empty as Map <Int >Int
empty = undefined

----------------------------------------------------------------------------
-- | State Space
----------------------------------------------------------------------------

-- States
stale       :: { v : Int | v = 2 }
stale       =  2
good        :: { v : Int | v = 3 }
good        =  3

----------------------------------------------------------------------------
-- | The ST Monad ----------------------------------------------------------
----------------------------------------------------------------------------
bind :: rforall a, b, p, q, r, s, t, u.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

pure :: rforall a, p, q, s, t. x:a -> ST <p >q >a
pure = undefined

thenn :: rforall a, b, p, q, r, s, t, u.
  ST <p >q >a ->
  ST <q >r >b ->
  ST <p >r >b
thenn = \f g -> bind f (\underscore -> g)

fmap :: rforall a, b, p, q, s, t.
  (underscore:a -> b) ->
  ST <p >q >a ->
  ST <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))

----------------------------------------------------------------------------
-- | The Token API ----------------------------------------------------------
----------------------------------------------------------------------------
-- nextPage :: m:{Map <Int >Int} ~> t:{v:Int | select m v = good /\ v ≠ done} -> Σt':Int. ST <{m} >{v = store (store m t stale) t' good} >{v = t'}
nextPage as
  m:(Map <Int >Int) ~>
  token:{v: Int | (select m v = good) /\ (v ≠ done)} ->
  (exists tok:Int.
    (ST <{v:Map <Int >Int | v = m}
        >{v:Map <Int >Int | v = store (store m token stale) tok good}
        >{v:Int | v = tok}))
nextPage = undefined

-- start :: m:{Map <Int >Int} ~> _:Int -> (Σstart:Int. ST <{m} >{v = store m start good} >{v = start})
start as underscore:Int ->
  (exists tok:Int.
    ST <{v:Map <Int >Int | v = empty}
       >{v:Map <Int >Int | v = store empty tok good}
       >{v:Int | v = tok})
start = undefined

client :: m:(Map <Int >Int) ~> token:{v:Int | select m v = good} ->
  (ST <{v:Map <Int >Int | v = m} >{v:Map <Int >Int | select v done = good} >Int)
client = \token ->
  if token == done
  then pure 1
  else unpack (next, mnext) = nextPage token in
       bind mnext (\tok -> client token) -- reusing a token

main :: ST <{v: Map <Int >Int | v = empty} >{v: Map <Int >Int | select v done = good} >Int
main = unpack (token, mstart) = start 1 in
       bind mstart (\startToken -> client startToken)

