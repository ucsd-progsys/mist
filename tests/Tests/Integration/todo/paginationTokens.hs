done as Int
done = 0

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

undefined as rforall a. a
undefined = 0

----------------------------------------------------------------------------
-- | The Token API ----------------------------------------------------------
----------------------------------------------------------------------------
-- nextPage :: m:{Map <Int >Int} ~> t:{v:Int | select m v = good /\ v ≠ done} -> Σt':Int. ST <{m} >{v = store (store m t stale) t' good} >{v = t'}
nextPage as rforall p, q, a.
  m:(Map <Int >Int) ~>
  token:{v: Int | select m v == good /\ v ≠ done} ->
    (tok:Int ~>
     (ST <{v:Map <Int >Int | v == m}
         >{v:Map <Int >Int | v == store (store m token stale) tok good}
         >{v:Int | v = tok}) ->
      ST <p >q >a)
  -> ST <p >q >a
nextPage = undefined

-- start :: m:{Map <Int >Int} ~> _:Int -> (Σstart:Int. ST <{m} >{v = store m start good} >{v = start})
start :: rforall p, q, a.
  m:(Map <Int >Int) ~>
    (tStart: Int ~>
     (ST <{v:Map <Int >Int | v == m}
         >{v:Map <Int >Int | v == store m tStart good}
         >{v:Int | v == tStart})
      -> ST <p >q >a)
  -> ST <p >q >a
start = undefined

main :: m:(Map <Int >Int) ~> ST <{v: Map <Int >Int | v = m} >{v: Map <Int >Int | v = store m done good}
main = undefined

-- main = withPages
  -- (bind start
  --   (\tStart -> bind (next tStart))
  --     (\t1 -> pure t1))
  -- (bind (ne)
  --   (\tStart -> pure tStart))

----------------------------------------------------------------------------
-- loop :: m ~> m' <~ c -> ST <{v:Map <Int >Int| v = m /\ select v c /= error} >{v:Map <Int >Int| v=m'} >Unit
client :: empty:(Map <Int >Int) ~> ST <{v:Map <Int >Int| v == store empty done done} >(Map <Int >Int) >Int
client = newtoken (\c ->
         bind c (\c ->
         -- why is this m not being solved? well, m from newtoken isn't in
         -- scope. why is that? because ANF. damn.
         nextPage c (\c ->
         bind c (\c -> if c == done then pure c else
         -- m here not being solved because it's being stated in terms of
         -- ans which is not in scope yet!
         nextPage c (\c -> c)))))
