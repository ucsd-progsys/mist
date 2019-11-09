----------------------------------------------------------------------------
-- | The ST Monad ----------------------------------------------------------
----------------------------------------------------------------------------
undefined as rforall a. a
undefined = 0

bind :: rforall a, b, p, q, r, s, t, u.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

pure :: rforall a, p, q, s, t. x:a -> ST <p >q >a
pure = undefined

thenn :: rforall a, b, p, q, r, s, t, u.
  n:Int ~> m:Int ~>
  ST <p >q >a ->
  ST <q >r >b ->
  ST <p >r >b
thenn = \f g -> bind f (\underscore -> g)

fmap :: rforall a, b, p, q, s, t.
  n:Int ~>
  (underscore:a -> b) ->
  ST <p >q >a ->
  ST <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))

-- for2 :: (s ~> Σs':{v ⊇ s}. ST {v = s} {v = s'})
--      -> (z ~> Σz':{v ⊇ z}. ST {v = z} {v = z'})
for2 :: rforall a, b.
  ((rforall c, d.
     s:(Set >Int) ~>
     (s2:{v: Set >Int | setSubset s v} ~> (ST <{v: Set >Int | v = s} >{v: Set >Int | v = s2} >Int) -> ST <c >d >Int)
     -> ST <c >d >Int)) ->
    (z:(Set >Int) ~>
      (z2:{v: Set >Int | setSubset z v} ~> (ST <{v: Set >Int | v = z} >{v: Set >Int | v = z2} >Int) -> ST <a >b >Int)
      -> ST <a >b >Int)
for2 = \f -> \k -> f (\s1 -> f (\s2 -> k (thenn s1 s2)))
