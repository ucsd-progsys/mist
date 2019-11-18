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

thenn as rforall a, b. forall p.
  w1:p ~> w2:p ~> w3:p ~>
  ST <{v:p | v = w1} >{v:p | v = w2} >a ->
  ST <{v:p | v = w2} >{v:p | v = w3} >b ->
  ST <{v:p | v = w1} >{v:p | v = w3} >b
-- thenn :: rforall a, b, p, q, r, s, t, u.
--   ST <p >q >a ->
--   ST <q >r >b ->
--   ST <p >r >b
thenn = \f g -> bind f (\underscore -> g)

fmap :: rforall a, b, p, q, s, t.
  (underscore:a -> b) ->
  ST <p >q >a ->
  ST <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))


for2 :: (n:Int ~>
          under:Int ->
          (exists n2:{v: Int | v > n}.
            (ST <{v: Int | v = n} >{v: Int | v = n2} >Int)))
     -> (m:Int ~>
          score:Int ->
          (exists m2:{v: Int | v > m}.
            (ST <{v: Int | v = m} >{v: Int | v = m2} >Int)))
for2 = \f -> \score -> thenn (f 1) (f 2)
  -- unpack (s1, ms1) = f 1 in
  -- unpack (s2, ms2) = f 2 in
  -- (thenn ms1 ms2)

get as forall s. wg:s ~> Int -> ST <{v:s|v==wg} >{v:s|v==wg} >{v:s|v==wg}
get = undefined

-- I don't think the commented out line is a correct spec for put
-- put as forall s. wp:s -> ST <s >{v:s|v==wp} >Int
put as forall s. wg:s ~> wp:s -> ST <{v:s | v == wg} >{v:s|v==wp} >Int
put = undefined

foo :: x:Int ~>
       under:Int ->
       (exists x2:{v: Int | v > x}.
         (ST <{v: Int | v = x} >{v: Int | v = x2} >Int))
foo = \under -> bind (get 6) (\y -> put (y + 4))

bar :: x:Int ~>
       under:Int ->
       ST <{v: Int | v = x} >{v: Int | v = x + 1} >Int
bar = \under -> bind (get 8) (\y -> put (y + 1))

main :: x:{v: Int | v > 3} ~> ST <{v: Int | v = x} >{v: Int | v > 3} >Int
-- main = unpack (s1, ms1) = ((for2 foo) 8) in
--        unpack (s2, ms2) = ((for2 bar) 9) in
--        (thenn ms1 ms2)
main = thenn ((for2 foo) 8) ((for2 foo) 9)

-- for2 :: rforall a, b.
--   ((rforall c, d.
--      s:(Set >Int) ~>
--      (s2:{v: Set >Int | setSubset s v} ~> (ST <{v: Set >Int | v = s} >{v: Set >Int | v = s2} >Int) -> ST <c >d >Int)
--      -> ST <c >d >Int)) ->
--   (z:(Set >Int) ~>
--     (z2:{v: Set >Int | setSubset z v} ~> (ST <{v: Set >Int | v = z} >{v: Set >Int | v = z2} >Int) -> ST <a >b >Int)
--     -> ST <a >b >Int)
-- for2 = \f -> \k -> f (\ms1 -> f (\ms2 -> k (thenn ms1 ms2)))

