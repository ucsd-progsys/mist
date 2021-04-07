-- Monadic Interface
ret as rforall a. forall s. w:s ~> x:a -> ST <{v:s|v==w} >{v:s|v==w} >a
ret = (0)

bind as rforall a, b. forall s. w1:s ~> w2:s ~> w3:s ~> (ST <{v:s|v==w1} >{v:s|v==w2} >a)
  -> (unused:a -> ST <{v:s|v==w2} >{v:s|v==w3} >b)
  -> ST <{v:s|v==w1} >{v:s|v==w3} >b
bind = (0)

thenn as rforall a, b. forall s. ww1:s ~> w2:s ~> w3:s ~> (ST <{v:s|v==ww1} >{v:s|v==w2} >a)
  -> (ST <{v:s|v==w2} >{v:s|v==w3} >b)
  -> ST <{v:s|v==ww1} >{v:s|v==w3} >b
thenn = (0)

get as rforall s. wg:s ~> Bool -> ST <{v:s|v==wg} >{v:s|v==wg} >{v:s|v==wg}
get = (0)

put as forall s. wp:s -> ST <s >{v:s|v==wp} >Unit
put = (0)

-- fresh :: n:Int ~> ST <{w:Int|w==n} >{w:Int|w==n+1} >{v:Int|v==n}
-- fresh = (bind (get True) (\n -> (thenn (put (n+1)) (ret n))))

incr :: ST <{i:Int|i==2} >{w:Int|w==3} >{v: Int | v = 2}
incr = (bind (get True) (\n -> (thenn (put (n+1)) (ret n))))

-- incr2 :: ST <{i:Int|i==2} >{w:Int|w==2} >Int
-- incr2 = thenn (get True) (get True)
