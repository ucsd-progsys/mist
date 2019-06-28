-- Monadic Interface
ret as forall s, a. w:s ~> x:a -> ST <{v:s|v==w} >{v:s|v==w} >a
ret = (0)

bind as forall s, a, b. w1:s ~> w2:s ~> w3:s ~> (ST <{v:s|v==w1} >{v:s|v==w2} >a)
  -> (unused:a -> ST <{v:s|v==w2} >{v:s|v==w3} >b)
  -> ST <{v:s|v==w1} >{v:s|v==w3} >b
bind = (0)

thenn as forall s, a, b. w1:s ~> w2:s ~> w3:s ~> (ST <{v:s|v==w1} >{v:s|v==w2} >a)
  -> (ST <{v:s|v==w2} >{v:s|v==w3} >b)
  -> ST <{v:s|v==w1} >{v:s|v==w3} >b
thenn = (0)

get as forall s. w:s ~> Bool -> ST <{v:s|v==w} >{v:s|v==w} >{v:s|v==w}
get = (0)

put as forall s. w:s -> ST <s >{v:s|v==w} >Unit
put = (0)

-- incr
-- incr :: ST <Int >Int >Unit
-- incr = (bind (get True) (\n -> (put (n+1))))

incr2 :: ST <{i:Int|i==2} >{w:Int|w==2} >Int
incr2 = thenn (get True) (get True)
