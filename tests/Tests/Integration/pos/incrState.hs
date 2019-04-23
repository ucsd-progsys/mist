-- Monadic Interface
ret as forall a. w:Int ~> x:a -> ST <{v:Int|v==w} >{v:Int|v==w} >a
ret = (0)
bind as forall s, a, b. w1:Int ~> w2:Int ~> w3:Int ~> (ST <{v:Int|v==w1} >{v:Int|v==w2} >a)
  -> (unused:a -> ST <{v:Int|v==w2} >{v:Int|v==w3} >b)
  -> ST <{v:Int|v==w1} >{v:Int|v==w3} >b
bind = (0)
get as w:Int ~> Int -> ST <{v:Int|v==w} >{v:Int|v==w} >{v:Int|v==w}
get = (0)
put as w:Int -> ST <Int >{v:Int|v==w} >Unit
put  = (0)

-- incr
incr :: ST <Int >Int >Unit
incr = (bind (get 0) (\n -> (put (n+1))))
