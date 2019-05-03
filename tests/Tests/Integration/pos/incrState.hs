-- Monadic Interface
ret as forall a. wr:Int ~> x:a -> ST <{ri:Int|ri==wr} >{ro:Int|ro==wr} >a
ret = 0

thenn as w1:Int ~> w2:Int ~> w3:Int ~> (ST <{v:Int|v==w1} >{v:Int|v==w2} >Int)
  -> (ST <{v:Int|v==w2} >{v:Int|v==w3} >Int)
  -> ST <{v:Int|v==w1} >{v:Int|v==w3} >Int
thenn = 0

bind as forall s, a, b. w1:Int ~> w2:Int ~> w3:Int ~> (ST <{v:Int|v==w1} >{v:Int|v==w2} >a)
  -> (unused:a -> ST <{v:Int|v==w2} >{v:Int|v==w3} >b)
  -> ST <{v:Int|v==w1} >{v:Int|v==w3} >b
bind = 0

get as wg:Int ~> Bool -> ST <{gi:Int|gi==wg} >{go:Int|go==wg} >{gr:Int|gr==wg}
get = True

get2 as wg2:Int ~> Bool -> ST <{gi:Int|gi==wg2} >{go:Int|go==wg2} >{gr:Int|gr==wg2}
get2 = True

put as wp:Int -> ST <Int >{p:Int|p==wp} >Unit
put = 0

-- incr
incr :: ST <{i:Int|i==2} >{w:Int|w==2} >Int
incr = thenn (get True) (get2 True)
