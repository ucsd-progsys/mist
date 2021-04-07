set as h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
set = 0


-----------------------------------------------------------------------------
-- this works
setprimeprime :: h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
setprimeprime = \p -> \n -> set p n

--- but this doesn't
setprime :: forall a. h:(Map <Int >Int) ~> p:Int -> v:Int -> (z:a -> a) -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
setprime = \p -> \n -> \f -> set p n
