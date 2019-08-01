set as h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
set = undefined


-----------------------------------------------------------------------------
-- this works
setprime :: h:(Map <Int >Int) ~> p:Int -> v:Int -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
setprime = \p -> \n -> set p n

--- but this doesn't
setprime :: forall a. h:(Map <Int >Int) ~> p:Int -> v:Int -> (z:a -> a) -> ST <{hg:Map <Int >Int | h == hg} >{hg:Map <Int >Int | store h p v == hg} >Unit
setprime = \p -> \n -> \f -> set p n
