incr :: n:Int ~> (Int -> { v : Int | v == n }) -> { v : Int | v == n + 1 }
incr = \ f -> (f 0) + 1

test1 :: { v : Int | v == 11 }
test1 = incr (\x -> 10)

test2 :: m:Int -> { v : Int | v == m+1 }
test2 = \mv -> incr (\x -> mv)
