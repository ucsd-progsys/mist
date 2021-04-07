sum :: n:Int ~> m:Int ~> (Int -> { v : Int | v == n }) -> (Int -> { v : Int | v == m }) -> { v : Int | v == n + m }
sum = (\ f g -> (f 0) + (g 0))

test1 :: { v : Int | v == 11 }
test1 = sum (\ x -> 10) (\y -> 1)
