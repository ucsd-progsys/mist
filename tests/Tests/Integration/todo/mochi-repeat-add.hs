assert :: {v:Bool | v == True} -> Bool
assert = \x -> True

add :: x:Int -> y:Int -> {v:Int | v = x + y}
add = \ x1 x2 -> x1 + x2

repeat :: n:Int ~> (m:Int -> {v:Int| n = v - m}) -> k:{v:Int | 0 <= v} -> {v:Int | v == 0} -> {v:Int | v = k * n}
repeat = \f k x -> if k <= 0 then x else f (repeat f (k - 1) x)

-- main :: Int -> Int -> Bool
-- main = \ n k ->
--   if (0 <= n) /\ (k > 0) then assert (n <= repeat (add n) k 0) else True
