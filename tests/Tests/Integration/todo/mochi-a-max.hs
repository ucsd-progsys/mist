undefined as rforall a. a
undefined = 0

assert as {safe:Bool | safe == True} -> Int
assert = 0

randArray as x:Int -> i:Int -> {v:Int | v <= x}
randArray = undefined

-- #########################################################################
-- THIS RUNS FOR A VERY LONG TIME AND WON'T SUCCEED
-- #########################################################################
-- arrayMax :: max:Int ~> i:Int -> n:Int -> ar:(Int -> {v:Int | v <= max}) -> m:{v:Int | v <= max} -> {v:Int | v <= max}
-- arrayMax = \i n ar m ->
--   if n <= i then
--     m
--   else
--     let x = ar i in
--     let z = if x > m then x else m in
--       arrayMax (i + 1) n ar z

-- main :: n:Int -> x:Int -> Int
-- main = \n x ->
--   if (n > 0) /\ (0 <= x) then
--     let m = arrayMax 0 n (randArray x) (0 - 1) in
--       assert (m <= x)
--   else
--     1
