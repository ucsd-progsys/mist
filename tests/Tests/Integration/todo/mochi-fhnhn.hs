assert :: {v:Bool | v = True} -> Int
assert = \f -> 0

f :: n:Int ~> (Int -> {v:Int | v = n} ) -> (Int -> {v:Int | v = n} ) -> Int
f = \x y -> assert (x 0 = y 0)

h :: n:Int -> Int -> {v:Int| v == n}
h = \x u -> x

main :: Int -> Int
main = \n -> f (h n) (h n)
