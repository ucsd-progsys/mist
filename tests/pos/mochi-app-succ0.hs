bool :: Bool
bool = True

succ :: rforall a. n:Int ~> ({v:Int | v = n + 1} -> a) -> {v:Int | v = n} -> a
succ = \f x -> f (x + 1)

app :: rforall a. m:Int ~> ({v:Int | v = m} -> a) -> {v:Int | v = m} -> a
app = \f x -> if bool then app (succ f) (x - 1) else f x

check :: x:Int -> y:{v:Int | v == x} -> Int
check = \x y -> 0

main :: Int -> Int
main = \n ->
    app (check 0) 0
