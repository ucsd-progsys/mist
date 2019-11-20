check :: x:Int -> y:{v:Int | v == x} -> Int
check = \x y -> 0

bool :: Bool
bool = True

succ :: rforall a. Int -> (exists n:Int . ({v:Int | v == n + 1} -> a) -> {v:Int | v == n } -> a)
succ = \ f x -> f (x + 1)

app :: n:Int ~> (Int -> {v:Int | v == n}) -> {v:Int | v == n} -> Int
app = \ f x -> if bool then app (succ f) (x - 1) else f x

main :: Int -> Int
main = \n ->
    app (check n) n
