check :: x:Int -> y:{v:Int | x <= v} -> Int
check = \x y -> 0

bool :: Bool
bool = True

app :: i:Int ~> (x:{v: Int | i <= v} -> Int) -> {v:Int | i <= v} -> Int
app = \f x -> if bool then app f (x + 1) else f x

main :: Int -> Int
main = \ i -> app (check i) i
