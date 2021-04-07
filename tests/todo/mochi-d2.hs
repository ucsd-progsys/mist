assume as b:Bool -> {v:Int | b == True}
assume = 0

assert as {b:Bool | b == True} -> Int
assert = 0

bool as Bool
bool = 0

app :: n:Int ~> (x:{u:Int | n <= u} -> Int) -> {u:Int | n <= u} -> Int
app = \f x -> if bool then app f (x + 1) else f x

check :: x:Int -> {u:Int | x <= u} -> Int
check = \x y -> if x <= y then 1 else assert False

main :: Int -> Int
main = \i -> app (check i) i
