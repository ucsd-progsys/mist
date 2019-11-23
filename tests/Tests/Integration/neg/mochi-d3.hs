assume as b:Bool -> {v:Int | b == True}
assume = 0

assert as {b:Bool | b == True} -> Int
assert = 0

bool as Bool
bool = 0

succ :: b:Int ~> ({u:Int | b <= u} -> Int) -> {u:Int | b <= u} -> Int
succ = \f x -> f (x + 1)

app3 :: a:Int ~> ({u:Int | a <= u} -> Int) -> b:Int ~> (c:Int ~> ({u:Int | a <= u} -> Int) -> Int) -> Int
app3 = \f g -> if bool then app3 (succ f) g else g f

app :: x:Int -> a:Int ~> ({u:Int | x <= u} -> Int) -> Int
app = \x f -> f x

check :: x:Int -> {u:Int | x <= u} -> Int
check = \x y -> if x <= y then 1 else assert False

main :: Int -> Int
main = \i -> app3 (check i) (app i)
