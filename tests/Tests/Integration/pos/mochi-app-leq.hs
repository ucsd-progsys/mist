check as x:Bool -> y:{v:Bool | v == x} -> Int
check = 0

app :: rforall a, b, c. (x:a -> b) -> y:a -> b
app = \ f x -> f x

main :: Int -> Int -> Int
main = \a b -> app (check (a <= b)) (a <= b)
