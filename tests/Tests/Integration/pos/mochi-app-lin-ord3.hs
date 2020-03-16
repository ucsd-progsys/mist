check as x:Int -> y:{v:Int | v == x} -> Int
check = 0

app :: rforall a, b, c. (x:a -> b) -> y:a -> b
app = \ f x -> f x

foo :: rforall a, b, c. x:a -> (y:a -> b) -> b
foo = \ x k -> k x

main :: Int -> Int -> Int
main = \a b -> app (foo (4 * a + 2 * b)) (check (4 * a + 2 * b))
