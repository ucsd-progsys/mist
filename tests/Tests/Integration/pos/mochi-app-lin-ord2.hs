check as x:Int -> y:{v:Int | v == x} -> Int
check = 0

app :: rforall a, b, c. (x:a -> b) -> y:a -> b
app = \ f x -> f x

main :: Int -> Int -> Int
main = \a b ->app (check (4 * a + 2 * b)) (4 * a + 2 * b)
