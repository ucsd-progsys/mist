magic as x:Int -> y:Int -> {v: Int | x == y}
assert = 0

bar as x:Int ~> {y:Int | x == y} -> Int
bar = 0

f :: Int -> Int -> Int
f = \m p -> assert p (bar m)
