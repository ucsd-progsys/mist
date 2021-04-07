assertIs as x:Int -> {y: Int | x == y} -> Unit
assertIs = 0

bar as x:Int ~> Int -> {v: Int | v == x}
bar = 0

f :: x:Int -> Int -> Unit
f = \m p -> assertIs p (bar m)
