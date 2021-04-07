foo1 as n:Int ~> {v:Int | v = n} -> Unit
foo1 = (0)

bar1 :: m:Int -> {z:Int | z = m} -> Unit
bar1 = (\m z -> (foo z))

foo2 as n:Int ~> {v:Int | v = (C n)} -> Unit
foo2 = (0)

bar2 :: m:Int -> {z:Int | z = (C m)} -> Unit
bar2 = (\m z -> (foo z))
