incr :: x:Int -> {v:Int | v == x + 1}
incr = \x -> x + 1

moo :: {v:Int | v == 8}
moo = incr 7

id :: rforall a. {v:a | True} -> {v:a | True}
id = \x -> x

bar :: {v:Int | v == 8}
bar = incr (id 7)
