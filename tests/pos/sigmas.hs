bar as Int -> (exists n:Int. x:Int -> {v:Int | v = n})
bar = 0

main :: Int
main = let f = bar 1 in f 2
