makeArray as n:Int -> Map <{v:Int | (0 <= v) /\ (v <= n)} >Int
makeArray = 0

upd as n:Int -> m:(Map <{v:Int | (0 <= v) /\ (v <= n)} >Int) -> i:{v:Int | (0 <= v) /\ (v <= n)} -> x:Int -> {v:Map <{v:Int | (0 <= v) /\ (v <= n)} >Int | v = store m i x }
upd = 0

main :: n:Int -> i:Int -> x:Int -> {v:Map <{v:Int | (0 <= v) /\ (v <= n)} >Int | select v i = x}
main = \ n i x -> upd n (makeArray n) i x
