-- makeArray as n:Int -> Map <{v:Int | (0 <= v) /\ (v <= n)} >Int
-- makeArray = 0
-- 
-- upd as n:Int -> m:(Map <{v:Int | (0 <= v) /\ (v <= n)} >Int) -> i:{v:Int | (0 <= v) /\ (v <= n)} -> x:Int -> {v:Map <{v:Int | (0 <= v) /\ (v <= n)} >Int | v = store m i x }
-- upd = 0
-- 
-- main :: n:Int -> i:Int -> x:Int -> {v:Map <{v:Int | (0 <= v) /\ (v <= n)} >Int | select v i = x}
-- main = \ n i x -> upd n (makeArray n) i x
--

makeArray :: n:Int -> {v:Int | (0 <= v) /\ (v < n)} -> Int
makeArray = \ n i -> 0

upd :: n:Int -> m:({v:Int | (0 <= v) /\ (v < n)} -> Int) ->
                i:{v:Int | (0 <= v) /\ (v < n)} -> x:Int ->
                k:{v:Int | (0 <= v) /\ (v < n)} -> {v:Int | if k == i then (v = x) else (0 = 0)}
upd = \ n m i x k -> if k = i then x else m i

check :: x:Int ~> n:Int ->  i:{i:Int | (0<= i) /\ (i < n)} ~> (j:{v:Int | (0 <= v) /\ (v < n)} -> {v:Int| if i == j then v == x else True }) -> ii:{ii:Int | (i == ii)}-> xx:{xx:Int | x == xx}  -> Bool
check = \ n m i x -> m i == x

main :: n:Int -> i:Int -> x:Int -> Bool
main = \ n i x -> if (0 <= i) /\ (i < n) then check n ((upd n (makeArray n)) i x) i x else True
