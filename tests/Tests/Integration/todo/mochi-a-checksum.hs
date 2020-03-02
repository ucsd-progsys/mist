undefined as rforall a. a
undefined = 0

assert as {safe:Bool | safe == True} -> Unit
assert = 0

makePair as rforall a, b. fst:a -> snd:b -> Pair >a >b
makePair = undefined

fst as rforall a, b. pair:(Pair >a >b) -> a
fst = undefined

snd as rforall a, b. pair:(Pair >a >b) -> b
snd = undefined

makeArray :: n:Int -> Pair >{v:Int | v = n} >(i:{v:Int | (0 <= v) /\ (v < n)} -> Int)
makeArray = \n -> makePair n (\i -> 0)

update :: n:Int ~> p:(Pair >{v:Int | v = n} >(i:{v:Int | (0 <= v) /\ (v < n)} -> Int)) -> i:{v:Int | (0 <= v) /\ (v < n)} -> x:Int -> Pair >{v:Int | v = n} >(j:{v:Int | (0 <= v) /\ (v < n)} -> {v:Int | (j = i) => (v = x)})
update = \p i x -> makePair (fst p) (\j -> if j == i then x else (snd p) j)

checksum :: ar0:Int ~> ar1:Int ~> p:(Pair >{v:Int | v > 1} >(x:Int -> {v:Int | ((x = 0) => (v = ar0)) /\ ((x = 1) => (v = ar1))})) -> x:{v:Int | v = ar0 + ar1} -> Unit
checksum = \p x -> assert ((((snd p) 0) + ((snd p) 1)) == x)

main :: a:Int -> b:Int -> Unit
main = \a b -> checksum (update (update (makeArray 2) 0 a) 1 b) (a + b)
