undefined as rforall a. a
undefined = 0

assert as {safe:Bool | safe == True} -> Int
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

main :: n:Int -> i:Int -> x:Int -> Int
main = \n i x -> if (0 <= i) /\ (i < n)
  then assert (((snd (update (makeArray n) i x)) i) == x)
  else 1
