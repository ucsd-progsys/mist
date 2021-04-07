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

hd :: (Pair >Int >(Int -> Int)) -> Int
hd = \p -> (snd p) 0

tl :: (Pair >Int >(Int -> Int)) -> Pair >Int >(Int -> Int)
tl = \p -> makePair ((fst p) - 1) (\i -> (snd p) (i + 1))

isNil :: (Pair >Int >(Int -> Int)) -> Bool
isNil = \p -> (fst p) == 0

forAll :: s:(Set >Int) ~> n:Int ~> ({v:Int | v ∈ s} -> {v:Bool | v}) -> (Pair >{v:Int | v = n} >({v:Int | v < n} -> {v:Int | v ∈ s})) -> {v:Bool | v}
forAll = \f xs ->
  if isNil xs then
    True
  else
    (f (hd xs)) /\ (forAll f (tl xs))

main :: Int -> Unit
main = \len -> assert (forAll (\x -> x <= len) (makePair len (\i -> len - i)))
