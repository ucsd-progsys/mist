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

append :: len1:Int ~> len2:Int ~> xs:(Pair >{v:Int | v = len1} >(Int -> Int)) -> ys:(Pair >{v:Int | v = len2} >(Int -> Int)) -> Pair >{v:Int | v = len1 + len2} >(Int -> Int)
append = \xs ys ->
  if (fst xs) == 0 then
    makePair (fst ys) (snd ys)
  else
    let zs = append (makePair ((fst xs) - 1) (\i -> (snd xs) i + 1)) ys in
      makePair ((fst zs) + 1) (\i -> if i = 0 then (snd xs) 0 else (snd zs) (i - 1))

length :: n:Int ~> (Pair >{v:Int | v = n} >(Int -> Int)) -> {v:Int | v = n}
length = \xs ->
  if (fst xs) == 0 then
    0
  else
    1 + length (makePair ((fst xs) - 1) (\i -> (snd xs) (i + 1)))

main :: Int -> Int -> Unit
main = \len1 len2 ->
  assert ((length (append (makePair len1 (\i -> 1)) (makePair len2 (\i -> 2)))) == (len1 + len2))
