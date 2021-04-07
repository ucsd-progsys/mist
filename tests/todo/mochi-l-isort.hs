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

nil :: Pair >Int >({v:Int | False} -> Int)
nil = makePair 0 (\i -> assert False)

cons :: x:Int -> (Pair >Int >(Int -> Int)) -> Pair >Int >(i:Int -> {v:Int | (i = 0) => (v = x)})
cons = \x xs ->
  makePair ((fst xs) + 1) (\i -> if i = 0 then x else (snd xs) (i - 1))

-- hd :: out:Int ~> (Pair >Int >(i:Int -> {v:Int | (i = 0) => (v = out)})) -> {v:Int | v = out}
hd :: (Pair >Int >(Int -> Int)) -> Int
hd = \p -> (snd p) 0

tl :: (Pair >Int >(Int -> Int)) -> Pair >Int >(Int -> Int)
tl = \p -> makePair ((fst p) - 1) (\i -> (snd p) (i + 1))

isNil :: (Pair >Int >(Int -> Int)) -> {v:Bool | v = (len = 0)}
isNil = \p -> (fst p) == 0

insert :: x:Int -> (Pair >Int >(Int -> Int)) -> Pair >Int >(Int -> Int)
insert = \x ys ->
  if isNil ys then
    cons x nil
  else
    if x <= (hd ys) then
      cons x ys
    else
      cons (hd ys) (insert x (tl ys))

-- forAll :: s:(Set >Int) ~> n:Int ~> ({v:Int | v ∈ s} -> {v:Bool | v}) -> (Pair >{v:Int | v = n} >({v:Int | v < n} -> {v:Int | v ∈ s})) -> {v:Bool | v}
-- forAll = \f xs ->
--   if isNil xs then
--     True
--   else
--     (f (hd xs)) /\ (forAll f (tl xs))

-- main :: Int -> Unit
-- main = \len -> assert (forAll (\x -> x <= len) (makePair len (\i -> len - i)))
