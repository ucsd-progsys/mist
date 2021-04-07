fst as rforall a, b. (Pair >a >b) -> a
fst = True

snd as rforall a, b. (Pair >a >b) -> b
snd = True

mkPair as rforall a, b. x:a -> y:b -> Pair >a >b
mkPair = True

foo :: {v:Int | v == 1}
foo = fst (mkPair 1 True)
