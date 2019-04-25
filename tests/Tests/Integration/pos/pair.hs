fst as forall a, b. (Pair >a >b) -> a
fst = True

snd as forall a, b. (Pair >a >b) -> b
snd = True

mkPair as forall a, b. x:a -> y:b -> Pair >a >b
mkPair = True

foo :: {v:Int | v == 1}
foo = (fst (mkPair 1 1))
