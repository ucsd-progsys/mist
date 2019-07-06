measure mNil :: List [] -> Bool
measure mCons :: List [] -> Bool
measure mLength :: List [] -> Int

empty as forall a. x:(List <a) -> {v: Bool | v == mNil x}
empty = (0)

nil as forall a. {v: List <a | (mNil v) /\ (mLength v = 0)}
nil = (0)

cons as forall a. x:a -> xs:(List <a) -> {v: List <a | (mCons v) /\ (mLength v = mLength xs + 1)}
cons = (0)

first as forall a. {v: List <a | mCons v} -> a
first = (0)

rest as forall a. {v: List <a | mCons v} -> List <a
rest = (0)

append :: forall a. xs:(List <a) -> ys:(List <a) -> {v: List <a | mLength v = (mLength xs) + (mLength ys)}
append = \xs -> \ys ->
  if empty xs
    then ys
    else cons (first xs) (append (rest xs) ys)
