measure mNil :: List [] -> Bool
measure mCons :: List [] -> Bool
measure mLength :: List [] -> Int

empty as rforall a. x:(List <a) -> {v: Bool | v == mNil x}
empty = (0)

nil as rforall a. {v: List <a | (mNil v) /\ (mLength v = 0)}
nil = (0)

cons as rforall a. x:a -> xs:(List <a) -> {v: List <a | (mCons v) /\ (mLength v = mLength xs + 1)}
cons = (0)

first as rforall a. {v: List <a | mCons v} -> a
first = (0)

rest as rforall a. {v: List <a | mCons v} -> List <a
rest = (0)

append :: rforall a. xs:(List <a) -> ys:(List <a) -> {v: List <a | mLength v = mLength xs}
append = \xs -> \ys ->
  if empty xs
    then ys
    else cons (first xs) (append (rest xs) ys)
