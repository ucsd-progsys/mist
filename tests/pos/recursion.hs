measure mNil :: List [>Int] -> Bool
measure mCons :: List [>Int] -> Bool
measure mLength :: List [>Int] -> Int
measure not :: Bool -> Bool

empty as x:(List >Int) -> {v: Bool | (v == mNil x) /\ (v == not (mCons x)) /\ (v == (mLength x == 0))}
empty = (0)

nil as {v: List >Int | (mNil v) /\ (mLength v = 0) /\ (not (mCons v))}
nil = (0)

cons as x:Int -> xs:(List >Int) -> {v: List >Int | (mCons v) /\ (mLength v = mLength xs + 1) /\ (not (mNil v))}
cons = (0)

first as {v: List >Int | mCons v} -> Int
first = (0)

rest as rs:{v: List >Int | mCons v} -> {v: List >Int | mLength v + 1 == mLength rs }
rest = (0)

append :: xs:(List >Int) -> ys:(List >Int) -> {v: List >Int | mLength v = (mLength xs) + (mLength ys)}
append = \xs -> \ys ->
  if empty xs
    then ys
    else cons (first xs) (append (rest xs) ys)
