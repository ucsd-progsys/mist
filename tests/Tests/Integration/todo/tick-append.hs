{-

data Tick t a = Tick a
type T w a = T {v|v=w} a

pure :: x -> T 0 a
pure x = Tick x

</> :: t1 t2 -> T t1 (a -> b) -> T t2 a -> T (t1 + t2) b
Tick f </> Tick x = Tick (f x)

(++) :: xs:[a] -> ys:[a] -> T (len xs) {v|v=len xs + len ys}
[] ++ ys = pure ys
(x:xs') ++ ys = pure (x:) </> (xs' ++ ys)

(<*>) as forall a, b. t1:Int ~> t2: Int ~>
         Tick {v | v = t1} (a -> b)
      -> Tick {v | v = t2} a
      -> Tick {v | v = t1 + t2} b
Tick f <*> Tick x = Tick (f x)

(>>=) as forall a, b. t1:Int ~> t2: Int ~>
         Tick {v | v = t1} a
      -> (a -> Tick {v | v = t2} b)
      -> Tick {v | v = t1 + t2} b

step as forall a. t1:Int ~>
     -> m: Int
     -> Tick {v | v = t1} a
     -> Tick {v | v = t1 + m} a
step m (Tick x) = Tick x

(</>) as forall a, b. t1:Int ~> t2:Int
      -> Tick {v | v = t1} (a -> b)
      -> Tick {v | v = t2} a
      -> Tick {v | v = t1 + t2 + 1} b
(</>) = (<*>)

(++) :: forall a.
     -> xs: [a]
     -> ys: [a]
     -> Tick {v | v = length xs} {v | v = length xs + length ys}
[] ++ ys = pure ys
(x:xs') ++ ys = pure (x:) </> (xs' ++ ys)

reverse :: xs:[a] -> Tick {v | v = ((length xs * length xs) / 2) + ((length xs + 1) / 2)} [a]
reverse [] = pure []
reverse (x:xs) = reverse xs >>= (++ [x])
-}

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

rest as rs:{v: List >Int | mCons v} -> {v: List >Int | mLength v == mLength rs - 1 }
rest = (0)

pure as rforall a. x:a -> Tick >{v:Int | v == 0} >a
pure = (0)

ap as rforall a, b. t1:Int ~> t2:Int ~>
  (Tick >{v:Int | v == t1} >x:a -> b) ->
  Tick >{v:Int | v == t2} >a ->
  Tick >{v:Int | v == t1 + t2 + 1} >b
ap = (0)

ap0 as rforall a, b. t10:Int ~> t20:Int ~>
  (Tick >{v:Int | v == t10} >x:a -> b) ->
  Tick >{v:Int | v == t20} >a ->
  Tick >{v:Int | v == t10 + t20} >b
ap0 = (0)

append :: xs:(List >Int) -> ys:(List >Int) ->
  Tick >{v:Int | v = mLength xs} >{v: List >Int | mLength v = (mLength xs) + (mLength ys)}
append = \xs -> \ys ->
  if empty xs
    then pure ys
    else (ap (pure (\rest -> cons (first xs) rest)) (append (rest xs) ys))

mapA :: n:Int ~>
  (x:Int -> Tick >{v:Int | v == n} >Int) ->
  xs:(List >Int) ->
  Tick >{v:Int | v == n * (mLength xs)} >(List >Int)
mapA = \f xs ->
  if empty xs
    then pure nil
    else (ap0 (ap0 (pure cons) (f (first xs))) (mapA f (rest xs)))
