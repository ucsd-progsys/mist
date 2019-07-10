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

pure as rforall a. x:a -> Tick ^{v:Int | v == 0} >a
pure = (0)

ap as rforall a, b. t1:Int ~> t2:Int ~> (Tick ^{v:Int | v == t1} >x:a -> b) -> (Tick ^{v:Int | v == t2} >a) -> Tick ^{v:Int | v == t1 + t2} >b
ap = (0)

append :: rforall a. xs:(List <a) -> ys:(List <a) -> Tick ^{v:Int | v = mLength xs} >{v: List <a | mLength v = (mLength xs) + (mLength ys)}
append = \xs -> \ys ->
  if empty xs
    then pure ys
    else (ap (pure (\rest -> cons (first xs) rest)) (append (rest xs) ys))
