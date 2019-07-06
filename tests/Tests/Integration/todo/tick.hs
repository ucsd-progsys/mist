{-

type Tick t a = Tick a

pure as forall a. x:a -> Tick 0 {v:a | v = x}
pure x = Tick 0 x

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
