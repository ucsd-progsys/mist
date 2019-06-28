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

{−@ insert :: Ord a ⇒ x : a → xs : OList a
→ {t : Tick {zs : OList a | length zs == 1 + length xs} | tcost t <= length xs} @−}

insert :: Ord a ⇒ a → [a] → Tick [a] insert x [ ] = pure [ x ]
insert x (y : ys)
|x<=y =wait(x:y:ys)
| otherwise = pure (y:) </> insert x ys

{−@ isort :: Ord a ⇒ xs : [a]
→ { t : Tick { zs : OList a | length zs == length xs } | tcost t <= length xs ∗ length xs } @−}

isort :: Ord a ⇒ [ a ] → Tick [ a ] isort [ ] = return [ ] isort(x:xs)=insertx=<<isortxs

{−@(=<<{·})::n:Nat→f :(a→{tf :Tickb|tcosttf <=n})→t:Ticka → {t : Tick b | tcost t <= tcost t + n} @−}
(=<<{·}) :: Int → (a → Tick b) → Tick a → Tick b f =<<{n} t = f =<< t

isort :: Ord a ⇒ [a] → Tick [a]
isort [] = return []
isort (x : xs) = insert x =<<{lenдth xs} isort xs

-}
