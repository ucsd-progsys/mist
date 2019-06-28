{-

type Linear size e1 e2 t a = Reader [t] a

pure as forall t, a. size:Nat ~> e1
  ~> x:a
  -> Linear size e1 e2 t {v:a | v = x}
pure x = pure x

(>>=) as forall t, a, b. size:Nat ~> e1 ~> e2 ~> e3
  ~> Linear size e1 e2 t a
  -> (a -> Linear size e2 e3 t b)
  -> Linear size e1 e3 t b

read as forall t. size:Nat ~> e
  ~> n:{v: Int | v >= 0 && v < size && v ∉ e}
  -> Linear size e {v | v = e + {n}} t t
read = ask >>= (\r -> pure r!n)

runLinear as forall t, a. size:Nat ~> Linear [] {v | len v = size} a
  ~> {v: [t] | len v = size}
  -> a

runAffine as forall t, a. size:Nat ~> Linear [] {v | len v <= size} a
  ~> {v: [t] | len v = size}
  -> a
-}
