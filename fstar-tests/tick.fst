module Tick

type tick (n:Ghost.erased nat) (a:Type) : Type =
| Tick : a -> tick n a


let pure (#a:Type) (x:a) : tick 0 a = Tick x

let app (#n #m:Ghost.erased nat) (#a #b:Type) (Tick f:tick n (a -> b)) (Tick x:tick m a)
: tick (n + m + 1) b
= Tick (f x)

module L = FStar.List.Tot

let rec append (#a:Type) (xs ys:list a)
: tick (L.length xs) (list a)
= match xs with
  | []    -> pure ys
  | x::xs -> pure (Cons x) `app` append xs ys