module Flar

noeq
type flar (out:int) =
  | Flar : (int -> v:int{v = out}) -> flar out

val appFlar (#out:int) (f:flar out) (x:int) : v:int{v = out}
let appFlar #out f x = match f with
    | Flar f -> f x

val incr : #n:int -> f:(flar n) -> v:int{v = n + 1}
let incr #n f = (appFlar f 0) + 1

val test1 : v:int{v = 11}
let test1 = incr (Flar (fun x -> 10))
