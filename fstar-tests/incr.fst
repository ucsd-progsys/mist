module Incr

val incr : #n:int -> f:(int -> v:int{v = n}) -> v:int{v = n + 1}
let incr #n f = (f 0) + 1

val test1 : v:int{v = 11}
let test1 = incr (fun x -> 10)

val test2 : m:int -> v:int{v = m + 1}
let test2 m = incr (fun x -> m)

type sint (n:int) = x:int{x = n}

val sincr : #n:int -> f:(int -> sint n) -> sint (n + 1)
let sincr #n f = (f 0) + 1

val stest1 : sint 11
let stest1 = sincr (fun x -> 10)

val stest2 : m:int -> sint (m + 1)
let stest2 m = sincr (fun x -> m + 1)
