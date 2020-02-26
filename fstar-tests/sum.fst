module Sum

val sum : #n:int -> #m:int -> f:(int -> v:int{v = n}) -> g:(int -> v:int{v = m}) -> v:int{v = n + m}
let sum #n #m f g = (f 0) + (g 0)

val test1 : v:int{v = 11}
let test1 = sum (fun x -> 10) (fun y -> 1)
