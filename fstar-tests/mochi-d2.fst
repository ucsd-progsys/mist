module D2

assume val choice : bool

val app : #n:int -> f:(x:int{n <= x} -> int) -> u:int{n <= u} -> int
let rec app #n f x = if choice then app f (x + 1) else f x

val check : x:int -> u:int{x <= u} -> int
let check x y = if x <= y then 1 else (assert False; 2)

val main : int -> int
let main i = app (check i) i
