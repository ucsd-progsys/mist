let rec app f x = if Random.bool () then app f (x + 1) else f x
let check x y = if x <= y then () else assert false
let main i = app (check i) i
