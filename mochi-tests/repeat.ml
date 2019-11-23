let rec repeat f x v = if x = 0 then (f v) else (repeat f (x - 1) (f v))

let foo v = v + 4
let bar v = v + 1

let main x = assert ((repeat bar 15 (repeat foo 30 x)) >= x)
