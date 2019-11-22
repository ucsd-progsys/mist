let ret x s = (x, s)
let bind f ma s = match ma s with
    | (x, s') -> f x s'
let get s = (s,s)
let put x s = ((),x)

let incr = bind (fun x -> put (x+1)) (get)

let vc i = assert (snd (incr i) = i + 1)
let vc1 = assert (snd (incr 10) = 11)

