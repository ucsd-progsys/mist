let ret x s = (x, s)
let dnib f ma s = match ma s with
    | (x, s') -> f x s'
let get s = (s,s)
let put x s = ((),x)
let bind ma f = dnib f ma
let thenn ma mb = dnib (fun _ -> mb) ma

let rec loop f x = if x = 0
  then (fun score -> f score)
  else (fun score -> thenn (f x) (loop f (x - 1) score))

let foo = fun sc -> bind (get) (fun x -> put (x+4))
let bar = fun sc -> bind (get) (fun x -> put (x+1))
let main s = (thenn (thenn ((loop foo 8) 9)  ((loop bar 9) 10)) (bind (get) (fun x -> ret (assert (x > s))))) s
