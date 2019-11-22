(* module S = Set.Make(struct type t = string let compare = compare end) *)

let mem x s = s x
let add x s y = if y = x then true else s y
let remove x s y = if y = x then false else s y

let ret x s = (x, s)
let dnib f ma s = match ma s with
    | (x, s') -> f x s'
let bind : ('s -> ('a* 's)) -> ('a -> 's -> ('b* 's)) -> 's -> ('b* 's)  = fun ma f s -> match ma s with
    | (x, s') -> f x s'
let thenn ma mb = bind ma (fun _ -> mb)
let get s = (s,s)
let put x s = ((),x)
let modify f s = ((), f s)
let fmap f st s = let (x,s') = st s in (f x,s')

let canRead x = bind get (fun s -> ret (mem x s))
let grant x = modify (add x)
let revoke x = modify (remove x)
let read = (fun f s -> assert (mem f s) ; ret 0 s)

let foo f = (bind (grant f) (fun _ -> (bind (read f) (fun contents -> (bind (revoke f) (fun _ -> ret contents))))))
