(* module M = Map.Make(struct type t = int let compare = compare end) *)

let find x m = m x
let add k v m kk = if kk = k then v else m kk

let ret x s = (x, s)
let dnib f ma s = match ma s with
    | (x, s') -> f x s'
let bind ma f s = match ma s with
    | (x, s') -> f x s'
let thenn ma mb = bind ma (fun _ -> mb)
let get s = (s,s)
let put x s = ((),x)

let decr (r:int) = bind get (fun (m) -> put (add r ((find r m) - 1) m))

let rec zero r = bind get (fun m -> let n = find r m in if n <= 0 then ret () else (thenn (decr r) (zero r)))

let test n1 n2 =
  if n1 < 0 || n2 < 0 then ret () else
  let r1 = 0 in let r2 = 1 in
  bind get (fun m ->
    (thenn
    (thenn
    (thenn (put (add r1 n1 (add r2 n2 m)))
           (zero r1))
           (zero r2))
           (bind get (fun m -> ret (assert (find r1 m = 0 && find r2 m = 0))))))
