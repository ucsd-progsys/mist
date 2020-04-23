module DijkstraTick

let tick (a: Type) = int -> M (a * int)

val return_tick: a:Type -> x:a -> tick a
let return_tick a x = fun _ -> x, 0

val bind_tick: a:Type -> b:Type -> f:tick a -> g:(a -> tick b) -> tick b
let bind_tick a b f g = fun t0 ->
    let x, t1 = f t0 in
    g x (t1 + 1)

let get (_:unit): tick int =
    fun x -> x, x

let put (x: int): tick unit =
    fun _ -> (), x

total reifiable reflectable new_effect {
    TICK : a:Type -> Effect
    with repr     = tick
       ; bind     = bind_tick
       ; return   = return_tick
       ; get      = get
       ; put      = put
}

effect Tick (a:Type) (req:TICK?.pre) (ens: int -> a -> int -> GTot Type0) =
    TICK a (fun (t0:int) (p:TICK?.post a) -> req t0 /\
      (forall (r:a) (t1:int). (req t0 /\ ens t0 r t1) ==> p (r, t1)))


val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val append : xs:list 'a -> ys:list 'a -> zs:list 'a{length zs = length xs + length ys}  
let rec append xs ys = 
    match xs with
        | [] -> ys
        | x :: xs -> x :: (append xs ys)

val tappend : xs:list 'a -> ys:list 'a ->
    Tick (list 'a)
    (fun _ -> True)
    (fun t0 _ t1 -> t1 = t0 + length xs)
let rec tappend xs ys =
    match xs with
        | [] -> ys
        | x :: xs -> x :: (tappend xs ys)


