module IncrState

noeq
type hst (state:Type) (a:Type) (p q:state) =
  | State : (state -> (a & state)) -> hst state a p q

assume val pure (#state:Type) (#a:Type) (#w:state) (x:a) : hst state a w w
assume val bind (#state:Type) (#a #b:Type) (#w1 #w2 #w3:state)
  (f:hst state a w1 w2) (g:a -> hst state b w2 w3) : hst state b w1 w3


let get (#state:Type) (#w:state) : hst state state w w =
  State (fun _ -> w, w)

let set (#state:Type) (#w:state) (w1:state) : hst state unit w w1 =
  State (fun _ -> (), w1)

let fresh (#n:int) : hst int int n (n + 1) =
  get `bind` (fun _ -> set (n + 1) `bind` (fun _ -> pure n))