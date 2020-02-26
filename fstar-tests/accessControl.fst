module AccessControl

open FStar.GSet

noeq
type hst (state:Type) (a:Type) (p q:state) =
  | State : (state -> (a & state)) -> hst state a p q

assume val pure (#state:Type) (#a:Type) (#w:state) (x:a) : hst state a w w
assume val bind (#state:Type) (#a #b:Type) (#w1 #w2 #w3:state)
  (f:hst state a w1 w2) (g:a -> hst state b w2 w3) : hst state b w1 w3
assume val thenn (#state:Type) (#a #b:Type) (#w1 #w2 #w3:state)
  (f:hst state a w1 w2) (g:hst state b w2 w3) : hst state b w1 w3

let get (#state:Type) (#w:state) : hst state state w w =
  State (fun _ -> w, w)

let put (#state:Type) (#w:state) (w1:state) : hst state unit w w1 =
  State (fun _ -> (), w1)

assume val canRead (#acl:set int) (f:int) : (hst (set int) (v:bool{v = mem f acl}) acl acl)
assume val grant (#acl:set int) (f:int) : hst (set int) unit acl (union acl (singleton f))
assume val revoke (#acl:set int) (f:int) : hst (set int) unit acl (intersect acl (complement (singleton f)))
assume val read (#acl:set int) (f:int{mem f acl}) : hst (set int) string acl acl

val main (#acl:set int) (f:int) : hst (set int) string acl acl
let main #acl f =
  assume (equal acl (intersect (union acl (singleton f)) (complement (singleton f))));
  bind (grant f) (fun _ ->
    (bind (read f) (fun contents ->
      (bind (revoke f) (fun _ ->
        pure contents)))))
