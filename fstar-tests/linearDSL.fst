module LinearDSL

open FStar.GSet

noeq
type lin (env:set int) : Type =
  | Lin : lin env

assume val var (x:int) : lin (singleton x)
assume val lam (#env:set int) (n:int{~(mem n env)}) (e:lin (union env (singleton n))) : lin env
assume val app (#env1:set int) (#env2:(set int){equal (intersect env1 env2) empty}) (e1:lin env1) (e2:lin env2) : lin (union env1 env2)

val program1 : lin empty
let program1 =
  assume (equal (singleton 1) (union empty (singleton 1)));
  lam 1 (var 1)

val program2 : lin empty
let program2 =
  assume (equal (singleton 1) (union empty (singleton 1)));
  lam 1 (lam 2 (app (var 1) (var 2)))
