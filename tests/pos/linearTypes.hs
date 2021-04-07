undefined as rforall a. a
undefined = 0

var as x:Int -> (Lin >{v:Set >Int | v = setPlus emptySet x})
var = undefined

fun as env:(Set >Int) ~> n:{v:Int | (v ∈ env) ≠ True} -> (Lin >{v:Set >Int | v = setPlus env n}) -> (Lin >{v:Set >Int | v = env})
fun = undefined

app as env1:(Set >Int) ~> env2:{v:Set >Int | env1 ∩ v = emptySet} ~> (Lin >{v:Set >Int | v = env1}) -> (Lin >{v:Set >Int | v = env2}) -> (Lin >{v:Set >Int | v = env1 ∪ env2})
app = undefined

typecheck as (Lin >{v:Set >Int | v = emptySet}) -> (Lin >(Set >Int))
typecheck = undefined

program1 :: Lin >(Set >Int)
program1 = typecheck (fun 1 (var 1))

program2 :: Lin >(Set >Int)
program2 = typecheck (fun 1 (fun 2 (app (var 1) (var 2))))
