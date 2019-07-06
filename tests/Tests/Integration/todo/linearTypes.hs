{-

data L = Fun Int L
       | App L L
       | Var Int

type Lin env = Lin L

var as n:Int -> Lin {v | v = singleton n}

fun as env ~> n:Int -> Lin {v | v = env - (singleton n)} -> Lin {v | v = env}

app as env ~> env' -> Lin {v | v = env} -> Lin {v | v = env'} -> Lin {v | v = union env env'}

typecheck as Lin {v | v = emptyset} -> L

term :: L
term = typecheck $ (app (fun 1 (var 1)) (fun 1 (var 1)))

badTerm :: L
badTerm = typecheck $ (fun 1 (app (var 1) (var 1)))

-}
