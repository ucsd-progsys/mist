{-

data L = Fun Int L
       | App L L
       | Var Int

type Lin env = Lin L

var as n:Int -> Lin {v | v = single n}

fun as env ~> n:Int -> Lin {v | v = env - (single n)} -> Lin {v | v = env}

app as env ~> env' -> Lin {v | v = env} -> Lin {v | v = env'} -> Lin {v | v = union env env'}

typecheck as Lin {v | v = emptyset} -> L
typecheck (Lin term) = term

term :: L
term = typecheck $ (app (fun 1 (var 1)) (fun 1 (var 1)))

badTerm :: L
badTerm = typecheck $ (fun 1 (app (var 1) (var 1)))

-}

{-

data LType = TFun LType LType
           | TUnit

data LExpr = LFun Int L
           | LApp L L
           | LVar Int
           | LUnit

type Lin env typ = Lin LExpr
type L e t = Lin {v|v=e} {v|v=t}

var :: t ~> n:Int -> L (single (n, t)) t
var n = LVar n

unit :: L ∅ TUnit
unit = LUnit

app :: env ~> env':{v|env ∩ env' = ∅} ~> t ~> t' ~> L env (TFun t t') -> L env' t -> L (env ∪ env') t'
app e1 e2 = LApp e1 e2

fun :: env ~> t' ~> t:LType -> n:Int{v|(v, t) ∉ env} -> L (env ∪ single (n, t)) t' -> L env (TFun t t')
fun _ n e = LFun n e

typecheck :: t:LType -> L ∅ t -> LExpr
typecheck _ (Lin e) = e

term :: LExpr
term = typecheck TUnit $ app (fun 1 TUnit (var 1)) unit

∃Γ.∃Δ.∃t.∃t'. (Γ ∩ Δ = ∅) ∧ (Γ ⊢ λ1:<>.1 : t -o t') ∧ (Δ ⊢ <> : t) ∧ (Γ ∪ Δ = ∅) ∧ (t' = <>)
-------------------------------------------------------------------------------------------
∅ ⊢ (λ1:<>.1) <> : <>

(Δ = ∅) ∧ (t = <>)
---------------------
Δ ⊢ <> : t

∃Γ'.∃t''. ((1, <>) ∉ Γ') ∧ (Γ' ∪ single (n, t) ⊢ 1 : t'') ∧ (Γ = Γ') ∧ (t -o t' = <> -o t'')
-------------------------------------------------------------------------------------------
Γ ⊢ λ1:<>.1 : t -o t'

∃t'''. (Γ' ∪ single (n, t'') = single (n, t''')) ∧ (t'' = t''')
--------------------------------------------------------------
Γ' ∪ single (n, t) ⊢ 1 : t''

necessary additions:
- a ∪ b = ∅ :~> a = ∅ ∧ b = ∅
- a ∪ {b} = {b'} :~> a = ∅ ∧ b = b'
- congruence f a b = f a' b' :~> a = a' ∧ b = b'

badTerm :: L
badTerm = typecheck (TFun (TFun TUnit TUnit) (TFun TUnit TUnit)) $ fun 1 (TFun TUnit TUnit) (app (var 1) (var 1))


-----------      ------------
x:t ⊢ x : t       ∅ ⊢ <> : 1


Γ ⊢ e : t -o t'   Δ ⊢ e' : t
----------------------------
    Γ ⊎ Δ ⊢ e e' : t'


  Γ, x:t ⊢ e : t'
--------------------
Γ ⊢ λx:t.e : t -o t'
-}
