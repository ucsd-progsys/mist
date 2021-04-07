bind as rforall a, b, p, q, r.
  M <p >q >a ->
  (underscore:a -> M <q >r >b) ->
  M <p >r >b
bind = 0

magic as rforall a. a
magic = 0

foo as x:Int ~> underscore:Int -> M <Int >{v:Int | v = x} >{v:Int | v = x}
foo = \underscore -> magic

bar as x:Int -> M <{v:Int | v = x} >{v: Int | v = x} >Int
bar = 0

main :: M <Int >Int >Int
main =
  bind (foo 0) (\x -> bar x)

foo2 :: rforall a.
  underscore:Int ->
  (x:Int ~> (M <Int >{v:Int | v = x} >{v:Int | v = x}) -> a) ->
  a
foo2 = \underscore -> (\k -> let thinged = magic in k thinged)

main2 :: M <Int >Int >Int
main2 =
  foo2 0 (\mx ->
    bind mx (\x -> bar x))


-- incr :: n:Int ~> (Int -> { v : Int | v == n }) -> { v : Int | v == n + 1 }
-- incr = \ f -> (f 0) + 1

-- test1 :: { v : Int | v == 11 }
-- test1 = incr (\x -> 10)
