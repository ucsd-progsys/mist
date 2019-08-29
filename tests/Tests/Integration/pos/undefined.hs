undefined as rforall a . a
undefined = 0

foo :: {v:Int | v > 9}
foo = undefined

bar as forall a. Bar >a -> Unit
bar = 2

baz as forall a. Baz <a -> Unit
baz = 3

qux :: Unit
qux = let x = (bar undefined),
          y = (baz undefined)
          in Unit
