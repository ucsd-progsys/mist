----------------------------------------------------------------------------
-- | The ST Monad ----------------------------------------------------------
----------------------------------------------------------------------------

measure mNil :: List [>Int] -> Bool
measure mCons :: List [>Int] -> Bool
measure mLength :: List [>Int] -> Int

empty as x:(List >Int) -> {v: Bool | v == mNil x}
empty = (0)

nil as {v: List >Int | (mNil v) /\ (mLength v = 0)}
nil = (0)

cons as x:Int -> xs:(List >Int) -> {v: List >Int | (mCons v) /\ (mLength v = mLength xs + 1)}
cons = (0)

first as {v: List >Int | mCons v} -> Int
first = (0)

rest as rs:{v: List >Int | mCons v} -> {v: List >Int | mLength v == mLength rs - 1 }
rest = (0)

undefined as rforall a. a
undefined = 0

bind as rforall a, b, p, q, r.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

pure as rforall a, p, q, s, t. x:a -> ST <p >q >a
pure = undefined

thenn as rforall a, b, p, q, r.
  ST <p >q >a ->
  ST <q >r >b ->
  ST <p >r >b
thenn = undefined

fmap as rforall a, b, p, q, s, t.
  (underscore:a -> b) ->
  ST <p >q >a ->
  ST <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))

get as forall s. wg:s ~> Int -> ST <{v:s|v==wg} >{v:s|v==wg} >{v:s|v==wg}
get = undefined

put as forall s. wp:s -> ST <s >{v:s|v==wp} >Int
put = undefined

while ::
  (n:Int ~>
   under:Int ->
   (exists n2:{v: Int | v > n}.
     (ST <{v: Int | v = n} >{v: Int | v = n2} >Int))) ->
  (Int -> Bool) ->
  (m:Int ~>
   score:Int ->
   (exists m2:{v: Int | v > m}.
     ST <{v: Int | v = m} >{v: Int | v = m2} >Int))
while = \f cond -> \score -> (bind (get 1) (\state -> if cond state then while f cond score else (f 1)))

foo :: x:Int ~>
       under:Int ->
       (exists x2:{v: Int | v > x}.
         (ST <{v: Int | v = x} >{v: Int | v = x2} >Int))
foo = \under -> bind (get 6) (\y -> put (y + 4))

bar :: x:Int ~>
       under:Int ->
       ST <{v: Int | v = x} >{v: Int | v = x + 1} >Int
bar = \under -> bind (get 8) (\y -> put (y + 1))

main :: x:{v: Int | v > 3} ~> ST <{v: Int | v = x} >{v: Int | v > 3} >Int
main = thenn ((while foo (\state -> False)) 8) ((while bar (\state -> state < 100)) 9)
