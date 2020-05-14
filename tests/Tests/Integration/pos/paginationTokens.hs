undefined as rforall a. a
undefined = 0

done as Int
done = undefined

startTok as Int
startTok = undefined

----------------------------------------------------------------------------
-- | The ST Monad ----------------------------------------------------------
----------------------------------------------------------------------------
bind :: rforall a, b, p, q, r, s, t, u.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

pure :: rforall a, p, q, s, t. x:a -> ST <p >q >a
pure = undefined

thenn :: rforall a, b, p, q, r, s, t, u.
  ST <p >q >a ->
  ST <q >r >b ->
  ST <p >r >b
thenn = \f g -> bind f (\underscore -> g)

fmap :: rforall a, b, p, q, s, t.
  (underscore:a -> b) ->
  ST <p >q >a ->
  ST <p >q >b
fmap = \f x -> bind x (\xx -> pure (f xx))

----------------------------------------------------------------------------
-- | The Token API ----------------------------------------------------------
----------------------------------------------------------------------------
nextPage as
  token:{v: Int | v ≠ done} ->
  (exists tok:Int.
    (ST <{v:Int | v = token}
        >{v:Int | (v = tok) /\ (v ≠ token)}
        >{v:Int | v = tok}))
nextPage = undefined

start as underscore:Int ->
  (exists tok:Int.
    ST <{v:Int | v = startTok}
       >{v:Int | (v = tok) /\ (v ≠ startTok)}
       >{v:Int | v = tok})
start = undefined

client :: token:Int ->
  (ST <{v:Int | v = token} >{v:Int | v = done} >Int)
client = \token ->
  if token == done
  then pure 1
  else bind (nextPage token) (\tok -> client tok)

main :: ST <{v: Int | v = startTok} >{v: Int | v = done} >Int
main = bind (start 1) (\startToken -> client startToken)

