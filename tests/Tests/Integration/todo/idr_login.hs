-- https://github.com/idris-lang/Idris-dev/blob/master/samples/ST/Intro.idr

undefined as rforall a. a
undefined = 0

assert :: {v:Bool | v} -> Unit
assert = \tru -> Unit
-----------------------------------------------------------------------------
-- | Library ----------------------------------------------------------------
-----------------------------------------------------------------------------
bind :: rforall a, b, p, q, r.
  ST <p >q >a ->
  (x:a -> ST <q >r >b) ->
  ST <p >r >b
bind = undefined

thenn :: rforall a, b, p, q, r.
  ST <p >q >a
  -> ST <q >r >b
  -> ST <p >r >b
thenn = undefined

pure :: rforall a, p, q.  x:a -> ST <p >q >a
pure = undefined

-- | Some opaque implementation of pointers to `Int` ------------------------

-- | Allocating a fresh `Int` with value `0`
new :: rforall a. ST <a >a >Var
new = undefined

read :: hg:(Map <Var >Access) ~> p:Var -> ST <{h:Map <Var >Access | h == hg} >{h:Map <Var >Access | h == hg} >{v:Access| v == select hg p}
read = undefined

write :: h:(Map <Var >Access) ~> p:Var -> v:Access -> ST <{hg:Map <Var >Access | h == hg} >{hg:Map <Var >Access | store h p v == hg} >Unit
write = undefined

-----------------------------------------------------------------------------
-- data Access = LoggedOut | LoggedIn
loggedOut as Access
loggedOut = 0
loggedIn as Access
loggedIn = 1

-- data LoginResult = OK | BadPassword
oK as LoginResult
oK = 0
badPassword as LoginResult
badPassword = 1

-- data Store :: Access -> Type
-- Store x = State String -- represents secret data

withConnection :: rforall p, q, a. init:(Map <Var >Access) ~> (server:Var ~> (ST <{v:Map <Var >Access | v = init } >{v:Map <Var >Access | select server v = loggedOut} >{v:Var | v = server}) -> ST <p >q >a) -> ST <p >q >a
withConnection = \f -> (bind new (\v -> f (thenn (write v loggedOut) (pure v))))

{-
disconnect :: (store : Var) -> ST m () [remove store (Store LoggedOut)]
disconnect store = delete store
-}

readSecret :: stor : Var -> ST <{v:Map <Var >Access | select v stor = loggedIn } >{v:Map <Var >Access | select v stor = loggedIn } >Int
readSecret = \ stor -> read stor

{-
login :: (store : Var) ->
        ST m LoginResult [store ::: Store LoggedOut :->
                           (\res => Store (case res of
                                                OK => LoggedIkkn
                                                BadPassword => LoggedOut))]
login store = do putStr "Enter password: "
                 p <- getStr
                 if p == "Mornington Crescent"
                    then pure OK
                    else pure BadPassword

logout :: (store : Var) ->
         ST m () [store ::: Store LoggedIn :-> Store LoggedOut]
logout store = pure ()

getData :: (ConsoleIO m, DataStore m) => ST m () []
getData = do st <- connect
             OK <- login st
                | BadPassword => do putStrLn "Failure"
                                    disconnect st
             secret <- readSecret st
             putStrLn ("Secret is: " ++ show secret)
             logout st
             disconnect st


main :: IO ()
main = run getData
-}
