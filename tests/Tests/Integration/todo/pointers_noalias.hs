-- module State where

-- rjhala [10:45 AM]
-- The idris people have a bunch of nice STATE examples here:https://github.com/idris-lang/Idris-dev/tree/master/samples/STFor a start, how about [login.idr](https://github.com/idris-lang/Idris-dev/blob/master/samples/ST/Login.idr)
-- except in a way where you can clearly tell what’s going on…
--
-- rjhala [11:43 AM]
-- here’s a super simple example: can you get it to work with suitable annotations?

-----------------------------------------------------------------------------
-- | Library ----------------------------------------------------------------
-----------------------------------------------------------------------------
-- | Some opaque implementation of pointers to `Int` ------------------------
-- type Ptr = ()

-- | Allocating a fresh `Ptr` with value `0`
new :: ST Ptr
new = undefined "assumed"

-- | Read a `Ptr`
get :: Ptr -> ST Int
get = undefined "assumed"

-- | Write a `Ptr`
set :: Ptr -> Int -> ST Int
set = undefined "assumed"

-----------------------------------------------------------------------------

decr :: r:Ptr -> ST ()
decr r = do
   n <- get r
   set r (n - 1)
   return ()

init :: n:Int -> ST Ptr
init n = do
   r <- new
   set r n
   return r

zero :: r:Ptr -> ST ()
zero r = do
   n <- get
   if (n <= 0)
       then return ()
       else decr r >> zero r

test :: Nat -> Nat -> ST ()
test n1 n2 = do
   r1 <- init n1
   r2 <- init n2
   zero r1
   zero r2
   v1 <- get r1
   v2 <- get r2
   assert (v1 == 0 && v2 == 0)
   return ()
-----------------------------------------------------------------------------
