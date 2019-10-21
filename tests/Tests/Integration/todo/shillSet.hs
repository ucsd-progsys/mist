-- The Shill example from the BRTs paper
-- Ulitmately this should be written with a map of sets, but let's do it
-- with just sets first and see how that goes.

-- | The API
-- Caps: lst, lookup (do we need this?), contents, read, create, write
-- Monad interface: pure, bind, thenn

measure mNil :: List [] -> Bool
measure mCons :: List [] -> Bool
measure mLength :: List [] -> Int

empty as rforall a. x:(List <a) -> {v: Bool | v == mNil x}
empty = (0)

nil as rforall a. {v: List <a | (mNil v) /\ (mLength v = 0)}
nil = (0)

cons as rforall a. x:a -> xs:(List <a) -> {v: List <a | (mCons v) /\ (mLength v = mLength xs + 1)}
cons = (0)

write as lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
  f:{v:Int | v ∈ writeSet} -> (String) ->
  Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | v == lstSet} >{v:Set >Int | v == lookupSet} >{v:Set >Int | v == contentsSet} >{v:Set >Int | v == readSet} >{v:Set >Int | v == createSet} >{v:Set >Int | v == writeSet}
    >Unit
write = 0

read as lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
  f:{v:Int | v ∈ readSet} ->
  Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | v == lstSet} >{v:Set >Int | v == lookupSet} >{v:Set >Int | v == contentsSet} >{v:Set >Int | v == readSet} >{v:Set >Int | v == createSet} >{v:Set >Int | v == writeSet}
    >String
read = 0

-- Does this rforall correctly capture the fact that we inherit permissions?
-- lst as rforall a. lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
--   d:{v:a | v ∈ lstSet} ->
--   Shill
--     <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
--     >{v:Set >Int | v == lstSet} >{v:Set >Int | v == lookupSet} >{v:Set >Int | v == contentsSet} >{v:Set >Int | v == readSet} >{v:Set >Int | v == createSet} >{v:Set >Int | v == writeSet}
--     >(List >a)
-- lst = 0

-- this is what is called createWO
create as rforall a. lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
  d:{v:a | v ∈ createSet} ->
  Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | v == lstSet} >{v:Set >Int | v == lookupSet} >{v:Set >Int | v == contentsSet} >{v:Set >Int | v == readSet} >{v:Set >Int | v == createSet} >{v:Set >Int | v == setPlus writeSet d}
    >a
create = 0

pure as rforall a. lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
  x:a ->
  Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | v == lstSet} >{v:Set >Int | v == lookupSet} >{v:Set >Int | v == contentsSet} >{v:Set >Int | v == readSet} >{v:Set >Int | v == createSet} >{v:Set >Int | v == writeSet}
    >a
pure = 0

bind as rforall a, b .
  lstSet1:(Set >Int) ~> lookupSet1:(Set >Int) ~> contentsSet1:(Set >Int) ~> readSet1:(Set >Int) ~> createSet1:(Set >Int) ~> writeSet1:(Set >Int) ~>
  lstSet2:(Set >Int) ~> lookupSet2:(Set >Int) ~> contentsSet2:(Set >Int) ~> readSet2:(Set >Int) ~> createSet2:(Set >Int) ~> writeSet2:(Set >Int) ~>
  lstSet3:(Set >Int) ~> lookupSet3:(Set >Int) ~> contentsSet3:(Set >Int) ~> readSet3:(Set >Int) ~> createSet3:(Set >Int) ~> writeSet3:(Set >Int) ~>
  (Shill
    <{v:Set >Int | v == lstSet1} <{v:Set >Int | v == lookupSet1} <{v:Set >Int | v == contentsSet1} <{v:Set >Int | v == readSet1} <{v:Set >Int | v == createSet1} <{v:Set >Int | v == writeSet1}
    >{v:Set >Int | v == lstSet2} >{v:Set >Int | v == lookupSet2} >{v:Set >Int | v == contentsSet2} >{v:Set >Int | v == readSet2} >{v:Set >Int | v == createSet2} >{v:Set >Int | v == writeSet2}
    >a) ->
  (x:a -> Shill
    <{v:Set >Int | v == lstSet2} <{v:Set >Int | v == lookupSet2} <{v:Set >Int | v == contentsSet2} <{v:Set >Int | v == readSet2} <{v:Set >Int | v == createSet2} <{v:Set >Int | v == writeSet2}
    >{v:Set >Int | v == lstSet3} >{v:Set >Int | v == lookupSet3} >{v:Set >Int | v == contentsSet3} >{v:Set >Int | v == readSet3} >{v:Set >Int | v == createSet3} >{v:Set >Int | v == writeSet3}
    >b) ->
  Shill
    <{v:Set >Int | v == lstSet1} <{v:Set >Int | v == lookupSet1} <{v:Set >Int | v == contentsSet1} <{v:Set >Int | v == readSet1} <{v:Set >Int | v == createSet1} <{v:Set >Int | v == writeSet1}
    >{v:Set >Int | v == lstSet3} >{v:Set >Int | v == lookupSet3} >{v:Set >Int | v == contentsSet3} >{v:Set >Int | v == readSet3} >{v:Set >Int | v == createSet3} >{v:Set >Int | v == writeSet3}
    >b
bind = 0

thenn as rforall a, b .
  lstSet1:(Set >Int) ~> lookupSet1:(Set >Int) ~> contentsSet1:(Set >Int) ~> readSet1:(Set >Int) ~> createSet1:(Set >Int) ~> writeSet1:(Set >Int) ~>
  lstSet2:(Set >Int) ~> lookupSet2:(Set >Int) ~> contentsSet2:(Set >Int) ~> readSet2:(Set >Int) ~> createSet2:(Set >Int) ~> writeSet2:(Set >Int) ~>
  lstSet3:(Set >Int) ~> lookupSet3:(Set >Int) ~> contentsSet3:(Set >Int) ~> readSet3:(Set >Int) ~> createSet3:(Set >Int) ~> writeSet3:(Set >Int) ~>
  (Shill
    <{v:Set >Int | v == lstSet1} <{v:Set >Int | v == lookupSet1} <{v:Set >Int | v == contentsSet1} <{v:Set >Int | v == readSet1} <{v:Set >Int | v == createSet1} <{v:Set >Int | v == writeSet1}
    >{v:Set >Int | v == lstSet2} >{v:Set >Int | v == lookupSet2} >{v:Set >Int | v == contentsSet2} >{v:Set >Int | v == readSet2} >{v:Set >Int | v == createSet2} >{v:Set >Int | v == writeSet2}
    >a) ->
  (Shill
    <{v:Set >Int | v == lstSet2} <{v:Set >Int | v == lookupSet2} <{v:Set >Int | v == contentsSet2} <{v:Set >Int | v == readSet2} <{v:Set >Int | v == createSet2} <{v:Set >Int | v == writeSet2}
    >{v:Set >Int | v == lstSet3} >{v:Set >Int | v == lookupSet3} >{v:Set >Int | v == contentsSet3} >{v:Set >Int | v == readSet3} >{v:Set >Int | v == createSet3} >{v:Set >Int | v == writeSet3}
    >b) ->
  Shill
    <{v:Set >Int | v == lstSet1} <{v:Set >Int | v == lookupSet1} <{v:Set >Int | v == contentsSet1} <{v:Set >Int | v == readSet1} <{v:Set >Int | v == createSet1} <{v:Set >Int | v == writeSet1}
    >{v:Set >Int | v == lstSet3} >{v:Set >Int | v == lookupSet3} >{v:Set >Int | v == contentsSet3} >{v:Set >Int | v == readSet3} >{v:Set >Int | v == createSet3} >{v:Set >Int | v == writeSet3}
    >b
thenn = 0

-- should be in the monad
isFile as f:Int -> Bool
isFile = 0

isDir as f:Int -> Bool
isDir  = 0

-- NEXT: forShill

-- Hmm, I think forShill needs to enforece that @f@ is monotonic and return
-- a monotonically larger world in order to account for creation, but the
-- BRTs example simply returns a world over which all the same predicates
-- hold, so let's try that first
--
-- Actually, this doesn't seem to work, so let's do it with subsets, but
-- let's do the inside of that loop first

forShill as rforall a, b, c, d, e, f, g, h.
  lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
  (lstSet2:{v: Set >Int | setSubset lstSet v} ~> lookupSet2:{v: Set >Int | setSubset lookupSet v} ~> contentsSet2:{v: Set >Int | setSubset contentsSet v} ~> readSet2:{v: Set >Int | setSubset readSet v} ~> createSet2:{v: Set >Int | setSubset createSet v} ~> writeSet2:{v: Set >Int | setSubset writeSet v} ~>
  x:a ->
  Shill
    <{v:Set >Int | v == lstSet2} <{v:Set >Int | v == lookupSet2} <{v:Set >Int | v == contentsSet2} <{v:Set >Int | v == readSet2} <{v:Set >Int | v == createSet2} <{v:Set >Int | v == writeSet2}
    >{v:Set >Int | setSubset lstSet2 v} >{v:Set >Int | setSubset lookupSet2 v} >{v:Set >Int | setSubset contentsSet2 v} >{v:Set >Int | setSubset readSet2 v} >{v:Set >Int | setSubset createSet2 v} >{v:Set >Int | setSubset writeSet2 v}
    >h) ->
  List >a ->
  Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | setSubset lstSet v} >{v:Set >Int | setSubset lookupSet v} >{v:Set >Int | setSubset contentsSet v} >{v:Set >Int | setSubset readSet v} >{v:Set >Int | setSubset createSet v} >{v:Set >Int | setSubset writeSet v}
    >h
-- We can implement forShill using Lists (see append.hs)
forShill = 0


undefined as rforall a . a
undefined = 0

-- why does this fail? do we not encode bools properly?
and as a:Bool -> b:Bool -> {v:Bool | v == a /\ b}
and = \a -> \b -> if a == True then (if b == True then True else False) else False

-- The "Client"

-- copyRec :: lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
--   f:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} ->
--   t:{v:Int | v ∈ createSet /\ v ∈ writeSet} ->
--   Shill
--     <{v:(Set >Int) | v == lstSet} <{v:(Set >Int) | v == lookupSet} <{v:(Set >Int) | v == contentsSet} <{v:(Set >Int) | v == readSet} <{v:(Set >Int) | v == createSet} <{v:(Set >Int) | v == writeSet}
--     >{v:(Set >Int) | setSubset lstSet v} >{v:(Set >Int) | setSubset lookupSet v} >{v:(Set >Int) | setSubset contentsSet v} >{v:(Set >Int) | setSubset readSet v} >{v:(Set >Int) | setSubset createSet v} >{v:(Set >Int) | setSubset writeSet v}
--     >Unit -- This should return a Unit, but we don't have a value-level unit terms
-- copyRec = \f -> \t -> bind (read f) (write t)

-- doesn't work:
-- copyRec = \f -> \t -> bind (lst f) (\x -> (forShill x (\y -> pure 0)))
-- works:
-- copyRec = \f -> \t -> bind (lst f) (\x -> pure 0)

-- oops, copyRec is a BRTs invention. Let's do `find` from the shill papers



-- find :: lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int) ~>
--   ({v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} -> Bool) ->
--   cur:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} ->
--   Shill
--     <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
--     >{v:Set >Int | setSubset lstSet v} >{v:Set >Int | setSubset lookupSet v} >{v:Set >Int | setSubset contentsSet v} >{v:Set >Int | setSubset readSet v} >{v:Set >Int | setSubset createSet v} >{v:Set >Int | setSubset writeSet v}
--     >Int -- This should return a Unit, but we don't have a value-level unit terms
-- find = \lstSet ~> \lookupSet ~> \filter -> \f -> if and (isFile f) (filter f)
--              then pure f
--              else (if (isDir f)
--                      then (bind (lst f)
--                           (let finder :: lstSetAnn:(Set >Int) ~> lookupSetAnn:(Set >Int) ~> contentsSetAnn:(Set >Int) ~> readSetAnn:(Set >Int) ~> createSetAnn:(Set >Int) ~> writeSetAnn:(Set >Int) ~>
--                                          cur:{v:Int | v ∈ lstSetAnn /\ v ∈ lookupSetAnn /\ v ∈ readSetAnn} ->
--                                          Shill <{v:Set >Int | v == lstSetAnn} <{v:Set >Int | v == lookupSetAnn} <{v:Set >Int | v == contentsSetAnn} <{v:Set >Int | v == readSetAnn} <{v:Set >Int | v == createSetAnn} <{v:Set >Int | v == writeSetAnn}
--                                          >{v:Set >Int | setSubset lstSetAnn v} >{v:Set >Int | setSubset lookupSetAnn v} >{v:Set >Int | setSubset contentsSetAnn v} >{v:Set >Int | setSubset readSetAnn v} >{v:Set >Int | setSubset createSetAnn v} >{v:Set >Int | setSubset writeSetAnn v}
--                                          >Int
--                                = (find filter) in forShill finder))
--                      else (pure 0))


-- find
--   :: lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int)
--   ~> (Int -> Bool)
--   -> cur:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet}
--   -> Shill <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
--     >{v:Set >Int | setSubset lstSet v} >{v:Set >Int | setSubset lookupSet v} >{v:Set >Int | setSubset contentsSet v} >{v:Set >Int | setSubset readSet v} >{v:Set >Int | setSubset createSet v} >{v:Set >Int | setSubset writeSet v}
--     >Int
-- find = \lstSet ~> \lookupSet ~> \contentsSet ~> \readSet ~> \createSet ~> \writeSet ~>
--   \filter -> \f ->
--     if and (isFile f) (filter f)
--       then pure f
--       else (if (isDir f)
--               then (let finder
--                       :: lstSetAnn:{v: Set >Int | setSubset lstSet v} ~> lookupSetAnn:{v: Set >Int | setSubset lookupSet v} ~> contentsSetAnn:{v: Set >Int | setSubset contentsSet v} ~> readSetAnn:{v: Set >Int | setSubset readSet v} ~> createSetAnn:{v: Set >Int | setSubset createSet v} ~> writeSetAnn:{v: Set >Int | setSubset writeSet v}
--                       ~> cur:{v:Int | v ∈ lstSetAnn /\ v ∈ lookupSetAnn /\ v ∈ readSetAnn}
--                         -> Shill
--                           <{v:Set >Int | v == lstSetAnn} <{v:Set >Int | v == lookupSetAnn} <{v:Set >Int | v == contentsSetAnn} <{v:Set >Int | v == readSetAnn} <{v:Set >Int | v == createSetAnn} <{v:Set >Int | v == writeSetAnn}
--                           >{v:Set >Int | setSubset lstSetAnn v} >{v:Set >Int | setSubset lookupSetAnn v} >{v:Set >Int | setSubset contentsSetAnn v} >{v:Set >Int | setSubset readSetAnn v} >{v:Set >Int | setSubset createSetAnn v} >{v:Set >Int | setSubset writeSetAnn v}
--                           >Int
--                         = (find filter) in forShill finder empty)
--               else pure 0)

lst
  as lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int)
  ~> lstSetOut:{v: Set >Int | setSubset lstSet v} ~> lookupSetOut:{v: Set >Int | setSubset lookupSet v} ~> contentsSetOut:{v: Set >Int | setSubset contentsSet v} ~> readSetOut:{v: Set >Int | setSubset readSet v} ~> createSetOut:{v: Set >Int | setSubset createSet v} ~> writeSetOut:{v: Set >Int | setSubset writeSet v}
  ~> dir:{v:Int | v ∈ lstSet}
  -> Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | v == lstSetOut} >{v:Set >Int | v == lookupSetOut} >{v:Set >Int | v == contentsSetOut} >{v:Set >Int | v == readSetOut} >{v:Set >Int | v == createSetOut} >{v:Set >Int | v == writeSetOut}
    >{v: Int | ((dir ∈ lstSet) => (v ∈ lstSetOut)) /\ ((dir ∈ lookupSet) => (v ∈ lookupSetOut)) /\ ((dir ∈ contentsSet) => (v ∈ contentsSetOut)) /\ ((dir ∈ readSet) => (v ∈ readSetOut)) /\ ((dir ∈ createSet) => (v ∈ createSetOut)) /\ ((dir ∈ writeSet) => (v ∈ writeSetOut))}
lst = 0

find
  :: (Int -> Bool)
  -> lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int)
  ~> f:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet}
  -> Shill
    <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
    >{v:Set >Int | setSubset lstSet v} >{v:Set >Int | setSubset lookupSet v} >{v:Set >Int | setSubset contentsSet v} >{v:Set >Int | setSubset readSet v} >{v:Set >Int | setSubset createSet v} >{v:Set >Int | setSubset writeSet v}
    >Int
find =
  \filter -> \f ->
    if and (isFile f) (filter f)
      then pure f
      else (if (isDir f)
              then bind (lst f) (find filter)
              else pure 0)

-- CURRENT ATTEMPT
--------------------------------------------------------------------------------

-- lst
--   as lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int)
--   ~> lstSetOut:{v: Set >Int | setSubset lstSet v} ~> lookupSetOut:{v: Set >Int | setSubset lookupSet v} ~> contentsSetOut:{v: Set >Int | setSubset contentsSet v} ~> readSetOut:{v: Set >Int | setSubset readSet v} ~> createSetOut:{v: Set >Int | setSubset createSet v} ~> writeSetOut:{v: Set >Int | setSubset writeSet v}
--   ~> dir:{v:Int | v ∈ lstSet}
--   -> Shill
--     <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
--     >{v:Set >Int | v == lstSetOut} >{v:Set >Int | v == lookupSetOut} >{v:Set >Int | v == contentsSetOut} >{v:Set >Int | v == readSetOut} >{v:Set >Int | v == createSetOut} >{v:Set >Int | v == writeSetOut}
--     >(List >{v: Int | ((dir ∈ lstSet) => (v ∈ lstSetOut)) /\ ((dir ∈ lookupSet) => (v ∈ lookupSetOut)) /\ ((dir ∈ contentsSet) => (v ∈ contentsSetOut)) /\ ((dir ∈ readSet) => (v ∈ readSetOut)) /\ ((dir ∈ createSet) => (v ∈ createSetOut)) /\ ((dir ∈ writeSet) => (v ∈ writeSetOut))})
-- lst = 0

-- find
--   :: (Int -> Bool)
--   -> lstSet:(Set >Int) ~> lookupSet:(Set >Int) ~> contentsSet:(Set >Int) ~> readSet:(Set >Int) ~> createSet:(Set >Int) ~> writeSet:(Set >Int)
--   ~> f:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet}
--   -> Shill
--     <{v:Set >Int | v == lstSet} <{v:Set >Int | v == lookupSet} <{v:Set >Int | v == contentsSet} <{v:Set >Int | v == readSet} <{v:Set >Int | v == createSet} <{v:Set >Int | v == writeSet}
--     >{v:Set >Int | setSubset lstSet v} >{v:Set >Int | setSubset lookupSet v} >{v:Set >Int | setSubset contentsSet v} >{v:Set >Int | setSubset readSet v} >{v:Set >Int | setSubset createSet v} >{v:Set >Int | setSubset writeSet v}
--     >Int
-- find =
--   \filter -> \f ->
--     if and (isFile f) (filter f)
--       then pure f
--       else (if (isDir f)
--               then bind (lst f) (forShill (find filter))
--               else pure 0)
