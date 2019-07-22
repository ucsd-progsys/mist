-- The Shill example from the BRTs paper
-- Ulitmately this should be written with a map of sets, but let's do it
-- with just sets first and see how that goes.

-- | The API
-- Caps: lst, lookup (do we need this?), contents, read, create, write
-- Monad interface: pure, bind, thenn

write as lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  f:{v:Int | v ∈ writeSet} -> (String) ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | v == lstSet} >{v:Set | v == lookupSet} >{v:Set | v == contentsSet} >{v:Set | v == readSet} >{v:Set | v == createSet} >{v:Set | v == writeSet}
    >Unit
write = 0

read as lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  f:{v:Int | v ∈ readSet} ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | v == lstSet} >{v:Set | v == lookupSet} >{v:Set | v == contentsSet} >{v:Set | v == readSet} >{v:Set | v == createSet} >{v:Set | v == writeSet}
    >String
read = 0

-- Does this rforall correctly capture the fact that we inherit permissions?
lst as rforall a. lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  d:{v:a | v ∈ lstSet} ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | v == lstSet} >{v:Set | v == lookupSet} >{v:Set | v == contentsSet} >{v:Set | v == readSet} >{v:Set | v == createSet} >{v:Set | v == writeSet}
    >(List >a)
lst = 0

-- this is what is called createWO
create as rforall a. lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  d:{v:a | v ∈ createSet} ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | v == lstSet} >{v:Set | v == lookupSet} >{v:Set | v == contentsSet} >{v:Set | v == readSet} >{v:Set | v == createSet} >{v:Set | v == setPlus writeSet d}
    >a
create = 0

pure as rforall a. lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  x:a ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | v == lstSet} >{v:Set | v == lookupSet} >{v:Set | v == contentsSet} >{v:Set | v == readSet} >{v:Set | v == createSet} >{v:Set | v == writeSet}
    >a
pure = 0

bind as rforall a, b .
  lstSet1:Set ~>  lookupSet1:Set ~>  contentsSet1:Set ~>  readSet1:Set ~>  createSet1:Set ~>  writeSet1:Set ~>
  lstSet2:Set ~>  lookupSet2:Set ~>  contentsSet2:Set ~>  readSet2:Set ~>  createSet2:Set ~>  writeSet2:Set ~>
  lstSet3:Set ~>  lookupSet3:Set ~>  contentsSet3:Set ~>  readSet3:Set ~>  createSet3:Set ~>  writeSet3:Set ~>
  (Shill
    <{v:Set | v == lstSet1} <{v:Set | v == lookupSet1} <{v:Set | v == contentsSet1} <{v:Set | v == readSet1} <{v:Set | v == createSet1} <{v:Set | v == writeSet1}
    >{v:Set | v == lstSet2} >{v:Set | v == lookupSet2} >{v:Set | v == contentsSet2} >{v:Set | v == readSet2} >{v:Set | v == createSet2} >{v:Set | v == writeSet2}
    >a) ->
  (x:a -> Shill
    <{v:Set | v == lstSet2} <{v:Set | v == lookupSet2} <{v:Set | v == contentsSet2} <{v:Set | v == readSet2} <{v:Set | v == createSet2} <{v:Set | v == writeSet2}
    >{v:Set | v == lstSet3} >{v:Set | v == lookupSet3} >{v:Set | v == contentsSet3} >{v:Set | v == readSet3} >{v:Set | v == createSet3} >{v:Set | v == writeSet3}
    >b) ->
  Shill
    <{v:Set | v == lstSet1} <{v:Set | v == lookupSet1} <{v:Set | v == contentsSet1} <{v:Set | v == readSet1} <{v:Set | v == createSet1} <{v:Set | v == writeSet1}
    >{v:Set | v == lstSet3} >{v:Set | v == lookupSet3} >{v:Set | v == contentsSet3} >{v:Set | v == readSet3} >{v:Set | v == createSet3} >{v:Set | v == writeSet3}
    >b
bind = 0

thenn as rforall a, b .
  lstSet1:Set ~>  lookupSet1:Set ~>  contentsSet1:Set ~>  readSet1:Set ~>  createSet1:Set ~>  writeSet1:Set ~>
  lstSet2:Set ~>  lookupSet2:Set ~>  contentsSet2:Set ~>  readSet2:Set ~>  createSet2:Set ~>  writeSet2:Set ~>
  lstSet3:Set ~>  lookupSet3:Set ~>  contentsSet3:Set ~>  readSet3:Set ~>  createSet3:Set ~>  writeSet3:Set ~>
  (Shill
    <{v:Set | v == lstSet1} <{v:Set | v == lookupSet1} <{v:Set | v == contentsSet1} <{v:Set | v == readSet1} <{v:Set | v == createSet1} <{v:Set | v == writeSet1}
    >{v:Set | v == lstSet2} >{v:Set | v == lookupSet2} >{v:Set | v == contentsSet2} >{v:Set | v == readSet2} >{v:Set | v == createSet2} >{v:Set | v == writeSet2}
    >a) ->
  (Shill
    <{v:Set | v == lstSet2} <{v:Set | v == lookupSet2} <{v:Set | v == contentsSet2} <{v:Set | v == readSet2} <{v:Set | v == createSet2} <{v:Set | v == writeSet2}
    >{v:Set | v == lstSet3} >{v:Set | v == lookupSet3} >{v:Set | v == contentsSet3} >{v:Set | v == readSet3} >{v:Set | v == createSet3} >{v:Set | v == writeSet3}
    >b) ->
  Shill
    <{v:Set | v == lstSet1} <{v:Set | v == lookupSet1} <{v:Set | v == contentsSet1} <{v:Set | v == readSet1} <{v:Set | v == createSet1} <{v:Set | v == writeSet1}
    >{v:Set | v == lstSet3} >{v:Set | v == lookupSet3} >{v:Set | v == contentsSet3} >{v:Set | v == readSet3} >{v:Set | v == createSet3} >{v:Set | v == writeSet3}
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
  lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  (x:a ->
  Shill
    <{v:Set | setSubset lstSet v} <{v:Set | setSubset lookupSet v} <{v:Set | setSubset contentsSet v} <{v:Set | setSubset readSet v} <{v:Set | setSubset createSet v} <{v:Set | setSubset writeSet v}
    >{v:Set | setSubset lstSet v} >{v:Set | setSubset lookupSet v} >{v:Set | setSubset contentsSet v} >{v:Set | setSubset readSet v} >{v:Set | setSubset createSet v} >{v:Set | setSubset writeSet v}
    >h) ->
  List >a ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | setSubset lstSet v} >{v:Set | setSubset lookupSet v} >{v:Set | setSubset contentsSet v} >{v:Set | setSubset readSet v} >{v:Set | setSubset createSet v} >{v:Set | setSubset writeSet v}
    >h
-- We can implement forShill using Lists (see append.hs)
forShill = 0


undefined as rforall a . a
undefined = 0

-- why does this fail? do we not encode bools properly?
and as a:Bool -> b:Bool -> {v:Bool | v == a /\ b}
and = \a -> \b -> if a == True then (if b == True then True else False) else False

-- The "Client"

-- copyRec :: lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
--   f:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} ->
--   t:{v:Int | v ∈ createSet /\ v ∈ writeSet} ->
--   Shill
--     <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
--     >{v:Set | setSubset lstSet v} >{v:Set | setSubset lookupSet v} >{v:Set | setSubset contentsSet v} >{v:Set | setSubset readSet v} >{v:Set | setSubset createSet v} >{v:Set | setSubset writeSet v}
--     >Unit -- This should return a Unit, but we don't have a value-level unit terms
-- copyRec = \f -> \t -> bind (read f) (write t)

-- doesn't work:
-- copyRec = \f -> \t -> bind (lst f) (\x -> (forShill x (\y -> pure 0)))
-- works:
-- copyRec = \f -> \t -> bind (lst f) (\x -> pure 0)

-- oops, copyRec is a BRTs invention. Let's do `find` from the shill papers

find :: lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  ({v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} -> Bool) ->
  cur:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | setSubset lstSet v} >{v:Set | setSubset lookupSet v} >{v:Set | setSubset contentsSet v} >{v:Set | setSubset readSet v} >{v:Set | setSubset createSet v} >{v:Set | setSubset writeSet v}
    >Int -- This should return a Unit, but we don't have a value-level unit terms
find = \filter -> \f -> if and (isFile f) (filter f)
               then pure f
             else (if (isDir f) then (bind (lst f) (forShill (find filter))) else (pure 0))
