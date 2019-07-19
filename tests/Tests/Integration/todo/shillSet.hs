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
    >a
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

-- The "Client"

copyRec :: lstSet:Set ~>  lookupSet:Set ~>  contentsSet:Set ~>  readSet:Set ~>  createSet:Set ~>  writeSet:Set ~>
  f:{v:Int | v ∈ lstSet /\ v ∈ lookupSet /\ v ∈ readSet} ->
  t:{v:Int | v ∈ createSet /\ v ∈ writeSet} ->
  Shill
    <{v:Set | v == lstSet} <{v:Set | v == lookupSet} <{v:Set | v == contentsSet} <{v:Set | v == readSet} <{v:Set | v == createSet} <{v:Set | v == writeSet}
    >{v:Set | setSubset v lstSet} >{v:Set | setSubset v lookupSet} >{v:Set | setSubset v contentsSet} >{v:Set | setSubset v readSet} >{v:Set | setSubset v createSet} >{v:Set | setSubset v writeSet}
    >Int -- This should return a Unit, right? Do we not have value-level Unit, still?
copyRec = \f -> \t -> (pure 0)
