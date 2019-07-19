foo :: set:Set ~> sub:{v:Set | setSubset set v} -> {v:Int | v ∈ set} -> {v:Int | v ∈ sub}
foo = \sub -> \v -> v
