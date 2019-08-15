foo :: set:(Set >Int) ~> sub:{v:Set >Int | setSubset set v} -> {v:Int | v ∈ set} -> {v:Int | v ∈ sub}
foo = \sub -> \v -> v
