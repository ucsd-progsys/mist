let decr x = x := !x - 1 

let rec zero r = let n = !r in if n <= 0 then () else (decr r; zero r)

let test n1 n2 = let r1 = ref n1 in
             let r2 = ref n2 in
             (zero r1 ; zero r2; assert (!r1 = 0); assert (!r2 = 0))
