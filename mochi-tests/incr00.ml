let incr f = (f 0) + 1

let test1 = assert ( 11 = incr (fun x-> 10) )
let test2 m = assert ( (m+1) = incr (fun x -> m) )
