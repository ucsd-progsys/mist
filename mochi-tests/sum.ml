let sum f g = (f 0) + (g 0)

let test2 = assert ( 11  = sum (fun x -> 10) (fun x -> 1))
let test1 n m = assert ( m + n = sum (fun x -> n) (fun x -> m))
