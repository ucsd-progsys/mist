module TickAppend

open FStar.Ref

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val n : ref int
let n = ST.alloc 0

let step _ =
    let n0 = read n in
    write n (n0 + 1)

val append : xs:list 'a -> ys:list 'a ->
    ST (list 'a)
    (fun _ -> True)
    (fun h0 _ h1 -> sel h1 n = sel h0 n + length xs)
let rec append xs ys = 
    match xs with
        | [] -> ys
        | x :: xs -> step (); x :: (append xs ys)
