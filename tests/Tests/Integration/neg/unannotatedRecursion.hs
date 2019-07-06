top :: {v: Int | v == 5}
top =
    let foo = \ n -> (foo n)
    in 5
