-- Monadic Interface
ret as forall s, a. w:s ~> x:a -> ST <{v:s|v==w} >{v:s|v==w} >a
ret = (0)

bind as forall s, a, b. w1:s ~> w2:s ~> w3:s ~> (ST <{v:s|v==w1} >{v:s|v==w2} >a)
  -> (unused:a -> ST <{v:s|v==w2} >{v:s|v==w3} >b)
  -> ST <{v:s|v==w1} >{v:s|v==w3} >b
bind = (0)

thenn as forall s, a, b. w1:s ~> w2:s ~> w3:s ~> (ST <{v:s|v==w1} >{v:s|v==w2} >a)
  -> (ST <{v:s|v==w2} >{v:s|v==w3} >b)
  -> ST <{v:s|v==w1} >{v:s|v==w3} >b
thenn = (0)

get as forall s. w:s ~> Bool -> ST <{v:s|v==w} >{v:s|v==w} >{v:s|v==w}
get = (0)

put as forall s. w:s -> ST <s >{v:s|v==w} >Unit
put = (0)

-- incr
-- incr :: ST <Int >Int >Unit
-- incr = (bind (get True) (\n -> (put (n+1))))

incr2 :: ST <{i:Int|i==2} >{w:Int|w==2} >Int
incr2 = thenn (get True) (get True)


{-
(let ret##0as forall s##1. forall a##2. w##3 :{fresh0##4 :s##1 | (PAnd [])} ~> x##5 :{fresh0##6 :a##2 | (PAnd [])} -> CT "ST" [(),(),()] = 0

in (let bind##10as forall s##11. forall a##12. forall b##13. w1##14 :{fresh0##15 :s##11 | (PAnd [])} ~> w2##16 :{fresh0##17 :s##11 | (PAnd [])} ~> w3##18 :{fresh0##19 :s##11 | (PAnd [])} ~> fresh0##20 :CT "ST" [(),(),()] -> fresh0##24 :unused##25 :{fresh0##26 :a##12 | (PAnd [])} -> CT "ST" [(),(),()] -> CT "ST" [(),(),()] = 0

in (let thenn##33as forall s##34. forall a##35. forall b##36. w1##37 :{fresh0##38 :s##34 | (PAnd [])} ~> w2##39 :{fresh0##40 :s##34 | (PAnd [])} ~> w3##41 :{fresh0##42 :s##34 | (PAnd [])} ~> fresh0##43 :CT "ST" [(),(),()] -> fresh0##47 :CT "ST" [(),(),()] -> CT "ST" [(),(),()] = 0

in (let get##54as forall s##55. w##56 :{fresh0##57 :s##55 | (PAnd [])} ~> fresh0##58 :{fresh0##59 :Bool | (PAnd [])} -> CT "ST" [(),(),()] = 0

in (let put##63as forall s##64. w##65 :{fresh0##66 :s##64 | (PAnd [])} -> CT "ST" [(),(),()] = 0

in (let incr##69: CT "ST" [(),(),()] = (let anf##9:: (Int) => ST[Int, Int, Unit[]] = (\ n##72:: Int -> (let anf##7:: Int = 1 in (let anf##5:: (Int) => (Int) => Int = + in (let anf##6:: (Int) => Int = (anf##5 n##72) in (let anf##8:: Int = (anf##6 anf##7) in (let anf##4:: (Int) => ST[Int, Int, Unit[]] = (put##63 @ Int) in (anf##4 anf##8))))))) in (let anf##2:: Bool = True in (let anf##1:: (Bool) => ST[Int, Int, Int] = (get##54 @ Int) in (let anf##3:: ST[Int, Int, Int] = (anf##1 anf##2) in (let anf##0:: (ST[Int, Int, Int]) => ((Int) => ST[Int, Int, Unit[]]) => ST[Int, Int, Unit[]] = (((bind##10 @ Int) @ Int) @ Unit[]) in ((anf##0 anf##3) anf##9))))))

in (let incr2##73: CT "ST" [(),(),()] = (let anf##15:: Bool = True in (let anf##14:: (Bool) => ST[Int, Int, Int] = (get##54 @ Int) in (let anf##16:: ST[Int, Int, Int] = (anf##14 anf##15) in (let anf##12:: Bool = True in (let anf##11:: (Bool) => ST[Int, Int, Int] = (get##54 @ Int) in (let anf##13:: ST[Int, Int, Int] = (anf##11 anf##12) in (let anf##10:: (ST[Int, Int, Int]) => (ST[Int, Int, Int]) => ST[Int, Int, Int] = (((thenn##33 @ Int) @ Int) @ Int) in ((anf##10 anf##13) anf##16)))))))) in ())))))))

let incr##69 : ST [Int, Int, Unit] =
  let anf##9 : (Int) => ST [Int, Int, Unit] =
    \n##72 : Int ->
      let anf##7 : Int = 1
      let anf##5 : (Int) => (Int) => Int = +
      let anf##6 : (Int) => (Int) = anf##5 n##72
      let anf##8 : Int = anf##6 anf##7
      let anf##4 : (Int) => ST [Int, Int, Unit] = put##63 @ Int
        anf##4 anf##8
  let anf##2 : Bool = True
  let anf##1 : (Bool) => ST [Int, Int, Int] = get##54 @ Int
  let anf##3 : ST [Int, Int, Int] = anf##1 anf##2
  let anf##0 : (ST[Int, Int, Int]) => ((Int) => ST[Int, Int, Unit]) => ST[Int, Int, Unit] = ((bind##10 @ Int) @ Int) @ Unit[]
    (anf##0 anf##3) anf##9

let incr2##73 : ST <{i:Int|i==2} >{w:Int|w==2} >Int =
  let anf##15 : Bool = True
  let anf##14 : (Bool) => ST[Int, Int, Int] = get##54 @ Int
  let anf##16 : ST[Int, Int, Int] = anf##14 anf##15
  let anf##12 : Bool = True
  let anf##11 : (Bool) => ST[Int, Int, Int] = get##54 @ Int
  let anf##13 : ST[Int, Int, Int] = anf##11 anf##12
  let anf##10 : (ST[Int, Int, Int]) => (ST[Int, Int, Int]) => ST[Int, Int, Int] = ((thenn##33 @ Int) @ Int) @ Int
    (anf##10 anf##13) anf##16

-}
