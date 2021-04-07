-- pagination in Mist

thenn as rforall p, q, r.
  ST <p >q -> ST <q >r -> ST <p >r
thenn = 0

nextPage as n:Int ~> ST <{v:Int | v = n} >{v:Int | v = n+1}
nextPage = 0

-- pos
main :: ST <{v:Int | v = 0} >{v:Int | v = 2}
main = thenn nextPage nextPage

