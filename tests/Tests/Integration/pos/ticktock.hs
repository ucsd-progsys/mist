-- tick and tock in Mist

thenn as rforall p, q, r.
  ST <p >q -> ST <q >r -> ST <p >r
thenn = 0

ticked as State
ticked = 0
tocked as State
tocked = 0

tick as ST <{v:State | v = tocked} >{v:State | v = ticked}
tick = 0

tock as ST <{v:State | v = ticked} >{v:State | v = tocked}
tock = 0

-- pos
-- main = tick >> tock >> tick >> tock
main :: ST <{v:State | v = tocked} >State
main = thenn tick tock
-- neg
-- main = tick >> tick


