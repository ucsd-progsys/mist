abz :: Int -> {v: Int | v >0}
abz = (\ n -> 
	   if n < 0 
         then 0 - n
         else n
      )

top :: {v: Int | v == 5}
top = ( let t0 = (abz 0) in 
		let t1 = (abz 5) in
          (abz (t0 - t1))
      )
