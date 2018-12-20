let x = 100, 
    y = print(sub1(add1(x))),
    z = if x == y:
	      let tmp = print(true) in
          x + x
   	    else:
		  let tmp = print(false) in
	      x - x 
in
   z
