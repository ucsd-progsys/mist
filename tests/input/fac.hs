def fac(n):
  let t = print(n) in
  if (n < 1):
    1
  else:
    n * fac(n - 1)
in
fac(5)
