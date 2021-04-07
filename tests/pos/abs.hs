abz :: Int -> {v: Int | (0 <= v)}
abz = \ n ->
  if n < 0
    then 0 - n
    else n

