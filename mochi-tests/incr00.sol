sat
(model 
  (define-fun |incr[0:0][0:1][0:0]| ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun |incr[0:1][0:0]| ((x!0 Int)) Bool
    (exists ((x!1 Int)) (= x!0 (+ 1 x!1))))
  (define-fun |fail_34[0:0]| ((x!0 Int)) Bool
    true)
)
