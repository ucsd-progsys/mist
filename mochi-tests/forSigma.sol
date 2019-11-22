sat
(model 
  (define-fun |loop[0:2][0:0][0:0]| ((x!0 Int) (x!1 Int)) Bool
    true)
  (define-fun |loop[0:0][0:0]| ((x!0 Int)) Bool
    true)
  (define-fun |thenn[0:0][0:1][0:1]| ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun |bind[0:2][0:0][0:0]| ((x!0 Int)) Bool
    true)
  (define-fun |thenn[0:1][0:1][0:1]| ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun |bind[0:0][0:1][0:1]| ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun |loop[0:1]| ((x!0 Int)) Bool
    true)
  (define-fun |bind[0:2][0:0][0:1][0:1]| ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun |loop[0:0][0:1][0:0][0:0]| ((x!0 Int) (x!1 Int)) Bool
    (let ((a!1 (exists ((x!2 Int)) (and (not (= x!2 0)) (= x!0 0)))))
      (or (= x!0 0) a!1)))
  (define-fun |loop[0:2][0:0][0:1][0:0][0:1][0:1]| ((x!0 Int)
   (x!1 Int)
   (x!2 Int)
   (x!3 Int)
   (x!4 Int)) Bool
    true)
  (define-fun |thenn[0:1][0:0]| ((x!0 Int)) Bool
    true)
  (define-fun |loop[0:2][0:0][0:1][0:0][0:0]| ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    (let ((a!1 (exists ((x!3 Int))
                 (and (not (= x!3 0)) (= x!0 (+ (- 1) x!3)) (= x!1 0)))))
      (or (and (= x!0 9) (= x!1 0)) (and (= x!0 8) (= x!1 0)) a!1)))
  (define-fun |bind[0:1][0:0]| ((x!0 Int)) Bool
    true)
  (define-fun |bind[0:1][0:1][0:0][0:1][0:1]| ((x!0 Int)
   (x!1 Int)
   (x!2 Int)
   (x!3 Int)) Bool
    (let ((a!1 (exists ((x!4 Int)) (and (= x!3 (+ 1 x!0)) (= x!3 (+ 1 x!4)))))
          (a!2 (exists ((x!4 Int)) (and (= x!3 (+ 4 x!0)) (= x!3 (+ 4 x!4)))))
          (a!3 (exists ((x!4 Int)) (and (= x!3 (+ 1 x!4)) (= x!3 (+ 1 x!0)))))
          (a!4 (exists ((x!4 Int)) (and (= x!3 (+ 4 x!4)) (= x!3 (+ 4 x!0))))))
      (or a!1 a!2 a!3 a!4)))
  (define-fun |loop[0:0][0:1][0:0][0:1][0:1]| ((x!0 Int)
   (x!1 Int)
   (x!2 Int)
   (x!3 Int)) Bool
    true)
  (define-fun |thenn[0:2][0:0][0:1][0:1]| ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
  (define-fun |fail_88[0:0]| ((x!0 Int)) Bool
    true)
)
