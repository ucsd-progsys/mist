(set-logic HORN)
(set-info :source |
  Benchmark: /home/atondwal/src/mist/mochi-tests/incr00.ml
  Generated by MoCHi
|)
(set-info :status unknown)
(declare-fun |fail_34[0:0]| ( Int) Bool)
(declare-fun |incr[0:1][0:0]| ( Int) Bool)
(declare-fun |incr[0:0][0:1][0:0]| ( Int  Int) Bool)
(assert (not (exists ((x0 Int)) (|fail_34[0:0]| x0))))
(assert (forall ((x0 Int)(x3 Int)) (=> (and (|incr[0:1][0:0]| x3) (|incr[0:1][0:0]| 11)) (|fail_34[0:0]| x0))))
(assert (forall ((x0 Int)(var46 Int)) (=> (and (|incr[0:0][0:1][0:0]| 0 var46) (= x0 (+ 1 var46))) (|incr[0:1][0:0]| x0))))
(assert (forall ((x2 Int)(x3 Int)) (=> (|incr[0:1][0:0]| 11) (|incr[0:0][0:1][0:0]| x2 x3))))
(assert (forall ((x0 Int)(var47 Int)) (=> (and (|incr[0:0][0:1][0:0]| 0 var47) (= x0 (+ 1 var47))) (|incr[0:1][0:0]| x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (= x1 10) (|incr[0:0][0:1][0:0]| x0 x1))))
(check-sat)
(get-model)
(exit)
