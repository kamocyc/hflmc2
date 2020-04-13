(set-logic HORN)
(set-info :source |
  Benchmark: /home/hogeyama/kenkyu-code/hflmc2/benchmark/inputs/ml/test_safe_2019/adt/all_equal.ml
  Generated by MoCHi
|)
(set-info :status unknown)
(declare-fun |fail_65[0:0]| ( Int) Bool)
(declare-fun |all_equal[0:2][0:1][0:0]| ( Int  Int  Int  Int) Bool)
(declare-fun |all_equal[0:1]| ( Int  Int) Bool)
(declare-fun |replicate[0:2][0:1][0:1][0:0]| ( Int  Int  Int  Int  Int) Bool)
(declare-fun |replicate[0:2][0:0]| ( Int  Int  Int) Bool)
(declare-fun |replicate[0:1]| ( Int  Int) Bool)
(assert (not (exists ((x0 Int)) (|fail_65[0:0]| x0))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (and (|all_equal[0:2][0:1][0:0]| x2 x1 0 x3) (and (|all_equal[0:1]| x2 x1) (and (>= x1 1) (not (= x2 x3))))) (|fail_65[0:0]| x0))))
(assert (forall ((x3 Int)(x4 Int)(x1 Int)(x2 Int)(x0 Int)) (=> (and (|all_equal[0:1]| x3 x4) (and (|replicate[0:2][0:1][0:1][0:0]| x3 x0 x4 x1 x2) (|replicate[0:2][0:0]| x3 x0 x4))) (|all_equal[0:2][0:1][0:0]| x3 x4 x1 x2))))
(assert (forall ((x2 Int)(x3 Int)(x4 Int)(x0 Int)(x1 Int)(var360 Int)(var365 Int)(var364 Int)(var361 Int)(var363 Int)(var362 Int)) (=> (and (|replicate[0:2][0:0]| x2 var364 var365) (and (|replicate[0:2][0:0]| x2 var361 var362) (and (|replicate[0:2][0:1][0:1][0:0]| x2 var361 var362 var363 x1) (and (|replicate[0:2][0:0]| x2 x3 x4) (and (|replicate[0:1]| x2 x3) (and (= var360 (+ 1 var365)) (and (= x4 (+ 1 var365)) (and (= (+ 1 var364) x3) (and (= (+ 1 var361) x3) (and (= (+ 1 var363) x0) (and (not (= x0 0)) (>= x3 1)))))))))))) (|replicate[0:2][0:1][0:1][0:0]| x2 x3 x4 x0 x1))))
(assert (forall ((x2 Int)(x3 Int)(x4 Int)(x0 Int)(x1 Int)(var368 Int)(var370 Int)(var369 Int)) (=> (and (|replicate[0:2][0:0]| x2 var369 var370) (and (|replicate[0:2][0:0]| x2 x3 x4) (and (|replicate[0:1]| x2 x3) (and (= var368 (+ 1 var370)) (and (= x4 (+ 1 var370)) (and (= (+ 1 var369) x3) (and (= x0 0) (and (>= x3 1) (= x1 x2))))))))) (|replicate[0:2][0:1][0:1][0:0]| x2 x3 x4 x0 x1))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(var377 Int)(var376 Int)) (=> (and (|replicate[0:1]| x1 x0) (and (|replicate[0:2][0:0]| x1 var376 var377) (and (= x2 (+ 1 var377)) (and (>= x0 1) (= (+ 1 var376) x0))))) (|replicate[0:2][0:0]| x1 x0 x2))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)) (=> (and (|replicate[0:1]| x1 x2) (and (= x0 0) (<= x2 0))) (|replicate[0:2][0:0]| x1 x2 x0))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (and (|replicate[0:1]| x1 x2) (and (= (+ 1 x0) x2) (>= x2 1))) (|replicate[0:1]| x1 x0))))
(assert (forall ((x3 Int)(x0 Int)(x1 Int)(x4 Int)(var379 Int)(x2 Int)(var378 Int)) (=> (and (|replicate[0:2][0:0]| x3 var378 x2) (and (|replicate[0:1]| x3 x1) (and (= (+ 1 x0) x1) (and (not (= x4 0)) (and (= var379 (+ 1 x2)) (and (= (+ 1 var378) x1) (>= x1 1))))))) (|replicate[0:1]| x3 x0))))
(assert (forall ((x0 Int)(x2 Int)(x1 Int)) (=> (|replicate[0:2][0:0]| x0 x1 x2) (|all_equal[0:1]| x0 x2))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(var381 Int)(var380 Int)) (=> (and (|replicate[0:1]| x1 x0) (and (|replicate[0:2][0:0]| x1 var380 var381) (and (= x2 (+ 1 var381)) (and (>= x0 1) (= (+ 1 var380) x0))))) (|replicate[0:2][0:0]| x1 x0 x2))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)) (=> (and (|replicate[0:1]| x1 x2) (and (= x0 0) (<= x2 0))) (|replicate[0:2][0:0]| x1 x2 x0))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (and (|replicate[0:1]| x1 x2) (and (= (+ 1 x0) x2) (>= x2 1))) (|replicate[0:1]| x1 x0))))
(assert (forall ((x0 Int)(x1 Int)) (|replicate[0:1]| x0 x1)))
(check-sat)
(get-model)
(exit)