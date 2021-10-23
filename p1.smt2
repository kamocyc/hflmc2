(model
  (define-fun X2
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) Bool
    (and
      (or (and (>= v_0 0)
            (= v_1 0)
            (= v_2 0)
            (>= (+ v_5 (* (- 1) v_3)) 1)
            (>= (+ v_5 (* v_0 (- 1))) 1)
            (>= (+ v_5 v_3) 1)
            (>= (+ v_4 (* (- 1) v_0) (* v_2 (- 1))) 2))
        (and (>= v_0 0)
            (>= (+ v_5 (* (- 1) v_0)) 1)
            (>= v_4 3)
            (>= (+ v_4 v_0 (* (- 1) v_1)) 2)
            (>= (+ v_4 (* (- 1) v_0) (* (- 1) v_2)) 2)))
      (>= v_5 1)
    )
  )
  (define-fun X84
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (>= v_1 1) (>= (+ v_1 (* (- 1) v_0)) 1))
  )
  (define-fun X3
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    true
  )
  (define-fun X1
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (or (and (>= v_1 0)
            (= v_2 0)
            (= v_3 0)
            (>= (+ v_6 (* (- 1) v_4)) 1)
            (>= (+ v_6 (* v_1 (- 1))) 1)
            (>= (+ v_6 v_4) 1)
            (>= (+ v_5 (* v_1 (- 1)) (* v_3 (- 1))) 2))
      (and (>= v_1 0)
            (>= (+ v_6 (* (- 1) v_1)) 1)
            (>= v_5 3)
            (>= (+ v_5 v_1 (* v_2 (- 1))) 2)
            (>= (+ v_5 (* (- 1) v_1) (* v_3 (- 1))) 2)))
  )

  (define-fun X137
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (and
      (>= v_1 1)
      (>= (+ v_6 (* (- 1) v_1)) 1)
      (>= v_5 3)
      (>= (+ v_5 v_1 (* v_2 (- 1))) 2)
      (>= (+ v_5 (* (- 1) v_1) (* v_3 (- 1))) 2)
    )
  )

  (define-fun X136
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    false
  )
  (define-fun X135
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    false
  )
  (define-fun X134
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (and
      (>= v_1 1)
      (>= (+ v_6 (* (- 1) v_1)) 1)
      (>= v_5 3)
      (>= (+ v_5 v_1 (* v_2 (- 1))) 2)
      (>= (+ v_5 (* (- 1) v_1) (* v_3 (- 1))) 2)
    )
  )

  (define-fun X133
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) ) Bool
    (and
        (<= v_0 0)
      (or (and (>= v_0 0)
              (= v_1 0)
              (= v_2 0)
              (>= (+ v_5 (* v_3 (- 1))) 1)
              (>= (+ v_5 v_3) 1)
              (>= (+ v_4 (* (- 1) v_0) (* v_2 (- 1))) 2))
          (and (>= v_0 0) (>= v_4 3) (>= (+ v_4 v_0 (* v_1 (- 1))) 2) (>= (+ v_4 (* (- 1) v_0) (* v_2 (- 1))) 2)))
    (>= v_5 1))
  )
  (define-fun X10
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (and
        (>= v_1 1)
    (>= (+ v_6 (* (- 1) v_1)) 1)
    (>= v_5 3)
    (>= (+ v_5 v_1 (* v_2 (- 1))) 2)
    (>= (+ v_5 (* (- 1) v_1) (* v_3 (- 1))) 2))
  )
  (define-fun X131
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (and
        (>= (+ v_0 (* (- 1) v_1)) 1)
    (>= v_2 1)
    (>= (+ v_0 (* v_2 (- 1))) 0)
    (>= (+ v_1 v_0) 1)
    (>= (+ v_3 (* (- 1) v_2)) 1))
  )
  (define-fun X130
    ( (v_0 Int) (v_1 Int) ) Bool
    (and   (>= (+ v_0 (* (- 1) v_1)) 1)
    (>= (+ v_1 v_0) 1))
  )

  (define-fun X118
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun X117
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun X116
    ( ) Bool
    true
  )
  (define-fun X93
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (and 
        (>= v_2 1)
    (>= (+ v_3 (* (- 1) v_2)) 1))
  )
  (define-fun X92
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (and
      (>= v_1 1)
      (>= (+ v_2 (* (- 1) v_1)) 1))
  )
  (define-fun X85
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (or (and (>= v_2 1) (>= (+ v_2 (* (- 1) v_1)) 1))
      (exists ((v_4!1 Int) (v_3!1 Int))
        (and (>= v_1 1)
              (>= (+ v_4!1 v_3!1) 1)
              (>= v_4!1 1)
              (>= (+ v_4!1 (* (- 1) v_1)) 0)
              (>= (+ v_4!1 (* (- 1) v_3!1)) 1)
              (and (>= v_2 1) (>= (+ v_2 (* (- 1) v_1)) 1))
              (or (and (>= (+ v_1 (- 1)) 0)
                      (= 0 0)
                      (= 0 0)
                      (>= (+ v_4!1 (* (- 1) v_3!1)) 1)
                      (>= (+ v_4!1 (* (+ v_1 (- 1)) (- 1))) 1)
                      (>= (+ v_4!1 v_3!1) 1)
                      (>= (+ v_2 (* (- 1) (+ v_1 (- 1))) (* 0 (- 1))) 2))
                  (and (>= (+ v_1 (- 1)) 0)
                      (>= (+ v_4!1 (* (- 1) (+ v_1 (- 1)))) 1)
                      (>= v_2 3)
                      (>= (+ v_2 (+ v_1 (- 1)) (* (- 1) 0)) 2)
                      (>= (+ v_2 (* (- 1) (+ v_1 (- 1))) (* (- 1) 0)) 2)))
              (>= v_4!1 1)
              true)))
  )
  (define-fun X83
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (and
        (>= v_2 1)
    (>= (+ v_2 (* (- 1) v_1)) 1))
  )
  (define-fun X132
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) (v_4 Int) (v_5 Int) (v_6 Int) ) Bool
    (and
        (<= v_1 0)
    (or (and (>= v_1 0)
            (= v_2 0)
            (= v_3 0)
            (>= (+ v_6 (* (- 1) v_4)) 1)
            (>= (+ v_6 v_4) 1)
            (>= (+ v_5 (* v_1 (- 1)) (* v_3 (- 1))) 2))
        (and (>= v_1 0)
            (>= v_5 3)
            (>= (+ v_5 v_1 (* v_2 (- 1))) 2)
            (>= (+ v_5 (* (- 1) v_1) (* v_3 (- 1))) 2)))
    (>= v_6 1))
  )
)