; n-Queens problem with representation row -> col. The datastructure necessarily guarantees
; that each queen will be on a unique row now without the need for a constraint

(declare-const queens (Array Int Int))
(declare-const n Int)
(assert (= n 8))

; Constrain integers between valid values for both the coordinate components and also the queen array index
(define-fun in_bounds ((x Int)) Bool (and (>= x 0) (< x n)))

(assert (forall ((i Int)) (=> (in_bounds i) (in_bounds (select queens i)))))

(assert (forall ((i Int) (j Int))
    (=> (and (in_bounds i) (in_bounds j) (not (= i j)))
        (and (not (= (select queens i) (select queens j)))
             (not (= (abs (- i j)) (abs (- (select queens i) (select queens j)))))
        )
    )))

(check-sat)
(get-value ((select queens 0)
            (select queens 1)
            (select queens 2)
            (select queens 3)
            (select queens 4)
            (select queens 5)
            (select queens 6)
            (select queens 7))
)
; Solution produced after ~3s in z3
; (0, 5), (1, 2), (2, 0), (3, 7), (4, 3), (5, 1), (6, 6), (7, 4)