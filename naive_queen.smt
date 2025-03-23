; Naive n-Queens formulation
; Keep track of an array of coordinates representing the placement of Queens
(declare-datatype Coord ((c (x Int) (y Int))))
(declare-const queens (Array Int Coord))
(declare-const n Int)
(assert (= n 8))

; Constrain integers between valid values for both the coordinate components and also the queen array index
(define-fun in_bounds ((x Int)) Bool (and (>= x 0) (< x n)))

(assert
    (forall ((i Int)) 
        (=> (in_bounds i)
            (and (in_bounds (x (select queens i)))
                 (in_bounds (y (select queens i)))))))

; Define a function which indicates whether two queens are attacking each other
(define-fun see ((q1 Coord) (q2 Coord)) Bool
    (or (or (= (x q1) (x q2)) (= (y q1) (y q2))) ; horizontal and vertical sights
        (exists ((a Int))
            (or (and (= (+ (x q1) a) (x q2)) (= (+ (y q1) a) (y q2))) ; diagonal sights
                (and (= (+ (x q1) a) (x q2)) (= (- (y q1) a) (y q2)))
    ))))

; Formulation of the problem; all pairs of queens should not be able to 'see' each other
; (assert (forall ((i Int) (j Int))
;     (=> (and (and (in_bounds i) (in_bounds j)) (not (= i j)))
;     (not (see (select queens i) (select queens j))))))
; This one doesn't converge after an hour of running

(define-fun dont_see ((qns (Array Int Coord)) (i Int) (j Int)) Bool (not (see (select qns i) (select qns j))))

; More explicit formulation
(assert
(and
(dont_see queens 0 1) (dont_see queens 0 2) (dont_see queens 0 3) (dont_see queens 0 4) (dont_see queens 0 5) (dont_see queens 0 6) (dont_see queens 0 7)
(dont_see queens 1 2) (dont_see queens 1 3) (dont_see queens 1 4) (dont_see queens 1 5) (dont_see queens 1 6) (dont_see queens 1 7)
(dont_see queens 2 3) (dont_see queens 2 4) (dont_see queens 2 5) (dont_see queens 2 6) (dont_see queens 2 7)
(dont_see queens 3 4) (dont_see queens 3 5) (dont_see queens 3 6) (dont_see queens 3 7)
(dont_see queens 4 5) (dont_see queens 4 6) (dont_see queens 4 7)
(dont_see queens 5 6) (dont_see queens 5 7)
(dont_see queens 6 7)
)
)
; Solution produced in a couple seconds:
; (2, 4), (3, 6), (0, 5), (4, 0), (7, 7), (6, 1), (5, 3), (1, 2)

(check-sat)
(get-value (queens))
; (get-model)