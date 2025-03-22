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
(assert (forall ((i Int) (j Int))
    (=> (and (and (in_bounds i) (in_bounds j)) (not (= i j)))
    (not (see (select queens i) (select queens j))))))

(check-sat)
(get-model)