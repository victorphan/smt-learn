; Detect if two integers have opposite signs

(declare-const in_x (_ BitVec 32))
(declare-const in_y (_ BitVec 32))

; true iff x and y have opposite signs
(define-fun spec_opposite_signs ((x (_ BitVec 32)) (y (_ BitVec 32))) Bool
    (ite (= (bvsge x (_ bv0 32)) (bvsge y (_ bv0 32))) false true)
)

; bool f = ((x ^ y) < 0);
(define-fun impl_opposite_signs ((x (_ BitVec 32)) (y (_ BitVec 32))) Bool
    (ite (bvslt (bvxor x y) (_ bv0 32)) true false)
)

(push 1)
(echo "spec_opposite_signs != impl_opposite_signs")
(assert (not (= (spec_opposite_signs in_x in_y) (impl_opposite_signs in_x in_y))))
(check-sat)
(echo "")
(pop 1)