; Determining if an integer is a power of 2
(declare-const in (_ BitVec 32))

(define-fun spec_is_pow2 ((v (_ BitVec 32))) Bool
    (exists ((n (_ BitVec 32))) (and (not (= v (_ bv0 32))) (= v (bvshl (_ bv1 32) n))))
)

; f = (v & (v - 1)) == 0;
(define-fun impl0_is_pow2 ((v (_ BitVec 32))) Bool
    (= (bvand v (bvsub v (_ bv1 32))) (_ bv0 32))
)

(push 1)
(echo "spec_is_pow2 != impl0_is_pow2: expect sat")
(assert (not (= (spec_is_pow2 in) (impl0_is_pow2 in))))
(check-sat)
(get-value (in))
(eval (spec_is_pow2 in))
(eval (impl0_is_pow2 in))
(echo "")
(push 1)
; Note that 0 is incorrectly considered a power of 2 here.
(echo "spec_is_pow2 != impl0_is_pow2, in != 0: expect unsat")
(assert (not (= in (_ bv0 32))))
(check-sat)
(echo "")
(pop 2)

; f = v && !(v & (v - 1));
(define-fun impl1_is_pow2 ((v (_ BitVec 32))) Bool
    (and (not (= v (_ bv0 32))) (= (bvand v (bvsub v (_ bv1 32))) (_ bv0 32)))
)


(push 1)
(echo "spec_is_pow2 != impl1_is_pow2: expect unsat")
(assert (not (= (spec_is_pow2 in) (impl1_is_pow2 in))))
(check-sat)
(echo "")
(pop 1)