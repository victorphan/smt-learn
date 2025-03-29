; Compute the integer absolute value (abs) without branching

; int v;           // we want to find the absolute value of v
(declare-const in (_ BitVec 32))

(define-fun spec_abs ((v (_ BitVec 32))) (_ BitVec 32)
    (ite (bvslt v (_ bv0 32)) (bvneg v) v)
)

; int const mask = v >> sizeof(int) * CHAR_BIT - 1;
; r = (v + mask) ^ mask;
(define-fun impl0_abs ((v (_ BitVec 32))) (_ BitVec 32)
    (let (
        (mask (bvashr v (_ bv31 32)))
    )
    (bvxor (bvadd v mask) mask)
    )
)

(push 1)
(echo "spec_abs != impl0_abs")
(assert (not (= (spec_abs in) (impl0_abs in))))
(check-sat)
(echo "")
(pop 1)

; Patented variation:
; r = (v ^ mask) - mask;
(define-fun impl1_abs ((v (_ BitVec 32))) (_ BitVec 32)
    (let (
        (mask (bvashr v (_ bv31 32)))
    )
    (bvsub (bvxor v mask) mask)
    )
)

(push 1)
(echo "spec_abs != impl1_abs")
(assert (not (= (spec_abs in) (impl1_abs in))))
(check-sat)
(echo "")
(pop 1)
