; Compute the sign of an integer

; int v;      // we want to find the sign of v
(declare-const v (_ BitVec 32))

; if v < 0 then -1, else 0.
(define-fun spec_sign ((v (_ BitVec 32))) (_ BitVec 32)
    (ite (bvslt v (_ bv0 32)) (bvneg (_ bv1 32)) (_ bv0 32))
)

; CHAR_BIT is the number of bits per byte (normally 8).
; sign = -(v < 0);
(define-fun impl0_sign ((v (_ BitVec 32))) (_ BitVec 32)
    (bvneg (ite (bvslt v (_ bv0 32)) (_ bv1 32) (_ bv0 32)))
)

(push 1)
(assert (not (= (spec_sign v) (impl0_sign v))))
(check-sat)
(pop 1)

; or, to avoid branching on CPUs with flag registers (IA32):
; sign = -(int)((unsigned int)((int)v) >> (sizeof(int) * CHAR_BIT - 1));
(define-fun impl1_sign ((v (_ BitVec 32))) (_ BitVec 32)
    (bvneg (bvlshr v (_ bv31 32)))
)

(push 1)
(assert (not (= (spec_sign v) (impl1_sign v))))
(check-sat)
(pop 1)

; or, for one less instruction (but not portable):
; sign = v >> (sizeof(int) * CHAR_BIT - 1);
(define-fun impl2_sign ((v (_ BitVec 32))) (_ BitVec 32)
    (bvashr v (_ bv31 32))
)

(push 1)
(assert (not (= (spec_sign v) (impl2_sign v))))
(check-sat)
(pop 1)

; victorphan: my implementation, extract sign bit and then sign extend
(define-fun impl3_sign ((v (_ BitVec 32))) (_ BitVec 32)
    ((_ sign_extend 31) ((_ extract 31 31) v))
)

(push 1)
(assert (not (= (spec_sign v) (impl3_sign v))))
(check-sat)
(pop 1)

; Alternatively, if you prefer the result be either -1 or +1, then use:
; if v < 0 then -1, else +1
(define-fun spec_sign_alt ((v (_ BitVec 32))) (_ BitVec 32)
    (ite (bvslt v (_ bv0 32)) (bvneg (_ bv1 32)) (_ bv1 32))
)

; sign = +1 | (v >> (sizeof(int) * CHAR_BIT - 1));
(define-fun impl_sign_alt ((v (_ BitVec 32))) (_ BitVec 32)
    (bvor (_ bv1 32) (bvashr v (_ bv31 32)))
)

(push 1)
(assert (not (= (spec_sign_alt v) (impl_sign_alt v))))
(check-sat)
(pop 1)

; On the other hand, if you prefer the result be either -1, 0, or +1, then use:
(define-fun spec_sign_with_eq_zero ((v (_ BitVec 32))) (_ BitVec 32)
    (ite (bvslt v (_ bv0 32)) (bvneg (_ bv1 32)) (ite (= v (_ bv0 32)) (_ bv0 32) (_ bv1 32)))
)

(define-fun spec_sign_with_eq_zero_alt ((v (_ BitVec 32))) (_ BitVec 32)
    (bvor (ite (not (= v (_ bv0 32))) (_ bv1 32) (_ bv0 32))
        (spec_sign v)
    )
)

(push 1)
(assert (not (= (spec_sign_with_eq_zero v) (spec_sign_with_eq_zero_alt v))))
(check-sat)
(pop 1)

; sign = (v != 0) | -(int)((unsigned int)((int)v) >> (sizeof(int) * CHAR_BIT - 1));
(define-fun impl0_sign_with_eq_zero ((v (_ BitVec 32))) (_ BitVec 32)
    (bvor (ite (not (= v (_ bv0 32))) (_ bv1 32) (_ bv0 32))
        (bvneg (bvlshr v (_ bv31 32)))
    )
)

(push 1)
(assert (not (= (spec_sign_with_eq_zero v) (impl0_sign_with_eq_zero v))))
(check-sat)
(pop 1)

; Or, for more speed but less portability:
; sign = (v != 0) | (v >> (sizeof(int) * CHAR_BIT - 1));  // -1, 0, or +1
(define-fun impl1_sign_with_eq_zero ((v (_ BitVec 32))) (_ BitVec 32)
    (bvor (ite (not (= v (_ bv0 32))) (_ bv1 32) (_ bv0 32))
        (bvashr v (_ bv31 32))
    )
)

(push 1)
(assert (not (= (spec_sign_with_eq_zero v) (impl1_sign_with_eq_zero v))))
(check-sat)
(pop 1)

; // Or, for portability, brevity, and (perhaps) speed:
; sign = (v > 0) - (v < 0); // -1, 0, or +1
(define-fun impl2_sign_with_eq_zero ((v (_ BitVec 32))) (_ BitVec 32)
    (bvsub (ite (bvsgt v (_ bv0 32)) (_ bv1 32) (_ bv0 32))
        (ite (bvslt v (_ bv0 32)) (_ bv1 32) (_ bv0 32)))
)

(push 1)
(assert (not (= (spec_sign_with_eq_zero v) (impl2_sign_with_eq_zero v))))
(check-sat)
(pop 1)

; If instead you want to know if something is non-negative, resulting in +1 or else 0, then use:
; if v < 0 then 0, else 1
(define-fun spec_non_negative ((v (_ BitVec 32))) (_ BitVec 32)
    (ite (bvslt v (_ bv0 32)) (_ bv0 32) (_ bv1 32))
)

; sign = 1 ^ ((unsigned int)v >> (sizeof(int) * CHAR_BIT - 1));
(define-fun impl_non_negative ((v (_ BitVec 32))) (_ BitVec 32)
    (bvxor (_ bv1 32) (bvlshr v (_ bv31 32)))
)

(push 1)
(assert (not (= (spec_non_negative v) (impl_non_negative v))))
(check-sat)
(pop 1)
