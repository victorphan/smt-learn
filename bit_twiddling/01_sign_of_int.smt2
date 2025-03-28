; Compute the sign of an integer

; int v;      // we want to find the sign of v
(declare-const v (_ BitVec 32))

; if v < 0 then -1, else 0.
(define-fun spec_sign ((v (_ BitVec 32))) (_ BitVec 32)
    (ite (bvslt v (_ bv0 32)) (bvneg (_ bv1 32)) (_ bv0 32))
)

; // CHAR_BIT is the number of bits per byte (normally 8).
; sign = -(v < 0);
(define-fun sign0 ((v (_ BitVec 32))) (_ BitVec 32)
    (bvneg (ite (bvslt v (_ bv0 32)) (_ bv1 32) (_ bv0 32)))
)

(push 1)
(assert (not (= (spec_sign v) (sign0 v))))
(check-sat)
(pop 1)

; // or, to avoid branching on CPUs with flag registers (IA32):
; sign = -(int)((unsigned int)((int)v) >> (sizeof(int) * CHAR_BIT - 1));
(define-fun sign1 ((v (_ BitVec 32))) (_ BitVec 32)
    (bvneg (bvlshr v (_ bv31 32)))
)

(push 1)
(assert (not (= (spec_sign v) (sign1 v))))
(check-sat)
(pop 1)

; // or, for one less instruction (but not portable):
; sign = v >> (sizeof(int) * CHAR_BIT - 1);
(define-fun sign2 ((v (_ BitVec 32))) (_ BitVec 32)
    (bvashr v (_ bv31 32))
)

(push 1)
(assert (not (= (spec_sign v) (sign2 v))))
(check-sat)
(pop 1)

; victorphan: my implementation, extract sign bit and then sign extend
(define-fun sign3 ((v (_ BitVec 32))) (_ BitVec 32)
    ((_ sign_extend 31) ((_ extract 31 31) v))
)

(push 1)
(assert (not (= (spec_sign v) (sign3 v))))
(check-sat)
(pop 1)