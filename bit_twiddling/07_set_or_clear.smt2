; Conditionally set or clear bits without branching

(declare-const in_f Bool)
(declare-const in_w (_ BitVec 32))
(declare-const in_m (_ BitVec 32))

; if (f) w |= m; else w &= ~m;
(define-fun spec_set_or_clear ((f Bool) (w (_ BitVec 32)) (m (_ BitVec 32))) (_ BitVec 32)
    (ite f (bvor w m) (bvand w (bvnot m)))
)

; w ^= (-f ^ w) & m;
(define-fun impl0_set_or_clear ((f Bool) (w (_ BitVec 32)) (m (_ BitVec 32))) (_ BitVec 32)
    (bvxor w (bvand (bvxor (bvneg (ite f (_ bv1 32) (_ bv0 32))) w) m))
)

(push 1)
(echo "spec_set_or_clear != impl0_set_or_clear")
(assert (not (= (spec_set_or_clear in_f in_w in_m) (impl0_set_or_clear in_f in_w in_m))))
(check-sat)
(echo "")
(pop 1)

; w = (w & ~m) | (-f & m);
(define-fun impl1_set_or_clear ((f Bool) (w (_ BitVec 32)) (m (_ BitVec 32))) (_ BitVec 32)
    (bvor (bvand w (bvnot m)) (bvand (bvneg (ite f (_ bv1 32) (_ bv0 32))) m))
)

(push 1)
(echo "spec_set_or_clear != impl1_set_or_clear")
(assert (not (= (spec_set_or_clear in_f in_w in_m) (impl1_set_or_clear in_f in_w in_m))))
(check-sat)
(echo "")
(pop 1)
