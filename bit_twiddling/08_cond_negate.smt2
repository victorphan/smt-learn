; Conditionally negate a value without branching

(declare-const in_f Bool)
(declare-const in_v (_ BitVec 32))

; fDontNegate ? v : -v;
(define-fun spec_cond_negate ((f Bool) (v (_ BitVec 32))) (_ BitVec 32)
    (ite f v (bvneg v))
)

; r = (fDontNegate ^ (fDontNegate - 1)) * v;
(define-fun impl_cond_negate ((f Bool) (v (_ BitVec 32))) (_ BitVec 32)
(let (
(f_int (ite f (_ bv1 32) (_ bv0 32)))
)
(bvmul (bvxor f_int (bvsub f_int (_ bv1 32))) v)
)
)

(push)
(echo "spec_cond_negate != impl_cond_negate")
(assert (not (= (spec_cond_negate in_f in_v) (impl_cond_negate in_f in_v))))
(check-sat)
(echo "")
(pop)