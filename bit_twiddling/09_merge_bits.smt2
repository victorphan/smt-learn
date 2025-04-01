; Merge bits from two values according to a mask

; (a & ~mask) | (b & mask)
(define-fun spec_merge_bits ((a (_ BitVec 32)) (b (_ BitVec 32)) (mask (_ BitVec 32))) (_ BitVec 32)
(bvor (bvand a (bvnot mask)) (bvand b mask))
)

; r = a ^ ((a ^ b) & mask);
(define-fun impl_merge_bits ((a (_ BitVec 32)) (b (_ BitVec 32)) (mask (_ BitVec 32))) (_ BitVec 32)
(bvxor a (bvand (bvxor a b) mask))
)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const mask (_ BitVec 32))

(push)
(echo "spec_merge_bits != impl_merge_bits")
(assert (not (= (spec_merge_bits a b mask) (impl_merge_bits a b mask))))
(check-sat)
(echo "")
(pop)