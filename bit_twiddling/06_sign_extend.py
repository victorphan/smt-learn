# Sign extending from a variable bit-width
# Sometimes we need to extend the sign of a number but we don't know a priori the number of bits, b, in which it is represented.

# unsigned b; // number of bits representing the number in x
# int x;      // sign extend this b-bit number to r
# int r;      // resulting sign-extended number
# int const m = 1U << (b - 1); // mask can be pre-computed if b is fixed
# x = x & ((1U << b) - 1);  // (Skip this if bits in x above position b are already zero.)
# r = (x ^ m) - m;

from z3 import *

s = Solver()

for b in range(1, 33):
    s.push()
    mask = BitVec('mask', 32)
    s.add(mask == 1 << (b - 1))
    x = BitVec('x', b)
    r = BitVec('r', 32)
    s.add(r == (ZeroExt(32 - b, x) ^ mask) - mask)

    s.add(Not(SignExt(32 - b, x) == r))

    print(f'b = {b}: {s.check()}')
    s.pop()