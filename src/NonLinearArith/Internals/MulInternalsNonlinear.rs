
/** Declares some helper lemmas about multiply, for internal use */

/* WARNING: Think three times before adding to this file, as nonlinear
verification is highly unstable! */

// may be try to use singular?
use vstd::prelude::*;

verus! {

/* multiplying two positive integers will result in a positive integer */
#[verifier(nonlinear)]
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
{}

/* Integral Domain */
/* multiplying two nonzero integers will never result in 0 as the poduct */
#[verifier(nonlinear)]
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
{}

/* multiplication is associative */
#[verifier(nonlinear)]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
{}

/* multiplication is distributive */
#[verifier(nonlinear)]
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
{}

/* the product of two integers is greater than the value of each individual integer */
#[verifier(nonlinear)]
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires 
        x != 0,
        y != 0,
        0 <= x * y
    ensures 
        x * y >= x && x * y >= y
{}

/* multiplying by a positive integer preserves inequality */
#[verifier(nonlinear)]
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0
    ensures
        x * z < y * z
{}

// TODO
// failed to play around with integer rings

// spec fn dist1 (x: int, y: int, m:int) -> bool
// {
//   (x-y) % m == 0
// }

// spec fn mod_dist2 (x: int, y: int, z:int, m:int) -> bool
// {
//   (x*z - y*z) % m == 0
// }

// #[verifier(integer_ring)]
// // #[verifier(nonlinear)]
// proof fn simple_modulo(x: int, y: int, z:int, m:int)
//   requires ( (x - y) % m == 0 )
//   ensures  ( (x * z - y * z) % m == 0 )
// {
// }

}