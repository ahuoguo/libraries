//! Lemma for multiplication

/* Every lemma comes in 2 forms: 'LemmaProperty' and 'LemmaPropertyAuto'. The
former takes arguments and may be more stable and less reliant on Z3
heuristics. The latter includes automation and its use requires less effort */

use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternalsNonlinear as MulINL;

use crate::NonLinearArith::Internals::MulInternal::*;

/// The built-in syntax of multiplication results in the same product as multiplication
/// through recursive addition
pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
    ensures (x * y) == mul_recursive(x, y)
{
    if (x >= 0) { 
        lemma_mul_is_mul_pos(x, y);
        assert (x * y == mul_pos(x, y));
    }
    else { 
        lemma_mul_is_mul_pos(-x, y);
        assert (-x * y == mul_pos(-x, y));
    }
}

pub proof fn lemma_mul_is_mul_recursive_auto()
    ensures forall |x: int, y: int| x * y == mul_recursive(x, y)
{
    assert forall |x: int, y: int| x * y == mul_recursive(x, y) by { 
        lemma_mul_is_mul_recursive(x, y) };
}

/// the built-in syntax of multiplying two positive integers results in the same product as 
/// MulPos, which is achieved by recursive addition
proof fn lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
{
    // How does dafny `reveal` work, and why is it different here in verus?
    lemma_mul_induction_auto(x, |u: int| u >= 0 ==> u * y == mul_pos(u, y));
}

}