use vstd::prelude::*;

use crate::NonLinearArith::Internals::GeneralInternals::{is_le, lemma_induction_helper};

verus! {

/// performs multiplication for positive integers using recursive addition
/// change x to nat?
// NEED TO ASK, here, we either change x into nat or return 0 when x < 0
// This is because we do not have partial functions
// and the recommend clause is too weak so that we actually need to consider
// the x < 0 case
#[verifier(opaque)]
pub open spec fn mul_pos(x: int, y: int) -> int
    recommends x >= 0
    decreases x
    // any design reason for using recommends instead of requires?
{
    if x <= 0 {
        0 
    } else {
        y + mul_pos(x - 1, y) 
    }
}

/// performs multiplication for both positive and negative integers
pub open spec fn mul_recursive(x: int, y: int) -> int
{
    if x >= 0 { mul_pos(x, y) }
    else { -1 * mul_pos(-1 * x, y) }
}


/* you need these add, sub because by importing the GeneralInternals add,
    it will still complain it is an arithmetic expression */
pub open spec fn add (a: int, b: int) -> int
{
    // or a + b
    crate::NonLinearArith::Internals::GeneralInternals::add(a, b)
} 

pub open spec fn sub (a: int, b: int) -> int
{
    // or a + b
    crate::NonLinearArith::Internals::GeneralInternals::sub(a, b)
}

pub open spec fn mul (a: int, b: int) -> int
{
    a * b
}

/// performs induction on multiplication
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires 
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add(i, 1)),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub(i, 1)),
        // TODO how about this proof style? seems to distablize one or two proofs
        // forall |i: int, j:int| i >= 0 && j == i + 1 && #[trigger] f(i) ==> #[trigger] f(j),
        // forall |i: int, j:int| i <= 0 && j == i - 1 && #[trigger] f(i) ==> #[trigger] f(j),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert (forall |i: int| f(add(i, 1)) ==> #[trigger] f(crate::NonLinearArith::Internals::GeneralInternals::add(i, 1)));  // OBSERVE
    assert (forall |i: int| f(sub(i, 1)) ==> #[trigger] f(crate::NonLinearArith::Internals::GeneralInternals::sub(i, 1)));   // OBSERVE

    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

/// proves that multiplication is always commutative
#[verifier(spinoff_prover)]
proof fn lemma_mul_commutes()
    ensures 
        forall |x: int, y: int| #[trigger] mul(x, y) == mul(y, x)
{}

#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
        forall |x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z),
        forall |x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z),
{
    assume(false);
}

/// groups distributive and associative properties of multiplication
#[verifier(spinoff_prover)]
pub open spec fn mul_auto() -> bool
{
    &&& forall |x:int, y:int| #[trigger](x * y) == (y * x)
    &&& forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
    &&& forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z)
}

/// proves that mul_auto is valid
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_auto()
    ensures  mul_auto()
{
    lemma_mul_distributes();
}

/// performs auto induction on multiplication for all i s.t. f(i) exists */
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_induction_auto(x: int, f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        f(x),
{
    lemma_mul_auto();
    assume (forall |i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert (forall |i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

// not called anywhere else
// /// performs auto induction on multiplication for all i s.t. f(i) exists
// lemma LemmaMulInductionAutoForall(f: int -> bool)
//     requires MulAuto() ==> f(0)
//                         && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1))
//                         && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1))
//     ensures  MulAuto()
//     ensures  forall i {:trigger f(i)} :: f(i)
// {
//     LemmaMulCommutes();
//     LemmaMulDistributes();
//     assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
//     assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
//     LemmaMulInduction(f);
// }

}