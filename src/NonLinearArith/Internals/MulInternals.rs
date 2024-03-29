use vstd::prelude::*;

use crate::NonLinearArith::Internals::GeneralInternals::{is_le, lemma_induction_helper};
use crate::NonLinearArith::Internals::MulInternalsNonlinear as MulINL;

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
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
proof fn lemma_mul_commutes()
    ensures 
        forall |x: int, y: int| #[trigger] mul(x, y) == mul(y, x)
{}

/// proves the distributive property of multiplication when multiplying an interger
/// by (x +/- 1)
#[verifier::spinoff_prover]
proof fn lemma_mul_successor()
    ensures 
        forall |x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y,
        forall |x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y,
{
    assert forall |x:int, y:int| #[trigger]((x + 1) * y) == x * y + y by {
        MulINL::lemma_mul_is_distributive_add(y, x, 1);
    }
    
    assert forall |x:int, y:int| #[trigger]((x - 1) * y) == x * y - y by {
        assert((x - 1) * y  == y * (x - 1));
        MulINL::lemma_mul_is_distributive_add(y, x, -1);
        assert(y * (x - 1) == y * x + y * -1);
        assert(-1 * y == -y);
        assert(x * y + (-1 * y) == x * y - y);
    }
}

/// proves the distributive property of multiplication
#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
    forall |x: int, y: int, z: int| #[trigger]((x + y) * z) == (x * z + y * z),
    forall |x: int, y: int, z: int| #[trigger]((x - y) * z) == (x * z - y * z),
{
    lemma_mul_successor();

    assert forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
        by
    {
        let f1 = |i: int| ((x + i) * z) == (x * z + i * z);
        assert(f1(0));
        assert forall |i: int| i >= 0 && #[trigger] f1(i) implies #[trigger]f1(add(i, 1)) by {
            assert(  (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z);

        };
        assert forall |i: int| i <= 0 && #[trigger] f1(i) implies #[trigger]f1(sub(i, 1)) by {
            assert((x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z);
        };
        lemma_mul_induction(f1);
        assert(f1(y));


    }

    assert forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z) by {
        let f2 = |i: int| ((x - i) * z) == (x * z - i * z);
        assert(f2(0));
        assert forall |i: int| i >= 0 && #[trigger] f2(i) implies #[trigger]f2(add(i, 1)) by {
            assert(  (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z);

        };
        assert forall |i: int| i <= 0 && #[trigger] f2(i) implies #[trigger]f2(sub(i, 1)) by {
            assert((x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z);
        };

        lemma_mul_induction(f2);
        assert(f2(y));
    }

}

/// groups distributive and associative properties of multiplication
#[verifier::spinoff_prover]
pub open spec fn mul_auto() -> bool
{
    &&& forall |x:int, y:int| #[trigger](x * y) == (y * x)
    &&& forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
    &&& forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z)
}

/// proves that mul_auto is valid
#[verifier::spinoff_prover]
pub proof fn lemma_mul_auto()
    ensures  mul_auto()
{
    lemma_mul_distributes();
}

/// performs auto induction on multiplication for all i s.t. f(i) exists */
#[verifier::spinoff_prover]
pub proof fn lemma_mul_induction_auto(x: int, f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        f(x),
{
    lemma_mul_auto();
    assert (forall |i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
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