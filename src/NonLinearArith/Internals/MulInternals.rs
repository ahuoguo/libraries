use vstd::prelude::*;

#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternalsNonlinear::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternalsNonlinear::*;

use crate::NonLinearArith::Internals::GeneralInternals::*;

verus! {

/// performs multiplication for positive integers using recursive addition
/// change x to nat?

// NEED TO ASK, here, we either change x into nat or return 0 when x < 0
// This is because we do not have partial functions
// and the recommend clause is too weak so that we actually need to consider
// the x < 0 case
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
spec fn add (a: int, b: int) -> int
{
    // or a + b
    crate::NonLinearArith::Internals::GeneralInternals::add(a, b)
} 

spec fn sub (a: int, b: int) -> int
{
    // or a + b
    crate::NonLinearArith::Internals::GeneralInternals::sub(a, b)
}

pub open spec fn mul (a: int, b: int) -> int
{
    a * b
}

/// performs induction on multiplication
/* TODO */
/* HOW TO LET THE ADD/add COMMUNICATE */
/* NEED REVIEW */
proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires 
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add(i, 1)),
        forall |i: int, j:int| i>=0 && j == i+1 && #[trigger] f(i) ==> #[trigger] f(j),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub(i, 1)),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert (forall |i: int| f(add(i, 1)) ==> #[trigger] f(crate::NonLinearArith::Internals::GeneralInternals::add(i, 1)));  // OBSERVE
    assert (forall |i: int| f(sub(i, 1)) ==> #[trigger] f(crate::NonLinearArith::Internals::GeneralInternals::sub(i, 1)));   // OBSERVE

    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

/// proves that multiplication is always commutative
proof fn lemma_mul_commutes()
    ensures 
        forall |x: int, y: int| #[trigger] mul(x, y) == mul(y, x)
{
    // not important
    // assert forall |x:int, y:int| (mul(x, y) == mul(y, x)) by { lemma_mul_induction(|i: int| x * i == i * x) };
}

spec fn dist_base_add(x:int, y:int) -> int
{
    x * y + y
}

spec fn dist_base_sub(x:int, y:int) -> int
{
    x * y - y
}

pub open spec fn dist_left_add (a: int, b: int, c: int) -> int
{
    (a + b) * c
}

pub open spec fn dist_right_add (a: int, b: int, c: int) -> int
{
    a * c + b * c
}

pub open spec fn dist_left_sub (a: int, b: int, c: int) -> int
{
    (a - b) * c
}

pub open spec fn dist_right_sub (a: int, b: int, c: int) -> int
{
    a * c - b * c
}

/// proves the distributive property of multiplication when multiplying an interger
/// by (x +/- 1)

// TODO: confirm the use of `forall_arith`, otherwise we need a wrapper function
// for every arithmetic expressions

proof fn lemma_mul_successor()
// forall_arith(|x:int, y:int| #[trigger]((x + 1) * y) == x * y + y),
// forall_arith(|x:int, y:int| #[trigger]((x - 1) * y) == x * y - y)
// LATER: forall_arith seems to be trivially verified
    ensures 
        forall |x:int, y:int| #[trigger] dist_left_add(x, 1, y) == dist_base_add(x, y),
        forall |x:int, y:int| #[trigger] dist_left_sub(x, 1, y) == dist_base_sub(x, y),
{
    // very different from the dafny proof, seems like the solver can figure out the sub case by itself
    lemma_mul_commutes();
    assert forall |x:int, y:int| #[trigger] dist_left_add(x, 1, y) == dist_base_add(x, y) by { lemma_mul_commutes() };
}


/// proves the distributive property of multiplication
proof fn lemma_mul_distributes()
    ensures
        forall |x, y, z| #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z),
        forall |x, y, z| #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z)
{
    // YOU DO NOT NEED TO ADD ANYTHING TO VERIFY THIS
    // lemma_mul_successor();
    // forall x:int, y:int, z:int
    // ensures (x + y) * z == x * z + y * z
    // ensures (x - y) * z == x * z - y * z
    // {
    // var f1 := i => (x + i) * z == x * z + i * z;
    // var f2 := i => (x - i) * z == x * z - i * z;
    // assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
    // assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
    // assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
    // assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
    // lemma_mul_induction(f1);
    // lemma_mul_induction(f2);
    // assert f1(y);
    // assert f2(y);
    // }
}

// experimental
pub open spec fn mul_auto1() -> bool
{
    &&& forall |x:int, y:int| #[trigger](x * y) == (y * x)
    &&& forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
    &&& forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z)
}

// cannot be proven
// after I added this proof, some of the following proofs started to fail

pub proof fn lemma_mul_auto1()
    ensures  mul_auto1()
{
    // VERY IMPORTANT
    lemma_mul_commutes(); // OBSERVE
    lemma_mul_distributes(); // OBSERVE
}

/// groups distributive and associative properties of multiplication
pub open spec fn mul_auto() -> bool
{
    &&& (forall |x:int, y:int| #[trigger]mul(x, y) == mul(y, x))
    &&& (forall |x:int, y:int, z:int| #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z))
    &&& (forall |x:int, y:int, z:int| #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z))
}

/// proves that mul_auto is valid
pub proof fn lemma_mul_auto()
    ensures  mul_auto()
{
    // lemma_mul_commutes();
    // lemma_mul_distributes();
}

// TODO: why this mul_anto antecedent is necessary?
/// performs auto induction on multiplication for all i s.t. f(i) exists */
pub proof fn lemma_mul_induction_auto(x: int, f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        f(x),
{
    // the commented out lemmas shuold be automatically inferred if I did not
    // add the lemma_mul_auto1 proof
    // lemma_mul_commutes();
    // lemma_mul_distributes();
    assert (forall |i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert (forall |i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
    // assert (f(x));
}

}