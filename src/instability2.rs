// for mul_auto using arithmetic triggers

// changing mul_auto to mul_auto1 for lemma_mul_induction_auto 
// seems to fall into trigger matching loops
use vstd::prelude::*;

verus! {

/* GeneralInternals */

pub open spec fn add (a: int, b: int) -> int
{
    a + b
}

pub open spec fn sub (a: int, b: int) -> int
{
    a - b
}

pub open spec fn is_le(x: int, y: int) -> bool
{
    x <= y
}

/* aids in the process of induction for modulus */
#[verifier(spinoff_prover)]
proof fn lemma_induction_helper_pos(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x >= 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
    ensures
        f(x)
    decreases x
{
    if (x >= n)
    {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert (f (add(x - n, n)));
        assert(f((x - n) + n));
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_induction_helper_neg(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x < 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
    ensures
        f(x)
    decreases -x
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert (f (sub(x + n, n)));
        assert(f((x + n) - n));
    }
    else {
        lemma_induction_helper_neg(n, f, x + n);
        assert (f (sub(x + n, n)));
        assert(f((x + n) - n));
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_induction_helper(n: int, f: FnSpec(int) -> bool, x: int)
requires 
    n > 0,
    forall |i : int| 0 <= i < n ==> #[trigger] f(i),
    forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
    forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
ensures
    f(x)
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    }
    else {
        lemma_induction_helper_neg(n, f, x);
    }
}

/* MulInternals */

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

#[verifier(spinoff_prover)]
pub open spec fn mul_auto1() -> bool
{
    &&& forall |x:int, y:int| #[trigger] (x * y) == (y * x)
    &&& forall |x:int, y:int, z:int| #[trigger] ((x + y) * z) == (x * z + y * z)
    &&& forall |x:int, y:int, z:int| #[trigger] ((x - y) * z) == (x * z - y * z)
}

// after I added this proof, some of the following proofs started to fail
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_auto1()
    ensures  mul_auto1()
{}

// this mul_auto seems to be pretty stable, do not switch to auto1
/// groups distributive and associative properties of multiplication
pub open spec fn mul_auto() -> bool
{
    &&& (forall |x:int, y:int| #[trigger](x * y) == (y * x))
    &&& (forall |x:int, y:int, z:int| #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z))
    &&& (forall |x:int, y:int, z:int| #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z))
}

/// proves that mul_auto is valid
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_auto()
    ensures  mul_auto()
{}

#[verifier(spinoff_prover)]
proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires 
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add(i, 1)),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub(i, 1)),
        // TODO how about this proof style? seems to distablize one or two proofs
        // COMMENT: seems to be irrelevant in this case (with respect to instability2.rs)
        // forall |i: int, j:int| i >= 0 && j == i + 1 && #[trigger] f(i) ==> #[trigger] f(j),
        // forall |i: int, j:int| i <= 0 && j == i - 1 && #[trigger] f(i) ==> #[trigger] f(j),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}


#[verifier(spinoff_prover)]
pub proof fn lemma_mul_induction_auto(x: int, f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        f(x),
{
    assert (forall |i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert (forall |i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

#[verifier(opaque)]
pub open spec fn mul_pos(x: int, y: int) -> int
    recommends x >= 0
    decreases x
{
    if x <= 0 {
        0 
    } else {
        y + mul_pos(x - 1, y) 
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
{
    reveal(mul_pos);
    lemma_mul_induction_auto(x, |u: int| u >= 0 ==> u * y == mul_pos(u, y));
}


}

fn main () {}