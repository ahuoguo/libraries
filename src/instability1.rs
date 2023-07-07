// spinoff_prover is not working as wanted
// the existence of lemma_mul_induction_helper is affecting 
// the proof of mul_is_distributive

// To show the instability, try to comment out lemma_mul_induction_helper, and
// mul_is_distributive proof will fail

// Moreover, the assertion that shares x, y, z as variables cannot be proven
// (see the assertion in dist_unboxed.rs)

// this might be related to why in the non-spinoff prover version, revealing
// mul_pos is an adequate proof (check MulInternals for a demo)

// discovered during unwrapping the proof of mul_is_distributive
use vstd::prelude::*;

verus! {


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

pub open spec fn mul (a: int, b: int) -> int
{
    a * b
}


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
    }
    else {
        lemma_induction_helper_neg(n, f, x + n);
        assert (f (sub(x + n, n)));
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

#[verifier(spinoff_prover)]
proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires 
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add(i, 1)),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub(i, 1)),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}


#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
        forall |x: int, y: int, z: int| #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z),
        forall |x: int, y: int, z: int| #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z)
{
}

}

fn main() {}
