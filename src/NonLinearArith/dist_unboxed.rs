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

proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
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
    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}



#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
        forall |x, y, z| #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z),
        forall |x, y, z| #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z)
{
    assert forall |x:int, y:int, z:int| 
        #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z) 
     && #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z) by
    {
        // Interesting you need to assert one of the following
        let f2 = |i: int|  dist_left_sub(x, i, z) == dist_right_sub(x, i, z);
        lemma_mul_induction(f2);
        assert(f2(y));

        // let f1 = |i: int| dist_left_add(x, i, z) == dist_right_add(x, i, z);
        // lemma_mul_induction(f1);
        // assert(f1(y));
    }
}

}

fn main() {}