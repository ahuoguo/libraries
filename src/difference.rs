use vstd::prelude::*;

verus! { 

// experimental
pub open spec fn mul_auto1() -> bool
{
    &&& forall_arith(|x:int, y:int| #[trigger](x * y) == y * x)
    &&& forall_arith(|x:int, y:int, z:int| #[trigger]((x + y) * z) == x * z + y * z)
    &&& forall_arith(|x:int, y:int, z:int| #[trigger]((x - y) * z) == x * z - y * z)
}

// cannot be proven
pub proof fn lemma_mul_auto1()
    ensures  mul_auto1()
{
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
}

fn main() {
}