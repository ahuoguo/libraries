use vstd::prelude::*;

verus! {

#[verifier(integer_ring)]
proof fn mod_add_zero_int(a: int, b: int, c: int)
    requires
        (a % c) == 0,
        (b % c) == 0,
    ensures
        ((a + b) % c == 0)
{}

// #[verifier(integer_ring)]
// proof fn mod_after_mul(x: int, y: int, z:int, m:int)
//     requires (x-y) % m == 0
//     ensures( (x*z - y*z) % m == 0)
// {}
}

fn main() {}

