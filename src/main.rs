use vstd::prelude::*;

verus! {

mod Math;
mod NonLinearArith;
mod Collections;

fn main() {
    assert(Math::min(1, 2) == 1);
    assert(forall |x: int| Math::abs(x) >= 0);

}

}
