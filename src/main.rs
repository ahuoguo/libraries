use vstd::prelude::*;

verus! {

mod Math;
mod NonLinearArith;

fn main() {
    assert(Math::min(1, 2) == 1);
    assert(forall |x: int| Math::abs(x) >= 0);

}

}
