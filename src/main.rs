use vstd::prelude::*;

verus! {

mod math;
mod NonLinearArith;

fn main() {
    assert(math::min(1, 2) == 1);
    assert(forall |x: int| math::min(x) >= 0);

}

}
