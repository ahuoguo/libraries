use vstd::prelude::*;

verus! {

mod Math;
mod NonLinearArith;

fn main() {
    assert(Math::Min(1, 2) == 1);
    assert(forall |x: int| Math::Abs(x) >= 0);

}

}
