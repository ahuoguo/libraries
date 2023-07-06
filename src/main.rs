use vstd::prelude::*;

verus! {

mod Math;
mod NonLinearArith;
// mod Collections;

// imported for syntax highlighting
// mod instability1;
// mod instability2;
// mod instability3;
// mod instability4;
// mod instability5;
// mod instability6;


fn main() {
    assert(Math::min(1, 2) == 1);
    assert(forall |x: int| Math::abs(x) >= 0);

}

}
