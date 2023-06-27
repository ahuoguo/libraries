use vstd::prelude::*;

verus! {

proof fn add_comm()
    ensures forall |x:int, y:int| #[trigger](x + y) == (y + x)
{}

}

fn main() {}