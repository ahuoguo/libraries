use vstd::prelude::*;

verus! {

proof fn lemma_mul_distributes1()
    ensures
        forall |x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z),
        forall |x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z),
{
}

fn main() {}

}