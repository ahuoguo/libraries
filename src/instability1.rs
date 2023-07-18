// https://github.com/verus-lang/verus/issues/670
use vstd::prelude::*;

verus! {

#[verifier(spinoff_prover)]
proof fn lemma_mod_basics_auto(n: int)
    requires n > 0
    ensures  
        forall |x: int| #[trigger]((x + n) % n) == x % n,
        forall |x: int| #[trigger]((x - n) % n) == x % n,
        forall |x: int| #[trigger]((x + n) / n) == x / n + 1,
        // forall |x: int| #[trigger]((x - n) / n) == x / n - 1,
        // forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x,
{
    assume(forall |x: int| #[trigger]((x + n) % n) == x % n);
    assume(forall |x: int| #[trigger]((x - n) % n) == x % n);
    assume(forall |x: int| #[trigger]((x + n) / n) == x / n + 1);    
    // assume(forall |x: int| #[trigger]((x - n) % n) == x % n);
    // assume(forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x);
}




}

fn main() {}