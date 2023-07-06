// related to instabiltiy3, now a issue on github

// of course its the same, because the div/mod are treated as 
// uninterpreted functions functions

use vstd::prelude::*;

verus! {

proof fn lemma_div_basics_auto(n: int)
    requires n > 0
    ensures  
        forall |x:int| #[trigger]((x + n) / n) == x / n + 1,
{
    assume(forall |x:int| # [trigger]((x + n) / n) == x / n + 1);
}

}

fn main() {}