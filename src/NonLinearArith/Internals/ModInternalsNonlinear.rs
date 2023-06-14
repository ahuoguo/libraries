use vstd::prelude::*;

verus! {

spec fn Mod (x: int, y: int) -> int
{
    x % y
}

/* the remainder 0 divided by an integer is 0 */
proof fn LemmaModOfZeroIsZero(m:int)
    requires (0 as int) < m
    ensures 0 as int % m == 0 as int
{}

/* describes fundementals of the modulus operator */
#[verifier(nonlinear)]
proof fn LemmaFundamentalDivMod(x:int, d:int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
{}

/* the remained of 0 divided by any integer is always 0 */

proof fn Lemma0ModAnything()
ensures forall |m: int| m > 0 ==> #[trigger] Mod(0, m) == 0
{}

/* a natural number x divided by a larger natural number gives a remainder equal to x */
#[verifier(nonlinear)]
proof fn LemmaSmallMod(x:nat, m:nat)
    requires x < m,
             0 < m
    ensures #[trigger] Mod(x as int, m as int) == x as int
{}

/* the range of the modulus of any integer will be [0, m) where m is the divisor */
proof fn LemmaModRange(x:int, m:int)
    requires m > 0
    ensures 0 <= #[trigger] Mod(x, m) < m
{}

}