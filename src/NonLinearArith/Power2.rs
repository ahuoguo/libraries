use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use crate::NonLinearArith::Power::{pow, lemma_pow_positive}; 
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternals; 
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::GeneralInternals; 

#[verifier(opaque)]
spec fn pow2(e: nat) -> nat
    decreases e
    // ensures pow2(e) > 0  // cannot have ensurs clause in spec functions
{
    // reveal(pow);
    pow(2, e) as nat
}

proof fn pow2_pos(e: nat)
    ensures pow2(e) > 0
{
    reveal(pow2);
    lemma_pow_positive(2, e);
}

/// pow2() is equivalent to Pow() with base 2.
proof fn lemma_pow2(e: nat)
    ensures pow2(e) == pow(2, e) as int
    decreases e
{
    reveal(pow);
    reveal(pow2);
    if e != 0 {
    lemma_pow2((e - 1) as nat);
    }
}

proof fn lemma_pow2_auto()
    ensures forall |e: nat| #[trigger]pow2(e) == pow(2, e)
{
    reveal(pow);
    reveal(pow2);

    assert forall |e: nat| #[trigger]pow2(e) == pow(2, e) by
    {
    lemma_pow2(e);
    }
}

// /// (2^e - 1) / 2 = 2^(e - 1) - 1
// proof fn lemma_pow2_mask_div2(e: nat)
//     requires 0 < e
//     ensures (pow2(e) - 1) / 2 == pow2(e - 1) - 1
// {
//     lemma_pow_auto();
//     var f := e => 0 < e ==> (pow2(e) - 1) / 2 == pow2(e - 1) - 1;
//     assert forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
//     assert forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
//     lemma_mul_induction_auto(e, f);
// }

// proof fn lemma_pow2_mask_div2_auto()
//     ensures forall e: nat {:trigger pow2(e)} :: 0 < e ==>
//                                                 (pow2(e) - 1) / 2 == pow2(e - 1) - 1
// {
//     reveal pow2();
//     forall e: nat {:trigger pow2(e)} | 0 < e
//     ensures (pow2(e) - 1) / 2 == pow2(e - 1) - 1
//     {
//     lemma_pow2_mask_div2(e);
//     }
// }


proof fn lemma2_4()
{
    assert(pow2(0) == 0x1) by {
        reveal_with_fuel(pow2, 1);
    };
}

// // TODO: ill-typed AIR
// proof fn lemma2_5_reveal()
// {
//     assert(pow2(1) == 0x2) by {
//         reveal_with_fuel(pow2, 2);
//     };
// }


proof fn lemma2_5()
{
    assert(pow2(1) == 0x2) by (compute);
}

// // TODO: ill-typed AIR
proof fn lemma2_to64()
    ensures 
        pow2(0) == 0x1,
        pow2(1) == 0x2,
        pow2(2) == 0x4,
        pow2(3) == 0x8,
        pow2(4) == 0x10,
        pow2(5) == 0x20,
        pow2(6) == 0x40,
        pow2(7) == 0x80,
        pow2(8) == 0x100,
        pow2(9) == 0x200,
        pow2(10) == 0x400,
        pow2(11) == 0x800,
        pow2(12) == 0x1000,
        pow2(13) == 0x2000,
        pow2(14) == 0x4000,
        pow2(15) == 0x8000,
        pow2(16) == 0x10000,
        pow2(17) == 0x20000,
        pow2(18) == 0x40000,
        pow2(19) == 0x80000,
        pow2(20) == 0x100000,
        pow2(21) == 0x200000,
        pow2(22) == 0x400000,
        pow2(23) == 0x800000,
        pow2(24) == 0x1000000,
        pow2(25) == 0x2000000,
        pow2(26) == 0x4000000,
        pow2(27) == 0x8000000,
        pow2(28) == 0x10000000,
        pow2(29) == 0x20000000,
        pow2(30) == 0x40000000,
        pow2(31) == 0x80000000,
        pow2(32) == 0x100000000,
        pow2(64) == 0x10000000000000000
{
    // reveal(pow2);
    assert(        
        pow2(0) == 0x1&&
        pow2(1) == 0x2&&
        pow2(2) == 0x4&&
        pow2(3) == 0x8&&
        pow2(4) == 0x10&&
        pow2(5) == 0x20&&
        pow2(6) == 0x40&&
        pow2(7) == 0x80&&
        pow2(8) == 0x100&&
        pow2(9) == 0x200&&
        pow2(10) == 0x400&&
        pow2(11) == 0x800&&
        pow2(12) == 0x1000&&
        pow2(13) == 0x2000&&
        pow2(14) == 0x4000&&
        pow2(15) == 0x8000&&
        pow2(16) == 0x10000&&
        pow2(17) == 0x20000&&
        pow2(18) == 0x40000&&
        pow2(19) == 0x80000&&
        pow2(20) == 0x100000&&
        pow2(21) == 0x200000&&
        pow2(22) == 0x400000&&
        pow2(23) == 0x800000&&
        pow2(24) == 0x1000000&&
        pow2(25) == 0x2000000&&
        pow2(26) == 0x4000000&&
        pow2(27) == 0x8000000&&
        pow2(28) == 0x10000000&&
        pow2(29) == 0x20000000&&
        pow2(30) == 0x40000000&&
        pow2(31) == 0x80000000&&
        pow2(32) == 0x100000000&&
        pow2(64) == 0x10000000000000000) by(compute);
}   


}