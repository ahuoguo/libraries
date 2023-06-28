use vstd::prelude::*;

// what is the difference between dafny include and import?
// seems like include is not needed

verus! {
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::GeneralInternals::{is_le};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternals::{lemma_mod_basics, lemma_mod_induction_forall, mod_auto, lemma_mod_auto};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternalsNonlinear;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternalsNonlinear;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternals;

// TODO: discuss decrases, and opaque (the original dafny code has {:opaque} attribute)
// https://github.com/verus-lang/verus/blob/581d927b0cf8bafe4d00311eee7df1ac321d01c0/source/docs/manual/syntax.md?plain=1#L21
/// Performs division recursively with positive denominator.
#[verifier(opaque)]
pub open spec fn div_pos(x: int, d: int) -> int
    recommends d > 0
    // original dafny termination looks like this:
    decreases (if x < 0 {d - x} else {x}) when d > 0
    // but cannot prove termination
    // the following can prove termination (but only looked at one branch?)
    // decreases d - x when x < 0 && d > 0
{
    if x < 0 
    {
        -1 + div_pos(x + d, d) 
    } else if x < d {
        0
    }
    else {
        1 + div_pos(x - d, d)
    }
}

// TODO: original dafny code has {:opaque} attribute
/// Performs division recursively.
pub open spec fn div_recursive(x: int, d: int) -> int
    recommends d != 0
{
    // reveal(div_pos);
    if d > 0 {
        div_pos(x, d)
    } else {
        -1 * div_pos(x, -1 * d)
    }
}


// // same as lemma_mod_basics, we need to instantiate x
// /// Proves the basics of the division operation
// proof fn lemma_div_basics(n: int)
//     requires n > 0
//     ensures  
//         (n / n) == 1 &&  -((-n) / n) == 1,
//         forall |x:int| 0 <= x < n <==> #[trigger](x / n) == 0,
//         forall |x:int| #[trigger]((x + n) / n) == x / n + 1,
//         // forall |x:int| #[trigger]((x - n) / n) == x / n - 1,
// {
//     assert((n / n) == 1 &&  -((-n) / n) == 1) by {
//         DivInternalsNonlinear::lemma_div_by_self(n);
//     }
    
//     assert forall |x:int| 0 <= x < n <==> #[trigger](x / n) == 0 by {
//         DivInternalsNonlinear::lemma_small_div();
//         ModInternalsNonlinear::lemma_fundamental_div_mod(x, n);
//     }

//     assert forall |x:int| #[trigger]((x + n) / n) == x / n + 1 by {
//         // DivInternalsNonlinear::lemma_small_div();
//         lemma_mod_basics(n, x);
//         assert(((x + n) / n) == x / n + 1);

//     }
//     // assume(forall |x:int| #[trigger]((x + n) / n) == x / n + 1);

// }

// instantiated version of lemma_div_basics
#[verifier(spinoff_prover)]
proof fn lemma_div_basics(n: int, x: int)
    requires n > 0
    ensures
        (n / n) == 1 &&  -((-n) / n) == 1,
        0 <= x < n <==> #[trigger](x / n) == 0,
        #[trigger]((x + n) / n) == x / n + 1,
        #[trigger]((x - n) / n) == x / n - 1,
{
    assert((n / n) == 1 &&  -((-n) / n) == 1) by {
        DivInternalsNonlinear::lemma_div_by_self(n);
    }
    
    DivInternalsNonlinear::lemma_small_div();
    ModInternalsNonlinear::lemma_fundamental_div_mod(x, n);
    lemma_mod_basics(n, x);
}

// /// Automates the division operator process. Contains the identity property, a
// /// fact about when quotients are zero, and facts about adding and subtracting
// /// integers over a common denominator.
#[verifier(spinoff_prover)]
pub open spec fn div_auto(n: int) -> bool
    recommends n > 0
{
    &&& mod_auto(n)
    &&& (n / n == 1 && -((-n) / n) == 1)
    &&& forall |x: int| 0 <= x < n <==> #[trigger](x / n) == 0
    // &&& (forall |x: int, y: int|
    //      {let z = (x % n) + (y % n);
    //      (  (0 <= z < n && #[trigger]((x + y) / n) == x / n + y / n)
    //          || (n <= z < n + n && #[trigger]((x + y) / n) == x / n + y / n + 1))})
    // &&& (forall |x: int, y: int|
    //     {let z = (x % n) - (y % n);
    //     (  (0 <= z < n && #[trigger]((x - y) / n) == x / n - y / n)
    //         || (-n <= z < 0  && #[trigger]((x - y) / n) == x / n - y / n - 1))})
}

// /// Ensures that div_auto is true 
#[verifier(spinoff_prover)]
pub proof fn lemma_div_auto(n: int)
    requires n > 0
    ensures  div_auto(n)
{
    lemma_mod_auto(n);
    
    DivInternalsNonlinear::lemma_div_by_self(n);

    // this also has a split error
    // assert ((n / n == 1) && (-((-n) / n) == 1)) by {
    //     DivInternalsNonlinear::lemma_div_by_self(n);
    // }

    assert forall |x: int| 0 <= x < n <==> #[trigger](x / n) == 0 by {
        lemma_div_basics(n, x);
    }
//     assert (0 + n) / n == 1;
//     assert (0 - n) / n == -1;



//     forall x:int, y:int {:trigger (x + y) / n}
//     ensures  var z := (x % n) + (y % n);
//             (|| (0 <= z < n && (x + y) / n == x / n + y / n)
//                 || (n <= z < 2 * n && (x + y) / n == x / n + y / n + 1))
//     {
//     var f := (xx:int, yy:int) =>
//         (var z := (xx % n) + (yy % n);
//         (   (0 <= z < n && (xx + yy) / n == xx / n + yy / n)
//             || (n <= z < 2 * n && (xx + yy) / n == xx / n + yy / n + 1)));
//     forall i, j
//         ensures j >= 0 && f(i, j) ==> f(i, j + n)
//         ensures i < n  && f(i, j) ==> f(i - n, j)
//         ensures j < n  && f(i, j) ==> f(i, j - n)
//         ensures i >= 0 && f(i, j) ==> f(i + n, j)
//     {
//         assert ((i + n) + j) / n == ((i + j) + n) / n;
//         assert (i + (j + n)) / n == ((i + j) + n) / n;
//         assert ((i - n) + j) / n == ((i + j) - n) / n;
//         assert (i + (j - n)) / n == ((i + j) - n) / n;
//     }
//     forall i, j
//         ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
//     {
//         assert ((i + n) + j) / n == ((i + j) + n) / n;
//         assert (i + (j + n)) / n == ((i + j) + n) / n;
//         assert ((i - n) + j) / n == ((i + j) - n) / n;
//         assert (i + (j - n)) / n == ((i + j) - n) / n;
//     }
//     lemma_mod_induction_forall2(n, f);
//     assert f(x, y);
//     }
//     forall x:int, y:int {:trigger (x - y) / n}
//     ensures  var z := (x % n) - (y % n);
//             (|| (0 <= z < n && (x - y) / n == x / n - y / n)
//                 || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))
//     {
//     var f := (xx:int, yy:int) =>
//         (var z := (xx % n) - (yy % n);
//         (   (0 <= z < n && (xx - yy) / n == xx / n - yy / n)
//             || (-n <= z < 0 && (xx - yy) / n == xx / n - yy / n - 1)));
//     forall i, j
//         ensures j >= 0 && f(i, j) ==> f(i, j + n)
//         ensures i < n  && f(i, j) ==> f(i - n, j)
//         ensures j < n  && f(i, j) ==> f(i, j - n)
//         ensures i >= 0 && f(i, j) ==> f(i + n, j)
//     {
//         assert ((i + n) - j) / n == ((i - j) + n) / n;
//         assert (i - (j - n)) / n == ((i - j) + n) / n;
//         assert ((i - n) - j) / n == ((i - j) - n) / n;
//         assert (i - (j + n)) / n == ((i - j) - n) / n;
//     }
//     forall i, j
//         ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
//     {
//         assert ((i + n) - j) / n == ((i - j) + n) / n;
//         assert (i - (j - n)) / n == ((i - j) + n) / n;
//         assert ((i - n) - j) / n == ((i - j) - n) / n;
//         assert (i - (j + n)) / n == ((i - j) - n) / n;
//     }
//     lemma_mod_induction_forall2(n, f);
//     assert f(x, y);
//     }
}

pub open spec fn add(x: int, y: int) -> int
{
    x + y
}

pub open spec fn sub(x: int, y: int) -> int
{
    x - y
}

/// Performs auto induction for division 
#[verifier(spinoff_prover)]
pub proof fn lemma_div_induction_auto(n: int, x: int, f: FnSpec(int) -> bool)
    requires
        n > 0,
        div_auto(n) ==>{&&& (forall |i: int| #[trigger]is_le(0, i) && i < n ==> f(i))
                        &&& (forall |i: int| #[trigger]is_le(0, i) && f(i) ==> f(i + n))
                        &&& (forall |i: int| #[trigger]is_le(i + 1, n) && f(i) ==> f(i - n))}
    ensures  
        div_auto(n),
        f(x)
{
    lemma_div_auto(n);
    assert(forall |i: int| is_le(0, i) && i < n ==> f(i));
    assert(forall |i: int| is_le(0, i) && #[trigger]f(i) ==> #[trigger]f(add(i, n)));
    assert(forall |i: int| is_le(i + 1, n) && #[trigger]f(i) ==> #[trigger]f(sub(i, n)));
    assert forall |i: int| 0 <= i < n ==> #[trigger]f(i) by {
        if 0 <= i < n {
            assert(f(i)) by {
                assert(forall |i: int| is_le(0, i) && i < n ==> f(i));
                assert(is_le(0, i) && i < n);
            };
        }
    };
    assert(forall |i: int| i >= 0 && #[trigger]f(i) ==> #[trigger]f(add(i, n)));
    assert(forall |i: int| i < n && #[trigger]f(i) ==> #[trigger]f(sub(i, n)));
    assert forall |i: int| i >= 0 && #[trigger]f(i) ==> #[trigger]f(crate::NonLinearArith::Internals::ModInternals::add(i, n)) by {
        assert(crate::NonLinearArith::Internals::ModInternals::add(i, n) == add(i, n));
    }; // OBSERVE COMMUNICATION
    assert forall |i: int| i < n && #[trigger]f(i) ==> #[trigger]f(crate::NonLinearArith::Internals::ModInternals::sub(i, n)) by {
        assert(crate::NonLinearArith::Internals::ModInternals::sub(i, n) == sub(i, n));
    }; // OBSERVE COMMUNICATION
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

// same as the mod case, it is not invoked anywhere else
// /// Performs auto induction on division for all i s.t. f(i) exists 
// proof fn lemma_div_induction_auto_forall(n:int, f:int->bool)
//     requires n > 0
//     requires div_auto(n) ==> && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i))
//                             && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n))
//                             && (forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n))
//     ensures  div_auto(n)
//     ensures  forall i {:trigger f(i)} :: f(i)
// {
//     lemma_div_auto(n);
//     assert forall i :: IsLe(0, i) && i < n ==> f(i);
//     assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
//     assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
//     lemma_mod_induction_forall(n, f);
// }

}