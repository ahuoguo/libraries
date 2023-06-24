
// import opened GeneralInternals
// import opened Mul
// import opened MulInternalsNonlinear
// import opened MulInternals
// import opened ModInternalsNonlinear
// import opened DivInternalsNonlinear

use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use crate::NonLinearArith::Internals::GeneralInternals::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Mul::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternals::{lemma_mul_auto};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternalsNonlinear;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternalsNonlinear::lemma_fundemental_div_mod;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternalsNonlinear;

// TODO: similar to div_pos in DivInternals
/// Performs modulus recursively
spec fn mod_recursive(x: int, d: int) -> int
    recommends d > 0
    // decreases (if x < 0 {(d - x)} else {x})
    decreases d - x when x < 0 && d > 0
{
    if x < 0 {
        mod_recursive(d + x, d)
    } else if x < d {
        x
    } else {
        mod_recursive(x - d, d)
    }
}

spec fn add (x: int, y: int) -> int
{
    x + y
}

spec fn sub (x: int, y: int) -> int
{
    x - y
}

/// performs induction on modulus
proof fn lemma_mod_induction_forall(n: int, f: FnSpec(int) -> bool)
    requires 
        n > 0,
        forall |i: int| 0 <= i < n ==> #[trigger]f(i),
        forall |i: int| i >= 0 && #[trigger]f(i) ==> #[trigger]f(add(i, n)),
        forall |i: int| i < n  && #[trigger]f(i) ==> #[trigger]f(sub(i, n)),
    ensures  
        forall |i| #[trigger]f(i)
{
    assert forall |i: int| #[trigger]f(i) by {
        // TODO: communicating between the `add` functions are hard (and unecessary)
        assert forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (crate::NonLinearArith::Internals::GeneralInternals::add(i, n)) by {
            assert(crate::NonLinearArith::Internals::GeneralInternals::add(i, n) == add(i, n));
        };
        assert forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (crate::NonLinearArith::Internals::GeneralInternals::sub(i, n)) by {
            assert(crate::NonLinearArith::Internals::GeneralInternals::sub(i, n) == sub(i, n));
        };
        lemma_induction_helper(n, f, i);
    };
}

// /// given an integer x and divisor n, the remainder of x%n is equivalent to the remainder of (x+m)%n
// /// where m is a multiple of n
// proof fn lemma_mod_induction_forall2(n: int, f:FnSpec(int, int)->bool)
//     requires
//         n > 0,
//         forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger]f(i, j),
//         forall |i: int, j: int| i >= 0 && #[trigger]f(i, j) ==> #[trigger]f(add(i, n), j),
//         forall |i: int, j: int| j >= 0 && #[trigger]f(i, j) ==> #[trigger]f(i, add(j, n)),
//         forall |i: int, j: int| i < n  && #[trigger]f(i, j) ==> #[trigger]f(sub(i, n), j),
//         forall |i: int, j: int| j < n  && #[trigger]f(i, j) ==> #[trigger]f(i, sub(j, n)),
//     ensures forall |i: int, j: int| #[trigger]f(i, j)
// {
//     assert forall |x: int, y: int| #[trigger]f(x, y) by {
//         assert forall |i: int| 0 <= i < n ==> #[trigger]f(i, y) by {
//             let fj = |j| f(i, j);
//             assert(forall |i: int| 0 <= i < n ==> #[trigger]fj(i)) by {
//                 assert(forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger]f(i, j));
//             };
//             assert forall |i: int| i >= 0 && #[trigger]fj(i) ==> #[trigger]fj(crate::NonLinearArith::Internals::GeneralInternals::add(i, n)) by {
//                 assert(fj(add(i, n)) == fj(i + n));
//             };
//             assert forall |i: int| i >= 0 && #[trigger]fj(i) ==> #[trigger]fj(add(i, n)) by {
//                 assert(fj(add(i, n)) == fj(i + n));
//             };
//             lemma_mod_induction_forall(n, fj);
//             assert(fj(y));
//         }

//     };

//     // forall x, y
//     // ensures f(x, y)
//     // {
//     // forall i | 0 <= i < n
//     //     ensures f(i, y)
//     // {
//     //     var fj := j => f(i, j);
//     //     lemma_mod_induction_forall(n, fj);
//     //     assert fj(y);
//     // }
//     // var fi := i => f(i, y);
//     // lemma_mod_induction_forall(n, fi);
//     // assert fi(x);
//     // }
// }

// proof fn lemma_div_add_denominator(n: int, x: int)
//     requires n > 0
//     ensures (x + n) / n == x / n + 1
// {
//     lemma_fundemental_div_mod(x, n);
//     assert(x == n * (x / n) + (x % n));
//     lemma_fundemental_div_mod(x + n, n);
//     assert(x + n == n * ((x + n) / n) + ((x + n) % n));
//     assert(0 == n * ((x + n) / n) + ((x + n) % n) - x - n);
//     let zp = (x + n) / n - x / n - 1;
//     assert(n * zp == ((x + n) / n) * n - (x / n) * n - n) by { 
//         assert(n * zp == n * ((x + n) / n - x / n - 1));
//         lemma_mul_auto();

//     };
//     assert (0 == n * zp + ((x + n) % n) - (x % n)) by { lemma_mul_auto() };
//     if (zp > 0) { lemma_mul_inequality(1, zp, n); }
//     if (zp < 0) { lemma_mul_inequality(zp, -1, n); }

// }

// proof fn lemma_div_sub_denominator(n: int, x: int)
//     requires n > 0
//     ensures (x - n) / n == x / n - 1
// {
//     lemma_fundamental_div_mod(x, n);
//     lemma_fundamental_div_mod(x - n, n);
//     var zm := (x - n) / n - x / n + 1;
//     forall ensures 0 == n * zm + ((x - n) % n) - (x % n) { lemma_mul_auto(); }
//     if (zm > 0) { lemma_mul_inequality(1, zm, n); }
//     if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
// }

// proof fn lemma_mod_add_denominator(n: int, x: int)
//     requires n > 0
//     ensures (x + n) % n == x % n
// {
//     lemma_fundamental_div_mod(x, n);
//     lemma_fundamental_div_mod(x + n, n);
//     var zp := (x + n) / n - x / n - 1;
//     forall ensures 0 == n * zp + ((x + n) % n) - (x % n) { lemma_mul_auto(); }
//     if (zp > 0) { lemma_mul_inequality(1, zp, n); }
//     if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
// }

// proof fn lemma_mod_sub_denominator(n: int, x: int)
//     requires n > 0
//     ensures (x - n) % n == x % n
// {
//     lemma_fundamental_div_mod(x, n);
//     lemma_fundamental_div_mod(x - n, n);
//     var zm := (x - n) / n - x / n + 1;
//     forall ensures 0 == n * zm + ((x - n) % n) - (x % n) { lemma_mul_auto(); }
//     if (zm > 0) { lemma_mul_inequality(1, zm, n); }
//     if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
// }

// proof fn lemma_mod_below_denominator(n: int, x: int)
//     requires n > 0
//     ensures 0 <= x < n <==> x % n == x
// {
//     forall x: int
//     ensures 0 <= x < n <==> x % n == x
//     {
//     if (0 <= x < n) { lemma_small_mod(x, n); }
//     lemma_mod_range(x, n);
//     }
// }

// /* proves the basics of the modulus operation */
// proof fn lemma_mod_basics(n: int)
//     requires n > 0
//     ensures  forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
//       forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
//       forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
//       forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
//       forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
// {
//     forall x: int
//     ensures (x + n) % n == x % n
//     ensures (x - n) % n == x % n
//     ensures (x + n) / n == x / n + 1
//     ensures (x - n) / n == x / n - 1
//     ensures 0 <= x < n <==> x % n == x
//     {
//     lemma_mod_below_denominator(n, x);
//     lemma_mod_add_denominator(n, x);
//     lemma_mod_sub_denominator(n, x);
//     lemma_div_add_denominator(n, x);
//     lemma_div_sub_denominator(n, x);
//     }
// }

// /* proves the quotient remainder theorem */
// lemma {:vcs_split_on_every_assert} lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
//     requires n > 0
//      0 <= r < n
//      x == q * n + r
//     ensures  q == x / n
//     ensures  r == x % n
//     decreases if q > 0 then q else -q
// {
//     lemma_mod_basics(n);

//     if q > 0 {
//     MulInternalsNonlinear.lemma_mul_is_distributive_add(n, q - 1, 1);
//     lemma_mul_is_commutative_auto();
//     assert q * n + r == (q - 1) * n + n + r;
//     lemma_quotient_and_remainder(x - n, q - 1, r, n);
//     }
//     else if q < 0 {
//     Mul.lemma_mul_is_distributive_sub(n, q + 1, 1);
//     lemma_mul_is_commutative_auto();
//     assert q * n + r == (q + 1) * n - n + r;
//     lemma_quotient_and_remainder(x + n, q + 1, r, n);
//     }
//     else {
//     lemma_small_div();
//     assert r / n == 0;
//     }
// }

// /* automates the modulus operator process */
// ghost predicate ModAuto(n: int)
//     requires n > 0;
// {
//     && (n % n == (-n) % n == 0)
//     && (forall x: int {:trigger (x % n) % n} :: (x % n) % n == x % n)
//     && (forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x)
//     && (forall x: int, y: int {:trigger (x + y) % n} ::
//         (var z := (x % n) + (y % n);
//         (  (0 <= z < n     && (x + y) % n == z)
//             || (n <= z < n + n && (x + y) % n == z - n))))
//     && (forall x: int, y: int {:trigger (x - y) % n} ::
//         (var z := (x % n) - (y % n);
//         (   (0 <= z < n && (x - y) % n == z)
//             || (-n <= z < 0 && (x - y) % n == z + n))))
// }

// /* ensures that ModAuto is true */
// proof fn lemma_mod_auto(n: int)
//     requires n > 0
//     ensures  ModAuto(n)
// {
//     lemma_mod_basics(n);
//     lemma_mul_is_commutative_auto();
//     lemma_mul_is_distributive_add_auto();
//     lemma_mul_is_distributive_sub_auto();

//     forall x: int, y: int {:trigger (x + y) % n}
//     ensures var z := (x % n) + (y % n);
//             || (0 <= z < n && (x + y) % n == z)
//             || (n <= z < 2 * n && (x + y) % n == z - n)
//     {
//     var xq, xr := x / n, x % n;
//     lemma_fundamental_div_mod(x, n);
//     assert x == xq * n + xr;
//     var yq, yr := y / n, y % n;
//     lemma_fundamental_div_mod(y, n);
//     assert y == yq * n + yr;
//     if xr + yr < n {
//         lemma_quotient_and_remainder(x + y, xq + yq, xr + yr, n);
//     }
//     else {
//         lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
//     }
//     }

//     forall x: int, y: int {:trigger (x - y) % n}
//     ensures var z := (x % n) - (y % n);
//             || (0 <= z < n && (x - y) % n == z)
//             || (-n <= z < 0 && (x - y) % n == z + n)
//     {
//     var xq, xr := x / n, x % n;
//     lemma_fundamental_div_mod(x, n);
//     assert x == xq * n + xr;
//     var yq, yr := y / n, y % n;
//     lemma_fundamental_div_mod(y, n);
//     assert y == yq * n + yr;
//     if xr - yr >= 0 {
//         lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
//     }
//     else {
//         lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
//     }
//     }
// }

// /* performs auto induction for modulus */
// proof fn lemma_mod_induction_auto(n: int, x: int, f: int -> bool)
//     requires n > 0
//      ModAuto(n) ==> && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i))
//                             && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n))
//                             && (forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n))
//     ensures  ModAuto(n)
//     ensures  f(x)
// {
//     lemma_mod_auto(n);
//     assert forall i :: IsLe(0, i) && i < n ==> f(i);
//     assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
//     assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
//     lemma_mod_induction_forall(n, f);
//     assert f(x);
// }

// // not used in other files
// /* performs auto induction on modulus for all i s.t. f(i) exists */
// proof fn lemma_mod_induction_auto_forall(n: int, f: int -> bool)
//     requires n > 0
//      ModAuto(n) ==> && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i))
//                             && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n))
//                             && (forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n))
//     ensures  ModAuto(n)
//     ensures  forall i {:trigger f(i)} :: f(i)
// {
//     lemma_mod_auto(n);
//     assert forall i :: IsLe(0, i) && i < n ==> f(i);
//     assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
//     assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
//     lemma_mod_induction_forall(n, f);
// }

}