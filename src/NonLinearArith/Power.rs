use vstd::prelude::*;

verus! {
#[allow(unused_imports)]
use crate::NonLinearArith::DivMod;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::GeneralInternals::{is_le};
#[allow(unused_imports)]
use crate::NonLinearArith::Mul::{lemma_mul_basics, lemma_mul_basics_auto};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternals::{lemma_mul_induction_auto};

#[verifier(opaque)]
spec fn pow(b: int, e: nat) -> int
    decreases e
{
    if e == 0 {
        1
    } else {
        b * pow(b, (e - 1) as nat)
    }
}

/// A number raised to the power of 0 equals
proof fn lemma_pow0(b: int)
    ensures pow(b, 0) == 1
{
    reveal(pow);
}

proof fn lemma_pow0_auto()
    ensures forall |b: int| #[trigger]pow(b, 0 as nat) == 1
{
    reveal(pow);
}

use vstd::calc_macro::*;
/* A number raised to the power of 1 equals the number itself. */
proof fn lemma_pow1(b: int)
    ensures pow(b, 1) == b
{
    // reveal(pow);
    calc! {
    (==)
    pow(b, 1);
    { reveal(pow); }
    b * pow(b, 0);
    { lemma_pow0(b); }
    b * 1;
    { lemma_mul_basics_auto(); }    // do not have auto now
    b;
    }
}

// proof fn lemma_pow1_auto()
//     ensures forall b: nat {:trigger pow(b, 1)} :: pow(b, 1) == b
// {
//     reveal pow();
//     forall b: nat {:trigger pow(b, 1)}
//     ensures pow(b, 1) == b
//     {
//     lemma_pow1(b);
//     }
// }

/// 0 raised to a positive power equals 0.
proof fn lemma0_pow(e: nat)
    requires e > 0
    ensures pow(0, e) == 0
    decreases e
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 1 {
    lemma0_pow((e - 1) as nat);
    }
}

// proof fn lemma0_pow_auto()
//     ensures forall e: nat {:trigger pow(0, e)} :: e > 0 ==> pow(0, e) == 0
// {
//     reveal pow();
//     forall e: nat {:trigger pow(0, e)} | e > 0
//     ensures pow(0, e) == 0
//     {
//     lemma0_pow(e);
//     }
// }

/// 1 raised to any power equals 1.
proof fn lemma1_pow(e: nat)
    ensures pow(1, e) == 1
    decreases e
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 0 {
    lemma1_pow((e - 1) as nat);
    }
}

// proof fn lemma1_pow_auto()
//     ensures forall e: nat {:trigger pow(1, e)} :: pow(1, e) == 1
// {
//     reveal pow();
//     forall e: nat {:trigger pow(1, e)}
//     ensures pow(1, e) == 1
//     {
//     lemma1_pow(e);
//     }
// }

///* Squaring a number is equal to raising it to the power of 2.
proof fn lemma_square_is_pow2(x: int)
ensures pow(x, 2) == x * x
{
    // maybe I can do it with reveal_with_fuel? but I don't know how
    // the following doesn't work
    // assert(pow(x, 2) == x * x) by { 
        // reveal_with_fuel(pow, 2);
    //  };
    reveal(pow);
    assert(x as int * pow(x as int, 1) == x * (x as int * pow(x as int, 0)));
}

// proof fn lemma_square_is_pow2_auto()
//     ensures forall x: nat {:trigger pow(x, 2)} :: pow(x, 2) == x * x
// {
//     reveal pow();
//     forall x: nat {:trigger pow(x, 2)}
//     ensures pow(x, 2) == x * x
//     {}
// }

// LACK lemma's from Mul.rs
// /// A positive number raised to any power is positive.
// proof fn lemma_pow_positive(b: int, e: nat)
//     requires b > 0
//     ensures 0 < pow(b, e)
// {
//     // lemma_mul_increases_auto();
//     let f = |u: int| 0 <= u ==> 0 < pow(b, u as nat);
//     assert ({ &&&  f(0)
//               &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
//               &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))});
//     lemma_mul_induction_auto(e as int, |u: int| 0 <= u ==> 0 < pow(b, u as nat));
// }

// proof fn lemma_pow_positive_auto()
//     ensures forall b: int, e: nat {:trigger pow(b, e)}
//             :: b > 0 ==> 0 < pow(b, e)
// {
//     reveal pow();
//     forall b: int, e: nat {:trigger pow(b, e)} | b > 0
//     ensures 0 < pow(b, e)
//     {
//     lemma_pow_positive(b, e);
//     }
// }

// /* Add exponents when multiplying powers with the same base. */
// proof fn lemma_pow_adds(b: int, e1: nat, e2: nat)
//     decreases e1
//     ensures pow(b, e1 + e2) == pow(b, e1) * pow(b, e2)
// {
//     if e1 == 0 {
//     calc {
//         pow(b, e1) * pow(b, e2);
//         { lemma_pow0(b); }
//         1 * pow(b, e2);
//         { lemma_mul_basics_auto(); }
//         pow(b, 0 + e2);
//     }
//     }
//     else {
//     calc {
//         pow(b, e1) * pow(b, e2);
//         { reveal pow(); }
//         (b * pow(b, e1 - 1)) * pow(b, e2);
//         { lemma_mul_is_associative_auto(); }
//         b * (pow(b, e1 - 1) * pow(b, e2));
//         { lemma_pow_adds(b, e1 - 1, e2); }
//         b * pow(b, e1 - 1 + e2);
//         { reveal pow(); }
//         pow(b, e1 + e2);
//     }
//     }
// }

// proof fn lemma_pow_adds_auto()
//     ensures forall b: int, e1: nat, e2: nat {:trigger pow(b, e1 + e2)}
//             :: pow(b, e1 + e2) == pow(b, e1) * pow(b, e2)
// {
//     reveal pow();
//     forall b: int, e1: nat, e2: nat {:trigger pow(b, e1 + e2)}
//     ensures pow(b, e1 + e2) == pow(b, e1) * pow(b, e2)
//     {
//     lemma_pow_adds(b, e1, e2);
//     }
// }

// proof fn lemma_pow_sub_add_cancel(b: int, e1: nat, e2: nat)
//     decreases e1
//     requires e1 >= e2
//     ensures pow(b, e1 - e2) * pow(b, e2) == pow(b, e1)
// {
//     lemma_pow_adds(b, e1 - e2, e2);
// }

// proof fn lemma_pow_sub_add_cancel_auto()
//     ensures forall b: int, e1: nat, e2: nat {:trigger pow(b, e1 - e2)} | e1 >= e2
//             :: pow(b, e1 - e2) * pow(b, e2) == pow(b, e1)
// {
//     reveal pow();
//     forall b: int, e1: nat, e2: nat | e1 >= e2
//     {
//     lemma_pow_sub_add_cancel(b, e1, e2);
//     }
// }

// /* Subtract exponents when dividing powers. */
// proof fn lemma_pow_subtracts(b: nat, e1: nat, e2: nat)
//     requires b > 0
//     requires e1 <= e2
//     ensures pow(b, e1) > 0
//     ensures pow(b, e2 - e1) == pow(b, e2) / pow(b, e1) > 0
// {
//     lemma_pow_positive_auto();
//     calc {
//     pow(b, e2) / pow(b, e1);
//     { lemma_pow_sub_add_cancel(b, e2, e1); }
//     pow(b, e2 - e1) * pow(b, e1) / pow(b, e1);
//     { lemma_div_by_multiple(pow(b, e2 - e1), pow(b, e1)); }
//     pow(b, e2 - e1);
//     }
// }

// proof fn lemma_pow_subtracts_auto()
//     ensures forall b: nat, e1: nat :: b > 0 ==> pow(b, e1) > 0
//     ensures forall b: nat, e1: nat, e2: nat {:trigger pow(b, e2 - e1)}
//             :: b > 0 && e1 <= e2 ==>
//                     pow(b, e2 - e1) == pow(b, e2) / pow(b, e1) > 0
// {
//     reveal pow();
//     lemma_pow_positive_auto();
//     forall b: nat, e1: nat, e2: nat {:trigger pow(b, e2 - e1)}
//     | b > 0 && e1 <= e2
//     ensures pow(b, e2 - e1) == pow(b, e2) / pow(b, e1) > 0
//     {
//     lemma_pow_subtracts(b, e1, e2);
//     }
// }

// /* Multiply exponents when finding the power of a power. */
// proof fn lemma_pow_multiplies(a: int, b: nat, c: nat)
//     decreases c
//     ensures 0 <= b * c
//     ensures pow(pow(a, b), c) == pow(a, b * c)
// {
//     lemma_mul_nonnegative(b, c);
//     if c == 0 {
//     lemma_mul_basics_auto();
//     calc {
//         pow(a, b * c);
//         { lemma_pow0(a); }
//         1;
//         { lemma_pow0(pow(a, b)); }
//         pow(pow(a, b), c);
//     }
//     }
//     else {
//     calc {
//         b * c - b;
//         { lemma_mul_basics_auto(); }
//         b * c - b * 1;
//         { lemma_mul_is_distributive_auto(); }
//         b * (c - 1);
//     }
//     lemma_mul_nonnegative(b, c - 1);
//     assert 0 <= b * c - b;

//     calc {
//         pow(a, b * c);
//         pow(a, b + b * c - b);
//         { lemma_pow_adds(a, b, b * c - b); }
//         pow(a, b) * pow(a, b * c - b);
//         pow(a, b) * pow(a, b * (c - 1));
//         { lemma_pow_multiplies(a, b, c - 1); }
//         pow(a, b) * pow(pow(a, b), c - 1);
//         { reveal pow(); }
//         pow(pow(a, b), c);
//     }
//     }
// }

// proof fn lemma_pow_multiplies_auto()
//     ensures forall b: nat, c: nat {:trigger b * c} :: 0 <= b * c
//     ensures forall a: int, b: nat, c: nat {:trigger pow(a, b * c)}
//             :: pow(pow(a, b), c) == pow(a, b * c)
// {
//     reveal pow();
//     lemma_mul_nonnegative_auto();
//     forall a: int, b: nat, c: nat {:trigger pow(a, b * c)}
//     ensures pow(pow(a, b), c) == pow(a, b * c)
//     {
//     lemma_pow_multiplies(a, b, c);
//     }
// }

// /* Distribute the power to factors of a product. */
// proof fn lemma_pow_distributes(a: int, b: int, e: nat)
//     decreases e
//     ensures pow(a * b, e) == pow(a, e) * pow(b, e)
// {
//     reveal pow();
//     lemma_mul_basics_auto();
//     if e > 0 {
//     calc {
//         pow(a * b, e);
//         (a * b) * pow(a * b, e - 1);
//         { lemma_pow_distributes(a, b, e - 1); }
//         (a * b) * (pow(a, e - 1) * pow(b, e - 1));
//         { lemma_mul_is_associative_auto(); lemma_mul_is_commutative_auto(); }
//         (a * pow(a, e - 1)) * (b * pow(b, e - 1));
//         pow(a, e) * pow(b, e);
//     }
//     }
// }

// proof fn lemma_pow_distributes_auto()
//     ensures forall a: int, b: int, e: nat {:trigger pow(a * b, e)}
//             :: pow(a * b, e) == pow(a, e) * pow(b, e)
// {
//     reveal pow();
//     forall a: int, b: int, e: nat {:trigger pow(a * b, e)}
//     ensures pow(a * b, e) == pow(a, e) * pow(b, e)
//     {
//     lemma_pow_distributes(a, b, e);
//     }
// }

// /* Group properties of powers. */
// proof fn lemma_pow_auto()
//     ensures forall x: int {:trigger pow(x, 0)} :: pow(x, 0) == 1
//     ensures forall x: int {:trigger pow(x, 1)} :: pow(x, 1) == x
//     ensures forall x: int, y: int {:trigger pow(x, y)} :: y == 0 ==> pow(x, y) == 1
//     ensures forall x: int, y: int {:trigger pow(x, y)} :: y == 1 ==> pow(x, y) == x
//     ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
//     ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
//     ensures forall x: int, y: nat, z: nat {:trigger pow(x, y + z)} :: pow(x, y + z) == pow(x, y) * pow(x, z)
//     ensures forall x: int, y: nat, z: nat {:trigger pow(x, y - z)} :: y >= z ==> pow(x, y - z) * pow(x, z) == pow(x, y)
//     ensures forall x: int, y: int, z: nat {:trigger pow(x * y, z)} :: pow(x * y, z) == pow(x, z) * pow(y, z)
// {
//     reveal pow();

//     lemma_pow0_auto();
//     lemma_pow1_auto();

//     lemma_pow_distributes_auto();
//     lemma_pow_adds_auto();
//     lemma_pow_sub_add_cancel_auto();

//     lemma_mul_auto();
//     lemma_mul_increases_auto();
//     lemma_mul_strictly_increases_auto();
// }

// /* A positive number raised to a power strictly increases as the power
// strictly increases. */
// proof fn lemma_pow_strictly_increases(b: nat, e1: nat, e2: nat)
//     requires 1 < b
//     requires e1 < e2
//     ensures pow(b, e1) < pow(b, e2)
// {
//     lemma_pow_auto();
//     var f := e => 0 < e ==> pow(b, e1) < pow(b, e1 + e);
//     forall i {:trigger IsLe(0, i)} | IsLe(0, i) && f(i)
//     ensures f(i + 1)
//     {
//     calc {
//         pow(b, e1 + i);
//     <= { lemma_pow_positive(b, e1 + i);
//             lemma_mul_left_inequality(pow(b, e1 + i), 1, b); }
//         pow(b, e1 + i) * b;
//     == { lemma_pow1(b); }
//         pow(b, e1 + i) * pow(b, 1);
//     == { lemma_pow_adds(b, e1 + i, 1); }
//         pow(b, e1 + i + 1);
//     }
//     }
//     lemma_mul_induction_auto(e2 - e1, f);
// }

// proof fn lemma_pow_strictly_increases_auto()
//     ensures forall b: nat, e1: nat, e2: nat {:trigger pow(b, e1),
//             pow(b, e2)} :: (1 < b && e1 < e2) ==> pow(b, e1) < pow(b, e2)
// {
//     reveal pow();
//     forall b: nat, e1: nat, e2: nat {:trigger pow(b, e1), pow(b, e2)}
//     | 1 < b && e1 < e2
//     ensures pow(b, e1) < pow(b, e2)
//     {
//     lemma_pow_strictly_increases(b, e1, e2);
//     }
// }

// /* A positive number raised to a power increases as the power increases. */
// proof fn lemma_pow_increases(b: nat, e1: nat, e2: nat)
//     requires b > 0
//     requires e1 <= e2
//     ensures pow(b, e1) <= pow(b, e2)
// {
//     lemma_pow_auto();
//     var f := e => 0 <= e ==> pow(b, e1) <= pow(b, e1 + e);
//     forall i {:trigger IsLe(0, i)} | IsLe(0, i) && f(i)
//     ensures f(i + 1)
//     {
//     calc {
//         pow(b, e1 + i);
//     <= { lemma_pow_positive(b, e1 + i);
//             lemma_mul_left_inequality(pow(b, e1 + i), 1, b); }
//         pow(b, e1 + i) * b;
//     == { lemma_pow1(b); }
//         pow(b, e1 + i) * pow(b, 1);
//     == { lemma_pow_adds(b, e1 + i, 1); }
//         pow(b, e1 + i + 1);
//     }
//     }
//     lemma_mul_induction_auto(e2 - e1, f);
// }

// proof fn lemma_pow_increases_auto()
//     ensures forall b: nat, e1: nat, e2: nat {:trigger pow(b, e1),
//             pow(b, e2)} :: (1 < b && e1 <= e2) ==> pow(b, e1) <= pow(b, e2)
// {
//     reveal pow();
//     forall b: nat, e1: nat, e2: nat {:trigger pow(b, e1), pow(b, e2)}
//     | 1 < b && e1 <= e2
//     ensures pow(b, e1) <= pow(b, e2)
//     {
//     lemma_pow_increases(b, e1, e2);
//     }
// }

// /* A power strictly increases as a positive number raised to the power
// strictly increases. */
// proof fn lemma_pow_strictly_increases_converse(b: nat, e1: nat, e2: nat)
//     requires b > 0
//     requires pow(b, e1) < pow(b, e2)
//     ensures e1 < e2
// {
//     if e1 >= e2 {
//     lemma_pow_increases(b, e2, e1);
//     assert false;
//     }
// }

// proof fn lemma_pow_strictly_increases_converse_auto()
//     ensures forall b: nat, e1: nat, e2: nat
//             {:trigger pow(b, e1), pow(b, e2)}
//             :: b > 0 && pow(b, e1) < pow(b, e2) ==> e1 < e2
// {
//     reveal pow();
//     forall b: nat, e1: nat, e2: nat {:trigger pow(b, e1), pow(b, e2)}
//     | b > 0 && pow(b, e1) < pow(b, e2)
//     ensures e1 < e2
//     {
//     lemma_pow_strictly_increases_converse(b, e1, e2);
//     }
// }

// /* A power increases as a positive number raised to the power increases. */
// proof fn lemma_pow_increases_converse(b: nat, e1: nat, e2: nat)
//     requires 1 < b
//     requires pow(b, e1) <= pow(b, e2)
//     ensures e1 <= e2
// {
//     if e1 > e2 {
//     lemma_pow_strictly_increases(b, e2, e1);
//     assert false;
//     }
// }

// proof fn lemma_pow_increases_converse_auto()
//     ensures forall b: nat, e1: nat, e2: nat
//             {:trigger pow(b, e1), pow(b, e2)}
//             :: 1 < b && pow(b, e1) <= pow(b, e2) ==> e1 <= e2
// {
//     reveal pow();
//     forall b: nat, e1: nat, e2: nat {:trigger pow(b, e1), pow(b, e2)}
//     | 1 < b && pow(b, e1) <= pow(b, e2)
//     ensures e1 <= e2
//     {
//     lemma_pow_increases_converse(b, e1, e2);
//     }
// }

// /* (b^xy)^z = (b^x)^yz */
// proof fn lemma_pull_out_pows(b: nat, x: nat, y: nat, z: nat)
//     requires b > 0
//     ensures 0 <= x * y
//     ensures 0 <= y * z
//     ensures pow(pow(b, x * y), z) == pow(pow(b, x), y * z)
// {
//     lemma_mul_nonnegative(x, y);
//     lemma_mul_nonnegative(y, z);
//     lemma_pow_positive(b, x);
//     calc {
//     pow(pow(b, x * y), z);
//     { lemma_pow_multiplies(b, x, y); }
//     pow(pow(pow(b, x), y), z);
//     { lemma_pow_multiplies(pow(b, x), y, z); }
//     pow(pow(b, x), y * z);
//     }
// }

// proof fn lemma_pull_out_pows_auto()
//     ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
//     ensures forall b: nat, x: nat, y: nat, z: nat
//             {:trigger pow(pow(b, x * y), z)}
//             :: b > 0 ==> pow(pow(b, x * y), z) == pow(pow(b, x), y * z)
// {
//     reveal pow();
//     lemma_mul_nonnegative_auto();
//     forall b: nat, x: nat, y: nat, z: nat {:trigger pow(pow(b, x * y), z)}
//     | b > 0 ensures pow(pow(b, x * y), z) == pow(pow(b, x), y * z)
//     {
//     lemma_pull_out_pows(b, x, y, z);
//     }
// }

// /* Inequality due to smaller numerator, same denominator. */
// proof fn lemma_pow_division_inequality(x: nat, b: nat, e1: nat, e2: nat)
//     requires b > 0
//     requires e2 <= e1
//     requires x < pow(b, e1)
//     ensures pow(b, e2) > 0
//     ensures x / pow(b, e2) < pow(b, e1 - e2)
// {
//     lemma_pow_positive_auto();
//     calc ==> {
//     x / pow(b, e2) >= pow(b, e1 - e2);
//     { lemma_mul_inequality(pow(b, e1 - e2), x / pow(b, e2), pow(b, e2)); }
//     x / pow(b, e2) * pow(b, e2) >= pow(b, e1 - e2) * pow(b, e2);
//     { lemma_fundamental_div_mod(x, pow(b, e2));
//         lemma_mul_is_commutative_auto(); }
//     x - x % pow(b, e2) >= pow(b, e1 - e2) * pow(b, e2);
//     { lemma_pow_adds(b, e1 - e2, e2); }
//     x - x % pow(b, e2) >= pow(b, e1);
//     { lemma_mod_properties_auto(); }
//     x >= pow(b, e1);
//     false;
//     }
// }

// proof fn lemma_pow_division_inequality_auto()
//     ensures forall b: nat, e2: nat :: b > 0 ==> pow(b, e2) > 0
//     ensures forall x: nat, b: nat, e1: nat, e2: nat
//             {:trigger x / pow(b, e2), pow(b, e1 - e2)}
//             :: b > 0 && e2 <= e1 && x < pow(b, e1) ==>
//                     x / pow(b, e2) < pow(b, e1 - e2)
// {
//     reveal pow();
//     lemma_pow_positive_auto();
//     forall x: nat, b: nat, e1: nat, e2: nat
//     {:trigger x / pow(b, e2), pow(b, e1 - e2)}
//     | b > 0 && e2 <= e1 && x < pow(b, e1)
//     ensures x / pow(b, e2) < pow(b, e1 - e2)
//     {
//     lemma_pow_division_inequality(x, b, e1, e2);
//     }
// }

// /* b^e % b = 0 */
// proof fn lemma_pow_mod(b: nat, e: nat)
//     requires b > 0 && e > 0
//     ensures pow(b, e) % b == 0;
// {
//     reveal pow();
//     calc {
//     pow(b, e) % b;
//     (b * pow(b, e - 1)) % b;
//     { lemma_mul_is_associative_auto(); }
//     (pow(b, e - 1) * b) % b;
//     {
//         lemma_pow_positive_auto();
//         lemma_mod_multiples_basic(pow(b, e-1) , b);
//     }
//     0;
//     }
// }

// proof fn lemma_pow_mod_auto()
//     ensures forall b: nat, e: nat {:trigger pow(b, e)}
//             :: b > 0 && e > 0 ==> pow(b, e) % b == 0
// {
//     reveal pow();
//     forall b: nat, e: nat {:trigger pow(b, e)} | b > 0 && e > 0
//     ensures pow(b, e) % b == 0
//     {
//     lemma_pow_mod(b, e);
//     }
// }

// /* ((b % e)^e) % m = b^e % m */
// proof fn lemma_pow_mod_noop(b: int, e: nat, m: int)
//     decreases e
//     requires m > 0
//     ensures pow(b % m, e) % m == pow(b, e) % m
// {
//     reveal pow();
//     lemma_mod_properties_auto();
//     if e > 0 {
//     calc {
//         pow(b % m, e) % m;
//         ((b % m) * pow(b % m, e - 1)) % m;
//         { lemma_mul_mod_noop_general(b, pow(b % m, e - 1), m); }
//         ((b % m) * (pow(b % m, e - 1) % m) % m) % m;
//         { lemma_pow_mod_noop(b, e - 1, m); }
//         ((b % m) * (pow(b, e - 1) % m) % m) % m;
//         { lemma_mul_mod_noop_general(b, pow(b, e - 1), m); }
//         (b * (pow(b, e - 1)) % m) % m;
//         (b * (pow(b, e - 1))) % m;
//         pow(b, e) % m;
//     }
//     }
// }

// proof fn lemma_pow_mod_noop_auto()
//     ensures forall b: nat, e: nat, m: nat {:trigger pow(b % m, e)}
//             :: m > 0 ==> pow(b % m, e) % m == pow(b, e) % m
// {
//     reveal pow();
//     forall b: nat, e: nat, m: nat {:trigger pow(b % m, e)}
//     | m > 0 ensures pow(b % m, e) % m == pow(b, e) % m
//     {
//     lemma_pow_mod_noop(b, e, m);
//     }
// }


}
