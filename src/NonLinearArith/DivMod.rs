// DEPRECATED

// This file has been separated to Div.rs and Modulus.rs
// I think maybe being in the same module does make it significantly slower
// when using --verify-module

// experience: some lemmas will break when introducing one new auto lemma
// but will work by going to make its original form when introduing new
// ones. I ended up deciding importing the last 30ish auto lemma at once
// (with only syntax checking and it somewhat worked fine)

// TODO: try integer_ring feature?
// should work well when there are only equalities in pre/post-condition

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::calc_macro::*;

verus! {

#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternals::{div_recursive, lemma_div_induction_auto, div_auto, div_pos, lemma_div_auto};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternalsNonlinear as DivINL;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternals::{lemma_mod_auto, mod_recursive};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternalsNonlinear as ModINL;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::MulInternals::{lemma_mul_induction_auto, lemma_mul_auto, mul_auto, lemma_mul_induction};
#[allow(unused_imports)]
use crate::NonLinearArith::Mul::*;
// use crate::NonLinearArith::Mul::{lemma_mul_strictly_positive_auto, lemma_mul_is_associative_auto, lemma_mul_is_distributive_auto, lemma_mul_is_commutative_auto, lemma_mul_strict_inequality_converse_auto, lemma_mul_inequality_auto, lemma_mul_increases_auto};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::GeneralInternals::{is_le};



/*****************************************************************************
 * Division:
 *****************************************************************************/

/// the common syntax of division gives the same quotient as performing division through recursion
#[verifier::spinoff_prover]
pub proof fn lemma_div_is_div_recursive(x: int, d: int)
    requires 0 < d
    ensures div_recursive(x, d) == x / d
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_induction_auto(d, x, |u: int| div_recursive(u, d) == u / d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_is_div_recursive_auto()
    ensures forall |x: int, d: int| d > 0 ==> div_recursive(x, d) == #[trigger](x / d)
{
    reveal(div_recursive);
    assert forall |x: int, d: int| d > 0 implies div_recursive(x, d) == #[trigger](x / d) by
    {
    lemma_div_is_div_recursive(x, d);
    }
}

/// the quotient of an integer divided by itself is 1
#[verifier::spinoff_prover]
pub proof fn lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
{
    DivINL::lemma_div_by_self(d);
}

/// zero divided by an integer besides 0 is 0
#[verifier::spinoff_prover]
pub proof fn lemma_div_of0(d: int)
    requires d != 0
    ensures 0 as int  / d == 0
{
    DivINL::lemma_div_of0(d);
}

/// ensures the basic propoerties of division: 0 divided by any integer is 0; any integer 
/// divided by 1 is itself; any integer divided by itself is 1
#[verifier::spinoff_prover]
pub proof fn lemma_div_basics(x: int)
    ensures 
        x != 0 as int ==> 0 as int / x == 0,
        x / 1 == x,
        x != 0 ==> x / x == 1,
{
    if (x != 0) {
    lemma_div_by_self(x);
    lemma_div_of0(x);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_basics_auto()
    ensures
        forall |x: int| x != 0 ==> #[trigger](0int / x) == 0,
        forall |x: int| #[trigger](x / 1) == x,
        forall |x: int, y: int| x >= 0 && y > 0 ==> #[trigger](x / y) >= 0,
        forall |x: int, y: int| x >= 0 && y > 0 ==> #[trigger](x / y) <= x,
{
    assert forall |x: int| (x != 0 ==> #[trigger](0int / x) / x == 0) && (#[trigger](x / 1) == x) by
    {
    lemma_div_basics(x);
    };
    
    assert forall |x: int, y: int| x >= 0 && y > 0 implies 0 <= #[trigger](x / y) <= x by
    {
    lemma_div_pos_is_pos(x, y);
    lemma_div_is_ordered_by_denominator(x, 1, y);
    };
}

/// if a dividend is a whole number and the divisor is a natural number and their
/// quotient is 0, this implies that the dividend is smaller than the divisor
#[verifier::spinoff_prover]
pub proof fn lemma_small_div_converse_auto()
    ensures forall |x: int, d:int| 0 <= x && 0 < d && #[trigger](x / d) == 0 ==> x < d,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d &&  #[trigger](x / d) == 0 implies x < d by
    {
        lemma_div_induction_auto(d, x, |u: int| 0 <= u && 0 < d && u / d == 0 ==> u < d); 
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_non_zero(x: int, d: int)
    requires x >= d > 0
    ensures x / d > 0
{
    lemma_div_pos_is_pos_auto();
    if x / d == 0 {
    lemma_small_div_converse_auto();
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_non_zero_auto()
    ensures forall |x: int, d: int| x >= d > 0 ==> #[trigger] (x / d) > 0
{
    assert forall |x: int, d: int| x >= d > 0 implies #[trigger] (x / d) > 0 by
    {
        lemma_div_non_zero(x, d);
    }
}

spec fn div (x:int, y: int) -> int
    recommends y != 0
{
    x / y
}

/// given two fractions with the same numerator, the order of numbers is determined by 
/// the denominators. However, if the numerator is 0, the fractions are equal regardless of 
/// the denominators' values
#[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires 
        0 <= x,
        1 <= y <= z
    ensures 
        x / y >= x / z
    decreases x
{
    reveal(div_recursive);
    reveal(div_pos); // OBSERVE
    lemma_div_is_div_recursive_auto();

    assert(forall |u: int, d: int| d > 0 ==> #[trigger]div_recursive(u, d) == #[trigger](div(u, d)));

    if (x < z)
    {
        lemma_div_is_ordered(0, x, y);
    }
    else
    {
        lemma_div_is_ordered(x - z, x - y, y);
        lemma_div_is_ordered_by_denominator(x - z, y, z);
    }

}

#[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered_by_denominator_auto()
    ensures forall |x: int, y: int, z: int| 0 <= x && 1 <= y <= z ==> #[trigger](x / y) >= #[trigger](x / z)
{
    assert forall |x: int, y: int, z: int| 0 <= x && 1 <= y <= z implies #[trigger](x / y) >= #[trigger](x / z) by
    {
        lemma_div_is_ordered_by_denominator(x, y, z);
    }
}

/// given two fractions with the same numerator, the order of numbers is strictly determined by 
/// the denominators.
#[verifier::spinoff_prover]
pub proof fn lemma_div_is_strictly_ordered_by_denominator(x: int, d: int)
    requires 
        0 < x, 
        1 < d
    ensures 
        x / d  < x
    decreases x
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_is_strictly_ordered_by_denominator_auto()
    ensures forall |x: int, d: int|  0 < x && 1 < d ==> #[trigger](x / d) < x,
{
    assert forall |x: int, d: int|  0 < x && 1 < d implies #[trigger](x / d) < x by
    {
        lemma_div_is_strictly_ordered_by_denominator(x, d);
    }
}

/// Rounding is different when multiplying the sum of two integers by a fraction d/d vs. 
/// first multiplying each integer by d/d and then adding the quotients
#[verifier::spinoff_prover]
pub proof fn lemma_dividing_sums(a: int, b: int, d: int, r: int)
    requires 
        0 < d,
        r == a % d + b % d - (a + b) % d,
    ensures 
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d)
{
    ModINL::lemma_fundamental_div_mod(a + b, d);
    ModINL::lemma_fundamental_div_mod(a, d);
    ModINL::lemma_fundamental_div_mod(b, d);
    // calc ==> {
    // a % d + b % d == r + (a + b) % d;
    // (a + b) - (a + b) % d - r == a - (a % d) + b - (b % d);
    // {
    //     lemma_fundamental_div_mod(a + b, d);
    //     lemma_fundamental_div_mod(a, d);
    //     lemma_fundamental_div_mod(b, d);
    // }
    // d * ((a + b) / d) - r == d * (a / d) + d * (b / d);
    // }
}

#[verifier::spinoff_prover]
pub proof fn lemma_dividing_sums_auto()
    ensures forall |a: int, b: int, d: int, r: int| 
    #![trigger (d * ((a + b) / d) - r), (d * (a / d) + d * (b / d))] 
    0 < d && r == a % d + b % d - (a + b) % d ==> 
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d),
{
    assert forall |a: int, b: int, d: int, r: int| 
    0 < d && r == a % d + b % d - (a + b) % d implies
        #[trigger](d * ((a + b) / d) - r) == #[trigger](d * (a / d) + d * (b / d)) by
    {
        lemma_dividing_sums(a, b, d, r);
    }
}

/// dividing a whole number by a natural number will result in a quotient that is 
/// greater than or equal to 0
#[verifier::spinoff_prover]
pub proof fn lemma_div_pos_is_pos(x: int, d: int)
    requires 
        0 <= x,
        0 < d
    ensures 
        0 <= x / d
{
    lemma_div_auto(d);
    assert(div_auto(d));
    let f = |u: int| 0 <= u ==> u / d >= 0;

    assert forall |i: int| #[trigger]is_le(0, i) && f(i) implies f(i + d) by {
        assert(i / d >= 0);
    };

    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d >= 0);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_pos_is_pos_auto()
    ensures
        forall |x: int, d: int|  0 <= x && 0 < d ==> 0 <= #[trigger](x / d)
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger] (x / d) by
    {
    lemma_div_pos_is_pos(x, d);
    }
}

/// dividing an integer and then adding 1 to the quotient is the same as adding 
/// the divisor and the integer, and then dividing that sum by the divisor
#[verifier::spinoff_prover]
pub proof fn lemma_div_plus_one(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
{
    lemma_div_auto(d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_plus_one_auto()
    ensures
        forall |x: int, d: int| #![trigger (1 + x / d), ((d + x) / d)] 0 < d ==> 1 + (x / d) == (d + x) / d,
{
    // // TODO: can't write as follows
    // assert forall |x: int, d: int| #![trigger (1 + x / d), ((d + x) / d)] 
    //     0 < d implies  1 + x / d == (d + x) / d 
    // by {
    // lemma_div_plus_one(x, d);
    // }
    assert forall |x: int, d: int|  0 < d implies  #[trigger](1 + x / d) == #[trigger]((d + x) / d) by
    {
        lemma_div_plus_one(x, d);
    }
}

/// dividing an integer and then subtracting 1 from the quotient is the same as subtracting 
/// the divisor from the integer, and then dividing that difference by the divisor
#[verifier::spinoff_prover]
pub proof fn lemma_div_minus_one(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
{
    lemma_div_auto(d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_minus_one_auto()
    ensures forall |x: int, d: int| #![trigger (-1 + x / d), ((-d + x) / d)] 
        0 < d ==> -1 + x / d == (-d + x) / d,
{
    assert forall |x: int, d: int|  0 < d implies  #[trigger](-1 + x / d) == #[trigger]((-d + x) / d) by
    {
        lemma_div_minus_one(x, d);
    }
}

/// dividing a smaller integer by a larger integer results in a quotient of 0
#[verifier::spinoff_prover]
pub proof fn lemma_basic_div(d: int)
    requires 0 < d
    ensures forall |x: int| 0 <= x < d ==> #[trigger](x / d) == 0
{
    lemma_div_auto(d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_basic_div_auto()
    ensures forall |x: int, d: int| 0 <= x < d ==> #[trigger](x / d) == 0
{
    assert forall |x: int, d: int| 0 <= x < d implies #[trigger](x / d) == 0 by
    {
        lemma_basic_div(d);
    }
}

/// numerical order is preserved when dividing two seperate integers by a common positive divisor
#[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered(x: int, y: int, z: int)
    requires 
        x <= y,
        0 < z,
    ensures x / z <= y / z
{
    lemma_div_auto(z);
    let f = |xy: int| xy <= 0 ==> (xy + y) / z <= y / z;

    assert forall |i: int| #[trigger]is_le(i + 1, z) && f(i) implies f(i - z) by {
        if (i - z <= 0) {
            assert( f(i) );
            assert( i <= 0 ==> (i + y) / z <= y / z );
            if (i > 0) {
                assert ( z > 0 );
                assert( i <= z );
                assert ( ((i + y) - z) / z <= y / z );
            } else {
                assert( (i + y) / z <= y / z );
            }
            assert( (i - z + y) / z <= y / z );
        }
    };

    lemma_div_induction_auto(z, x - y, |xy: int| xy <= 0 ==> (xy + y) / z <= y / z);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered_auto()
    ensures forall |x: int, y: int, z: int| x <= y && 0 < z ==> #[trigger](x / z) <= #[trigger](y / z)
{
    assert forall |x: int, y: int, z: int| x <= y && 0 < z implies #[trigger](x / z) <= #[trigger](y / z) by
    {
        lemma_div_is_ordered(x, y, z);
    }
}

/* dividing an integer by 2 or more results in a quotient that is smaller than the 
original dividend */
#[verifier::spinoff_prover]
pub proof fn lemma_div_decreases(x: int, d: int)
    requires 
        0 < x,
        1 < d,
    ensures 
        x / d  < x
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_decreases_auto()
    ensures 
        forall |x: int, d: int| 0 < x && 1 < d ==> #[trigger](x / d) < x,
{
    assert forall |x: int, d: int| 0 < x && 1 < d implies #[trigger](x / d) < x by
    {
        lemma_div_decreases(x, d);
    };
}

/// dividing an integer by 1 or more results in a quotient that is less than or equal to 
/// the original dividend
#[verifier::spinoff_prover]
pub proof fn lemma_div_nonincreasing(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures 
        x / d  <= x
{
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d <= u);
}

proof fn lemma_div_nonincreasing_auto()
    ensures forall |x: int, d: int| 0 <= x && 0 < d ==> #[trigger](x / d) <= x,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies #[trigger](x / d) <= x by
    {
        lemma_div_nonincreasing(x, d);
    }
}

/// a natural number x divided by a larger natural number gives a remainder equal to x
#[verifier::spinoff_prover]
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires 
        x < m,
        0 < m
    ensures 
        x % m == x
{
    ModINL::lemma_small_mod(x, m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_breakdown(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        0 < y * z,
        x % (y * z) == y * ((x / y) % z) + x % y,
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    assert(0 <= x / y);

    // TODO: the following code is kinda buggy because it does
    // not encode the "<" info
    calc! {
    (<=)
    (y * (x / y)) % (y * z) + (x % y) % (y * z);
    (<=)    { lemma_part_bound1(x, y, z); }
    y * (z - 1) + (x % y) % (y * z);
    (<)    { lemma_part_bound2(x, y, z); }
    y * (z - 1) + y;
    (==)    { lemma_mul_basics_auto(); }
    y * (z - 1) + y * 1;
    (==)    { lemma_mul_is_distributive_auto(); }
    y * (z - 1 + 1);
    (==) {}
    y * z;
    }

    // translated the calc proof above
    assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z) by {
        lemma_part_bound1(x, y, z);
        lemma_part_bound2(x, y, z);
        lemma_mul_basics_auto();
        lemma_mul_is_distributive_auto();
    };


    calc! {
    (==)
    x % (y * z);
    { ModINL::lemma_fundamental_div_mod(x,y); }
    (y * (x / y) + x % y) % (y * z);
    {
        lemma_mod_properties_auto();
        assert(0 <= x % y);
        lemma_mul_nonnegative(y, x / y);
        assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
        lemma_mod_adds(y * (x / y), x % y, y * z);
    }
    (y * (x / y)) % (y * z) + (x % y) % (y * z);
    {
        lemma_mod_properties_auto();
        lemma_mul_increases(z, y);
        lemma_mul_is_commutative_auto();
        assert((x % y) < y && y <= (y * z)); // comparison op can't be chained??
        lemma_small_mod((x % y) as nat, (y * z) as nat);
        assert((x % y) % (y * z) == x % y);
    }
    (y * (x / y)) % (y * z) + x % y;
    { lemma_truncate_middle(x / y, y, z); }
    y * ((x / y) % z) + x % y;
    }
}

// unstable
#[verifier::spinoff_prover]
pub proof fn lemma_breakdown_auto()
    ensures 
        forall |x: int, y: int, z: int| #![trigger (y * z), (x % (y * z)), (y * ((x / y) % z) + x % y)] 0 <= x && 0 < y && 0 < z ==> 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y,
        // forall |x: int, y: int, z: int| #![trigger (y * z), (x % (y * z)), (y * ((x / y) % z) + x % y)] 
        //     0 <= x && 0 < y && 0 < z ==> 0 < y * z,
        // forall |x: int, y: int, z: int| #![trigger (y * z), (x % (y * z)), (y * ((x / y) % z) + x % y)] 
        //     0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,

{
    assert forall |x: int, y: int, z: int|(0 <= x && 0 < y && 0 < z) implies 0 < #[trigger](y * z) && #[trigger](x % (y * z)) == #[trigger](y * ((x / y) % z) + x % y) by
    {
        // TO BE DISCUSSED
        lemma_breakdown(x, y, z);
        // OBSERVE: this is weird
        if (0 <= x && 0 < y && 0 < z) {
            assert(0 < z);
            lemma_breakdown(x, y, z);
        }
    }
    assert(forall |x: int, y: int, z: int|(0 <= x && 0 < y && 0 < z) ==> 0 < #[trigger](y * z) && #[trigger](x % (y * z)) == #[trigger](y * ((x / y) % z) + x % y));
}

#[verifier::spinoff_prover]
pub proof fn lemma_remainder_upper(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures 
        x - d < x / d * d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u - d < u / d * d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_remainder_upper_auto()
    ensures forall |x: int, d: int| #![trigger (x - d), (x / d * d)] 0 <= x && 0 < d ==> (x - d) < (x / d * d)
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies #[trigger](x - d) < #[trigger](x / d * d) by
    {
        lemma_remainder_upper(x, d);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_remainder_lower(x: int, d: int)
    requires 
        0 <= x,
        0 < d
    ensures
        x >= x / d * d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u >= u / d * d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_remainder_lower_auto()
    ensures
        forall |x: int, d: int| 0 <= x && 0 < d ==> x >= #[trigger](x / d * d)
{
    assert forall |x: int, d: int| (0 <= x && 0 < d) implies x >= #[trigger](x / d * d) by
    {
        lemma_remainder_lower(x, d);
    }
}


#[verifier::spinoff_prover]
pub proof fn lemma_remainder(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures
        0 <= x - (x / d * d) < d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x,|u: int| 0 <= u - u / d * d < d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_remainder_auto()
    ensures 
        forall |x: int, d: int| 0 <= x && 0 < d ==> 0 <= #[trigger](x - (x / d * d)) < d,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger](x - (x / d * d)) < d by
    {
        lemma_remainder(x, d);
    }
}

/// describes fundamental of the modulus operator
#[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
{
    ModINL::lemma_fundamental_div_mod(x, d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod_auto()
    ensures forall |x: int, d: int| d != 0 ==> x == #[trigger](d * (x / d) + (x % d))
{
    assert forall |x: int, d: int| d != 0 implies x == #[trigger](d * (x / d) + (x % d)) by
    {
        lemma_fundamental_div_mod(x, d);
    }
}

// change to int because verus `*` does not support mixing nat and int
// I changed the input from nat to int (compared to the dafny library)
/// dividing a fraction by a divisor is equivalent to multiplying the fraction's 
/// denominator with the divisor
#[verifier::spinoff_prover]
pub proof fn lemma_div_denominator(x: int, c: int, d: int)
    requires 
        0 <= x,
        0 < c,
        0 < d
    ensures 
        c * d != 0,
        (x / c) / d == x / (c * d)
{
    lemma_mul_strictly_positive_auto();
    let r = x % (c as int * d as int);
    lemma_mod_properties_auto();

    lemma_div_pos_is_pos(r, c as int);
    if (r / c as int >= d) {
    ModINL::lemma_fundamental_div_mod(r, c as int);
    lemma_mul_inequality(d as int, r / c as int, c as int);
    lemma_mul_is_commutative_auto();
    }
    assert(r / (c as int) < d);

    lemma_mul_basics_auto();

    lemma_fundamental_div_mod_converse(r / c, d, 0, r / c);

    assert((r / c as int) % d as int == r / c as int);

    lemma_fundamental_div_mod(r, c);
    assert(c * (r / c) + r % c == r);
    
    assert(c * ((r / c as int) % d as int) + r % c as int == r);
    
    let k = x / (c as int * d as int);
    lemma_fundamental_div_mod(x, c * d);
    assert(x == (c * d) * (x / (c * d)) + x % (c * d));
    assert(r == x - (c * d) * (x / (c * d)));
    assert(r == x - (c * d) * k);

    calc! {
    (==)
    c * ((x / c) % d) + x % c;
    { lemma_mod_multiples_vanish(-k, x / c, d); lemma_mul_is_commutative_auto(); }
    c * ((x / c + (-k) * d) % d) + x % c;
    { lemma_hoist_over_denominator(x, (-k) * d, c as nat); }
    c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
    { lemma_mul_is_associative(-k, d, c); }
    c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
    { lemma_mul_unary_negation(k, d * c); }
    c * (((x + (-(k * (d * c)))) / c) % d) + x % c;    { lemma_mul_is_associative(k, d, c); }
    c * (((x + (-(k * d * c))) / c) % d) + x % c;
    { }
    c * (((x - k * d * c) / c) % d) + x % c;
    {
        lemma_mul_is_associative_auto();
        lemma_mul_is_commutative_auto();
    }
    c * ((r / c) % d) + x % c;
    { }
    c * (r / c) + x % c;
    { lemma_fundamental_div_mod(r, c);
        assert(r == c * (r / c) + r % c);
        lemma_mod_mod(x, c, d);
        assert(r % c == x % c);
    }
    r;
    { lemma_mod_is_mod_recursive_auto(); }
    r % (c * d);
    { }
    (x - (c * d) * k) % (c * d);
    { lemma_mul_unary_negation(c * d, k); }
    (x + (c * d) * (-k)) % (c * d);
    { lemma_mod_multiples_vanish(-k, x, c * d); }
    x % (c * d);
    }

    
    
    assert (c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d) ==> x - r == c * (x / c) - c * ((x / c) % d)) by {
        lemma_fundamental_div_mod(x, c);
    };
    
    assert((x / c) / d == x / (c * d)) by {
        lemma_fundamental_div_mod(x / c, d);
        lemma_mul_is_associative_auto();
        lemma_mul_is_distributive_auto();
        lemma_fundamental_div_mod(x, c * d);
        lemma_mul_equality_converse(c * d, (x / c) / d, x / (c * d));
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_denominator_auto()
    ensures
        forall |c: int, d: int| 0 < c && 0 < d ==> #[trigger](c * d) != 0,
        forall |x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d ==> #[trigger]((x / c) / d) == x / (c * d)
{
    lemma_mul_nonzero_auto();
    assert forall |x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d implies #[trigger]((x / c) / d) == x / (c * d) by
    {
        lemma_div_denominator(x, c, d);
    }
}

/// multiplying an integer by a fraction is equivalent to multiplying the integer by the
/// fraction's numerator
#[verifier::spinoff_prover]
pub proof fn lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < z
    ensures x * (y / z) <= (x * y) / z
{
    calc! {
    (==)
    (x * y) / z;
    (==)   { lemma_fundamental_div_mod(y, z); }
    (x * (z * (y / z) + y % z)) / z;
    (==)    { lemma_mul_is_distributive_auto(); }
    (x * (z * (y / z)) + x * (y % z)) / z;
    }

    assert ((x * (z * (y / z)) + x * (y % z)) / z >=  x * (y / z)) by {
        lemma_mod_properties_auto();
        lemma_mul_nonnegative(x, y % z);
        lemma_div_is_ordered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z);
        lemma_mul_is_associative_auto();
        lemma_mul_is_commutative_auto();
        lemma_div_multiples_vanish(x * (y / z), z);
    };
    // (>=)  {
    //     lemma_mod_properties_auto();
    //     lemma_mul_nonnegative(x, y % z);
    //     lemma_div_is_ordered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z); }
    // (x * (z * (y / z))) / z;
    //     { lemma_mul_is_associative_auto();
    //     lemma_mul_is_commutative_auto(); }
    // (z * (x * (y / z))) / z;
    //     { lemma_div_multiples_vanish(x * (y / z), z); }
    // x * (y / z);
    // }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_hoist_inequality_auto()
    ensures
        forall |x: int, y: int, z: int| #![trigger (x * (y / z)), ((x * y) / z)] 0 <= x && 0 < z ==> (x * (y / z)) <= ((x * y) / z),
{
    assert forall |x: int, y: int, z: int| 0 <= x && 0 < z implies #[trigger](x * (y / z)) <= #[trigger]((x * y) / z) by
    {
        lemma_mul_hoist_inequality(x, y, z);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires
        0 < d,
        0 <= a - a % d <= b < a + d - a % d,
    ensures a / d == b / d
{
    lemma_div_induction_auto(d, a - b, |ab: int| {let u = ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d});
}

#[verifier::spinoff_prover]
pub proof fn lemma_indistinguishable_quotients_auto()
    ensures
        forall |a: int, b: int, d: int| #![trigger (a / d), (b / d)] 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> (a / d) == (b / d)
{
    assert forall |a: int, b: int, d: int| 0 < d && 0 <= a - a % d <= b < a + d - a % d implies #[trigger](a / d) == #[trigger](b / d) by
    {
        lemma_indistinguishable_quotients(a, b, d);
    }
}

/// common factors from the dividend and divisor of a modulus operation can be factored out
#[verifier::spinoff_prover]
pub proof fn lemma_truncate_middle(x: int, b: int, c: int)
    requires 
        0 <= x,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * x) % (b * c) == b * (x % c)
{
    lemma_mul_strictly_positive_auto();
    lemma_mul_nonnegative_auto();
    calc! {
    (==)
    b * x;
    { ModINL::lemma_fundamental_div_mod(b * x, b * c); }
    (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
    { lemma_div_denominator(b * x, b, c); }
    (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
    { lemma_mul_is_commutative_auto(); lemma_div_by_multiple(x, b); }
    (b * c) * (x / c) + (b * x) % (b * c);
    }

    assert(b * x == (b * c) * (x / c) + b * (x % c)) by {
        ModINL::lemma_fundamental_div_mod(x, c);
        lemma_mul_is_distributive_auto();
        lemma_mul_is_associative_auto();
    };
    // calc ==> {
    // true;
    // { lemma_fundamental_div_mod(x, c); }
    // x == c * (x / c) + x % c;
    // b * x == b * (c * (x / c) + x % c);
    // { lemma_mul_is_distributive_auto(); }
    // b * x == b * (c * (x / c)) + b * (x % c);
    // { lemma_mul_is_associative_auto(); }
    // b * x == (b * c) * (x / c) + b * (x % c);
    // }
}

#[verifier::spinoff_prover]
pub proof fn lemma_truncate_middle_auto()
    ensures forall |x: int, b: int, c: int| #![trigger (b * (x % c))] 0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c)
{
    assert forall |x: int, b: int, c: int| 0 <= x && 0 < b && 0 < c && 0 < b * c implies #[trigger](b * (x % c)) == ((b * x) % (b * c)) by
    {
        lemma_truncate_middle(x, b, c);
    }
}

/// multiplying the numerator and denominator by an integer does not change the quotient
#[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires
        0 < x,
        0 <= a,
        0 < d,
    ensures
        0 < x * d,
        a / d == (x * a) / (x * d),
{
    lemma_mul_strictly_positive(x,d);
    calc! {
    (==)
    (x * a) / (x * d);
    {
        lemma_mul_nonnegative(x, a);
        lemma_div_denominator(x * a, x, d); 
    }
    ((x * a) / x) / d;
    { lemma_div_multiples_vanish(a, x); }
    a / d;
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_quotient_auto()
    ensures forall |x: int, a: int, d: int| #![trigger (a / d), (x * a), (x * d)] 0 < x && 0 <= a && 0 < d ==> 0 < x * d && a / d == (x * a) / (x * d)
{
    assert(true); // OBSERVE?????????
    assert forall |x: int, a: int, d: int| 0 < x && 0 <= a && 0 < d implies 0 < #[trigger](x * d) && #[trigger](a / d) == (#[trigger](x * a) / #[trigger](x * d)) by
    {
        if (0 < x && 0 <= a && 0 < d) {
        lemma_div_multiples_vanish_quotient(x, a, d);
        assert(0 < (x * d) && (a / d) == ((x * a) / (x * d)));
        }
    }
}

/// rounds down when adding an integer r to the dividend a that is smaller than the divisor d, and then
/// multiplying by d
#[verifier::spinoff_prover]
pub proof fn lemma_round_down(a: int, r: int, d: int)
    requires
        0 < d,
        a % d == 0,
        0 <= r < d,
    ensures
        a == d * ((a + r) / d),
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, a, |u: int| u % d == 0 ==> u == d * ((u + r) / d));
}

#[verifier::spinoff_prover]
pub proof fn lemma_round_down_auto()
    ensures forall |a: int, r: int, d: int| #![trigger (d * ((a + r) / d))] 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d),
{
    assert forall |a: int, r: int, d: int| 0 < d && a % d == 0 && 0 <= r < d implies #[trigger](d * ((a + r) / d)) == a by
    {
        lemma_round_down(a, r, d);
    }
}

// TO BE DISCUSSED
/// this is the same as writing x + (b/d) == x when b is less than d; this is true because (b/d) == 0
#[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires 
        0 < d,
        0 <= b < d,
    ensures 
        (d * x + b) / d == x
{
    lemma_div_auto(d);
    let f = |u: int| (d * u + b) / d == u;
    
    lemma_mul_auto();
    lemma_mul_induction(f);

    // OBSERVE: the original code uses the auto lemma, which cause the rlimit to complain
    // lemma_mul_induction_auto(x, f);
    assert(f(x));
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_fancy_auto()
    ensures forall |x: int, b: int, d: int| #![trigger (d * x + b) / d] 0 < d && 0 <= b < d ==> (d * x + b) / d == x,
{
    assert forall |x: int, b: int, d: int| 0 < d && 0 <= b < d implies #[trigger]((d * x + b) / d) == x by
    {
        lemma_div_multiples_vanish_fancy(x, b, d);
    }
}

/// multiplying an integer by a common numerator and denominator results in the original integer
#[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish(x: int, d: int)
    requires 0 < d
    ensures (d * x) / d == x
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_auto()
    ensures forall |x: int, d: int| #![trigger (d * x) / d] 0 < d ==> (d * x) / d == x,
{
    assert forall |x: int, d: int| 0 < d implies #[trigger]((d * x) / d) == x by
    {
        lemma_div_multiples_vanish(x, d);
    }
}

/// multiplying a whole number by a common numerator and denominator results in the original integer
#[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple(b: int, d: int)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{
    lemma_div_multiples_vanish(b, d);
    lemma_mul_auto(); // commutativity
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple_auto()
    ensures forall |b: int, d: int| #![trigger ((b * d) / d)] 0 <= b && 0 < d ==> (b * d) / d == b,
{
    assert forall |b: int, d: int| 0 <= b && 0 < d implies #[trigger]((b * d) / d) == b by
    {
        lemma_div_by_multiple(b, d);
    }
}

/// a dividend y that is a positive multiple of the divisor z will always yield a greater quotient 
/// than a dividend x that is less than y
#[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires
        x < y,
        y == m * z,
        0 < z,
    ensures
        x / z < y / z
{
    lemma_mod_multiples_basic(m, z);
    lemma_div_induction_auto(z, y - x, |yx: int| {let u = yx + x; x < u && u % z == 0 ==> x / z < u / z});
}

#[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple_is_strongly_ordered_auto()
    ensures forall |x: int, y: int, m: int, z: int| #![trigger x / z, m * z, y / z] x < y && y == m * z && 0 < z ==> x / z < y / z,
{
    assert forall |x: int, y: int, m: int, z: int| x < y && y == #[trigger](m * z) && 0 < z implies #[trigger](x / z) < #[trigger](y / z) by
    {
        lemma_div_by_multiple_is_strongly_ordered(x, y, m, z);
    }
}

/// if an integer a is less than or equal to the product of two other integers b and c, then the 
/// quotient of a/b will be less than or equal to c
#[verifier::spinoff_prover]
pub proof fn lemma_multiply_divide_le(a: int, b: int, c: int)
    requires
        0 < b,
        a <= b * c,
    ensures
        a / b <= c
{
    lemma_mod_multiples_basic(c, b);
    lemma_div_induction_auto(b, b * c - a, |i: int| 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b);
    lemma_div_multiples_vanish(c, b);
}

proof fn lemma_multiply_divide_le_auto()
    ensures forall |a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a <= b * c ==> a / b <= c,
{
    assert forall |a: int, b: int, c: int| 0 < b && a <= #[trigger](b * c) implies #[trigger](a / b) <= c by
    {
        lemma_multiply_divide_le(a, b, c);
    }
}

/// if an integer a is less than the product of two other integers b and c, then the quotient 
/// of a/b will be less than c
// got disproved at some point
#[verifier::spinoff_prover]
pub proof fn lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires 
        0 < b,
        a < b * c,
    ensures
        a / b < c
{
    lemma_mod_multiples_basic(c, b);
    let f = |i: int| 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b;
    lemma_div_induction_auto(b, b * c - a, f);
    assert(f(b * c - a)); // OBSERVE
    lemma_div_multiples_vanish(c, b);
}

#[verifier::spinoff_prover]
pub proof fn lemma_multiply_divide_lt_auto()
    ensures forall |a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a < b * c ==> a / b < c,
{
    assert forall |a: int, b: int, c: int| 0 < b && a < #[trigger](b * c) implies #[trigger](a / b) < c by
    {
        lemma_multiply_divide_lt(a, b, c);
    }
}

/// expresses the equality of giving fractions common denominators and then adding them together
#[verifier::spinoff_prover]
pub proof fn lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d as int + j == (x + j * d) / d as int
{
    lemma_div_auto(d as int);
    let f = |u: int| x / d as int + u == (x + u * d) / d as int;
    // OBSERVE: push precondition on its on scope
    assert (  f(0)
        && (forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger]f(crate::NonLinearArith::Internals::MulInternals::add(i, 1)))
        && (forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger]f(crate::NonLinearArith::Internals::MulInternals::sub(i, 1)))) by {
            lemma_mul_auto();
    }
    lemma_mul_induction(f);
    assert(f(j));
}

#[verifier::spinoff_prover]
pub proof fn lemma_hoist_over_denominator_auto()
    ensures forall |x: int, j: int, d: nat| #![trigger x / d as int + j] 0 < d ==> x / d as int + j == (x + j * d) / d as int,
{
    assert forall |x: int, j: int, d: nat| 0 < d implies #[trigger](x / d as int + j) == (x + j * d) / d as int by
    {
        lemma_hoist_over_denominator(x, j, d);
    }
}
//     ensures forall x: int, j: int, d: nat {:trigger  x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
// {
//     forall x: int, j: int, d: nat | 0 < d
//     ensures x / d + j == (x + j * d) / d
//     {
//     lemma_hoist_over_denominator(x, j, d);
//     }
// }

#[verifier::spinoff_prover]
pub proof fn lemma_part_bound1(a: int, b: int, c: int)
    requires 
        0 <= a,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * (a / b) % (b * c)) <= b * (c - 1)
{
    lemma_mul_strictly_positive_auto();
    calc! {
    (==)
    b * (a / b) % (b * c);
    { ModINL::lemma_fundamental_div_mod(b * (a / b), b * c); }
    b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
    { lemma_mul_is_associative_auto(); }
    b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
    { lemma_mul_is_distributive_auto(); }
    b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }

    assert(b * (a / b) % (b * c) <= b * (c - 1)) by
        { lemma_mul_is_commutative_auto(); lemma_mul_inequality_auto(); };

    // calc is an overkill, but it would be nice if calc! supports ==>
    // calc! {
    // (==>)
    // true;
    // { lemma_mod_properties_auto(); }
    // b * (a / b) % (b * c) < b * c;
    // b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) < b * c;
    // { lemma_mul_is_commutative_auto(); lemma_mul_strict_inequality_converse_auto(); }
    // ((a / b) - (c * ((b * (a / b)) / (b * c)))) < c;
    // ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= c - 1;
    // { lemma_mul_is_commutative_auto(); lemma_mul_inequality_auto(); }
    // b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= b * (c - 1);
    // b * (a / b) % (b * c) <= b * (c - 1);
    // }
}

proof fn lemma_part_bound1_auto()
    ensures forall |a: int, b: int, c: int| #![trigger (b * (a / b) % (b * c))] 0 <= a && 0 < b && 0 < c ==> 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1),
{
    assert forall |a: int, b: int, c: int| 0 <= a && 0 < b && 0 < c implies 0 < #[trigger](b * c) && #[trigger](b * (a / b) % (b * c)) <= b * (c - 1) by
    {
        lemma_part_bound1(a, b, c);
    }
}


// /*******************************************************************************
//  * Modulus:
//  *******************************************************************************/

/// the common syntax of the modulus operation results in the same remainder as recursively
/// calculating the modulus
#[verifier::spinoff_prover]
pub proof fn lemma_mod_is_mod_recursive(x: int, m: int)
    requires m > 0
    ensures mod_recursive(x, m) == x % m
    decreases (if x < 0 { -x + m } else { x })
{
    reveal(mod_recursive);
    if x < 0 {
    calc! {
        (==)
        mod_recursive(x, m); {}
        mod_recursive(x + m, m);
        { lemma_mod_is_mod_recursive(x + m, m); }
        (x + m) % m;
        { lemma_add_mod_noop(x, m, m); }
        ((x % m) + (m % m)) % m;
        { lemma_mod_basics_auto(); }
        (x % m) % m;
        { lemma_mod_basics_auto(); }
        x % m;
    }
    } else if x < m {
    lemma_small_mod(x as nat, m as nat);
    } else {
    calc! {
        (==)
        mod_recursive(x, m); {}
        mod_recursive(x - m, m);
        { lemma_mod_is_mod_recursive(x - m, m); }
        (x - m) % m;
        { lemma_sub_mod_noop(x, m, m); }
        ((x % m) - (m % m)) % m;
        { lemma_mod_basics_auto(); }
        (x % m) % m;
        { lemma_mod_basics_auto(); }
        x % m;
    }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_is_mod_recursive_auto()
    ensures forall |x: int, d: int| d > 0 ==> mod_recursive(x, d) == #[trigger](x % d)
{
    reveal(mod_recursive);
    assert forall |x: int, d: int| d > 0 implies mod_recursive(x, d) == #[trigger](x % d) by
    {
        lemma_mod_is_mod_recursive(x, d);
    };
}

/// proves basic properties of the modulus operation: any integer divided by itself does not have a
/// remainder; performing (x % m) % m gives the same result as simply perfoming x % m 
#[verifier::spinoff_prover]
pub proof fn lemma_mod_basics_auto()
    ensures 
        forall |m: int|  m > 0 ==> #[trigger](m % m) == 0,
        forall |x: int, m: int|  m > 0 ==> #[trigger]((x % m) % m) == x % m,
{
    assert forall |m: int| m > 0 implies #[trigger](m % m) == 0 by {
        lemma_mod_auto(m);
    };
    assert forall |x: int, m: int| m > 0 implies #[trigger]((x % m) % m) == x % m by {
        lemma_mod_auto(m);
    };
}

/// describes the properties of the modulus operation including those described in lemma_mod_basics_auto. 
/// This lemma also states that the remainder of any division will be less than the divisor's value
#[verifier::spinoff_prover]
pub proof fn lemma_mod_properties_auto()
    ensures 
        forall |m: int| m > 0 ==> #[trigger](m % m) == 0,
        forall |x: int, m: int| m > 0 ==> #[trigger]((x % m) % m) == x % m,
        forall |x: int, m: int| m > 0 ==> 0 <= #[trigger](x % m) < m,
{
    lemma_mod_basics_auto();

    assert forall |x: int, m: int| m > 0 implies 0 <= #[trigger](x % m) < m by
    {
    lemma_mod_auto(m);
    }
}

/// the remainder of a natural number x divided by a natural number d will be less
/// than or equal to x
#[verifier::spinoff_prover]
pub proof fn lemma_mod_decreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
{
    lemma_mod_auto(m as int);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_decreases_auto()
    ensures forall |x: nat, m: nat| 0 < m ==> #[trigger](x % m) <= x,
{
    assert forall |x: nat, m: nat| 0 < m implies #[trigger](x % m) <= x by
    {
        lemma_mod_decreases(x, m);
    }
}

/// if x % y is zero and x is greater than zero, x is greater than y.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_is_zero(x: nat, m: nat)
    requires
        x > 0 && m > 0,
        x % m == 0,
    ensures 
        x >= m
{
    if (x < m) {
        lemma_small_mod(x, m);
    }
    // calc ==> {
    // x < m;
    // { lemma_small_mod(x, m); }
    // x % m == x;
    // false;
    // }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_is_zero_auto()
    ensures forall |x: nat, m: nat| x > 0 && m > 0 && #[trigger](x % m) == 0 ==> x >= m,
{
    assert forall |x: nat, m: nat| x > 0 && m > 0 && #[trigger](x % m) == 0 implies x >= m by
    {
        lemma_mod_is_zero(x, m);
    }
}

/// a dividend that is any multiple of the divisor will result in a remainder of 0
#[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_basic(x: int, m: int)
    requires m > 0
    ensures (x * m) % m == 0
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (u * m) % m == 0;
    lemma_mul_induction(f);
    assert(f(x));
    // lemma_mul_induction_auto(x, |u: int| (u * m) % m == 0);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_basic_auto()
    ensures forall |x: int, m: int| m > 0 ==> #[trigger]((x * m) % m) == 0,
{
    assert forall |x: int, m: int| m > 0 implies #[trigger]((x * m) % m) == 0 by
    {
        lemma_mod_multiples_basic(x, m);
    }
}

/// the remainder of adding the divisor m to the dividend b will be the same
/// as simply performing b % m
#[verifier::spinoff_prover]
pub proof fn lemma_mod_add_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_add_multiples_vanish_auto()
    ensures forall |b: int, m: int| m > 0 ==> ((m + b) % m) == #[trigger](b % m),
{
    assert forall |b: int, m: int| m > 0 implies ((m + b) % m) == #[trigger](b % m) by
    {
        lemma_mod_add_multiples_vanish(b, m);
    }
}

/// the remainder of subtracting the divisor m from the dividend b will be the same
/// as simply performing b % m
#[verifier::spinoff_prover]
pub proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_sub_multiples_vanish_auto()
    ensures forall |b: int, m: int| m > 0 ==> ((-m + b) % m) == #[trigger](b % m),
{
    assert forall |b: int, m: int| m > 0 implies ((-m + b) % m) == #[trigger](b % m) by
    {
        lemma_mod_sub_multiples_vanish(b, m);
    }
}

/// the remainder of adding any multiple of the divisor m to the dividend b will be the same
/// as simply performing b % m
#[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires 0 < m
    ensures (m * a + b) % m == b % m
    decreases (if a > 0 { a } else { -a })
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    lemma_mul_induction_auto(a, |u: int| (m * u + b) % m == b % m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_vanish_auto()
    ensures forall |a: int, b: int, m: int| m > 0 ==> #[trigger]((m * a + b) % m) == b % m,
{
    assert forall |a: int, b: int, m: int| m > 0 implies #[trigger]((m * a + b) % m) == b % m by
    {
        lemma_mod_multiples_vanish(a, b, m);
    }
}

/// proves equivalent forms of modulus subtraction
#[verifier::spinoff_prover]
pub proof fn lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires 
        0 < d, 
        0 <= s <= x % d
    ensures 
        x % d - s % d == (x - s) % d as int
{
    lemma_mod_auto(d as int);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_subtraction_auto()
    ensures forall |x: nat, s: nat, d: nat| #![trigger ((x - s) % d as int)] 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d as int,
{
    assert forall |x: nat, s: nat, d: nat| 0 < d && 0 <= s <= x % d implies x % d - s % d == #[trigger]((x - s) % d as int) as int by
    {
        lemma_mod_subtraction(x, s, d);
    }
}

/// describes expanded and succinct version of modulus operator in relation to addition (read "ensures")
#[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x + y) % m
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x + y) % m] 0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) + (y % m)) % m == #[trigger]((x + y) % m) by
    {
        lemma_add_mod_noop(x, y, m);
    }
}

/// describes expanded and succinct version of modulus operator in relation to addition (read "ensures")
#[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x + y) % m
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x + y) % m] 0 < m ==> (x + (y % m)) % m == (x + y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x + (y % m)) % m == #[trigger]((x + y) % m) by
    {
        lemma_add_mod_noop_right(x, y, m);
    }
}

/// describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures")
#[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x - y) % m
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) - (y % m)) % m == #[trigger]((x - y) % m) by
    {
        lemma_sub_mod_noop(x, y, m);
    }
}

/// describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures")
#[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x - y) % m
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| #![trigger ((x - y) % m)] 0 < m ==> (x - (y % m)) % m == (x - y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x - (y % m)) % m == #[trigger]((x - y) % m) by
    {
        lemma_sub_mod_noop_right(x, y, m);
    }
}

/// proves equivalent forms of modulus addition
#[verifier::spinoff_prover]
pub proof fn lemma_mod_adds(a: int, b: int, d: int)
    requires 0 < d
    ensures 
        a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
        (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
{
    lemma_mul_auto();
    lemma_div_auto(d);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_adds_auto()
    ensures forall |a: int, b: int, d: int| #![trigger ((a + b) % d)] 0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
{
    assert forall |a: int, b: int, d: int| 0 < d implies a % d + b % d == #[trigger]((a + b) % d) + d * ((a % d + b % d) / d) by
    {
        lemma_mod_adds(a, b, d);
    }
}

// {:vcs_split_on_every_assert}
// this proof times out a lot
#[verifier::spinoff_prover]
pub proof fn lemma_mod_neg_neg(x: int, d: int)
    requires 0 < d
    ensures x % d == (x * (1 - d)) % d
{
    assert ((x - x * d) % d == x % d) by {
        let f = |i: int| (x - i * d) % d == x % d;
        lemma_mul_auto();
        assert (  f(0)
                && (forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger]f(crate::NonLinearArith::Internals::MulInternals::add(i, 1)))
                && (forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger]f(crate::NonLinearArith::Internals::MulInternals::sub(i, 1))))
        by {
            lemma_mod_auto(d);
        };
        lemma_mul_induction(f);
        assert(f(x));
        // lemma_mul_induction_auto(x, f);
    }
    // lemma_mod_auto(d);
    lemma_mul_auto();
}


/// proves the validity of the quotient and remainder
// {:timeLimitMultiplier 5} from dafny
// this proof breaks a lot when introducing new auto lemma
// this proof verifies for a long time
// now it verifies for 2-8s ish
#[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
    requires 
        d != 0,
        0 <= r < d,
        x == q * d + r,
    ensures 
        q == x / d,
        r == x % d
{
    // TODO: shorten this?
    // TO BE DISCUSSED
    // OBSERVE
    // making mul_auto in the larger context will exceed rlimit
    let f = |u: int| u == (u * d + r) / d;
    assert(f(q)) by {
        assert
        forall |i: int| i >= 0 && #[trigger] f(i) implies #[trigger] f(crate::NonLinearArith::Internals::MulInternals::add(i, 1))
        by {
            lemma_div_auto(d);
            // lemma_mul_auto();
            assert(i * d + r + d == (i + 1) * d + r) by {
                lemma_mul_auto();
            };
        };
        assert
            forall |i: int| i <= 0 && #[trigger] f(i) implies #[trigger] f(crate::NonLinearArith::Internals::MulInternals::sub(i, 1))
         by {
            lemma_div_auto(d);
            lemma_mul_auto();
        };
        assert(f(0)) by {
            assert(0 == (0 * d + r) / d) by {
                lemma_mul_by_zero_is_zero_auto();
                crate::NonLinearArith::Internals::DivInternals::lemma_div_basics(d);
            };
        };
        lemma_mul_induction(f);
        assert(f(q));
    }
    let g = |u: int| r == (u * d + r) % d;
    assert(g(q)) by {
        lemma_div_auto(d);
        assert
        forall |i: int| i >= 0 && #[trigger] g(i) implies #[trigger] g(crate::NonLinearArith::Internals::MulInternals::add(i, 1))
        by {
            lemma_div_auto(d);
            lemma_mul_auto();
        };
        assert
            forall |i: int| i <= 0 && #[trigger] g(i) implies #[trigger] g(crate::NonLinearArith::Internals::MulInternals::sub(i, 1))
         by {
            lemma_div_auto(d);
            lemma_mul_auto();
        }
        assert(g(0)) by {
            lemma_div_auto(d);
            lemma_mul_auto();
        };
        lemma_mul_induction(g);
        assert(g(q));
    };
    // the original dafny proof
    // lemma_div_auto(d);
    // lemma_mul_induction_auto(q, |u: int| u == (u * d + r) / d);
    // lemma_mul_induction_auto(q, |u: int| r == (u * d + r) % d);
}

// // {:timeLimitMultiplier 5}
// // TO DO
// #[verifier::spinoff_prover]
// proof fn lemma_fundamental_div_mod_converse_auto()
//     ensures 
//         forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == (x / d) && r == #[trigger](x % d),
//         // forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == #[trigger](x / d),
//         // forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> r == #[trigger](x % d),
// {
//     assert forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) implies q == (x / d) && r == #[trigger](x % d) by
//     {
//         if ( d != 0 && 0 <= r < d && x == (q * d + r)) {
//         lemma_fundamental_div_mod_converse(x, d, q, r);
//         }
//     }
// }
//     ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d}
//             :: d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d && r == x % d
// {
//     forall x: int, d: int, q: int, r: int | d != 0 && 0 <= r < d && x == q * d + r
//     ensures q == x / d && r == x % d
//     {
//     lemma_fundamental_div_mod_converse(x, d, q, r);
//     }
// }


/// the remainder of any natural number x divided by a positive integer m is always less than m
#[verifier::spinoff_prover]
pub proof fn lemma_mod_pos_bound(x: int, m: int)
    requires 
        0 <= x,
        0 < m,
    ensures  0 <= x % m < m
    decreases x
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_pos_bound_auto()
    ensures forall |x: int, m: int| 0 <= x && 0 < m ==> 0 <= #[trigger](x % m) < m,
{
    assert forall |x: int, m: int| 0 <= x && 0 < m implies 0 <= #[trigger](x % m) < m by
    {
        lemma_mod_pos_bound(x, m);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * y % m == x * y % m
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, |u: int| (x % m) * u % m == x * u % m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_left_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> (x % m) * y % m == #[trigger](x * y % m),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x % m) * y % m == #[trigger](x * y % m) by
    {
        lemma_mul_mod_noop_left(x, y, m);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == (x * y) % m
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, |u: int| u * (y % m) % m == (u * y) % m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> x * (y % m) % m == #[trigger]((x * y) % m),
{
    assert forall |x: int, y: int, m: int| 0 < m implies x * (y % m) % m == #[trigger]((x * y) % m) by
    {
        lemma_mul_mod_noop_right(x, y, m);
    }
}

/// combines previous no-op mod lemmas into a general, overarching lemma
// TODO: verifies for a long time when spinoff prover is used
#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires 0 < m
    ensures 
        ((x % m) * y      ) % m == (x * y) % m,
        ( x      * (y % m)) % m == (x * y) % m,
        ((x % m) * (y % m)) % m == (x * y) % m
{
    lemma_mod_properties_auto();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_general_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == #[trigger]((x * y) % m)),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == #[trigger]((x * y) % m)) by
    {
        lemma_mul_mod_noop_general(x, y, m);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x * y) % m
{
    lemma_mul_mod_noop_general(x, y, m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> ((x % m) * (y % m) % m == #[trigger]((x * y) % m)),
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) * (y % m) % m == #[trigger]((x * y) % m)) by
    {
        lemma_mul_mod_noop(x, y, m);
    }
}

/// proves modulus equivalence in two forms
#[verifier::spinoff_prover]
pub proof fn lemma_mod_equivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
{
    lemma_mod_auto(m);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_equivalence_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x % m), (y % m)] 0 < m ==> (x % m == y % m <==> (x - y) % m == 0),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (#[trigger](x % m) == #[trigger](y % m) <==> (x - y) % m == 0) by
    {
        lemma_mod_equivalence(x, y, m);
    }
}

// // TODO: the following two proofs are styled very differently from dafny
// /// true if x%n and y%n are equal */
// pub open spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
//     recommends m > 0
//     // ensures x % m == y % m <==> (x - y) % m == 0
// {
//     // lemma_mod_equivalence(x, y, m);
//     x % m == y % m <==> (x - y) % m == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
// }

// TODO: even introducing this fact will break proofs
// #[verifier::opaque]
// pub closed spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
// {
//     x % m == y % m <==> (x - y) % m == 0
// }

// having a function name is_mod_equialent is just too risky
// I change the following two proofs by replacing is_mod_equivalent
/// if x % m == y % m, then (x * z) % m == (y * z) % m.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_mul_equivalent(x: int, y: int, z: int, m: int)
    requires
        m > 0,
        // is_mod_equivalent(x, y, m),
        x % m == y % m <==> (x - y) % m == 0,
    ensures
        // is_mod_equivalent(x * z, y * z, m)
        (x * z) % m == (y * z) % m <==> (x * z - y * z) % m == 0
{
    // reveal(is_mod_equivalent);
    lemma_mul_mod_noop_left(x, z, m);
    lemma_mul_mod_noop_left(y, z, m);
    lemma_mod_equivalence(x, y, m);
    lemma_mod_equivalence(x * z, y * z, m);
}

// #[verifier::spinoff_prover]
// proof fn lemma_mod_mul_equivalent_auto()
//     ensures forall |x: int, y: int, z: int, m: int|  m > 0 && ( x % m == y % m <==> (x - y) % m == 0) ==> #[trigger]is_mod_equivalent(x * z, y * z, m),
// {
//     assert forall |x: int, y: int, z: int, m: int| m > 0 && is_mod_equivalent(x, y, m) implies #[trigger]is_mod_equivalent(x * z, y * z, m) by
//     {
//         lemma_mod_mul_equivalent(x, y, z, m);
//     }
// }
//     ensures forall x: int, y: int, z: int, m: int
//             {:trigger is_mod_equivalent(x * z, y * z, m)}
//             :: m > 0 && is_mod_equivalent(x, y, m) ==> is_mod_equivalent(x * z, y * z, m)
// {
//     forall x: int, y: int, z: int, m: int | m > 0 && is_mod_equivalent(x, y, m)
//     ensures is_mod_equivalent(x * z, y * z, m)
//     {
//     lemma_mod_mul_equivalent(x, y, z, m);
//     }
// }

/// the remainder can increase with a larger divisor
#[verifier::spinoff_prover]
pub proof fn lemma_mod_ordering(x: int, k: int, d: int)
    requires 
        1 < d,
        0 < k,
    ensures 
        0 < d * k,
        x % d <= x % (d * k)
{
    lemma_mul_strictly_increases(d,k);
    calc! {
    (==)
    x % d + d * (x / d);
    { lemma_fundamental_div_mod(x, d); }
    x;
    { lemma_fundamental_div_mod(x, d * k); }
    x % (d * k) + (d * k) * (x / (d * k));
    { lemma_mul_is_associative_auto(); }
    x % (d * k) + d * (k * (x / (d * k)));
    }
    calc! {
    (==)
    x % d;
    { lemma_mod_properties_auto(); }
    (x % d) % d;
    { lemma_mod_multiples_vanish(x / d  - k * (x / (d * k)), x % d, d); }
    (x % d + d * (x / d  - k * (x / (d * k)))) % d;
    { lemma_mul_is_distributive_sub_auto(); }
    (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d; {}
    (x % (d * k)) % d;
    }

    assert( (x % (d * k)) % d <= x % (d * k)) by {
        lemma_mod_properties_auto();
        lemma_mod_decreases((x % (d * k)) as nat, d as nat);
    };
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_ordering_auto()
    ensures forall |x: int, k: int, d: int| 1 < d && 0 < k ==> (x % d <= #[trigger](x % (d * k))),
{
    assert forall |x: int, k: int, d: int| 1 < d && 0 < k implies (x % d <= #[trigger](x % (d * k))) by
    {
        lemma_mod_ordering(x, k, d);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_mod(x: int, a: int, b: int)
    requires 
        0 < a,
        0 < b,
    ensures
        0 < a * b,
        (x % (a * b)) % a == x % a,
{
    lemma_mul_strictly_positive_auto();
    calc! {
    (==)
    x;
    { lemma_fundamental_div_mod(x, a * b); }
    (a * b) * (x / (a * b)) + x % (a * b);
    { lemma_mul_is_associative_auto(); }
    a * (b * (x / (a * b))) + x % (a * b);
    { lemma_fundamental_div_mod(x % (a * b), a); }
    a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a;
    { lemma_mul_is_distributive_auto(); }
    a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    lemma_mod_properties_auto();
    lemma_mul_is_commutative_auto();
    lemma_fundamental_div_mod_converse(x, a, b * (x / (a * b)) + x % (a * b) / a, (x % (a * b)) % a);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_mod_auto()
    ensures forall |x: int, a: int, b: int| #![trigger (a * b), (x % a)](0 < a && 0 < b) ==> ((0 < a * b) && ((x % (a * b)) % a == (x % a))),
{
    assert(true); // OBSERVE??????
    assert forall |x: int, a: int, b: int| 0 < a && 0 < b implies 0 < #[trigger](a * b) && ((x % (a * b)) % a == #[trigger](x % a)) by
    {
        lemma_mod_mod(x, a, b);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_part_bound2(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        y * z > 0,
        (x % y) % (y * z) < y,
{
    lemma_mul_strictly_positive_auto();
    lemma_mod_properties_auto();
    assert(x % y < y);
    lemma_mul_increases_auto();
    lemma_mul_is_commutative_auto();
    assert(y <= y * z);
    assert(0 <= x % y < y * z);
    lemma_mod_properties_auto();
    lemma_small_mod((x % y) as nat, (y * z) as nat);
    assert((x % y) % (y * z) == x % y);
}

// // TODO: bug
// // TO BE DISCUSSED
// // Even introducing this fact breaks proof here and there
// #[verifier::spinoff_prover]
// proof fn lemma_part_bound2_auto()
//     // ensures forall |x: int, y: int, z: int| #![trigger (y * z), (x % y)] (0 <= x && 0 < y && 0 < z) ==> (y * z > 0 && (x % y) % (y * z) < y),
//     // ensures forall |x: int, y: int, z: int| (0 <= x && 0 < y && 0 < z) ==> ((#[trigger](y * z) > 0) && ((#[trigger](x % y)) % (y * z) < y))
//     ensures 
//         forall |y: int, z: int| (0 < y && 0 < z) ==> #[trigger](y * z) > 0,
//         forall |x: int, y: int, z: int| (0 <= x && 0 < y && 0 < z) ==> (#[trigger](x % y) % #[trigger](y * z) < y),

    
// {
//     assume(forall |y: int, z: int| (0 < y && 0 < z) ==> #[trigger](y * z) > 0);
//     assume(forall |x: int, y: int, z: int| (0 <= x && 0 < y && 0 < z) ==> (#[trigger](x % y) % #[trigger](y * z) < y));

//     // assume(forall |x: int, y: int, z: int| (0 <= x && 0 < y && 0 < z) ==> (#[trigger](y * z) > 0 && (#[trigger](x % y)) % (y * z) < y));
//     // assert forall |x: int, y: int, z: int| (0 <= x && 0 < y && 0 < z) implies (#[trigger](y * z) > 0 && #[trigger](x % y) % (y * z) < y) by
//     // {
//     //     if 0 <= x && 0 < y && 0 < z {
//     //         lemma_part_bound2(x, y, z);
//     //     }
//     //     lemma_part_bound2(x, y, z);
//     // }
// }

/* ensures the validity of an expanded form of the modulus operation,
as expressed in the pre and post conditions */
#[verifier::spinoff_prover]
pub proof fn lemma_mod_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        y * z > 0,
        x % (y * z) == y * ((x / y) % z) + x % y
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    assert(0 <= x / y);

    // translated the calc proof in lemma_breakdown
    assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z) by {
        lemma_part_bound1(x, y, z);
        lemma_part_bound2(x, y, z);
        lemma_mul_basics_auto();
        lemma_mul_is_distributive_auto();
    };

    calc! {
    (==)
    x % (y * z);
    { lemma_fundamental_div_mod(x, y); }
    (y * (x / y) + x%  y) % (y * z);
    {
        lemma_mod_properties_auto();
        assert(0 <= x % y);
        lemma_mul_nonnegative(y, x / y);
        assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
        lemma_mod_adds(y * (x / y), x % y, y * z);
    }
    (y * (x / y)) % (y * z) + (x % y) % (y * z);
    {
        lemma_mod_properties_auto();
        lemma_mul_increases(z, y);
        lemma_mul_is_commutative_auto();
        assert(x % y < y && y <= y * z);
        lemma_small_mod((x % y) as nat, (y * z) as nat);
        assert((x % y) % (y * z) == x % y);
    }
    (y * (x / y)) % (y * z) + x % y;
    { lemma_truncate_middle(x / y, y, z); }
    y * ((x / y) % z) + x % y;
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_breakdown_auto()
    ensures forall |x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z ==> y * z > 0 && #[trigger](x % (y * z)) == y * ((x / y) % z) + x % y,
{
    assert forall |x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z implies y * z > 0 && #[trigger](x % (y * z)) == y * ((x / y) % z) + x % y by
    {
        lemma_mod_breakdown(x, y, z);
    }
}

}