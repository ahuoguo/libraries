//! Lemma for multiplication

/* Every lemma comes in 2 forms: 'lemma_property' and 'lemma_property_auto'. The
former takes arguments and may be more stable and less reliant on Z3
heuristics. The latter includes automation and its use requires less effort */

use vstd::prelude::*;

verus! {

use crate::NonLinearArith::Internals::MulInternalsNonlinear as MulINL;

use crate::NonLinearArith::Internals::MulInternals::*;

use crate::NonLinearArith::Internals::GeneralInternals::is_le;

/// The built-in syntax of multiplication results in the same product as multiplication
/// through recursive addition
pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
    ensures (x * y) == mul_recursive(x, y)
{
    if (x >= 0) { 
        lemma_mul_is_mul_pos(x, y);
        assert (x * y == mul_pos(x, y));
        // assert((x * y) == mul_recursive(x, y));
    }
    else { 
        lemma_mul_is_mul_pos(-x, y);
        assert (-1 * -x * y == x * y);
        assert(x < 0);
        // assert( mul_recursive(x, y) == -1 * mul_pos(-1 * x, y)); // it cannot run -x??
        assert (-x * y == mul_pos(-x, y));
        assert(-1 * mul_pos(-1 * x, y) == -1 * (-x * y));
        assert( -1 * (-1 * (x * y)) == (-1 * -1) * (x * y)) by { lemma_mul_is_associative(-1, -1, (x * y)) };
        assert (x * y == -1 * (-1 * (x * y)));
        assert (x * y == -1 * (-1 * (x * y)));
        assert (x * y == -1 * (-x * y)) by { lemma_mul_is_associative(-1, -x, y) };
        assert((x * y) == mul_recursive(x, y));

    }
}

pub proof fn lemma_mul_is_mul_recursive_auto()
    ensures forall |x: int, y: int| x * y == mul_recursive(x, y)
{
    assert forall |x: int, y: int| x * y == mul_recursive(x, y) by { 
        lemma_mul_is_mul_recursive(x, y) };
}

/// the built-in syntax of multiplying two positive integers results in the same product as 
/// MulPos, which is achieved by recursive addition
pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
{
    // How does dafny `reveal` work, and why is it different here in verus?
    lemma_mul_induction_auto(x, |u: int| u >= 0 ==> u * y == mul_pos(u, y));
}

/// ensures that the basic properties of multiplication, including the identity and zero properties
pub proof fn lemma_mul_basics(x: int)
    ensures 
        0 * x == 0,
        x * 0 == 0,
        x * 1 == x,
        1 * x == x,
{}

// expreimental
pub proof fn lemma_mul_basics_auto()
    ensures 
        forall_arith(|x: int| #[trigger](0 * x) == 0),
        forall_arith(|x: int| #[trigger](x * 0) == 0),
        forall_arith(|x: int| #[trigger](1 * x) == x),
        forall_arith(|x: int| #[trigger](x * 1)  == x),
{}

/// multiplying two nonzero integers will never result in 0 as the poduct
// property of being an integral domain
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
{
    MulINL::lemma_mul_nonzero(x, y);
}

pub proof fn lemma_mul_nonzero_auto()
    ensures forall |x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0
{
    assert forall |x: int, y: int| #[trigger](x * y) != 0 <==> x != 0 && y != 0 by
    {
    lemma_mul_nonzero(x, y);
    }
}

/// any integer multiplied by 0 results in a product of 0
pub proof fn lemma_mul_by_zero_is_zero_auto()
    ensures forall |x: int| (#[trigger](x * 0) == 0 && #[trigger](0 * x) == 0)
{
    assert forall |x: int| ((#[trigger](x * 0)) == 0 && #[trigger](0 * x) == 0) by
    {
    lemma_mul_basics(x);
    }
}

/// multiplication is associative
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
{
    MulINL::lemma_mul_is_associative(x, y, z);
}

// experimental
/// multiplication is always associative for all integers
proof fn lemma_mul_is_associative_auto()
    ensures forall|x: int, y: int, z: int| #[trigger](x * (y * z)) == #[trigger]((x * y) * z)
{
    assert forall|x: int, y: int, z: int| #[trigger](x * (y * z)) == #[trigger]((x * y) * z)
    by {
        lemma_mul_is_associative(x, y, z);
    }
    // forall (x: int, y: int, z: int)
    // ensures x * (y * z) == (x * y) * z
    // {
    // lemma_mul_is_associative(x, y, z);
    // }
}

/// multiplication is commutative
pub proof fn lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
{}

/// multiplication is always commutative for all integers
pub proof fn lemma_mul_is_commutative_auto()
    ensures forall |x: int, y: int| #[trigger](x * y) == (y * x)
{}

/// the product of two integers is greater than the value of each individual integer
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires 
        x != 0,
        y != 0,
        0 <= x * y,
    ensures 
        x * y >= x && x * y >= y
{
    MulINL::lemma_mul_ordering(x, y);
}

/// the product of two positive integers is always greater than the individual value of either 
/// multiplied integer
proof fn lemma_mul_ordering_auto()
    ensures forall |x: int, y: int| (0 != x && 0 != y && #[trigger] (x * y) >= 0) ==> x * y >= x && #[trigger] (x * y) >= y,
{
    assert
    forall |x: int, y: int| 0 != x && 0 != y && x * y >= 0 ==> #[trigger](x * y) >= x && #[trigger](x * y) >= y
    by 
    {
        if 0 != x && 0 != y && x * y >= 0 { lemma_mul_ordering(x, y); }
    }
}


pub proof fn lemma_mul_equality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
{}

pub proof fn lemma_mul_equality_auto()
    ensures forall |x: int, y: int, z: int| x == y ==> #[trigger](x * z) == #[trigger](y * z)
{
    assert forall |x: int, y: int, z: int| x == y ==> #[trigger](x * z) == #[trigger](y * z)
    by
    { if x == y { lemma_mul_equality(x, y, z); } }
}

/// two integers that are multiplied by a positive number will maintain their numerical order
pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires 
        x <= y,
        z >= 0
    ensures  x * z <= y * z
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// any two integers that are multiplied by a positive number will maintain their numerical order
pub proof fn lemma_mul_inequality_auto()
    ensures forall |x: int, y: int, z: int| x <= y && z >= 0 ==> #[trigger](x * z) <= #[trigger](y * z)
{
    assert forall |x: int, y: int, z: int| x <= y && z >= 0 ==>
    #[trigger](x * z) <= #[trigger](y * z)
    by
    {
    if  x <= y && z >= 0  {lemma_mul_inequality(x, y, z);}
    }
}

/// multiplying by a positive integer preserves inequality
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires 
        x < y,
        z > 0
    ensures 
        x * z < y * z
{
    MulINL::lemma_mul_strict_inequality(x, y, z);
}

/// multiplying by a positive integer preserves inequality for all integers
pub proof fn lemma_mul_strict_inequality_auto()
    ensures  forall |x: int, y: int, z: int| x < y && z > 0 ==> #[trigger](x * z) < #[trigger](y * z)
{
    assert forall |x: int, y: int, z: int | x < y && z > 0 ==> #[trigger](x * z) < #[trigger](y * z)
    by
    {
        if x < y && z > 0 { lemma_mul_strict_inequality(x, y, z); }
    }
}

/// the product of two bounded integers is less than or equal to the product of their upper bounds
pub proof fn lemma_mul_upper_bound(x: int, XBound: int, y: int, YBound: int)
    requires 
        x <= XBound,
        y <= YBound,
        0 <= x,
        0 <= y
    ensures 
        x * y <= XBound * YBound
{
    lemma_mul_inequality(x, XBound, y);
    lemma_mul_inequality(y, YBound, XBound);
}

pub proof fn lemma_mul_upper_bound_auto()
    ensures forall |x: int, XBound: int, y: int, YBound: int|
    x <= XBound && y <= YBound && 0 <= x && 0 <= y ==> #[trigger](x * y) <= #[trigger](XBound * YBound),
{
    assert forall |x: int, XBound: int, y: int, YBound: int| 
    x <= XBound && y <= YBound && 0 <= x && 0 <= y
    ==> #[trigger](x * y) <= #[trigger](XBound * YBound)
    by
    {
        if x <= XBound && y <= YBound && 0 <= x && 0 <= y { lemma_mul_upper_bound(x, XBound, y, YBound); }
    }
}

/// the product of two strictly upper bounded integers is less than the product of their upper bounds */
pub proof fn lemma_mul_strict_upper_bound(x: int, XBound: int, y: int, YBound: int)
    requires 
        x < XBound,
        y < YBound,
        0 < x,
        0 < y
    ensures 
    x * y <= (XBound - 1) * (YBound - 1)
{
    lemma_mul_inequality(x, XBound - 1, y);
    assert(x * y <= (XBound - 1) * y);
    lemma_mul_inequality(y, YBound - 1, XBound - 1);
    assert( y * (XBound - 1) <= (YBound - 1) * (XBound - 1));
    lemma_mul_is_commutative((XBound - 1), y)
}

pub proof fn lemma_mul_strict_upper_bound_auto()
    ensures forall |x: int, XBound: int, y: int, YBound: int| x < XBound && y < YBound && 0 < x && 0 < y ==> #[trigger](x * y) <= #[trigger]((XBound - 1) * (YBound - 1))
{
    assert forall |x: int, XBound: int, y: int, YBound: int | x < XBound && y < YBound && 0 < x && 0 < y ==>
    #[trigger](x * y) <= #[trigger]((XBound - 1) * (YBound - 1))
    by
    {
        if x < XBound && y < YBound && 0 < x && 0 < y { lemma_mul_strict_upper_bound(x, XBound, y, YBound); }
    }
}

/// any two integers that are multiplied by a positive number will maintain their numerical order
pub proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
    requires 0 < x
    ensures 
        y <= z ==> x * y <= x * z,
        y < z ==> x * y < x * z
{
    // I need to add this line after adding `lemma_mul_strict_inequality_converse`
    let f = |u: int| u > 0 ==> y <= z ==> u * y <= u * z;
    assert (mul_auto() ==> { &&&  f(0)
                             &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                             &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}); // OBSERVE
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y <= z ==> u * y <= u * z);
    let f = |u: int| u > 0 ==> y < z ==> u * y < u * z;
    assert (mul_auto() ==> { &&&  f(0)
                             &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                             &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}); // OBSERVE
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y < z ==> u * y < u * z);
}

pub proof fn lemma_mul_left_inequality_auto()
    ensures forall |x: int, y: int, z: int| x > 0 ==> (y <= z ==> #[trigger](x * y) <= #[trigger](x * z)) && (y < z ==> #[trigger](x * y) < #[trigger](x * z))
{
    assert forall |x: int, y: int, z: int | (y <= z || y < z) && 0 < x ==>
    (y <= z ==> #[trigger](x * y) <= #[trigger](x * z)) && (y < z ==> #[trigger](x * y) < #[trigger](x * z))
    by
    {
        if (y <= z || y < z) && 0 < x { lemma_mul_left_inequality(x, y, z); }
    }
}

/// if two seperate integers are each multiplied by a common integer and the products are equal, the 
/// two original integers are equal */
pub proof fn lemma_mul_equality_converse(m: int, x: int, y: int)
    requires 
        m != 0,
        m * x == m * y
    ensures 
        x == y
{
    if m > 0 {
        lemma_mul_induction_auto(m, |u| x > y && 0 < u ==> x * u > y * u);
        assert (x * m == y * m) by { lemma_mul_is_commutative(x, m); lemma_mul_is_commutative(y, m);};
        lemma_mul_induction_auto(m, |u: int| x < y && 0 < u ==> x * u < y * u);
    }
    if m < 0 {
        lemma_mul_induction_auto(m, |u: int| x > y && 0 > u ==> x * u < y * u);
        assert (x * m == y * m) by { lemma_mul_is_commutative(x, m); lemma_mul_is_commutative(y, m);};
        lemma_mul_induction_auto(m, |u: int| x < y && 0 > u ==> x * u > y * u);
    }
}

/// if any two seperate integers are each multiplied by a common integer and the products are equal, the 
/// two original integers are equal
pub proof fn lemma_mul_equality_converse_auto()
    ensures forall |m: int, x: int, y: int| (m != 0 && #[trigger](m * x) == #[trigger](m * y)) ==> x == y,
{
    assert forall |m: int, x: int, y: int | m != 0 && #[trigger](m * x) == #[trigger](m * y) ==> x == y
    by
    {
        if m != 0 && #[trigger](m * x) == #[trigger](m * y) { lemma_mul_equality_converse(m, x, y); }
    }
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z
pub proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires 
        x * z <= y * z,
        z > 0
    ensures  x <= y
{
    lemma_mul_induction_auto(z, |u: int| x * u <= y * u && u > 0 ==> x <= y);
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z 
/// for all valid values of x, y, and z
pub proof fn lemma_mul_inequality_converse_auto()
    ensures forall |x: int, y: int, z: int| #[trigger](x * z) <= #[trigger](y * z) && z > 0 ==> x <= y
{
    assert forall |x: int, y: int, z: int | #[trigger](x * z) <= #[trigger](y * z) && z > 0 ==> x <= y
    by
    {
        if x * z <= y * z && z > 0 { lemma_mul_inequality_converse(x, y, z); }
    }
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z
pub proof fn lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires 
        x * z < y * z,
        z >= 0
    ensures
        x < y
{
    lemma_mul_induction_auto(z, |u: int| x * u < y * u && u >= 0 ==> x < y);
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z 
/// for all valid values of x, y, and z
pub proof fn lemma_mul_strict_inequality_converse_auto()
    ensures  forall |x: int, y: int, z: int| #[trigger](x * z) < #[trigger](y * z) && z >= 0 ==> x < y,
{
    assert forall |x: int, y: int, z: int | #[trigger](x * z) < #[trigger](y * z) && z >= 0 ==> x < y
    by
    {
        if x * z < y * z && z >= 0 { lemma_mul_strict_inequality_converse(x, y, z); }
    }
}

/// multiplication is distributive
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
{
    // DISCUSS: this can automatically be verified
    // Probably due to the (non-boxing) SMT encoding
    // MulINL::lemma_mul_is_distributive_add(x, y, z);
}

/// for all integers, multiplication is distributive with addition in the form x * (y + z)
proof fn lemma_mul_is_distributive_add_auto()
    ensures forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
{
    assert forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z by
    {
    lemma_mul_is_distributive_add(x, y, z);
    }
}

/// for all integers, multiplication is distributive with addition in the form (y + z) * x
pub proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
{}

proof fn lemma_mul_is_distributive_add_other_way_auto()
    ensures forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
{
    assert forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x by
    {
    lemma_mul_is_distributive_add_other_way(x, y, z);
    }
}

/// multiplication is distributive with subtraction
pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
{}

/// for all integers, multiplication is distributive with subtraction
proof fn lemma_mul_is_distributive_sub_auto()
    ensures forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
{
    assert forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z by
    {
    lemma_mul_is_distributive_sub(x, y, z);
    }
}

/// proves the overall distributive nature of multiplication
pub proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures 
        x * (y + z) == x * y + x * z,
        x * (y - z) == x * y - x * z,
        (y + z) * x == y * x + z * x,
        (y - z) * x == y * x - z * x,
        x * (y + z) == (y + z) * x,
        x * (y - z) == (y - z) * x,
        x * y == y * x,
        x * z == z * x,
{
    lemma_mul_auto();
}

/// for all integers, multiplication is distributive
proof fn lemma_mul_is_distributive_auto()
    ensures
        forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
        forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
        forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
        forall |x: int, y: int, z: int| #[trigger]((y - z) * x) == y * x - z * x,
{
    // lemma_mul_is_distributive_add_auto();
    // lemma_mul_is_distributive_sub_auto();
    // lemma_mul_is_commutative_auto();
}

/* multiplying two positive integers will result in a positive integer */
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
{
    MulINL::lemma_mul_strictly_positive(x, y);
}

/// multiplying any two positive integers will result in a positive integer
proof fn lemma_mul_strictly_positive_auto()
    ensures forall |x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger](x * y)),
{
    assert forall |x: int, y: int| 0 < x && 0 < y ==> 0 < #[trigger](x * y) by
    {
        if 0 < x && 0 < y { lemma_mul_strictly_positive(x, y); }
    }
}

/// multiplying a positive integer by an integer greater than 1 will result in a product that 
/// is greater than the original integer
pub proof fn lemma_mul_strictly_increases(x: int, y: int)
    requires 
        1 < x,
        0 < y,
    ensures 
        y < x * y
{
    lemma_mul_induction_auto(x, |u: int| 1 < u ==> y < u * y);
}

/// multiplying any positive integer by any integer greater than 1 will result in a product that 
/// is greater than the original integer
proof fn lemma_mul_strictly_increases_auto()
    ensures forall |x: int, y: int| 1 < x && 0 < y  ==> y < #[trigger](x * y)
{
    assert forall |x: int, y: int| 1 < x && 0 < y ==> y < #[trigger](x * y) by
    {
        if 1 < x && 0 < y { lemma_mul_strictly_increases(x, y); }
    }
}

/// multiplying an integer by a positive integer will result in a product that is greater than or
/// equal to the original integer
pub proof fn lemma_mul_increases(x: int, y: int)
    requires 
        0 < x,
        0 < y
    ensures 
        y <= x * y
{
    lemma_mul_induction_auto(x, |u: int| 0 < u ==> y <= u * y);
}

spec fn mul (x: int, y: int) -> int 
{
    x * y
}

/// multiplying any integer by any positive integer will result in a product that is greater than or
/// equal to the original integer
proof fn lemma_mul_increases_auto()
    ensures forall |x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger](x * y))
{
    // assert(forall |x:int, y:int| mul(x, y) == x * y);
    // TODO/NEED TO ASK: it would be nice if there's a assert forall_arith ...
    assert forall |x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger](x * y)) by {
        if (0 < x && 0 < y) {
            lemma_mul_increases(x, y);
        } else {
            // assert(!(0 < x && 0 < y));
            // assert ( (0 < x && 0 < y) ==> (y <= #[trigger](x * y)));
        }
    }
}

/* multiplying two positive numbers will result in a positive product */
pub proof fn lemma_mul_nonnegative(x: int, y: int)
    requires 
        0 <= x,
        0 <= y
    ensures  0 <= x * y
{
    lemma_mul_induction_auto(x, |u: int| 0 <= u ==> 0 <= u * y);
}

/// multiplying any two positive numbers will result in a positive product
proof fn lemma_mul_nonnegative_auto()
    ensures forall |x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger](x * y)
{
    assert forall |x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger](x * y) by
    {
        if 0 <= x && 0 <= y { lemma_mul_nonnegative(x, y); }
    }
}

// TODO need trimming
/// shows the equivalent forms of using the unary negation operator
// now it just needs nothing .....
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_unary_negation(x: int, y: int)
    ensures 
        (-x) * y == -(x * y) && -(x * y) == x * (-y)
{
    // let f = |u: int| (-u) * y == -(u * y) && -(u * y) == u * (-y);
    // assert forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1) by {
    //     if (is_le(i, 0) && f(i)) {
    //         assert (f(i - 1)) by {
    //             assert ((-i + 1) * y == -((i - 1) * y) && -((i - 1) * y) == (i - 1) * (-y));
    //             assert ((-i) * y == -(i * y) && -(i * y) == i * (-y));
    //         }
    //     }
    // };
    
    // assert forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1) by {
    //     if (is_le(0, i) && f(i)) {
    //         assert (f(i + 1)) by {
    //             assert ((-i - 1) * y == -((i + 1) * y) && -((i + 1) * y) == (i + 1) * (-y));
    //             assert ((-i) * y == -(i * y) && -(i * y) == i * (-y));
    //         }
    //     }
    // };
    // lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) && -(u * y) == u * (-y));
}

/// shows the equivalent forms of using the unary negation operator for any integers
proof fn lemma_mul_unary_negation_auto()
    ensures forall |x: int, y: int| #[trigger]((-x) * y) == #[trigger](-(x * y)) && #[trigger](-(x * y)) == x * (-y),
{
    assert forall |x: int, y: int| #[trigger]((-x) * y) == #[trigger](-(x * y)) && #[trigger](-(x * y)) == x * (-y)
    by
    {
    lemma_mul_unary_negation(x, y);
    }
}

/// multiplying two negative integers, -x and -y, is equivalent to multiplying x and y
pub proof fn lemma_mul_cancels_negatives(x: int, y: int)
    ensures x * y == (-x) * (-y)
{
    // you do not need any proof for this lemma
}

/// multiplying two negative integers, -x and -y, is equivalent to multiplying x and y
proof fn lemma_mul_cancels_negatives_auto()
    ensures forall |x: int, y: int| #[trigger](x * y) == (-x) * (-y)
{
    assert forall |x: int, y: int|
    #[trigger](x * y) == (-x) * (-y)
    by
    {
    lemma_mul_cancels_negatives(x, y);
    }
}

/// includes all properties of multiplication
proof fn lemma_mul_properties()
    ensures 
    forall |x: int, y: int| #[trigger](x * y) == y * x,
    forall |x: int| #[trigger](x * 1) == x && #[trigger](1 * x) == x,
    forall |x: int, y: int, z: int| x < y && z > 0 ==>  #[trigger](x * z) < #[trigger](y * z),
    forall |x: int, y: int, z: int| x <= y && z >= 0 ==> #[trigger](x * z) <= #[trigger](y * z),
    forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
    forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
    forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
    forall |x: int, y: int, z: int| #[trigger]((y - z) * x) == y * x - z * x,
    forall |x: int, y: int, z: int| #[trigger](x * (y * z)) == #[trigger]((x * y) * z),
    forall |x: int, y: int| #[trigger](x * y) != 0 <==> x != 0 && y != 0,
    forall |x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger](x * y),
    forall |x: int, y: int| 0 < x && 0 < y && 0 <= x * y ==> x <= #[trigger](x * y) && y <= #[trigger](x * y),
    forall |x: int, y: int| (1 < x && 0 < y) ==> (y < #[trigger](x * y)),
    forall |x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger](x * y)),
    forall |x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger](x * y)),
{
    lemma_mul_strict_inequality_auto();
    lemma_mul_inequality_auto();
    lemma_mul_is_distributive_auto();
    lemma_mul_is_associative_auto();
    lemma_mul_ordering_auto();
    lemma_mul_nonzero_auto();
    lemma_mul_nonnegative_auto();
    lemma_mul_strictly_increases_auto();
    lemma_mul_increases_auto();
}


}