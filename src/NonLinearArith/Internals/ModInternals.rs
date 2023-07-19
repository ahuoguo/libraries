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
use crate::NonLinearArith::Internals::ModInternalsNonlinear::{lemma_fundamental_div_mod, lemma_mod_range, lemma_small_mod};
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternalsNonlinear;

// TODO: similar to div_pos in DivInternals
/// Performs modulus recursively
#[verifier(opaque)]
pub open spec fn mod_recursive(x: int, d: int) -> int
    recommends d > 0
    decreases (if x < 0 {(d - x)} else {x}) when d > 0
{
    if x < 0 {
        mod_recursive(d + x, d)
    } else if x < d {
        x
    } else {
        mod_recursive(x - d, d)
    }
}

pub open spec fn add (x: int, y: int) -> int
{
    x + y
}

pub open spec fn sub (x: int, y: int) -> int
{
    x - y
}

/// performs induction on modulus
#[verifier(spinoff_prover)]
pub proof fn lemma_mod_induction_forall(n: int, f: FnSpec(int) -> bool)
    requires 
        n > 0,
        forall |i: int| 0 <= i < n ==> #[trigger]f(i),
        forall |i: int| i >= 0 && #[trigger]f(i) ==> #[trigger]f(add(i, n)),
        forall |i: int| i < n  && #[trigger]f(i) ==> #[trigger]f(sub(i, n)),
        // another version like mul_induction_forall
        // TODO: this definition breaks lemma_mod_induction_forall2
        // forall |i: int, j:int| (i >= 0 && j == i + n && #[trigger] f(i)) ==> #[trigger] f(j),
        // forall |i: int, j:int| (i < n  && j == i - n && #[trigger] f(i)) ==> #[trigger] f(j),
        
    ensures  
        forall |i| #[trigger]f(i)
{
    assert forall |i: int| #[trigger]f(i) by {
        // TODO: communicating between the `add` functions are hard (and unecessary?)
        assert forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (crate::NonLinearArith::Internals::GeneralInternals::add(i, n)) by {
            assert(crate::NonLinearArith::Internals::GeneralInternals::add(i, n) == add(i, n));
        };
        assert forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (crate::NonLinearArith::Internals::GeneralInternals::sub(i, n)) by {
            assert(crate::NonLinearArith::Internals::GeneralInternals::sub(i, n) == sub(i, n));
        };
        lemma_induction_helper(n, f, i);
    };
}

// same as dafny
/// given an integer x and divisor n, the remainder of x%n is equivalent to the remainder of (x+m)%n
/// where m is a multiple of n
#[verifier(spinoff_prover)]
pub proof fn lemma_mod_induction_forall2(n: int, f:FnSpec(int, int)->bool)
    requires
        n > 0,
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger]f(i, j),
        forall |i: int, j: int| i >= 0 && #[trigger]f(i, j) ==> #[trigger]f(add(i, n), j),
        forall |i: int, j: int| j >= 0 && #[trigger]f(i, j) ==> #[trigger]f(i, add(j, n)),
        forall |i: int, j: int| i < n  && #[trigger]f(i, j) ==> #[trigger]f(sub(i, n), j),
        forall |i: int, j: int| j < n  && #[trigger]f(i, j) ==> #[trigger]f(i, sub(j, n)),
    ensures
        forall |i: int, j: int| #[trigger]f(i, j)
{
    assert forall |x: int, y: int| #[trigger]f(x, y) by {
        assert forall |i: int| 0 <= i < n implies #[trigger]f(i, y) by {
            let fj = |j| f(i, j);
            lemma_mod_induction_forall(n, fj);
            assert(fj(y));
        };
        let fi = |i| f(i, y);
        lemma_mod_induction_forall(n, fi);
        assert(fi(x));
    };
}

// same as dafny now
#[verifier(spinoff_prover)]
pub proof fn lemma_div_add_denominator(n: int, x: int)
    requires n > 0
    ensures (x + n) / n == x / n + 1
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);

    let zp = (x + n) / n - x / n - 1;
    // assert(n * zp == ((x + n) / n) * n - (x / n) * n - n) by { 
    //     lemma_mul_auto(); // OBSERVE
    //     // lemma_mul_is_distributive_auto();
    //     // assert(n * zp == n * ((x + n) / n - x / n - 1));
    //     // assert(n * zp == n * ((x + n) / n - x / n) - n);
    //     // assert(n * zp == n * ((x + n) / n - x / n) - n) by { lemma_mul_is_distributive(n, (x + n) / n - x / n, 1)}; // OBSERVE
    //     // assert (n * zp == n * ((x + n) / n) - n * (x / n) - n);
    // };

    assert (0 == n * zp + ((x + n) % n) - (x % n)) by {

        // assert((x + n) - n * ((x + n) / n)== (x + n) % n) by { 
        //     lemma_fundamental_div_mod(x + n, n); 
        // };

        // assert(n * zp == ((x + n) / n) * n - (x / n) * n - n);

        // assert(x - n * (x / n) == x % n) by { 
        //     lemma_fundamental_div_mod(x, n); 
        //     assert(x == n * (x / n) + (x % n)); 
        // };

        // assert(((x + n) / n) * n - n * ((x + n) / n) - (x / n) * n + (x + n)  - n - (x - n * (x / n)) == 0) by { lemma_mul_auto(); };

        // assert((n * ((x + n) / n) - n * (x / n) - n) + (x + n) - n * ((x + n) / n) - (x - n * (x / n)) == 0);
        
        // assert((n * ((x + n) / n) - n * (x / n) - n) + (x + n) - n * ((x + n) / n) - (x % n) == 0 );

        // assert (n * zp == ((x + n) / n) * n - (x / n) * n - n);
        // assert (n * zp == (n * ((x + n) / n) - (x / n) * n) - n);
        // lemma_mul_is_commutative_auto();
        // assert (n * zp == (n * ((x + n) / n) - n * (x / n) - n));
        // assert((n * zp) + (x + n) - n * ((x + n) / n) - (x % n) == 0 );
        
        lemma_mul_auto() 
    };
    if (zp > 0) { lemma_mul_inequality(1, zp, n); }
    if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
    
}

#[verifier(spinoff_prover)]
pub proof fn lemma_div_sub_denominator(n: int, x: int)
    requires n > 0
    ensures (x - n) / n == x / n - 1
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;

    assert (0 == n * zm + ((x - n) % n) - (x % n)) by { 
        assert (n * zm == n * (((x - n) / n - x / n) + 1));
        lemma_mul_is_distributive_auto();
        assert (n * zm == n * ((x - n) / n - x / n) + n) by {
            assert( n * (((x - n) / n - x / n) + 1) == (n * ((x - n) / n - x / n)) + n) by {
                lemma_mul_is_distributive_add(n, ((x - n) / n - x / n), 1);
            };
        };
        assert (n * zm == n * ((x - n) / n) - n * (x / n) + n);
        lemma_mul_auto(); 
    }
    if (zm > 0) { lemma_mul_inequality(1, zm, n); }
    if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_mod_add_denominator(n: int, x: int)
    requires n > 0
    ensures (x + n) % n == x % n
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    // DISCUSS: VERY UNSTABLE
    // assert (n * zp == n * (((x + n) / n - x / n) - 1));
    assert (n * zp == n * ((x + n) / n - x / n) - n) by {
        assert( n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n) by {
            lemma_mul_is_distributive_auto();
            assert(n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n * 1);
        };
        };


    assert(0 == n * zp + ((x + n) % n) - (x % n)) by { 
        // UNCOMMENT THIS PART
        // assert (n * zp == n * (((x + n) / n - x / n) - 1));
        // assert (n * zp == n * ((x + n) / n - x / n) - n) by {
        //     assert( n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n) by {
        //         lemma_mul_is_distributive_auto();
        //         assert(n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n * 1);
        //     };
        //     };
        assert (n * zp == n * ((x + n) / n) - n * (x / n) - n) by {
            lemma_mul_is_distributive_auto();
            assert(n * ((x + n) / n - x / n) == n * ((x + n) / n) - n * (x / n));

        };
        lemma_mul_auto(); 
    }

    if (zp > 0) { lemma_mul_inequality(1, zp, n); }
    if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_mod_sub_denominator(n: int, x: int)
    requires n > 0
    ensures (x - n) % n == x % n
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    assert (n * zm == n * (((x - n) / n - x / n) + 1));
    lemma_mul_is_distributive_auto(); // OBSERVE
    assert (n * zm == n * ((x - n) / n - x / n) + n) by {
        lemma_mul_is_distributive_auto();
    }

    assert(0 == n * zm + ((x - n) % n) - (x % n)) by { 
        // assert (n * zm == n * (((x - n) / n - x / n) + 1));
        // // lemma_mul_is_distributive_auto();
        // assert (n * zm == n * ((x - n) / n - x / n) + n) by {
        //     lemma_mul_is_distributive_auto();

        // }
        // lemma_mul_is_distributive_auto();
        assert (n * zm == n * ((x - n) / n) - n * (x / n) + n) by {
            lemma_mul_is_distributive_auto();
            assert(n * ((x - n) / n - x / n) == n * ((x - n) / n) - n * (x / n));
        };
        lemma_mul_auto(); 
    }

    if (zm > 0) { lemma_mul_inequality(1, zm, n); }
    if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_mod_below_denominator(n: int, x: int)
    requires n > 0
    ensures 0 <= x < n <==> x % n == x
{
    assert forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x by
    {
        if (0 <= x < n) { lemma_small_mod(x as nat, n as nat); }
        lemma_mod_range(x, n);
    }
}
// Hayley and Jay L chose to make the forall x be a formal parameter
// /// proves the basics of the modulus operation
#[verifier(spinoff_prover)]
pub proof fn lemma_mod_basics_auto(n: int)
    requires n > 0
    ensures  
        forall |x: int| #[trigger]((x + n) % n) == x % n,
        forall |x: int| #[trigger]((x - n) % n) == x % n,
        forall |x: int| #[trigger]((x + n) / n) == x / n + 1,
        forall |x: int| #[trigger]((x - n) / n) == x / n - 1,
        forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x,
{

    assert forall |x: int| #[trigger]((x + n) % n) == x % n by {
        lemma_mod_add_denominator(n, x);
    };

    assert forall |x: int| #[trigger]((x - n) % n) == x % n by {
        lemma_mod_sub_denominator(n, x);
        assert((x - n) % n == x % n);
    };

    assert forall |x: int| #[trigger]((x + n) / n) == x / n + 1 by
    {
        lemma_div_add_denominator(n, x);
    };
    
    assert forall |x: int| #[trigger]((x - n) / n) == x / n - 1 by {
        lemma_div_sub_denominator(n, x);
    };

    assert forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x by
    {
        lemma_mod_below_denominator(n, x);
    };
}

/// proves the quotient remainder theorem
// dafny has vcs_split_on_every_assert
#[verifier(spinoff_prover)]
pub proof fn lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
    requires 
        n > 0,
        0 <= r < n,
        x == q * n + r,
    ensures  
        q == x / n,
        r == x % n,
    decreases (if q > 0 { q } else { -q })
{
    lemma_mod_basics_auto(n);
    if q > 0 {
    MulInternalsNonlinear::lemma_mul_is_distributive_add(n, q - 1, 1);
    lemma_mul_is_commutative_auto();
    assert(q * n + r == (q - 1) * n + n + r);
    lemma_quotient_and_remainder(x - n, q - 1, r, n);
    }
    else if q < 0 {
    lemma_mul_is_distributive_sub(n, q + 1, 1);
    lemma_mul_is_commutative_auto();
    assert(q * n + r == (q + 1) * n - n + r);
    lemma_quotient_and_remainder(x + n, q + 1, r, n);
    }
    else {
    DivInternalsNonlinear::lemma_small_div();
    assert (r / n == 0);
    }
}

// TODO: split condition failure, also does not work if local variable z is eliminated by replacing
/// automates the modulus operator process
#[verifier(spinoff_prover)]
pub open spec fn mod_auto(n: int) -> bool
    recommends n > 0,
{
    &&& (n % n == 0 && (-n) % n == 0)
    &&& (forall |x: int| #[trigger]((x % n) % n) == x % n)
    &&& (forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x)
    &&& (forall |x: int, y: int|
         {let z = (x % n) + (y % n);
         (  (0 <= z < n && #[trigger]((x + y) % n) == z)
             || (n <= z < n + n && #[trigger]((x + y) % n) == z - n))})
    &&& (forall |x: int, y: int|
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && #[trigger]((x - y) % n) == z)
            || (-n <= z < 0  && #[trigger]((x - y) % n) == z + n))})
}

/// ensures that mod_auto is true
#[verifier(spinoff_prover)]
pub proof fn lemma_mod_auto(n: int)
    requires n > 0
    ensures 
        // puting mul_auto() here causes a split postcondition failure
        (n % n == 0 && (-n) % n == 0),
        (forall |x: int| #[trigger]((x % n) % n) == x % n),
        (forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x),
        // the following two cannot be verified, even when assuming them
        (forall |x: int, y: int|
            {let z = (x % n) + (y % n);
            (  (0 <= z < n && #[trigger]((x + y) % n) == z)
                || (n <= z < n + n && #[trigger]((x + y) % n) == z - n))}),
        (forall |x: int, y: int|
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && #[trigger]((x - y) % n) == z)
            || (-n <= z < 0  && #[trigger]((x - y) % n) == z + n))}),
        
{
    assert ((-n) % n == 0) by { lemma_mod_basics_auto(n); };

    assert forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x by {
        lemma_mod_basics_auto(n);
    };

    assert forall |x: int| #[trigger]((x % n) % n) == x % n by {
        lemma_mod_basics_auto(n);
        // (n, x);
    };

    assert forall |x: int, y: int|
    {let z = (x % n) + (y % n);
        (  (0 <= z < n &&  #[trigger]((x + y) % n) == z)
            || (n <= z < n + n && #[trigger]((x + y) % n) == z - n))} by
    {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert (x == n * ( x / n) + (x % n));
        lemma_mul_auto();
        assert(x == xq * n + xr);
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        assert (x + y == (xq + yq) * n + (xr + yr)) by {
            assert(y == yq * n + yr);
            assert(x == xq * n + xr);
            assert (x + y == xq * n + yq * n + (xr + yr));
            // lemma_mul_auto1(); // infinite loop
            lemma_mul_is_distributive(n, xq, yq);
            lemma_mul_auto();
        };
        if xr + yr < n {
            assert((x + y) == (xq + yq) * n + (xr + yr));
            lemma_quotient_and_remainder(x + y, xq + yq, xr + yr, n);
        }
        else {
            assert((x + y) == (xq + yq + 1) * n + (xr + yr - n)) by {
                lemma_mul_is_distributive(n, (xq + yq), 1);
                lemma_mul_auto();
            };
            lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
        }
    }

    assert forall |x: int, y: int|
    {let z = (x % n) - (y % n);
        (  (0 <= z < n &&  #[trigger]((x - y) % n) == z)
            || (-n <= z < 0 && #[trigger]((x - y) % n) == z + n))} by
    {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert (x == n * ( x / n) + (x % n));
        lemma_mul_auto();
        assert(x == xq * n + xr);
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        assert (x - y == (xq - yq) * n + (xr - yr)) by {
            assert(y == yq * n + yr);
            assert(x == xq * n + xr);
            assert (x - y == xq * n - yq * n + (xr - yr));
            // lemma_mul_auto1(); // infinite loop
            lemma_mul_is_distributive(n, xq, yq);
            lemma_mul_auto();
        };
        if xr - yr >= 0 {
            assert((x - y) == (xq - yq) * n + (xr - yr));
            lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
            assert(xq - yq == (x - y) / n);
            assert(xr - yr == (x - y) % n);
            assert(0 <= (xr - yr) < n && ((x - y) % n) == (xr - yr));
        }
        else {  // xr - yr < 0
            assert((x - y) == ((xq - yq) - 1) * n + (xr - yr + n)) by {
                lemma_mul_is_distributive(n, (xq - yq), 1);
                lemma_mul_auto();
            };
            lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
            assert (xq - yq - 1 == (x - y) / n);
            assert (xr - yr + n == (x - y) % n);
            assert (((x - y) % n) == ((xr - yr) + n));
        }
    }
}

// yay!! no need for communicating!!! this is a very promising case
/// performs auto induction for modulus
#[verifier(spinoff_prover)]
pub proof fn lemma_mod_induction_auto(n: int, x: int, f: FnSpec(int) -> bool)
    requires 
        n > 0,
        mod_auto(n) ==>{&&& (forall |i: int| #[trigger]is_le(0, i) && i < n ==> f(i))
                        &&& (forall |i: int| #[trigger]is_le(0, i) && f(i) ==> f(i + n))
                        &&& (forall |i: int| #[trigger]is_le(i + 1, n) && f(i) ==> f(i - n))}
    ensures 
        mod_auto(n),
        f(x)
{
    lemma_mod_auto(n);
    assume(forall |i: int| is_le(0, i) && i < n ==> f(i));
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
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

// // not used in any other files, especially divmod
// /* performs auto induction on modulus for all i s.t. f(i) exists */
// proof fn lemma_mod_induction_auto_forall(n: int, f: int -> bool)
//     requires n > 0
//      mod_auto(n) ==> && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i))
//                             && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n))
//                             && (forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n))
//     ensures  mod_auto(n)
//     ensures  forall i {:trigger f(i)} :: f(i)
// {
//     lemma_mod_auto(n);
//     assert forall i :: IsLe(0, i) && i < n ==> f(i);
//     assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
//     assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
//     lemma_mod_induction_forall(n, f);
// }

}