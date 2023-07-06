// deep water of instability

// the last lemma seems to affect line 270
// however, removing some auto lemmas from the context also helps


use vstd::prelude::*;

verus! {

// GeneralInternals

pub open spec fn add (a: int, b: int) -> int
{
    a + b
}

pub open spec fn sub (a: int, b: int) -> int
{
    a - b
}

pub open spec fn is_le(x: int, y: int) -> bool
{
    x <= y
}

/* aids in the process of induction for modulus */
#[verifier(spinoff_prover)]
proof fn lemma_induction_helper_pos(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x >= 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
    ensures
        f(x)
    decreases x
{
    if (x >= n)
    {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert (f (add(x - n, n)));
        assert(f((x - n) + n));
    }
}

#[verifier(spinoff_prover)]
proof fn lemma_induction_helper_neg(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x < 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
    ensures
        f(x)
    decreases -x
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert (f (sub(x + n, n)));
        assert(f((x + n) - n));
    }
    else {
        lemma_induction_helper_neg(n, f, x + n);
        assert (f (sub(x + n, n)));
        assert(f((x + n) - n));
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_induction_helper(n: int, f: FnSpec(int) -> bool, x: int)
requires 
    n > 0,
    forall |i : int| 0 <= i < n ==> #[trigger] f(i),
    forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
    forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
ensures
    f(x)
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    }
    else {
        lemma_induction_helper_neg(n, f, x);
    }
}

// MulInternals

pub open spec fn dist_left_add (a: int, b: int, c: int) -> int
{
    (a + b) * c
}

pub open spec fn dist_right_add (a: int, b: int, c: int) -> int
{
    a * c + b * c
}

pub open spec fn dist_left_sub (a: int, b: int, c: int) -> int
{
    (a - b) * c
}

pub open spec fn dist_right_sub (a: int, b: int, c: int) -> int
{
    a * c - b * c
}

// this mul_auto seems to be pretty stable, do not switch to auto1
/// groups distributive and associative properties of multiplication
pub open spec fn mul_auto() -> bool
{
    &&& (forall |x:int, y:int| #[trigger](x * y) == (y * x))
    &&& (forall |x:int, y:int, z:int| #[trigger] dist_left_add(x, y, z) == dist_right_add(x, y, z))
    &&& (forall |x:int, y:int, z:int| #[trigger] dist_left_sub(x, y, z) == dist_right_sub(x, y, z))
}


/// proves that mul_auto is valid
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_auto()
    ensures  mul_auto()
{}

#[verifier(spinoff_prover)]
proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires 
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add(i, 1)),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub(i, 1)),
        // TODO how about this proof style? seems to distablize one or two proofs
        // forall |i: int, j:int| i >= 0 && j == i + 1 && #[trigger] f(i) ==> #[trigger] f(j),
        // forall |i: int, j:int| i <= 0 && j == i - 1 && #[trigger] f(i) ==> #[trigger] f(j),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

#[verifier(spinoff_prover)]
pub proof fn lemma_mul_induction_auto(x: int, f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        f(x),
{
    assert (forall |i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert (forall |i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

// Mul

/// multiplication is distributive with subtraction
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
{}


/// multiplication is always commutative for all integers
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_is_commutative_auto()
    ensures forall |x: int, y: int| #[trigger](x * y) == (y * x)
{}

/// multiplication is distributive
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
{}

#[verifier(spinoff_prover)]
pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires 
        x <= y,
        z >= 0
    ensures  x * z <= y * z
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// proves the overall distributive nature of multiplication
#[verifier(spinoff_prover)]
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
{}

/// for all integers, multiplication is distributive
#[verifier(spinoff_prover)]
pub proof fn lemma_mul_is_distributive_auto()
    ensures
        forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
        forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
        forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
        forall |x: int, y: int, z: int| #[trigger]((y - z) * x) == y * x - z * x,
{}

// ModInternalsNonlinear

/* a natural number x divided by a larger natural number gives a remainder equal to x */
#[verifier(nonlinear)]
pub proof fn lemma_small_mod(x:nat, m:nat)
    requires 
        x < m,
        0 < m
    ensures 
        #[trigger] Mod(x as int, m as int) == x as int
{}

/* describes fundamentals of the modulus operator */
#[verifier(nonlinear)]
pub proof fn lemma_fundamental_div_mod(x:int, d:int)
    requires d != 0
    ensures  x == d * (x / d) + (x % d)
{}


pub open spec fn Mod (x: int, y: int) -> int
{
    x % y
}

/* the range of the modulus of any integer will be [0, m) where m is the divisor */
// Euclid's division lemma?
#[verifier(nonlinear)]
pub proof fn lemma_mod_range(x:int, m:int)
    requires m > 0
    ensures  0 <= #[trigger] Mod(x, m) < m
{}

// DivInternals
#[verifier(nonlinear)]
pub proof fn lemma_small_div()
    ensures forall |x: int, d: int| 0 <= x < d && d > 0 ==> #[trigger](x / d) == 0
{}

// ModInternals

#[verifier(spinoff_prover)]
pub proof fn lemma_div_add_denominator(n: int, x: int)
    requires n > 0
    ensures (x + n) / n == x / n + 1
{
    lemma_fundamental_div_mod(x, n);
    // assert(x == n * (x / n) + (x % n));
    lemma_fundamental_div_mod(x + n, n);
    // assert(x + n == n * ((x + n) / n) + ((x + n) % n));
    let zp = (x + n) / n - x / n - 1;
    assert(n * zp == ((x + n) / n) * n - (x / n) * n - n) by { 
        // lemma_mul_auto();
        lemma_mul_is_distributive_auto(); // OBSERVE
        assert(n * zp == n * ((x + n) / n - x / n - 1)); // OBSERVE
        lemma_mul_is_distributive_auto();
        assert(n * zp == n * ((x + n) / n - x / n) - n); // OBSERVE
        // assert(n * zp == n * ((x + n) / n - x / n) - n) by { lemma_mul_is_distributive(n, (x + n) / n - x / n, 1)}; // OBSERVE
        assert (n * zp == n * ((x + n) / n) - n * (x / n) - n); // OBSERVE
    };

    assert (0 == n * zp + ((x + n) % n) - (x % n)) by {

        // assert((x + n) - n * ((x + n) / n)== (x + n) % n) by { 
        //     lemma_fundamental_div_mod(x + n, n); 
        // };

        assert(n * zp == ((x + n) / n) * n - (x / n) * n - n);

        assert(x - n * (x / n) == x % n) by { 
            lemma_fundamental_div_mod(x, n); 
            assert(x == n * (x / n) + (x % n)); 
        };

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
    // assume (0 == n * zp + ((x + n) % n) - (x % n));

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
    // lemma_mul_is_distributive_auto();
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

#[verifier(spinoff_prover)]
pub proof fn lemma_mod_basics(n: int, x: int)
    requires n > 0
    ensures
        ((x + n) % n) == x % n,
        ((x - n) % n) == x % n,
        ((x + n) / n) == x / n + 1,
        ((x - n) / n) == x / n - 1,
        0 <= x < n <==> (x % n) == x,
{
    lemma_mod_below_denominator(n, x);
    lemma_mod_add_denominator(n, x);
    lemma_mod_sub_denominator(n, x);
    lemma_div_add_denominator(n, x);
    lemma_div_sub_denominator(n, x);
}

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
    lemma_mod_basics(n, x);
    if q > 0 {
    lemma_mul_is_distributive_add(n, q - 1, 1);
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
    lemma_small_div();
    assert (r / n == 0);
    }
}

// /// ensures that mod_auto is true
// #[verifier(spinoff_prover)]
// pub proof fn lemma_mod_auto(n: int)
//     requires n > 0
//     ensures 
//         (forall |x: int, y: int|
//             {let z = (x % n) + (y % n);
//             (  (0 <= z < n && #[trigger]((x + y) % n) == z)
//                 || (n <= z < n + n && #[trigger]((x + y) % n) == z - n))}),
//         (forall |x: int, y: int|
//         {let z = (x % n) - (y % n);
//         (  (0 <= z < n && #[trigger]((x - y) % n) == z)
//             || (-n <= z < 0  && #[trigger]((x - y) % n) == z + n))}),
        
// {
//     assume(false);
// }

}

fn main() {}