// currently needs to be run with the verus on vstd_augmenting branch

//！ Little endian interpretation of a sequence of numbers with a given base. The
//！ first element of a sequence is the least significant position; the last
//！ element is the most significant position.

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::seq_lib::*;
#[allow(unused_imports)]
use vstd::seq::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Div::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Modulus::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Mul::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Power::*;
#[allow(unused_imports)]
use vstd::calc_macro::*;

verus! {

// dafny:
// function BASE(): nat
// ensures BASE() > 1    

// current solution, every function has a base: int parameter, and add requires
// clause to for base > 1

// dafny:
// type uint = i: int | 0 <= i < BASE()

// I also only see the way is that reqruies every element in the sequence to
// be smaller than base

// might consider spec_affirm and spec(checked)

//////////////////////////////////////////////////////////////////////////////  
//
// ToNat definition and lemmas
//
//////////////////////////////////////////////////////////////////////////////

/// Converts a sequence to a nat beginning with the least significant position.
#[verifier::opaque]
pub open spec(checked) fn to_nat_right(xs: Seq<int>, base: int) -> int
    recommends
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    decreases
        xs.len()
{
    recommends_by(lemma_to_nat_right_rec);
    if xs.len() == 0 {
        0int
    } else {
        // lemma_mul_nonnegative_auto();
        let _ = spec_affirm(forall |x: int| xs.drop_first().contains(x) ==> 0 <= x < base);
        (to_nat_right(xs.drop_first(), base) * base + xs.first())
    }
}
// dafny
// function {:opaque} ToNatRight(xs: seq<uint>): nat
// {
//   if |xs| == 0 then 0
//   else
//     LemmaMulNonnegativeAuto();
//     ToNatRight(DropFirst(xs)) * BASE() + First(xs)
// }

/// Converts a sequence to a nat beginning with the most significant position.
#[verifier::opaque]
pub open spec(checked) fn to_nat_left(xs: Seq<int>, base: int) -> int
    recommends
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    decreases
        xs.len()
{
    recommends_by(lemma_to_nat_left_rec);
    if xs.len() == 0 {
        0int
    } else {
        (to_nat_left(xs.drop_last(), base) + xs.last() * pow(base, (xs.len() - 1) as nat))
    }
}

#[verifier::recommends_by]
pub proof fn lemma_to_nat_right_rec(xs: Seq<int>, base: int)
{
    assert forall |x: int| ((forall |x: int| xs.contains(x) ==> 0 <= x < base) && xs.len() > 0 && xs.drop_first().contains(x)) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }
}

#[verifier::recommends_by]
pub proof fn lemma_to_nat_left_rec(xs: Seq<int>, base: int)
{
    assert forall |x: int| ((forall |x: int| xs.contains(x) ==> 0 <= x < base) && xs.len() > 0 && xs.drop_last().contains(x)) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }
}

/// Given the same sequence, to_nat_right and to_nat_left return the same nat.
// {:vcs_split_on_every_assert}
#[verifier::spinoff_prover] // removing this spinoff prover will break the proof
pub proof fn lemma_to_nat_left_eqto_nat_right(xs: Seq<int>, base: int)
    requires
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures 
        to_nat_right(xs, base) == to_nat_left(xs, base)
    decreases
        xs.len()
{
    reveal(to_nat_right);
    reveal(to_nat_left);
    if xs.len() == 0 {
    } else {
        if xs.drop_last() == Seq::<int>::empty() {

            assert(to_nat_right(xs.drop_first(), base) == 0) by {
                assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
                    assert(xs.contains(x));
                    assert(0 <= x < base);
                }
                assert(xs.drop_last().len() == 0);
            };
            
            assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }            
            
            assert(to_nat_left(xs, base) == (xs.last() * pow(base, (xs.len() - 1) as nat))) by {
                assert(to_nat_left(xs.drop_last(), base) == 0);
            };
            
            calc! {
                (==)
                to_nat_left(xs, base);
                (==) {
                    assert(to_nat_left(xs.drop_last(), base) == 0);
                }
                (xs.last() * pow(base, (xs.len() - 1) as nat));
                (==) { reveal(pow); }
                xs.last();
                (==) {}
                xs.first();
                (==) { assert(to_nat_right(xs.drop_first(), base) == 0); } // cannot assert forall in calc! proof
                to_nat_right(xs, base);
            }
        } else {
            assert(to_nat_left(xs, base) == to_nat_left(xs.drop_last(), base) + xs.last() * pow(base, (xs.len() - 1) as nat)) by {
                assert forall |x: int| xs.drop_last().contains(x) implies 0 <= x < base by {
                    assert(xs.contains(x));
                    assert(0 <= x < base);
                }
            };

            assert forall |x: int| xs.drop_last().contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }

            assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }
            
            // droplast drop first
            assert(xs.drop_last() != Seq::<int>::empty());
            lemma_seq_properties::<int>();
            assert forall |x: int| (xs.drop_last().drop_first()).contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }

            assert forall |x: int| (xs.drop_first().drop_last()).contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }

            assert(to_nat_left(xs.drop_last().drop_first(), base) * base + xs.first() + xs.last() * pow(base, (xs.len() - 2) as nat) * base 
                        == to_nat_left(xs.drop_first(), base) * base + xs.first()) by {
                reveal(to_nat_left);
                assert(to_nat_left(xs.drop_first(), base) == to_nat_left(xs.drop_first().drop_last(), base) + xs.drop_first().last() * pow(base, (xs.drop_first().len() - 1) as nat));
                lemma_seq_properties::<int>();
                assert(xs.drop_last().drop_first() =~= xs.drop_first().drop_last());
                lemma_mul_is_distributive_auto();
            };
            lemma_seq_properties::<int>();
            calc! { (==)
                to_nat_left(xs, base); 
                {}
                (to_nat_left(xs.drop_last(), base) + xs.last() * pow(base, (xs.len() - 1) as nat)) ;
                { 
                    lemma_seq_properties::<int>();
                    lemma_to_nat_left_eqto_nat_right(xs.drop_last(), base); }
                to_nat_right(xs.drop_last(), base) + xs.last() * pow(base, (xs.len() - 1) as nat); 
                {}
                to_nat_right((xs.drop_last().drop_first()), base) * base + xs.first() + xs.last()
                * pow(base, (xs.len() - 1) as nat);
                { lemma_to_nat_left_eqto_nat_right((xs.drop_last().drop_first()), base); }
                to_nat_left((xs.drop_last().drop_first()), base) * base + xs.first() + xs.last() * pow(base, (xs.len() - 1) as nat);
                {
                assert((xs.drop_last().drop_first()) == xs.drop_last().drop_first());
                reveal(pow);
                lemma_mul_properties();
                }
                to_nat_left(xs.drop_last().drop_first(), base) * base + xs.first() + xs.last()
                * pow(base, (xs.len() - 2) as nat) * base;
                { lemma_mul_is_distributive_auto(); }
                to_nat_left(xs.drop_first(), base) * base + xs.first();
                {  lemma_to_nat_left_eqto_nat_right(xs.drop_first(), base); }
                to_nat_right(xs, base);
            }
        }
    }
}

// TODO: when refactorign, probably generalize this
// pub proof fn lemma_to_nat_left_helper(xs: Seq<int>, base: int)
// {
//     assert forall |x: int| ((forall |x: int| xs.contains(x) ==> 0 <= x < base) && xs.len() > 0 && xs.drop_last().contains(x)) implies 0 <= x < base by {
//         assert(xs.contains(x));
//         assert(0 <= x < base);
//     }
// }

// TODO: this auto lemma distableizes stuff sometimes
#[verifier::spinoff_prover]
pub proof fn lemma_to_nat_left_eqto_nat_right_auto()
    ensures forall |xs: Seq<int>, base: int| base > 1 && (forall |x: int| xs.contains(x) ==> 0 <= x < base) ==> #[trigger]to_nat_right(xs, base) == to_nat_left(xs, base)
{
    reveal(to_nat_right);
    reveal(to_nat_left);
    assert forall |xs: Seq<int>, base: int| base > 1 && (forall |x: int| xs.contains(x) ==> 0 <= x < base) implies to_nat_right(xs, base) == to_nat_left(xs, base) by {
        lemma_to_nat_left_eqto_nat_right(xs, base);
    }
}
// added, prove to_nat_left is greater than 0
#[verifier::spinoff_prover]
pub proof fn lemma_to_nat_left_basics(xs: Seq<int>, base: int)
    requires
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures 
        to_nat_left(xs, base) >= 0
    decreases
        xs.len()
{
    reveal(to_nat_left);
    if xs.len() == 0 {
        // assert(to_nat_left(xs, base) >= 0);
    } else {
        assert forall |x: int| xs.drop_last().contains(x) implies 0 <= x < base by {
            assert(xs.contains(x));
            assert(0 <= x < base);
        }
        assert(to_nat_left(xs, base) == (to_nat_left(xs.drop_last(), base) + xs.last() * pow(base, (xs.len() - 1) as nat)));
        lemma_to_nat_left_basics(xs.drop_last(), base);
        assert(to_nat_left(xs.drop_last(), base) >= 0);
        lemma_pow_positive_auto();
        assert(pow(base, (xs.len() - 1) as nat) >= 0);
        assert(xs.last() >= 0) by {
            assert(xs.contains(xs.last()));
            assert(0 <= xs.last() < base);
        };
        lemma_mul_strictly_positive_auto();
        assert(xs.last() * pow(base, (xs.len() - 1) as nat) >= 0);

        assert(to_nat_left(xs, base) >= 0);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_to_nat_basics(xs: Seq<int>, base: int)
    requires
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures 
        to_nat_left(xs, base) >= 0 && to_nat_right(xs, base) >= 0
{
    lemma_to_nat_left_basics(xs, base);
    lemma_to_nat_left_eqto_nat_right_auto();
}



/// The nat representation of a sequence of length 1 is its first (and only)
/// position.
#[verifier::spinoff_prover]
pub proof fn lemma_seq_len1(xs: Seq<int>, base: int)
    requires
        xs.len() == 1,
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures to_nat_right(xs, base) == xs.first()
{
    reveal(to_nat_right);
    assert(to_nat_right(xs.drop_first(), base) == 0);
}

/// The nat representation of a sequence of length 2 is sum of its first
/// position and the product of its second position and base.
#[verifier::spinoff_prover]
pub proof fn lemma_seq_len2(xs: Seq<int>, base: int)
    requires
        xs.len() == 2,
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures
        to_nat_right(xs, base) == xs.first() + xs[1] * base
{
    reveal(to_nat_right);
    assert forall |x: int| xs.drop_last().contains(x) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }
    assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }
    lemma_seq_len1(xs.drop_last(), base);
    lemma_seq_len1(xs.drop_first(), base);
}

/// Appending a zero does not change the nat representation of the sequence.
#[verifier::spinoff_prover]
pub proof fn lemma_seq_append_zero(xs: Seq<int>, base: int)
    requires
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures 
        to_nat_right(xs + seq![0], base) == to_nat_right(xs, base),
{
    // assert forall |x: int| (xs + seq![0]).contains(x) implies 0 <= x < base by {
    //     if xs.contains(x) {
    //         assert(0 <= x < base);
    //     } else {
    //         assert(x == 0);
    //         assert(0 <= x < base);
    //     }
    // }
    lemma_seq_properties::<int>();

    reveal(to_nat_left);
    lemma_to_nat_left_eqto_nat_right(xs + seq![0], base);
    lemma_to_nat_left_eqto_nat_right(xs, base);

    assert(to_nat_left(xs + seq![0], base) == to_nat_left(xs, base) + 0 * pow(base, xs.len() as nat)) by {
        lemma_mul_basics_auto();
        lemma_seq_properties::<int>();
        assert(to_nat_left(xs + seq![0], base) == (to_nat_left((xs + seq![0]).drop_last(), base) + (xs + seq![0]).last() * pow(base, ((xs + seq![0]).len() - 1) as nat)));
    };

    // calc! { (==)
    //     to_nat_right(xs + seq![0], base); {
    //         lemma_to_nat_left_eqto_nat_right(xs + seq![0], base);
    //     }
    //     to_nat_left(xs + seq![0], base); {}
    //     to_nat_left(xs, base) + 0 * pow(base, xs.len() as nat);
    //     { lemma_mul_basics_auto(); }
    //     to_nat_left(xs, base); {
    //         lemma_to_nat_left_eqto_nat_right(xs, base);
    //     }
    //     to_nat_right(xs, base);
    // }
}

/// The nat representation of a sequence is bounded by base to the power of
/// the sequence length.
#[verifier::spinoff_prover]
pub proof fn lemma_seq_nat_bound(xs: Seq<int>, base: int)
    requires
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures 
        to_nat_right(xs, base) < pow(base, xs.len())
    decreases
        xs.len()
{
    reveal(pow);
    if xs.len() == 0 {
        reveal(to_nat_right);
    } else {
        assert forall |x: int| xs.drop_last().contains(x) implies 0 <= x < base by {
            assert(xs.contains(x));
            assert(0 <= x < base);
        }

        let len1 = xs.len() - 1;
        let pow1 = pow(base, len1 as nat);

        calc! { (<)
        to_nat_right(xs, base);
        (==)    { lemma_to_nat_left_eqto_nat_right(xs, base); }
        to_nat_left(xs, base);
        (==)    { reveal(to_nat_left); }
        to_nat_left(xs.drop_last(), base) + xs.last() * pow1;
        (<)  {
            lemma_to_nat_left_eqto_nat_right(xs.drop_last(), base);
            lemma_seq_nat_bound(xs.drop_last(), base);
            }
        pow1 + xs.last() * pow1;
        (<=) {
            assert(xs.contains(xs.last()));
            lemma_pow_positive_auto();
            lemma_mul_inequality_auto();
            }
        pow1 + (base - 1) * pow1;
        (==)    { lemma_mul_is_distributive_auto(); }
        pow(base, (len1 + 1) as nat);
        }
    }
}

// /* The nat representation of a sequence can be calculated using the nat
// representation of its prefix. */
// {:vcs_split_on_every_assert} 
#[verifier::spinoff_prover]
pub proof fn lemma_seq_prefix(xs: Seq<int>, i: nat, base: int)
    requires 
        0 <= i <= xs.len(),
        base > 1,
        forall |x: int| xs.contains(x) ==> 0 <= x < base,
    ensures 
        to_nat_right(xs.subrange(0, i as int), base) + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, i) == to_nat_right(xs, base),
    decreases
        i
{
    reveal(to_nat_right);
    reveal(pow);
    lemma_seq_properties::<int>();

    assert forall |x: int| (xs.subrange(0, i as int).contains(x)) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }

    assert forall |x: int| (xs.subrange(i as int, xs.len() as int).contains(x)) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }


    if i == 1 {
        lemma_seq_properties::<int>();
        assert(to_nat_right(xs.subrange(0, 1), base) == to_nat_right(xs.subrange(0, 1).drop_first(), base) * base + xs.subrange(0, 1).first());
        assert(to_nat_right(xs.subrange(0, 1), base) == xs.first());
        assert(to_nat_right(xs, base) == to_nat_right(xs.drop_first(), base) * base + xs.first());
        assert(to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, 1) == to_nat_right(xs.subrange(i as int, xs.len() as int), base) * base) by {
            lemma_pow1_auto();
        };
        assert(xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, 1) == to_nat_right(xs, base));
    } else if i > 1 {
        assert(xs.len() > 1);

        assert forall |x: int| ((xs.subrange(0, i as int).drop_first()).contains(x)) implies 0 <= x < base by {
            assert(xs.contains(x));
            assert(0 <= x < base);
        }

        assert( to_nat_right(xs.subrange(0, i as int), base) + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, i) 
             == to_nat_right((xs.subrange(0, i as int).drop_first()), base) * base + xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, i));
        
        assert( to_nat_right((xs.subrange(0, i as int).drop_first()), base) * base + xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, i) 
             =~= to_nat_right(xs.drop_first().subrange(0, i - 1), base) * base + xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, (i - 1) as nat) * base) by {
            lemma_seq_properties::<int>();
            assert(xs.subrange(0, i as int).drop_first() =~= xs.drop_first().subrange(0, i - 1)); // OBSERVE
            lemma_mul_properties();
        };

        // xs.drop_first().subrange(0, i as int - 1)
        assert forall |x: int| #[trigger](xs.drop_first().subrange(0, i as int - 1).contains(x)) implies 0 <= x < base by {
            assert(xs.contains(x));
            assert(0 <= x < base);
        }

        // // to_nat_right(xs.drop_first().subrange(i - 1, xs.len() as int
        // assert(i - 1 <= xs.len());
        // assert forall |x: int| #[trigger](xs.drop_first().subrange(i - 1, xs.len() as int).contains(x)) implies 0 <= x < base by {
        //     assert(xs.contains(x));
        //     assert(0 <= x < base);
        // }

        assert (to_nat_right(xs.drop_first().subrange(0, i - 1), base) * base + xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, (i - 1) as nat) * base
            == (to_nat_right(xs.drop_first().subrange(0, i as int - 1), base) + to_nat_right(xs.drop_first().subrange(i - 1, xs.drop_first().len() as int), base) * pow(base,(i - 1) as nat)) * base + xs.first()) by {
            lemma_mul_is_distributive_auto();
        };

        assert((to_nat_right(xs.drop_first().subrange(0, i as int - 1), base) + to_nat_right(xs.drop_first().subrange(i - 1, xs.drop_first().len() as int), base) * pow(base,(i - 1) as nat)) * base + xs.first()
            == to_nat_right(xs, base) ) by 
        {
            assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }
            lemma_seq_prefix(xs.drop_first(), (i - 1) as nat, base);
        };

    
        // calc! { (==)
        // to_nat_right(xs.subrange(0, i as int), base) + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, i);
        // {}
        // to_nat_right((xs.subrange(0, i as int).drop_first()), base) * base + xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, i);
        // {
        //     assert(xs.subrange(0, i as int).drop_first() == xs.drop_first().subrange(0, i - 1));
        //     lemma_mul_properties();
        // }
        // to_nat_right(xs.drop_first().subrange(0, i - 1), base) * base + xs.first() + to_nat_right(xs.subrange(i as int, xs.len() as int), base) * pow(base, (i - 1) as nat) * base;
        // { lemma_mul_is_distributive_auto(); }
        // (to_nat_right(xs.drop_first().subrange(0, i as int - 1), base) + to_nat_right(xs.drop_first().subrange(i - 1, xs.drop_first().len() as int), base) * pow(base,(i - 1) as nat)) * base + xs.first();
        // { lemma_seq_prefix(xs.drop_first(), (i - 1) as nat, base); }
        // to_nat_right(xs, base);
        // }
    }
}

/// If there is an inequality between the most significant positions of two
/// sequences, then there is an inequality between the nat representations of
/// those sequences. Helper proof fn for lemma_seq_neq.
pub proof fn lemma_seq_msw_inequality(xs: Seq<int>, ys: Seq<int>, base: int)
    requires 
        xs.len() == ys.len() > 0,
        xs.last() < ys.last(),
        base > 1,
        forall |a: int| xs.contains(a) ==> 0 <= a < base,
        forall |a: int| ys.contains(a) ==> 0 <= a < base,
    ensures 
        to_nat_right(xs, base) < to_nat_right(ys, base)
{
    assert forall |x: int| xs.drop_last().contains(x) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }

    assert forall |x: int| ys.drop_last().contains(x) implies 0 <= x < base by {
        assert(ys.contains(x));
        assert(0 <= x < base);
    }
    reveal(to_nat_left);
    lemma_to_nat_left_eqto_nat_right_auto();
    let len1 = (xs.len() - 1) as nat;

    assert(to_nat_right(xs, base) == to_nat_left(xs, base)) by {
        // lemma_to_nat_left_eqto_nat_right(xs, base);
    };

    assert(to_nat_left(xs, base) < pow(base, len1) + xs.last() * pow(base, len1)) by {
        // assert( to_nat_left(xs, base) == to_nat_left(xs.drop_last(), base) + xs.last() * pow(base, len1));
        // lemma_to_nat_left_eqto_nat_right(xs.drop_last(), base);
        lemma_seq_nat_bound(xs.drop_last(), base);
    }

    assert(pow(base, len1) + xs.last() * pow(base, len1) == (1 + xs.last()) * pow(base, len1)) by {
        lemma_mul_is_distributive_auto();
    };

    assert((1 + xs.last()) * pow(base, len1) <= to_nat_left(ys, base)) by {
        assert(to_nat_left(ys, base) == 
               to_nat_left(ys.drop_last(), base) + ys.last() * pow(base, (ys.len() - 1) as nat));
        assert( len1 == (ys.len() - 1) as nat);
        assert(xs.last() < ys.last());
        assert(1 + xs.last() <= ys.last());
        lemma_pow_positive_auto(); 
        lemma_mul_inequality_auto();
        assert((1 + xs.last()) * pow(base, len1) <= ys.last() * pow(base, len1));    
        assert(ys.last() * pow(base, len1) == ys.last() * pow(base, (ys.len() - 1) as nat));
        lemma_to_nat_basics(ys.drop_last(), base);
        assert(ys.last() * pow(base, (ys.len() - 1) as nat) <= ys.last() * pow(base, (ys.len() - 1) as nat) + to_nat_left(ys.drop_last(), base));
    }

    assert(to_nat_left(ys, base) == to_nat_right(ys, base)) by {
        // lemma_to_nat_left_eqto_nat_right(ys, base);
    }

    // calc! { (<)
    //     to_nat_right(xs, base); 
    //     (==) { lemma_to_nat_left_eqto_nat_right(xs, base); }
    //     to_nat_left(xs, base);
    //     (<)  { lemma_seq_nat_bound(xs.drop_last(), base); }
    //     pow(base, len1) + xs.last() * pow(base, len1);
    //     (==) { lemma_mul_is_distributive_auto(); }
    //     (1 + xs.last()) * pow(base, len1);
    //     (<=) { lemma_pow_positive_auto(); lemma_mul_inequality_auto(); }
    //     to_nat_left(ys, base);
    //     (==) { lemma_to_nat_left_eqto_nat_right(ys, base); }
    //     to_nat_right(ys, base);
    // }
}

/// Two sequences do not have the same nat representations if their prefixes
/// do not have the same nat representations. Helper proof fn for lemma_seq_neq.
pub proof fn lemma_seq_prefix_neq(xs: Seq<int>, ys: Seq<int>, i: int, base: int)
    requires 
        base > 1,
        forall |a: int| xs.contains(a) ==> 0 <= a < base,
        forall |a: int| ys.contains(a) ==> 0 <= a < base,
        0 <= i <= xs.len() == ys.len(),
        to_nat_right(xs.subrange(0, i), base) != to_nat_right(ys.subrange(0, i), base),
    ensures 
        to_nat_right(xs, base) != to_nat_right(ys, base),
    decreases 
        (xs.len() - i)
{

    assert forall |x: int| xs.subrange(0, i).contains(x) implies 0 <= x < base by {
        assert(xs.contains(x));
        assert(0 <= x < base);
    }

    assert forall |x: int| ys.subrange(0, i).contains(x) implies 0 <= x < base by {
        assert(ys.contains(x));
        assert(0 <= x < base);
    }
    


    if i == xs.len() {
        lemma_seq_properties::<int>();
        assert(xs.subrange(0, i) == xs);
        assert(ys.subrange(0, i) == ys);
    } else {
        if xs[i] == ys[i] {
            reveal(to_nat_left);
            assert(xs.subrange(0, i+1).drop_last() =~= xs.subrange(0, i));
            assert(ys.subrange(0, i+1).drop_last() =~= ys.subrange(0, i));

            assert forall |x: int| #[trigger](xs.subrange(0, i + 1).contains(x)) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }
            assert forall |x: int| #[trigger](ys.subrange(0, i + 1).contains(x)) implies 0 <= x < base by {
                assert(ys.contains(x));
                assert(0 <= x < base);
            }

            // lemma_to_nat_left_eqto_nat_right_auto();
            lemma_to_nat_left_eqto_nat_right(xs.subrange(0, i+1), base);
            lemma_to_nat_left_eqto_nat_right(xs.subrange(0, i), base);

            lemma_to_nat_left_eqto_nat_right(ys.subrange(0, i+1), base);
            lemma_to_nat_left_eqto_nat_right(ys.subrange(0, i), base);



            assert(to_nat_right(xs.subrange(0, i + 1), base) == to_nat_left(xs.subrange(0, i + 1), base));
            lemma_seq_properties::<int>();
            assert(to_nat_right(xs.subrange(0, i), base) != to_nat_right(ys.subrange(0, i), base));
            reveal(to_nat_left);
            assert(to_nat_left(xs.subrange(0, i + 1), base) == (to_nat_left(xs.subrange(0, i + 1).drop_last(), base) + xs.subrange(0, i + 1).last() * pow(base, (xs.subrange(0, i + 1).len() - 1) as nat)));

            assert(to_nat_left(xs.subrange(0, i + 1), base) == (to_nat_left(xs.subrange(0, i + 1).drop_last(), base) + xs.subrange(0, i + 1).last() * pow(base, (xs.subrange(0, i + 1).len() - 1) as nat)));
            assert(to_nat_left(xs.subrange(0, i + 1).drop_last(), base) == to_nat_left(xs.subrange(0, i), base));
            assert( xs.subrange(0, i + 1).last() == xs[i] );
            assert( pow(base, (xs.subrange(0, i + 1).len() - 1) as nat) == pow(base, i as nat) );
            assert(to_nat_left(xs.subrange(0, i + 1), base) == to_nat_left(xs.subrange(0, i), base) + xs[i] * pow(base, i as nat));

            assert(to_nat_right(ys.subrange(0, i + 1), base) == to_nat_left(ys.subrange(0, i + 1), base));
            assert(to_nat_left(ys.subrange(0, i + 1), base) == (to_nat_left(ys.subrange(0, i + 1).drop_last(), base) + ys.subrange(0, i + 1).last() * pow(base, (ys.subrange(0, i + 1).len() - 1) as nat)));
            

            assert(to_nat_right(xs.subrange(0, i + 1), base) != to_nat_right(ys.subrange(0, i + 1), base));
            
        } else if xs[i] < ys[i] {
            assert forall |a: int| #[trigger](ys.subrange(0, i + 1).contains(a)) implies 0 <= a < base by {
                assert(ys.contains(a));
                assert(0 <= a < base);
            }
            assert forall |a: int| #[trigger](xs.subrange(0, i + 1).contains(a)) implies 0 <= a < base by {
                assert(xs.contains(a));
                assert(0 <= a < base);
            }
            lemma_seq_msw_inequality(xs.subrange(0, i+1), ys.subrange(0, i+1), base);
            assert(to_nat_right(xs.subrange(0, i + 1), base) != to_nat_right(ys.subrange(0, i + 1), base));
        } else {
            assert forall |a: int| #[trigger](ys.subrange(0, i + 1).contains(a)) implies 0 <= a < base by {
                assert(ys.contains(a));
                assert(0 <= a < base);
            }
            assert forall |a: int| #[trigger](xs.subrange(0, i + 1).contains(a)) implies 0 <= a < base by {
                assert(xs.contains(a));
                assert(0 <= a < base);
            }
            lemma_seq_msw_inequality(ys.subrange(0, i+1), xs.subrange(0, i+1), base);
            assert(to_nat_right(xs.subrange(0, i + 1), base) != to_nat_right(ys.subrange(0, i + 1), base));
        }
        reveal(to_nat_right);

        assert forall |a: int| #[trigger](xs.subrange(0, i + 1).contains(a)) implies 0 <= a < base by {
            assert(xs.contains(a));
            assert(0 <= a < base);
        }
        assert forall |a: int| #[trigger](ys.subrange(0, i + 1).contains(a)) implies 0 <= a < base by {
            assert(ys.contains(a));
            assert(0 <= a < base);
        }
    
        assert(0 <= i + 1 <= xs.len() == ys.len());
        lemma_seq_prefix_neq(xs, ys, i + 1, base);
    }
}

// refactored this into an inductive proof
/// If two sequences of the same length are not equal, their nat
/// representations are not equal.
pub proof fn lemma_seq_neq(xs: Seq<int>, ys: Seq<int>, base: int)
    requires 
        xs.len() == ys.len(),
        !(xs =~= ys),
        forall |a: int| #[trigger](xs.contains(a)) ==> 0 <= a < base,
        forall |a: int| #[trigger](ys.contains(a)) ==> 0 <= a < base,
        base > 1,
    ensures 
        to_nat_right(xs, base) != to_nat_right(ys, base)
    decreases
        xs.len()
{
    assert(exists |j: int| 0 <= j < xs.len() && xs[j] != ys[j]);

    if xs.len() == 0 {

    }
    else if xs.drop_first() =~= ys.drop_first() {
        // in this case, want to show xs.fist() != ys.first()
        assert(xs.first() != ys.first()) by {
            if ( xs.first() == ys.first() ) {
                assert forall |i: int|  0 <= i < xs.len() implies xs[i] == ys[i] by {
                    if (i == 0) {
                        assert(xs[i] == ys[i]);
                    } else {
                        assert(xs[i] == xs.subrange(1, xs.len() as int)[i - 1]);
                        assert(xs[i] == ys[i]);
                    }
                }
            }
        };
        reveal(to_nat_right);
        assert(to_nat_right(xs, base) != to_nat_right(ys, base));        
    } else {
        assert(!(xs.drop_first() =~= ys.drop_first()));
        assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
            assert(xs.contains(x));
            assert(0 <= x < base);
        }
        assert forall |x: int| ys.drop_first().contains(x) implies 0 <= x < base by {
            assert(ys.contains(x));
            assert(0 <= x < base);
        }
        lemma_seq_neq(xs.drop_first(), ys.drop_first(), base);
        assert(to_nat_right(xs.drop_first(), base) != to_nat_right(ys.drop_first(), base));
        if (xs.first() == ys.first()) {
            reveal(to_nat_right);
            assert(to_nat_right(xs, base) != to_nat_right(ys, base)) by {
                assert(base > 1);
                lemma_mul_strict_inequality_auto();
                assert(to_nat_right(xs.drop_first(), base) * base != to_nat_right(ys.drop_first(), base) * base);
                assert(to_nat_right(xs.drop_first(), base) * base + xs.first() != to_nat_right(ys.drop_first(), base) * base + ys.first());
            };
        } else {
            reveal(to_nat_right);
            assert(xs.first() != ys.first());
            lemma_mul_strict_inequality_auto();
            assert(to_nat_right(xs.drop_first(), base) != to_nat_right(ys.drop_first(), base));
            assert(xs.contains(xs.first()));
            assert(ys.contains(ys.first()));
            assert(0 <= xs.first() < base);
            assert(0 <= ys.first() < base);
            if (to_nat_right(xs.drop_first(), base) < to_nat_right(ys.drop_first(), base)) {
                assert(to_nat_right(xs.drop_first(), base) <= to_nat_right(ys.drop_first(), base) - 1);
                assert(to_nat_right(xs.drop_first(), base) * base <= to_nat_right(ys.drop_first(), base) * base - 1 * base) by {
                    lemma_mul_inequality(to_nat_right(xs.drop_first(), base), to_nat_right(ys.drop_first(), base), base);
                    lemma_mul_is_distributive(base, to_nat_right(ys.drop_first(), base), 1);
                };
                assert(to_nat_right(xs.drop_first(), base) * base + xs.first() != to_nat_right(ys.drop_first(), base) * base + ys.first());
            } else {
                // notably the direction of the <= seems to matter here
                assert(to_nat_right(ys.drop_first(), base)<= to_nat_right(xs.drop_first(), base) - 1);
                assert(to_nat_right(ys.drop_first(), base) * base <= to_nat_right(xs.drop_first(), base) * base - 1 * base) by {
                    lemma_mul_inequality(to_nat_right(ys.drop_first(), base), to_nat_right(xs.drop_first(), base), base);
                    lemma_mul_is_distributive(base, to_nat_right(xs.drop_first(), base), 1);
                };
                assert(to_nat_right(xs.drop_first(), base) * base + xs.first() != to_nat_right(ys.drop_first(), base) * base + ys.first());
            }
            assert(to_nat_right(xs, base) != to_nat_right(ys, base));
        }
        assert(to_nat_right(xs, base) != to_nat_right(ys, base));
    }
}

/// If the nat representations of two sequences of the same length are equal
/// to each other, the sequences are the same.
pub proof fn lemma_seq_eq(xs: Seq<int>, ys: Seq<int>, base: int)
    requires
        xs.len() == ys.len(),
        to_nat_right(xs, base) == to_nat_right(ys, base),
        forall |a: int| #[trigger](xs.contains(a)) ==> 0 <= a < base,
        forall |a: int| #[trigger](ys.contains(a)) ==> 0 <= a < base,
        base > 1,
    ensures 
        xs =~= ys
{
    if !(xs =~= ys) {
        lemma_seq_neq(xs, ys, base);
    }
}

/// The nat representation of a sequence and its least significant position are
/// congruent.
pub proof fn lemma_seq_lsw_mod_equivalence(xs: Seq<int>, base: int)
    requires 
        xs.len() >= 1,
        base > 1,
        forall |a: int| #[trigger](xs.contains(a)) ==> 0 <= a < base,
    ensures 
        is_mod_equivalent(to_nat_right(xs, base), xs.first(), base),
{
    if xs.len() == 1 {
        lemma_seq_len1(xs, base);
        lemma_mod_equivalence_auto();
        assert(is_mod_equivalent(to_nat_right(xs, base), xs.first(), base));
    } else {
        assert(is_mod_equivalent(to_nat_right(xs, base), xs.first(), base)) by {
            reveal(to_nat_right);
            assert forall |x: int| xs.drop_first().contains(x) implies 0 <= x < base by {
                assert(xs.contains(x));
                assert(0 <= x < base);
            }
            lemma_mod_equivalence(to_nat_right(xs, base), to_nat_right(xs.drop_first(), base) * base + xs.first(), base);
            assert(is_mod_equivalent(to_nat_right(xs, base), to_nat_right(xs.drop_first(), base) * base + xs.first(), base));
            reveal(to_nat_right);
            assert(to_nat_right(xs, base) == to_nat_right(xs.drop_first(), base) * base + xs.first());
            lemma_mod_multiples_basic_auto();
            assert( to_nat_right(xs.drop_first(), base) * base % base == 0);
            assert(xs.contains(xs.first()));
            assert(0 <= xs.first() < base);
            lemma_mod_properties_auto();
            assert( xs.first() % base == xs.first());
            let x = to_nat_right(xs, base);
            let y = xs.first();
            assert( x % base == y % base ==> (x - y) % base == 0) by {

            }
            assert( (x - y) % base == 0 ==> x % base == y % base) by {
                assert( y % base == y);
                assert( x % base == (to_nat_right(xs.drop_first(), base) * base + xs.first()) % base);
                lemma_mod_multiples_vanish(to_nat_right(xs.drop_first(), base), xs.first(), base);
                assert( (base * to_nat_right(xs.drop_first(), base) + xs.first()) % base == xs.first() % base);
                lemma_mod_multiples_vanish_auto();
                lemma_mul_is_commutative_auto();
                assert((to_nat_right(xs.drop_first(), base) * base + xs.first()) % base == xs.first() % base);

            }
            assert(is_mod_equivalent(to_nat_right(xs, base), xs.first(), base));

        }
    }
}

//////////////////////////////////////////////////////////////////////////////
//
// from_nat definition and lemmas (moved to LittleEndianNat1.rs)
//
//////////////////////////////////////////////////////////////////////////////

// /// converts a nat to a sequence
// spec fn from_nat(n: nat, base: int) -> (xs: Seq<int>)
//     recommends base > 1
//     decreases n via from_nat_decreases
//     // ensures to_nat_right(xs, base) == n
// {
//     if n == 0 {
//         seq![]
//     } else {
//         seq![n as int % base] + from_nat((n as int / base) as nat, base)
//     }
// }

// #[via_fn]
// proof fn from_nat_decreases(n: nat, base: int) {
//     lemma_div_basics_auto();
//     if n > 0 {
//         lemma_div_decreases_auto();
//         assume(false);
//         assert(((n as int / base) as nat) < n);
//     }
// }

//   /* Converts a nat to a sequence. */
//   function {:opaque} from_nat(n: nat): (xs: seq<uint>)
//   {
//     if n == 0 then []
//     else
//       LemmaDivBasicsAuto();
//       LemmaDivDecreasesAuto();
//       [n % BASE()] + from_nat(n / BASE())
//   }


// /* Ensures length of the sequence generated by from_nat is less than len.
// Helper proof fn for from_natWithLen. */
// pub proof fn lemma_from_nat_len(n: nat, len: nat)
// requires pow(base, len) > n
// ensures |from_nat(n)| <= len
// {
// reveal from_nat();
// if n == 0 {
// } else {
//     calc {
//     |from_nat(n)|;
//     == { lemma_div_basics_auto(); }
//     1 + |from_nat(n / base)|;
//     <= {
//         lemma_multiply_divide_lt_auto();
//         lemma_div_decreases_auto();
//         reveal pow();
//         lemma_from_nat_len(n / base, len - 1);
//         }
//     len;
//     }
// }
// }

// /* If we start with a nat, convert it to a sequence, and convert it back, we
// get the same nat we started with. */
// pub proof fn lemma_nat_seq_nat(n: nat)
// ensures to_nat_right(from_nat(n)) == n
// decreases n
// {
// reveal to_nat_right();
// reveal from_nat();
// if n == 0 {
// } else {
//     calc {
//     to_nat_right(from_nat(n));
//     { lemma_div_basics_auto(); }
//     to_nat_right([n % base] + from_nat(n / base));
//     n % base + to_nat_right(from_nat(n / base)) * base;
//     {
//         lemma_div_decreases_auto();
//         lemma_nat_seq_nat(n / base);
//     }
//     n % base + n / base * base;
//     { lemma_fundamental_div_mod(n, base); }
//     n;
//     }
// }
// }

// /* Extends a sequence to a specified length. */
// function {:opaque} SeqExtend(xs: Seq<int>, n: nat): (ys: Seq<int>)
// requires |xs| <= n
// ensures |ys| == n
// ensures to_nat_right(ys, base) == to_nat_right(xs, base)
// decreases n - |xs|
// {
// if |xs| >= n then xs else lemma_seq_append_zero(xs); SeqExtend(xs + seq![0], n)
// }

// /* Extends a sequence to a length that is a multiple of n. */
// function {:opaque} SeqExtendMultiple(xs: Seq<int>, n: nat): (ys: Seq<int>)
// requires n > 0
// ensures |ys| % n == 0
// ensures to_nat_right(ys, base) == to_nat_right(xs, base)
// {
// var newLen := |xs| + n - (|xs| % n);
// lemma_sub_mod_noop_right(|xs| + n, |xs|, n);
// lemma_mod_basics_auto();
// assert newLen % n == 0;

// lemma_seq_nat_bound(xs);
// lemma_pow_increases_auto();
// SeqExtend(xs, newLen)
// }

// /* Converts a nat to a sequence of a specified length. */
// function {:opaque} from_natWithLen(n: nat, len: nat): (xs: Seq<int>, base: int)
// requires pow(base, len) > n
// ensures |xs| == len
// ensures to_nat_right(xs, base) == n
// {
// lemma_from_nat_len(n, len);
// lemma_nat_seq_nat(n);
// SeqExtend(from_nat(n), len)
// }

// /* If the nat representation of a sequence is zero, then the sequence is a
// sequence of zeros. */
// pub proof fn lemma_seq_zero(xs: Seq<int>, base: int)
// requires to_nat_right(xs, base) == 0
// ensures forall i :: 0 <= i < |xs| ==> xs[i] == 0
// {
// reveal to_nat_right();
// if |xs| == 0 {
// } else {
//     lemma_mul_nonnegative_auto();
//     assert xs.first() == 0;

//     lemma_mul_nonzero_auto();
//     lemma_seq_zero(xs.drop_first());
// }
// }

// /* Generates a sequence of zeros of a specified length. */
// function {:opaque} SeqZero(len: nat): (xs: Seq<int>, base: int)
// ensures |xs| == len
// ensures forall i :: 0 <= i < |xs| ==> xs[i] == 0
// ensures to_nat_right(xs, base) == 0
// {
// lemma_pow_positive(base, len);
// var xs := from_natWithLen(0, len);
// lemma_seq_zero(xs);
// xs
// }

// /* If we start with a sequence, convert it to a nat, and convert it back to a
// sequence with the same length as the original sequence, we get the same
// sequence we started with. */
// pub proof fn lemma_seq_nat_seq(xs: Seq<int>, base: int)
// ensures pow(base, |xs|) > to_nat_right(xs, base)
// ensures from_natWithLen(to_nat_right(xs, base), |xs|) == xs
// {
// reveal from_nat();
// reveal to_nat_right();
// lemma_seq_nat_bound(xs);
// if |xs| > 0 {
//     calc {
//     from_natWithLen(to_nat_right(xs, base), |xs|) != xs;
//     { lemma_seq_neq(from_natWithLen(to_nat_right(xs, base), |xs|), xs); }
//     to_nat_right(from_natWithLen(to_nat_right(xs, base), |xs|)) != to_nat_right(xs, base);
//     to_nat_right(xs, base) != to_nat_right(xs, base);
//     false;
//     }
// }
// }

// //////////////////////////////////////////////////////////////////////////////
// //
// // Addition and subtraction
// //
// //////////////////////////////////////////////////////////////////////////////

// /* Adds two sequences. */
// function {:opaque} SeqAdd(xs: Seq<int>, ys: Seq<int>): (Seq<int>, nat)
// requires |xs| == |ys|
// ensures var (zs, cout) := SeqAdd(xs, ys);
//         |zs| == |xs| && 0 <= cout <= 1
// decreases xs
// {
// if |xs| == 0 then ([], 0)
// else
//     var (zs', cin) := SeqAdd(xs.drop_last(), DropLast(ys));
//     var sum: int := xs.last() + Last(ys) + cin;
//     var (sum_out, cout) := if sum < base then (sum, 0)
//                             else (sum - base, 1);
//     (zs' + [sum_out], cout)
// }

// /* SeqAdd returns the same value as converting the sequences to nats, then
// adding them. */
// proof fn vcs_split_on_every_assert} lemma_seq_add(xs: Seq<int>, ys: Seq<int>, zs: Seq<int>, cout: nat)
// requires |xs| == |ys|
// requires SeqAdd(xs, ys) == (zs, cout)
// ensures to_nat_right(xs, base) + to_nat_right(ys, base) == to_nat_right(zs) + cout * pow(base, |xs|)
// {
// reveal SeqAdd();
// if |xs| == 0 {
//     reveal to_nat_right();
// } else {
//     var pow := pow(base, (xs.len() - 1) as nat);
//     var (zs', cin) := SeqAdd(xs.drop_last(), DropLast(ys));
//     var sum: int := xs.last() + Last(ys) + cin;
//     var z := if sum < base then sum else sum - base;
//     assert sum == z + cout * base;

//     reveal to_nat_left();
//     lemma_to_nat_left_eqto_nat_right_auto();
//     calc {
//     to_nat_right(zs);
//     to_nat_left(zs);
//     to_nat_left(zs') + z * pow;
//     { lemma_seq_add(xs.drop_last(), DropLast(ys), zs', cin); }
//     to_nat_left(xs.drop_last()) + to_nat_left(DropLast(ys)) - cin * pow + z * pow;
//     {
//         lemma_mul_equality(sum, z + cout * base, pow);
//         assert sum * pow == (z + cout * base) * pow;
//         lemma_mul_is_distributive_auto();
//     }
//     to_nat_left(xs, base) + to_nat_left(ys, base) - cout * base * pow;
//     {
//         lemma_mul_is_associative(cout, base, pow);
//         reveal pow();
//     }
//     to_nat_left(xs, base) + to_nat_left(ys, base) - cout * pow(base, |xs|);
//     to_nat_right(xs, base) + to_nat_right(ys, base) - cout * pow(base, |xs|);
//     }
// }
// }

// /* Subtracts two sequences. */
// function {:opaque} SeqSub(xs: Seq<int>, ys: Seq<int>): (Seq<int>, nat)
// requires |xs| == |ys|
// ensures var (zs, cout) := SeqSub(xs, ys);
//         |zs| == |xs| && 0 <= cout <= 1
// decreases xs
// {
// if |xs| == 0 then ([], 0)
// else
//     var (zs, cin) := SeqSub(xs.drop_last(), DropLast(ys));
//     var (diff_out, cout) := if xs.last() >= Last(ys) + cin
//                             then (xs.last() - Last(ys) - cin, 0)
//                             else (base + xs.last() - Last(ys) - cin, 1);
//     (zs + [diff_out], cout)
// }

// /* SeqSub returns the same value as converting the sequences to nats, then
// subtracting them. */
// proof fn vcs_split_on_every_assert} lemma_seq_sub(xs: Seq<int>, ys: Seq<int>, zs: Seq<int>, cout: nat)
// requires |xs| == |ys|
// requires SeqSub(xs, ys) == (zs, cout)
// ensures to_nat_right(xs, base) - to_nat_right(ys, base) + cout * pow(base, |xs|) == to_nat_right(zs)
// {
// reveal SeqSub();
// if |xs| == 0 {
//     reveal to_nat_right();
// } else {
//     var pow := pow(base, (xs.len() - 1) as nat);
//     var (zs', cin) := SeqSub(xs.drop_last(), DropLast(ys));
//     var z := if xs.last() >= Last(ys) + cin
//     then xs.last() - Last(ys) - cin
//     else base + xs.last() - Last(ys) - cin;
//     assert cout * base + xs.last() - cin - Last(ys) == z;

//     reveal to_nat_left();
//     lemma_to_nat_left_eqto_nat_right_auto();
//     calc {
//     to_nat_right(zs);
//     to_nat_left(zs);
//     to_nat_left(zs') + z * pow;
//     { lemma_seq_sub(xs.drop_last(), DropLast(ys), zs', cin); }
//     to_nat_left(xs.drop_last()) - to_nat_left(DropLast(ys)) + cin * pow + z * pow;
//     {
//         lemma_mul_equality(cout * base + xs.last() - cin - Last(ys), z, pow);
//         assert pow * (cout * base + xs.last() - cin - Last(ys)) == pow * z;
//         lemma_mul_is_distributive_auto();
//     }
//     to_nat_left(xs, base) - to_nat_left(ys, base) + cout * base * pow;
//     {
//         lemma_mul_is_associative(cout, base, pow);
//         reveal pow();
//     }
//     to_nat_left(xs, base) - to_nat_left(ys, base) + cout * pow(base, |xs|);
//     to_nat_right(xs, base) - to_nat_right(ys, base) + cout * pow(base, |xs|);
//     }
// }
// }
}