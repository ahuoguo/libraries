use vstd::prelude::*;

// TODO
// if I don't have path, the `pub mod MulInternals` will
// report an error for the following two modules
// #[path = "ModInternalsNonlinear.rs"]
// mod ModInternalsNonlinear;
// #[path = "DivInternalsNonlinear.rs"]
// mod GeneralInternals;

#[allow(unused_imports)]
use crate::NonLinearArith::Internals::ModInternalsNonlinear::*;
#[allow(unused_imports)]
use crate::NonLinearArith::Internals::DivInternalsNonlinear::*;

use crate::NonLinearArith::Internals::GeneralInternals::*;

verus! {

    /* performs multiplication for positive integers using recursive addition */
    // change x to nat?
    // NEED TO ASK, here, we either change x into nat or return 0 when x < 0
    // This is because we do not have partial functions
    // and the recommend clause is too weak so that we actually need to consider
    // the x < 0 case
    spec fn mul_pos(x: int, y: int) -> int
        recommends x >= 0
        decreases x
        // any design reason for using recommends instead of requires?
    {
        if x <= 0 { 
            0 
        } else {
            y + mul_pos(x - 1, y) 
        }
    }

    /* performs multiplication for both positive and negative integers */
    spec fn mul_recursive(x: int, y: int) -> int
    {
        if x >= 0 { mul_pos(x, y) }
        else { -1 * mul_pos(-1 * x, y) }
    }


    /* you need these add1, sub1 because by importing the GeneralInternals add,
       it will still complain it is an arithmetic expression */
    spec fn add1 (a: int, b: int) -> int
    {
        // or a + b
        crate::NonLinearArith::Internals::GeneralInternals::add(a, b)
    } 

    spec fn sub1 (a: int, b: int) -> int
    {
        // or a + b
        crate::NonLinearArith::Internals::GeneralInternals::sub(a, b)
    }

    spec fn mul1 (a: int, b: int) -> int
    {
        a * b
    }

    /* performs induction on multiplication */
    /* TODO */
    /* HOW TO LET THE ADD/ADD1 COMMUNICATE */
    /* NEED REVIEW */
    proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
        requires 
            f(0),
            forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1)),
            forall |i: int, j:int| i>=0 && j == i+1 && #[trigger] f(i) ==> #[trigger] f(j),
            forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)),
        ensures
            forall |i: int| #[trigger] f(i)
    {
        assert (forall |i: int| f(add1(i, 1)) ==> #[trigger] f(crate::NonLinearArith::Internals::GeneralInternals::add(i, 1)));  // OBSERVE
        assert (forall |i: int| f(sub1(i, 1)) ==> #[trigger] f(crate::NonLinearArith::Internals::GeneralInternals::sub(i, 1)));   // OBSERVE

        assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
    }

    /* proves that multiplication is always commutative */
    proof fn lemma_mul_commutes()
        ensures 
            forall |x: int, y: int| #[trigger] mul1(x, y) == mul1(y, x)
    {
        // not important
        // assert forall |x:int, y:int| (mul1(x, y) == mul1(y, x)) by { lemma_mul_induction(|i: int| x * i == i * x) };
    }

    /* proves the distributive property of multiplication when multiplying an interger
    by (x +/- 1) */
    //rename for both directions ???
    // TODO: confirm the use of `forall_arith`
    proof fn lemma_mul_successor()
        ensures 
            forall_arith(|x:int, y:int| #[trigger]((x + 1) * y) == x * y + y),
            forall_arith(|x:int, y:int| #[trigger]((x - 1) * y) == x * y - y)
    {
        // LATER the following dafny proof seems to be unnecessary in verus

        // LemmaMulCommutes();
        // forall x:int, y:int
        // ensures (x + 1) * y == x * y + y
        // ensures (x - 1) * y == x * y - y
        // {
        // LemmaMulIsDistributiveAdd(y, x, 1);
        // LemmaMulIsDistributiveAdd(y, x, -1);
        // }
    }

    /* proves the distributive property of multiplication */
    proof fn LemmaMulDistributes()
        ensures 
            forall_arith(|x:int, y:int, z:int| #[trigger]((x + y) * z) == x * z + y * z),
            forall_arith(|x:int, y:int, z:int| #[trigger]((x - y) * z) == x * z - y * z)
    {
        // LemmaMulSuccessor();
        // forall x:int, y:int, z:int
        // ensures (x + y) * z == x * z + y * z
        // ensures (x - y) * z == x * z - y * z
        // {
        // var f1 := i => (x + i) * z == x * z + i * z;
        // var f2 := i => (x - i) * z == x * z - i * z;
        // assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
        // assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
        // assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
        // assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
        // LemmaMulInduction(f1);
        // LemmaMulInduction(f2);
        // assert f1(y);
        // assert f2(y);
        // }
    }

    /* groups distributive and associative properties of multiplication */
    // spec fn MulAuto() -> bool
    // {
    //     &&& (forall |x:int, y:int| x * y == y * x)
    //     &&& (forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z)
    //     &&& (forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z)
    // }

    // /* proves that MulAuto is valid */
    // proof fn LemmaMulAuto()
    //     ensures  MulAuto()
    // {
    //     LemmaMulCommutes();
    //     LemmaMulDistributes();
    // }

    // /* performs auto induction for multiplication */
    // proof fn LemmaMulInductionAuto(x: int, f: int -> bool)
    //     requires MulAuto() ==> && f(0)
    //                         && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1))
    //                         && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1))
    //     ensures  MulAuto()
    //     ensures  f(x)
    // {
    //     LemmaMulCommutes();
    //     LemmaMulDistributes();
    //     assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    //     assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    //     LemmaMulInduction(f);
    //     assert f(x);
    // }

    // /* performs auto induction on multiplication for all i s.t. f(i) exists */
    // proof fn LemmaMulInductionAutoForall(f: int -> bool)
    //     requires MulAuto() ==> && f(0)
    //                         && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1))
    //                         && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1))
    //     ensures  MulAuto()
    //     ensures  forall i {:trigger f(i)} :: f(i)
    // {
    //     LemmaMulCommutes();
    //     LemmaMulDistributes();
    //     assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    //     assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    //     LemmaMulInduction(f);
    // }


}