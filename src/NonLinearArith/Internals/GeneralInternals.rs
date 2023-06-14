
// /** Declares helper lemmas and predicates for non-linear arithmetic */
// module {:options "-functionSyntax:4"} Dafny.GeneralInternals
// {

//   /* this predicate is primarily used as a trigger */
//   ghost predicate IsLe(x: int, y: int)
//   {
//     x <= y
//   }

//   /* aids in the process of induction for modulus */
//   lemma LemmaInductionHelper(n: int, f: int -> bool, x: int)
//     requires n > 0
//     requires forall i :: 0 <= i < n ==> f(i)
//     requires forall i {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
//     requires forall i {:trigger f(i), f(i - n)} :: i < n  && f(i) ==> f(i - n)
//     ensures  f(x)
//     decreases if x >= n then x else -x
  // {
  //   if (x >= n)
  //   {
  //     LemmaInductionHelper(n, f, x - n);
  //     assert f((x - n) + n);
  //   }
  //   else if (x < 0)
  //   {
  //     LemmaInductionHelper(n, f, x + n);
  //     assert f((x + n) - n);
  //   }
//   }
// }

use vstd::prelude::*;

verus! {

    spec fn add (a: int, b: int) -> int
    {
        a + b
    }

    spec fn sub (a: int, b: int) -> int
    {
        a - b
    }

    // ghost?
    spec fn is_le(x: int, y: int) -> bool
    {
      x <= y
    }

  /* aids in the process of induction for modulus */
  // TODO: solve the following junks in a shorter way?
  // proof fn LemmaInductionHelper(n: int, f: FnSpec(int) -> bool, x: int)
  //   requires 
  //       x >= 0,
  //       n > 0,
  //       forall |i : int| 0 <= i < n ==> #[trigger] f(i),
  //       forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
  //       forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
  //   ensures
  //       f(x)
  //   decreases (if x >= n {x} else {-x})
  // {
  //   if (x >= n)
  //   {
  //     LemmaInductionHelper(n, f, x - n);
  //     assert(f(sub(x, n) + n));
  //     assert(f((x - n) + n));
  //   }
  //   else if (x < 0)
  //   {
  //     LemmaInductionHelper(n, f, x + n);
  //     assert(f((x + n) - n));
  //   }
  // }


  /* aids in the process of induction for mod */
  // TODO: more about FnSpec?, how does it actually works
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

    proof fn lemma_induction_helper(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x < 0,
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
}