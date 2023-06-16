use vstd::prelude::*;

verus! {

    pub open spec fn Min(a: int, b: int) -> int
    {
      if a < b
      { a }
      else
      { b }
    }

    pub open spec fn Max(a: int, b: int) -> int
    {
      if a < b { b } else { a }
    }

    pub open spec fn Max3(a: int, b: int, c: int) -> int
    {
      if a < b { Max(b, c) } else { Max(a, c) }
    }

    pub open spec fn Abs(a: int) -> (b: int)
    {
      if a >= 0 { a } else { -a }
    }

    pub open spec fn add (a: int, b: int) -> int
    {
        a + b
    }

    pub open spec fn sub (a: int, b: int) -> int
    {
        a - b
    }

}