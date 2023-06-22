use vstd::prelude::*;
//use std::vec::Vec;
mod relations;
use relations::strict_total_ordering;
use vstd::slice::slice_index_get;
//--no-lifetime to skip moved errors (should shut up if you remove ampersands)

verus!{

fn binary_search<T: std::ops::RangeBounds<T> + std::marker::Copy, F: std::clone::Clone>(s: &[T], key: T, Ghost(less_pure): Ghost<FnSpec(T,T) ->bool>, less: &F) -> (result: Option<usize>)
    where F: Fn(T, T) -> bool
    requires 
        s@.len() <  0xffff_ffff_ffff_ffff, //prevents arithmetic overflow
        forall |i: int, j:int| 0<=i<j<s@.len() ==> less_pure(s[i], s[j]) || s[i] == s[j],
        strict_total_ordering(less_pure),
        forall |x, y| #[trigger] less.requires((x, y)), // for any pair (x, y), it is safe to call leq(x, y)
        forall |x, y, b| #[trigger] less.ensures((x, y), b) ==> #[trigger] less_pure(x, y) == b // If `leq` takes input (x, y) and returns b, then leq_pure(x, y) == b
    ensures
        result.is_some() ==> result.unwrap() < s@.len() && s[result.unwrap() as int] == key,
        result.is_none() ==> !s@.contains(key),
{
    let mut lo = 0;
    let mut hi = s.len();
    assert(0<= lo <= s@.len());
    assert(s@.len() >=0);
    assert(hi == s@.len());
    assert(0<= hi <= s@.len());
    assert(!s@.subrange(hi as int,s@.len() as int).contains(key));
    assert(!s@.subrange(0,lo as int).contains(key));
    let mut mid = 0;
    while lo < hi
        invariant
            s@.len() <  0xffff_ffff_ffff_ffff, //prevents arithmetic overflow
            0<= lo <= hi <= s@.len(),
            0<=mid<=s@.len(),
            !s@.subrange(0,lo as int).contains(key) && !s@.subrange(hi as int,s@.len() as int).contains(key),
            forall |x, y| #[trigger] less.requires((x, y)), // for any pair (x, y), it is safe to call leq(x, y)
            forall |x, y, b| #[trigger] less.ensures((x, y), b) ==> #[trigger] less_pure(x, y) == b, // If `leq` takes input (x, y) and returns b, then leq_pure(x, y) == b
    
            //s@.subrange(0, s@.len() as int) == old(s)@,
    {
        mid = lo + (hi - lo)/2;
        //assert(mid == (lo + hi)/2 < (lo + hi) <= s@.len() + s@.len());
        if (less(key,*slice_index_get(s, mid))){
            hi = mid;
            let temp = *slice_index_get(s, mid);
            let ghost snap = temp;
            assert(snap == s@.index(mid as int));
            assert(less_pure(key, snap)); //FAILS
        } else if (less(*slice_index_get(s, mid), key)){
            lo = mid +1;
        } else {
            assert(mid < s@.len());
            assert(s@.index(mid as int) == key) by {lemma_must_be_equal(s@.index(mid as int), key, less_pure);}
            return Some(mid);
        }
    }
    assert(!s@.subrange(0,lo as int).contains(key) && !s@.subrange(hi as int,s@.len() as int).contains(key));
    assert(lo >=hi);
    assert(0<= lo <= hi <= s@.len());
    assert(forall |x :T| #[trigger] s@.contains(x) <== #[trigger] s@.subrange(0,lo as int).contains(x) 
        || #[trigger] s@.subrange(hi as int,s@.len() as int).contains(x));



    //proof{lemma_integer_overlap(lo,hi,mid,s@.len() as usize);}
    assert(forall |x :T| #[trigger] s@.contains(x) && lo>=hi ==> #[trigger] s@.subrange(0,lo as int).contains(x) 
        || #[trigger] s@.subrange(hi as int,s@.len() as int).contains(x)) by {
            lemma_integer_overlap(lo, hi, mid, s@.len() as usize);
            lemma_elts_between(s@, lo, hi);
            lemma_elts_overlap(s@, lo, hi);
        }
    assert(!s@.contains(key));
    None
}

fn main(){}

pub proof fn lemma_integer_overlap(lo :usize, hi :usize, index: usize, max :usize)
    requires
        indices_overlap(lo,hi),
        0<=hi<=lo<=max,
        0<=index<=max,
    ensures
        0<=index<=lo || hi<=index<=max
{}

#[verifier(external_body)]
pub proof fn lemma_elts_overlap<T>(s :Seq<T>, lo :usize, hi: usize)
    requires
        indices_overlap(lo,hi),
        lo<=s.len(),
        hi<=s.len(),
    ensures
        forall |x :T| #[trigger] s.contains(x) ==> #[trigger] s.subrange(0,lo as int).contains(x) 
            || #[trigger] s.subrange(hi as int,s.len() as int).contains(x),
{}


pub proof fn lemma_elts_between<T>(s :Seq<T>, lo :usize, hi :usize)
    requires
        0<=lo<=hi<=s.len(),
    ensures
        forall |x :T| #[trigger] s.subrange(lo as int, hi as int).contains(x) ==> #[trigger]s.contains(x),
{}

pub open spec fn indices_overlap(lo :usize, hi :usize) -> bool
{
    hi >= lo
}

#[verifier(external_body)]
pub proof fn lemma_must_be_equal<T>(a :T, b :T, less :FnSpec(T,T)->bool)
    requires
        less(a,b) == false,
        less(b,a) == false,
    ensures
        a == b
{}
}