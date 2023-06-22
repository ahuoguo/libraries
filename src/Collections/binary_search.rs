use vstd::prelude::*;
//use std::vec::Vec;
mod relations;
use relations::strict_total_ordering;
use vstd::slice::slice_index_get;

verus!{

fn binary_search<T: std::ops::RangeBounds<T> + std::clone::Clone, F: std::clone::Clone>(s: &[T], key: T, Ghost(less_pure): Ghost<FnSpec(T,T) ->bool>, less: &F) -> (result: Option<usize>)
    where F: Fn(T, T) -> bool
    requires 
        forall |i: int, j:int| 0<=i<j<s@.len() ==> less_pure(s[i], s[j]) || s[i] == s[j],
        strict_total_ordering(less_pure),
    ensures
        result.is_some() ==> result.unwrap() < s@.len() && s[result.unwrap() as int] == key,
        result.is_none() ==> !s@.contains(key),
{
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi
        invariant
            0<= lo <= hi <= s@.len(),
            s@.subrange(0,lo as int).contains(key) && s@.subrange(hi as int,s@.len() as int).contains(key),
            //s@.subrange(0, s@.len() as int) == old(s)@,
    {
        let mid = (lo + hi)/2;
        if less(key.copy(),*slice_index_get(s, mid)){
            hi = mid;
        } else if less(*slice_index_get(s, mid), &key){
            lo = mid +1;
        } else {
            return Some(mid);
        }
    }
    None
}

fn main(){}

}