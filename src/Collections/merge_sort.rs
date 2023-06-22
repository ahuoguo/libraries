use vstd::prelude::*;
use std::vec::Vec;
mod relations;
use relations::{total_ordering, sorted_by, lemma_new_first_element_still_sorted_by};

verus! {
    //Splits a sequence in two, sorts the two subsequences using itself, and merge the two sorted sequences using `MergeSortedWith`
    fn merge_sort_by<T: std::marker::Copy, F: std::clone::Clone>(v: Vec<T>, Ghost(leq_pure): Ghost<FnSpec(T,T) ->bool>, leq: &F) -> (result: Vec<T>)
        where F: Fn(T, T) -> bool
        requires
            total_ordering(leq_pure),
            forall |x, y| #[trigger] leq.requires((x, y)), // for any pair (x, y), it is safe to call leq(x, y)
            forall |x, y, b| #[trigger] leq.ensures((x, y), b) ==> #[trigger] leq_pure(x, y) == b // If `leq` takes input (x, y) and returns b, then leq_pure(x, y) == b
        ensures
            sorted_by(result@, leq_pure),
    {
        if v.len() <=1
        {
            v
        } else{
            let split_index = v.len() /2;
            let mut left = v;
            let right = left.split_off(split_index);
            
            let left_sorted = merge_sort_by(left, Ghost(leq_pure), leq);
            let right_sorted = merge_sort_by(right, Ghost(leq_pure), leq);

            assume(forall |x, y| #[trigger] leq.requires((x, y))); // for any pair (x, y), it is safe to call leq(x, y)
            merge_sorted_with(left_sorted, right_sorted, Ghost(leq_pure), leq)
        }
    }

    fn merge_sorted_with<T : std::marker::Copy, F>(left: Vec<T>, right: Vec<T>, 
            Ghost(leq_pure): Ghost<FnSpec(T,T) ->bool>, leq: &F) -> (result: Vec<T>)
        where F: Fn(T, T) -> bool
        requires 
            sorted_by(left@, leq_pure),
            sorted_by(right@, leq_pure),
            total_ordering(leq_pure),
            forall |x, y| #[trigger] leq.requires((x, y)), // for any pair (x, y), it is safe to call leq(x, y)
            forall |x, y, b| #[trigger] leq.ensures((x, y), b) ==> #[trigger] leq_pure(x, y) == b // If `leq` takes input (x, y) and returns b, then leq_pure(x, y) == b
        ensures
            forall|x: T| result@.contains(x) <==> left@.contains(x) || right@.contains(x),
            sorted_by(result@, leq_pure), 
    {
        if left.len() == 0{
            right
        } else if right.len() == 0{
            left
        }else if (leq(left[0], right[0])){
            assert(sorted_by(right@, leq_pure));
            assert(forall |x: T| right@.contains(x) ==> leq_pure(right[0], x));
            assert(leq_pure(left[0], right[0]));
            assert(forall |x: T| right@.contains(x) ==> leq_pure(left[0], x));
            let ghost original_left = left;
            let mut left = left;
            assert(left.len() ==1 || leq_pure(left[0], left[1]));
            let min = left.remove(0);
            assert(forall |i: int| 1<= i < original_left@.len() ==> original_left[i-1] == left[i]);

            assert(sorted_by(left@, leq_pure));
            assert(leq_pure(min, right[0]));
            assert(forall |x: T| right@.contains(x) ==> leq_pure(min, x));
            assert(left.len() ==0 || leq_pure(min, left[0]));
            proof{
                assert(left.len() == 0 || leq_pure(min, left@[0]));
                lemma_new_first_element_still_sorted_by(min, left@, leq_pure);
                assert(leq_pure(min, right@[0]));
                lemma_new_first_element_still_sorted_by(min, right@, leq_pure);
                assert(forall |x: T| left@.contains(x) ==> leq_pure(min, x));
                assert(forall |x: T| right@.contains(x) ==> leq_pure(min, x));
            }
            let mut result = Vec::new();
            assert(original_left@.contains(min));
            result.push(min);
            assert(result@.len() ==1);
            assert(result@.contains(min));
            assert(original_left@.contains(min));
            assert(forall|x: T| result@.contains(x) ==> original_left@.contains(x) || right@.contains(x));
            let mut temp = merge_sorted_with(left, right, Ghost(leq_pure), leq);
            assert(forall|x: T| temp@.contains(x) <==> left@.contains(x) || right@.contains(x));
            proof{
                assert(sorted_by(temp@, leq_pure));
                assert(forall|x: T| temp@.contains(x) <==> left@.contains(x) || right@.contains(x));
                assert(left.len() ==0 || leq_pure(min, left[0]));
                assert(leq_pure(min, right[0]));
                assert(forall |x: T| left@.contains(x) ==> leq_pure(min, x));
                assert(forall |x: T| right@.contains(x) ==> leq_pure(min, x));
                assert(forall |x: T| left@.contains(x) || right@.contains(x) ==> leq_pure(min, x));
                assert(forall|x: T| temp@.contains(x) ==> leq_pure(min, x));

                assert(forall|x: T| temp@.contains(x) ==> leq_pure(min, x));
                assert(temp@.len() == 0 || temp@.contains(temp@[0]));
                assert(temp@.len() == 0 || leq_pure(min, temp@[0]));
                lemma_new_first_element_still_sorted_by(min, temp@, leq_pure);
            }
            assert(forall|x: T| temp@.contains(x) ==> left@.contains(x) || right@.contains(x));
            assert(result@.len() ==1);
            assert(result@.contains(min) && original_left@.contains(min));
            assert(forall|x: T| result@.contains(x) ==> original_left@.contains(x) || right@.contains(x));
            assert(forall|x: T| result@.contains(x) <==> original_left[0] == x);
            assert(forall|x: T| temp@.contains(x) <==> left@.contains(x) || right@.contains(x));
            let ghost old_temp = temp;
            result.append(&mut temp);
            assert(forall|x: T| result@.contains(x) <==> old_temp@.contains(x) || original_left[0] == x);
            assert(forall|x: T| result@.contains(x) ==> original_left@.contains(x) || right@.contains(x));
            assert(forall|x: T| result@.contains(x) <==> left@.contains(x) || right@.contains(x) || original_left[0] == x);

            assert(original_left[0] == min);
            assert(original_left@.subrange(1, original_left@.len() as int) =~= left@);
            assert(forall |i: int| 1<= i < original_left@.len() ==> original_left[i-1] == left[i]);
            assert(original_left@ =~= original_left@.subrange(0,1).add(original_left@.subrange(1, original_left@.len() as int)));

            assert(forall|x: T| result@.contains(x) <==> original_left@.contains(x) || right@.contains(x)); //FAILS
            let result_unmut = result;
            // assert(forall|x: T| result_unmut@.contains(x) <==> left@.contains(x) || right@.contains(x));
            // assert(sorted_by(result_unmut@, leq_pure));
            result_unmut
        }
        else{
            assert(sorted_by(left@, leq_pure));
            assert(forall |x: T| left@.contains(x) ==> leq_pure(left[0], x));
            assert(!leq_pure(left[0], right[0]));
            assert(leq_pure(right[0], left[0]));
            assert(forall |x: T| left@.contains(x) ==> leq_pure(right[0], x));
            let ghost original_right = right;
            let mut right = right;
            assert(right.len() ==1 || leq_pure(right[0], right[1]));
            let min = right.remove(0);
            assert(forall |i: int| 1<= i < original_right@.len() ==> original_right[i-1] == right[i]);

            assert(sorted_by(right@, leq_pure));
            assert(leq_pure(min, left[0]));
            assert(forall |x: T| left@.contains(x) ==> leq_pure(min, x));
            assert(right.len() ==0 || leq_pure(min, right[0]));
            proof{
                assert(right.len() == 0 || leq_pure(min, right@[0]));
                lemma_new_first_element_still_sorted_by(min, right@, leq_pure);
                assert(leq_pure(min, left@[0]));
                lemma_new_first_element_still_sorted_by(min, left@, leq_pure);
                assert(forall |x: T| left@.contains(x) ==> leq_pure(min, x));
                assert(forall |x: T| right@.contains(x) ==> leq_pure(min, x));
            }
            let mut result = Vec::new();
            assert(original_right@.contains(min));
            result.push(min);
            assert(result@.len() ==1);
            assert(result@.contains(min));
            assert(original_right@.contains(min));
            assert(forall|x: T| result@.contains(x) ==> original_right@.contains(x) || left@.contains(x));
            let mut temp = merge_sorted_with(left, right, Ghost(leq_pure), leq);
            assert(forall|x: T| temp@.contains(x) <==> left@.contains(x) || right@.contains(x));
            proof{
                assert(sorted_by(temp@, leq_pure));
                assert(forall|x: T| temp@.contains(x) <==> left@.contains(x) || right@.contains(x));
                assert(right.len() ==0 || leq_pure(min, right[0]));
                assert(leq_pure(min, left[0]));
                assert(forall |x: T| left@.contains(x) ==> leq_pure(min, x));
                assert(forall |x: T| right@.contains(x) ==> leq_pure(min, x));
                assert(forall |x: T| left@.contains(x) || right@.contains(x) ==> leq_pure(min, x));
                assert(forall|x: T| temp@.contains(x) ==> leq_pure(min, x));

                assert(forall|x: T| temp@.contains(x) ==> leq_pure(min, x));
                assert(temp@.len() == 0 || temp@.contains(temp@[0]));
                assert(temp@.len() == 0 || leq_pure(min, temp@[0]));
                lemma_new_first_element_still_sorted_by(min, temp@, leq_pure);
            }
            assert(forall|x: T| temp@.contains(x) ==> left@.contains(x) || right@.contains(x));
            assert(result@.len() ==1);
            assert(result@.contains(min) && original_right@.contains(min));
            assert(forall|x: T| result@.contains(x) ==> original_right@.contains(x) || left@.contains(x));
            assert(forall|x: T| result@.contains(x) <==> original_right[0] == x);
            assert(forall|x: T| temp@.contains(x) <==> left@.contains(x) || right@.contains(x));
            let ghost old_temp = temp;
            result.append(&mut temp);
            assert(forall|x: T| result@.contains(x) <==> old_temp@.contains(x) || original_right[0] == x);
            assert(forall|x: T| result@.contains(x) ==> original_right@.contains(x) || left@.contains(x));
            assert(forall|x: T| result@.contains(x) <==> left@.contains(x) || right@.contains(x) || original_right[0] == x);

            assert(original_right[0] == min);
            assert(original_right@.subrange(1, original_right@.len() as int) =~= right@);
            assert(forall |i: int| 1<= i < original_right@.len() ==> original_right[i-1] == right[i]);
            assert(original_right@ =~= original_right@.subrange(0,1).add(original_right@.subrange(1, original_right@.len() as int)));

            assert(forall|x: T| result@.contains(x) <==> original_right@.contains(x) || left@.contains(x)); 
            let result_unmut = result;
            // assert(forall|x: T| result_unmut@.contains(x) <==> left@.contains(x) || right@.contains(x));
            // assert(sorted_by(result_unmut@, leq_pure));
            result_unmut
        }
    }
 
    fn main(){}
}