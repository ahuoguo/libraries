use vstd::prelude::*;
use vstd::relations::total_ordering;
use vstd::relations::sorted_by;
use vstd::relations::lemma_new_first_element_still_sorted_by;
use vstd::seq_lib::lemma_seq_properties;
use vstd::seq_lib::lemma_seq_union_to_multiset_commutative;
use vstd::seq_lib::lemma_multiset_commutative;

verus!{

pub open spec fn merge_sort_by<A>(s: Seq<A>, leq: FnSpec(A,A) ->bool) -> Seq<A>
    recommends
        total_ordering(leq),
    decreases
        s.len(),
{
    if s.len() <=1 {s}
    else{
        let split_index = s.len() /2;
        let left = s.subrange(0,split_index as int);
        let right = s.subrange(split_index as int, s.len() as int);
        
        let left_sorted = merge_sort_by(left, leq);
        let right_sorted = merge_sort_by(right, leq);
        merge_sorted_with(left_sorted, right_sorted, leq)
    }
}

pub open spec fn merge_sorted_with<A>(left: Seq<A>, right: Seq<A>, leq: FnSpec(A,A) ->bool) -> Seq<A>
    recommends
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    decreases
        left.len(), right.len()
{
    if left.len() == 0 {right}
    else if right.len() == 0 {left}
    else if leq(left.first(), right.first()){
        Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right, leq)
    } else {
        Seq::<A>::empty().push(right.first()) + merge_sorted_with(left, right.drop_first(), leq)
    }
}

pub proof fn lemma_merge_sort_by_ensures<A>(s: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        total_ordering(leq),
    ensures
        s.to_multiset() =~= merge_sort_by(s,leq).to_multiset(),
        sorted_by(merge_sort_by(s,leq), leq),
    decreases
        s.len(),
{
    if s.len() <=1 {
        //assert(s =~= merge_sort_by(s,leq));
        //assert(sorted_by(s, leq));
        //assert(s.to_multiset() =~= merge_sort_by(s,leq).to_multiset());
    }
    else{
        let split_index = s.len() /2;
        let left = s.subrange(0,split_index as int);
        let right = s.subrange(split_index as int, s.len() as int);
        
        assert(s =~= left + right);

        let left_sorted = merge_sort_by(left, leq);
        lemma_merge_sort_by_ensures(left, leq);
        let right_sorted = merge_sort_by(right, leq);
        lemma_merge_sort_by_ensures(right, leq);
        //assert(sorted_by(left_sorted, leq));
        //assert(sorted_by(right_sorted, leq));

        lemma_merge_sorted_with_ensures(left_sorted, right_sorted, leq);
       // assert((left_sorted+right_sorted).to_multiset() =~= merge_sorted_with(left_sorted, right_sorted, leq).to_multiset());
        //assert(merge_sort_by(s,leq) =~= merge_sorted_with(left_sorted, right_sorted, leq));
       // assert((left+right).to_multiset() =~= s.to_multiset());
        //assert(left.to_multiset() =~= left_sorted.to_multiset());
       // assert(right.to_multiset() =~= right_sorted.to_multiset());
        lemma_multiset_commutative(left,right);
        lemma_multiset_commutative(left_sorted,right_sorted);
        //assert((left+right).to_multiset() =~= left.to_multiset().add(right.to_multiset()));
        //assert((left_sorted+right_sorted).to_multiset() =~= left_sorted.to_multiset().add(right_sorted.to_multiset()));
        //goal:
        //assert(s.to_multiset() =~= merge_sort_by(s,leq).to_multiset());
    }
}

pub proof fn lemma_merge_sorted_with_ensures<A>(left: Seq<A>, right: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    ensures
        (left+right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset(),
        sorted_by(merge_sorted_with(left, right, leq), leq),
    decreases
        left.len(), right.len()
{
    lemma_seq_properties::<A>();
    if left.len() == 0 {
        assert(left+right =~= right);
       // assert(left+right =~= merge_sorted_with(left, right, leq));
       // assert(sorted_by(merge_sorted_with(left, right, leq), leq));

        //assert((left+right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset());
    }
    else if right.len() == 0 {
        // assert(left+right =~= left);
        // assert(left+right =~= merge_sorted_with(left, right, leq));
        // assert(sorted_by(merge_sorted_with(left, right, leq), leq));

        //assert((left+right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset());
    }
    else if leq(left.first(), right.first()){
        let result = Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right, leq);
        lemma_merge_sorted_with_ensures(left.drop_first(), right, leq);
        //assert(Seq::<A>::empty().push(left.first()) + left.drop_first() =~= left);
        //assert(sorted_by(merge_sorted_with(left.drop_first(), right, leq), leq));
        let rest = merge_sorted_with(left.drop_first(), right, leq);

        assert(rest.len() == 0 || rest.first() == left.drop_first().first() || rest.first() == right.first()) by {
            //assert(right.len() > 0);
            if left.drop_first().len() == 0 {/*assert(rest =~= right);*/}
            else if leq(left.drop_first().first(), right.first()) {
                assert(rest =~= Seq::<A>::empty().push(left.drop_first().first()) + merge_sorted_with(left.drop_first().drop_first(), right, leq));
                //assert(rest.first() == left.drop_first().first());
            }
            else {
                assert(rest =~= Seq::<A>::empty().push(right.first()) + merge_sorted_with(left.drop_first(), right.drop_first(), leq));
                //assert(rest.first() == right.first());
            }
        }
        if left.len() >1 {
           // assert(left.drop_first().first() == left[1]);
           // assert(leq(left.first(), left.drop_first().first()));
            //assert(rest.len() == 0 || leq(left.first(), rest.first()));
        }
        else {
            //assert(left.len() == 1);
            //assert(rest =~= right);
            //assert(leq(left.first(), rest.first()));
        }
        
        lemma_new_first_element_still_sorted_by(left.first(), rest, leq);

       // assert(sorted_by(merge_sorted_with(left, right, leq), leq));

        //assert((left.drop_first()+right).to_multiset() =~= merge_sorted_with(left.drop_first(), right, leq).to_multiset());
        assert((left.drop_first() + right) =~= (left + right).drop_first());
        // assert(merge_sorted_with(left.drop_first(), right, leq).to_multiset().insert(left.first())
        //         =~= merge_sorted_with(left, right, leq).to_multiset());
       // assert((left.drop_first() + right).to_multiset() =~= (left+right).to_multiset().remove(left.first()));
       // assert((left+right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset());


    } else {
        let result = Seq::<A>::empty().push(right.first()) + merge_sorted_with(left, right.drop_first(), leq);
        lemma_merge_sorted_with_ensures(left, right.drop_first(), leq);
        //assert(Seq::<A>::empty().push(right.first()) + right.drop_first() =~= right);

        let rest = merge_sorted_with(left, right.drop_first(), leq);

        assert(rest.len() == 0 || rest.first() == left.first() || rest.first() == right.drop_first().first()) by {
            assert(left.len() > 0);
            if right.drop_first().len() == 0 {/*assert(rest =~= left);*/}
            else if leq(left.first(), right.drop_first().first()) { //right might be length 1
                assert(rest =~= Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right.drop_first(), leq));
                // assert(rest.first() == left.first());
            }
            else {
                assert(rest =~= Seq::<A>::empty().push(right.drop_first().first()) + merge_sorted_with(left, right.drop_first().drop_first(), leq));
                // assert(rest.first() == right.drop_first().first());
            }
        }
       
        lemma_new_first_element_still_sorted_by(right.first(), merge_sorted_with(left, right.drop_first(), leq), leq);
        // assert(sorted_by(merge_sorted_with(left, right, leq), leq));



        // assert((left+right.drop_first()).to_multiset() =~= merge_sorted_with(left, right.drop_first(), leq).to_multiset());
        lemma_seq_union_to_multiset_commutative(left,right);
        // assert((left+right).to_multiset() =~= (right+left).to_multiset());
        assert((right.drop_first() + left) =~= (right + left).drop_first());
        // assert((right.drop_first() + left) =~= (right + left).drop_first());
        // assert(merge_sorted_with(left, right.drop_first(), leq).to_multiset().insert(right.first())
        //         =~= merge_sorted_with(left, right, leq).to_multiset());
        

        //assert((right.drop_first() + left).to_multiset() =~= (right+left).to_multiset().remove(right.first()));
        lemma_seq_union_to_multiset_commutative(right.drop_first(), left);
        //assert((right.drop_first() + left).to_multiset() =~= (left + right.drop_first()).to_multiset());
        //assert((left + right.drop_first()).to_multiset() =~= (left+right).to_multiset().remove(right.first())); //key
    
    
        //assert((right.drop_first() + left).to_multiset() =~= (right+left).to_multiset().remove(right.first()));

        //assert((left+right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset());


    }
}

fn main(){}

}