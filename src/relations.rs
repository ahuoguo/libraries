use vstd::prelude::*;

verus! {

    spec fn injective<X, Y>(r: FnSpec(X) -> Y) -> bool
    {
        forall|x1: X, x2: X| #[trigger] r(x1) == #[trigger] r(x2) ==> x1 == x2
    }

    spec fn commutative<T,U>(r: FnSpec(T,T) -> U) ->bool
    {
        forall|x: T, y: T| #[trigger] r(x,y)== #[trigger] r(y,x)
    }

    spec fn associative<T>(r: FnSpec(T,T) -> T) -> bool{
        forall|x: T, y: T, z: T| #[trigger] r(x,r(y,z)) ==  #[trigger] r(r(x,y),z)
    }

    spec fn reflexive<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall |x: T| #[trigger] r(x,x)
    }

    spec fn irreflexive<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall |x: T| #[trigger] r(x,x) == false
    }

    spec fn antisymmetric<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall|x: T, y: T| #[trigger] r(x,y) && #[trigger] r(y,x) ==> x == y
    }

    spec fn asymmetric<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall|x: T, y: T| #[trigger] r(x,y) ==> #[trigger] r(y,x) == false
    }

    spec fn symmetric<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall|x: T, y: T| #[trigger] r(x,y) <==> #[trigger] r(y,x)
    }

    spec fn connected<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall|x: T, y: T| x != y ==> #[trigger] r(x,y) || #[trigger] r(y,x)
    }

    spec fn strongly_connected<T>(r: FnSpec(T,T) -> bool) ->bool{
        forall|x: T, y: T| #[trigger] r(x,y) || #[trigger] r(y,x)
    }

    spec fn transitive<T>(r: FnSpec(T,T) -> bool) -> bool{
        forall|x: T, y: T, z: T| #[trigger] r(x,y) && #[trigger] r(y,z) ==>  #[trigger] r(x,z)
    }

    spec fn total_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
        &&& reflexive(r)
        &&& antisymmetric(r)
        &&& transitive(r)
        &&& strongly_connected(r)
    }

    spec fn strict_total_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
        &&& irreflexive(r)
        &&& antisymmetric(r)
        &&& transitive(r)
        &&& connected(r)
    }

    spec fn pre_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
        &&& reflexive(r)
        &&& transitive(r)
    }

    spec fn partial_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
        &&& reflexive(r)
        &&& transitive(r)
        &&& antisymmetric(r)
    }

    spec fn equivalence_relation<T>(r: FnSpec(T,T) ->bool) ->bool{
        &&& reflexive(r)
        &&& symmetric(r)
        &&& transitive(r)
    }

    /// This function returns true if the input sequence a is sorted, using the input function 
    /// less_than to sort the elements
    pub open spec fn sorted_by<T>(a: Seq<T>, less_than: FnSpec(T,T) -> bool) ->bool{
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] less_than(a[i], a[j])
    }

    /// An element in an ordered set is called a least element (or a minimum), if it is less than 
    /// every other element of the set.
    /// 
    /// change f to leq bc it is a relation. also these are an ordering relation
    spec fn is_least<T>(leq: FnSpec(T,T) ->bool, min: T, s: Set<T>) ->bool{
        s.contains(min) && forall|x: T| s.contains(x) ==> #[trigger] leq(min,x)
    }

    /// An element in an ordered set is called a minimal element, if no other element is less than it.
    spec fn is_minimal<T>(leq: FnSpec(T,T) ->bool, min: T, s: Set<T>) ->bool{
        s.contains(min) && forall|x: T| s.contains(x) && #[trigger] leq(x,min) ==> #[trigger] leq(min,x)
    }

    /// An element in an ordered set is called a greatest element (or a maximum), if it is greater than 
    ///every other element of the set.
    spec fn is_greatest<T>(leq: FnSpec(T,T) ->bool, max: T, s: Set<T>) ->bool{
        s.contains(max) && forall|x: T| s.contains(x) ==> #[trigger] leq(x,max)
    }

    /// An element in an ordered set is called a maximal element, if no other element is greater than it.
    spec fn is_maximal<T>(leq: FnSpec(T,T) ->bool, max: T, s: Set<T>) ->bool{
        s.contains(max) && forall|x: T| s.contains(x) && #[trigger] leq(max,x) ==> #[trigger] leq(x,max)
    }

    proof fn lemma_new_first_element_still_sorted_by<T>(x: T, s: Seq<T>, less_than: FnSpec(T, T) -> bool)
        requires 
            sorted_by(s, less_than), //says that s is sorted by the less than function
            s.len() == 0 || less_than(x, s[0]),
            total_ordering(less_than),
        ensures
            sorted_by(seq![x].add(s), less_than),
    {
        //s is empty case:
        assert(s.len() == 0 ==> sorted_by(seq![x].add(s), less_than));
        
        //s has one element case:
        if s.len() ==1
        {
            assert(sorted_by(seq![x].add(s), less_than));
        }
        //s not empty case:
        if s.len() > 1
        {
            //Basically saying that if s is sorted, then every element is smaller than the ones that follow.
            //So if x is smaller than the first element in s, it must be smaller than the rest of the elements in s.
            //Thus putting x at the beginning of the sequence keeps the sequence sorted
            assert(forall |index1: int, index2: int| 0<= index1 < index2 < s.len() ==> #[trigger] less_than(s[index1], s[index2]));
            assert(less_than(x, s[0]));
            assert(sorted_by(s, less_than));
            assert(forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] less_than(s[i], s[j]));
            assert(less_than(s[0], s[1]));
            assert(less_than(x,s[1]));
            assert(transitive(less_than));
            assert(forall |index1: int, index2: int| 0<= index1 < index2 < s.len() ==>
                (#[trigger] less_than(s[index1], s[index2]) && #[trigger] less_than(x, s[index1]) ==>
                    #[trigger] less_than(x, s[index2]))); //def of transitive
            //assert(forall |index: int| 0<= index< s.len() ==> #[trigger] less_than(x, s[index]));
        }
    }

    // proof fn helper<T>(x: T, s: Seq<T>, length: int, less_than: FnSpec(T, T) -> bool)
    //     requires 
    //         sorted_by(s, less_than),
    //         s.len() == 0 || less_than(x, s[0]),
    //         total_ordering(less_than),
    //     ensures
    //         sorted_by(seq![x].add(s), less_than),
    //     decreases length
    // {
    //     assert(s.len() == 0 ==> sorted_by(seq![x].add(s), less_than));
        
    //     //s not empty case:
    //     if s.len() > 1
    //     {
    //         assert(forall |index1: int, index2: int| 0<= index1 < index2 < s.len() ==> #[trigger] less_than(s[index1], s[index2]));
    //         assert(less_than(x, s[0]));
    //         assert(less_than(s[0], s[1]));
    //         assert(less_than(x,s[1]));
    //         assert(transitive(less_than));
    //         assert(forall |index1: int, index2: int| 0<= index1 < index2 < s.len() ==>
    //             (#[trigger] less_than(s[index1], s[index2]) && #[trigger] less_than(x, s[index1]) ==>
    //                 #[trigger] less_than(x, s[index2]))); //def of transitive
    //         //assert(forall |index: int| 0<= index< s.len() ==> #[trigger] less_than(x, s[index]));
    //         helper(x, s.subrange(1, s.len() as int),length-1, less_than);
    //     }
    // }

    fn main(){
        assert(sorted_by(seq![10u32, 20, 30], |x: u32, y: u32| less_than(x,y)));
    }

    spec fn less_than(a: u32, b:u32) ->bool{
        a < b
    }
}