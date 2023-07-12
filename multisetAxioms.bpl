// ---------------------------------------------------------------
// -- Axiomatization of multisets --------------------------------
// ---------------------------------------------------------------

function Math#min(a: int, b: int): int;
axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

// LIZ: done (.is_valid())
function $IsGoodMultiSet<T>(ms: MultiSet T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
// LIZ: done (axiom_is_valid) (PROBLEMATIC)
axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
  $IsGoodMultiSet(ms) <==>
  (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

//LIZ: done (.len())
function MultiSet#Card<T>(MultiSet T): int;
// LIZ: done (len returns nat)
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
// LIZ: TODO: i don't understand this one? Specifically `x := n` syntax
// I think it's saying that if you assign x to multiplicity n in multiset s,
// the cardinality of this new s is the same as the cardinality of the old s minus the cardinality
// of x in the old s plus the value of n
axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>(): MultiSet T;
// LIZ: done (axiom_multiset_empty)
axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
// LIZ: done (axiom_multiset_empty_len)
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T): MultiSet T;
// LIZ: done (axiom_multiset_singleton and axiom_multiset_singleton_different)
axiom (forall<T> r: T, o: T :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
                                                            (MultiSet#Singleton(r)[o] == 0 <==> r != o));
// LIZ: done (axiom_multiset_singleton_equivalency) (PROBLEMATIC)
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

// LIZ: same as insert
function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
// pure containment axiom (in the original multiset or is the added element)
// LIZ: done (axiom_insert_count)
axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#UnionOne(a,x)[o] }
  0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
// union-ing increases count by one
// LIZ: done (axiom_insert_increases_count_by_1)
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a, x) }
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);
// non-decreasing
// LIZ: done (axiom_insert_non_decreasing)
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
// other elements unchanged
// LIZ: done (axiom_insert_other_elements_unchanged)
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
// LIZ: done (axiom_insert_len)
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);


function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
// union-ing is the sum of the contents
// LIZ: already done (axiom_multiset_add)
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Union(a,b)[o] }
  MultiSet#Union(a,b)[o] == a[o] + b[o]);
// LIZ: already done (axiom_len_add)
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) }
  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));

// LIZ: done (fn intersection_with)
function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
// LIZ: done (axiom_intersection_count)
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Intersection(a,b)[o] }
  MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));

// left and right pseudo-idempotence
// LIZ: done (axiom_left_pseudo_idempotence)
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
// LIZ: done (axiom_right_pseudo_idempotence)
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));

// multiset difference, a - b. clip() makes it positive.
// LIZ: done (fn difference_with)
function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
// LIZ: done (axiom_difference_count)
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Difference(a,b)[o] }
  MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
// LIZ: done (axiom_difference_bottoms_out)
axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
// LIZ: TODO: is this necessary?
axiom (forall<T> a, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
    == MultiSet#Card(MultiSet#Union(a, b)) &&
  MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

// multiset subset means a must have at most as many of each element as b
// LIZ: done (fn subset_of)
function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
// LIZ: done (axiom_subset_of_specs)
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
  MultiSet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));

//LIZ: already done (=~=)
function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
// LIZ: already done (axiom_multiset_ext_equal)
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
// extensionality axiom for multisets
// LIZ: already done (axiom_multiset_ext_equal)
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) ==> a == b);

// LIZ: done (fn disjoint_with)
function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
// unsat core for LemmaNoDuplicatesInConcat
// LIZ: done (axiom_disjointness) PROBLEMATIC
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
  MultiSet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));

// conversion to a multiset. each element in the original set has duplicity 1.
// LIZ: done (in set_lib)
function MultiSet#FromSet<T>(Set T): MultiSet T;
// LIZ: 
axiom (forall<T> s: Set T, a: T :: { MultiSet#FromSet(s)[a] }
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
  (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
axiom (forall<T> s: Set T :: { MultiSet#Card(MultiSet#FromSet(s)) }
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

// conversion to a multiset, from a sequence.
// TODO
function MultiSet#FromSeq<T>(Seq T): MultiSet T uses {
  axiom (forall<T> :: MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);
}
// conversion produces a good map.
axiom (forall<T> s: Seq T :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
// cardinality axiom
axiom (forall<T> s: Seq T ::
  { MultiSet#Card(MultiSet#FromSeq(s)) }
    MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));
// building axiom
axiom (forall<T> s: Seq T, v: T ::
  { MultiSet#FromSeq(Seq#Build(s, v)) }
    MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
  );

// concatenation axiom
axiom (forall<T> a: Seq T, b: Seq T ::
  { MultiSet#FromSeq(Seq#Append(a, b)) }
    MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );

// update axiom
axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
    0 <= i && i < Seq#Length(s) ==>
    MultiSet#FromSeq(Seq#Update(s, i, v))[x] ==
      MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s,i))), MultiSet#Singleton(v))[x] );
  // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
axiom (forall<T> s: Seq T, x: T :: { MultiSet#FromSeq(s)[x] }
  (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );
