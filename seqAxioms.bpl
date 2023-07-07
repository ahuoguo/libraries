// Liz keywords: done, todo, and skipped

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

type Seq T;

function Seq#Length<T>(Seq T): int;
// LIZ: verus len returns nat, so this axiom is unnecessary
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>(): Seq T;
// LIZ: done
axiom (forall<T> :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);
// LIZ: done
axiom (forall<T> s: Seq T :: { Seq#Length(s) }
  (Seq#Length(s) == 0 ==> s == Seq#Empty())
// The following would be a nice fact to include, because it would enable verifying the
// GenericPick.SeqPick* methods in Test/dafny0/SmallTests.dfy.  However, it substantially
// slows down performance on some other tests, including running seemingly forever on
// some.
//  && (Seq#Length(s) != 0 ==> (exists x: T :: Seq#Contains(s, x)))
  );

// The empty sequence $Is any type
//axiom (forall<T> t: Ty :: {$Is(Seq#Empty(): Seq T, TSeq(t))} $Is(Seq#Empty(): Seq T, TSeq(t)));

// LIZ: done
function Seq#Singleton<T>(T): Seq T;
// LIZ: done
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T): Seq T;
function Seq#Build_inv0<T>(s: Seq T) : Seq T;
function Seq#Build_inv1<T>(s: Seq T) : T;
// LIZ: TODO, don't understand what these do
axiom (forall<T> s: Seq T, val: T ::
  { Seq#Build(s, val) }
  Seq#Build_inv0(Seq#Build(s, val)) == s &&
  Seq#Build_inv1(Seq#Build(s, val)) == val);

// LIZ: done (axiom_seq_push_len)
axiom (forall<T> s: Seq T, v: T ::
  { Seq#Build(s,v) }
  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
//LIZ: done (axiom_seq_push_index_same and axiom_seq_push_index_different)
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

// LIZ: todo, don't understand this one
// Build preserves $Is
axiom (forall s: Seq Box, bx: Box, t: Ty :: { $Is(Seq#Build(s,bx),TSeq(t)) }
    $Is(s,TSeq(t)) && $IsBox(bx,t) ==> $Is(Seq#Build(s,bx),TSeq(t)));

// LIZ: SKIPPED HEAP THINGS
function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType): Seq Box;
axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType ::
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) }
  $IsGoodHeap(heap) && 0 <= len ==>
  Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) == len);
axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int ::
  { Seq#Index(Seq#Create(ty, heap, len, init), i) }
  $IsGoodHeap(heap) && 0 <= i && i < len ==>
  Seq#Index(Seq#Create(ty, heap, len, init), i) == Apply1(TInt, ty, heap, init, $Box(i)));

// LIZ: done (axiom_seq_add_len)
function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int): T;
// LIZ: done (axiom_seq_singleton_index)
axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
// LIZ: done (axiom_seq_add_index1 and axiom_seq_add_index2)
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T): Seq T;
// LIZ: done (axiom_seq_update_len)
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
// LIZ: done (axiom_seq_update_same, axiom_seq_update_different)
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

function Seq#Contains<T>(Seq T, T): bool;
// LIZ: done (axiom_seq_contains)
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) <==>
    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
// LIZ: done (axiom_seq_empty_contains_nothing)
axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

// LIZ: done (axiom_seq_concat_contains_all_elements)
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

// LIZ: done (axiom_seq_contains_after_push)
axiom (forall<T> s: Seq T, v: T, x: T ::  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
  { Seq#Contains(Seq#Build(s, v), x) }
    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

// LIZ: done (axiom_seq_take_contains)
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
// LIZ: done (axiom_seq_drop_contains)
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T): bool;
// LIZ: done (axiom_seq_ext_equal)
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
// LIZ: done (axiom_seq_ext_equal)
axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

// LIZ: todo, is this necessary?
function Seq#SameUntil<T>(Seq T, Seq T, int): bool;
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
            0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
// LIZ: done (axiom_seq_take_len)
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);
// LIZ: done (axiom_seq_take_index)
axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Take(s,n), j) }
  { Seq#Index(s, j), Seq#Take(s,n) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
// LIZ: done (axiom_seq_drop_len)
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);
// LIZ: todo, causes problems (axiom_seq_drop_index)
axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
// LIZ: done (axiom_seq_drop_index2)
axiom (forall<T> s: Seq T, n: int, k: int ::
  {:weight 25}
  { Seq#Index(s, k), Seq#Drop(s,n) }
  0 <= n && n <= k && k < Seq#Length(s) ==>
    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

// LIZ: done (axiom_seq_append_take_drop)
axiom (forall<T> s, t: Seq T, n: int ::
  { Seq#Take(Seq#Append(s, t), n) }
  { Seq#Drop(Seq#Append(s, t), n) }
  n == Seq#Length(s)
  ==>
  Seq#Take(Seq#Append(s, t), n) == s &&
  Seq#Drop(Seq#Append(s, t), n) == t);

// LIZ: skipped heap stuff
function Seq#FromArray(h: Heap, a: ref): Seq Box;
axiom (forall h: Heap, a: ref ::
  { Seq#Length(Seq#FromArray(h,a)) }
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));
axiom (forall h: Heap, a: ref ::
  { Seq#FromArray(h, a) }
  (forall i: int ::
    // it's important to include both triggers, so that assertions about the
    // the relation between the array and the sequence can be proved in either
    // direction
    { read(h, a, IndexField(i)) }
    { Seq#Index(Seq#FromArray(h, a): Seq Box, i) }
    0 <= i &&
    i < Seq#Length(Seq#FromArray(h, a))  // this will trigger the previous axiom to get a connection with _System.array.Length(a)
    ==>
    Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));
axiom (forall h0, h1: Heap, a: ref ::
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
  ==>
  Seq#FromArray(h0, a) == Seq#FromArray(h1, a));
axiom (forall h: Heap, i: int, v: Box, a: ref ::
  { Seq#FromArray(update(h, a, IndexField(i), v), a) }
    0 <= i && i < _System.array.Length(a) ==> Seq#FromArray(update(h, a, IndexField(i), v), a) == Seq#Update(Seq#FromArray(h, a), i, v) );

// Commutability of Take and Drop with Update.
// LIZ: done (axiom_seq_take_update_commut1)
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
// LIZ: done (axiom_seq_take_update_commut2)
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
// LIZ: done (axiom_seq_drop_update_commut1)
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
// LIZ: TODO: breaks pervasive/bytes (axiom_seq_drop_update_commut2)
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// LIZ: skipped, heap stuff
// Extension axiom, triggers only on Takes from arrays.
axiom (forall h: Heap, a: ref, n0, n1: int ::
        { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
        n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a) ==> Seq#Take(Seq#FromArray(h, a), n1) == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)) );
// LIZ: done (axiom_seq_drop_build_commut)
// drop commutes with build.
axiom (forall<T> s: Seq T, v: T, n: int ::
        { Seq#Drop(Seq#Build(s, v), n) }
        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );


function Seq#Rank<T>(Seq T): int;
// LIZ: todo, not sure what this means
axiom (forall s: Seq Box, i: int ::
        { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
        0 <= i && i < Seq#Length(s) ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s) );
// LIZ: TODO, can't figure out what rank function does
axiom (forall<T> s: Seq T, i: int ::
        { Seq#Rank(Seq#Drop(s, i)) }
        0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s) );
// LIZ: TODO, can't figure out what rank function does
axiom (forall<T> s: Seq T, i: int ::
        { Seq#Rank(Seq#Take(s, i)) }
        0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s) );
// LIZ: TODO, can't figure out what rank function does
axiom (forall<T> s: Seq T, i: int, j: int ::
        { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
        0 <= i && i < j && j <= Seq#Length(s) ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s) );

// Additional axioms about common things
// LIZ: done (axiom_seq_drop_nothing)
axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) }
        n == 0 ==> Seq#Drop(s, n) == s);
// LIZ: done (axiom_seq_take_nothing)
axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) }
        n == 0 ==> Seq#Take(s, n) == Seq#Empty());
// LIZ: done (axiom_seq_drop_of_drop)
axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));
