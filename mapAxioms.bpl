
// ---------------------------------------------------------------
// -- Axiomatization of Maps -------------------------------------
// ---------------------------------------------------------------

type Map U V;

// A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.

function Map#Domain<U,V>(Map U V) : Set U;

// [U]V is a map type
// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf
// kinda correponds to index in the verus map.rs (This is the curried version)
function Map#Elements<U,V>(Map U V) : [U]V;

// TODO
function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

// TODO
axiom (forall<U, V> m: Map U V ::
  { Map#Card(m) }
  Map#Card(m) == 0 <==> m == Map#Empty());

// THE axiom_map_exmpty is related but not representitive
axiom (forall<U, V> m: Map U V ::
  { Map#Domain(m) }
  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));
axiom (forall<U, V> m: Map U V ::
  { Map#Values(m) }
  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));
axiom (forall<U, V> m: Map U V ::
  { Map#Items(m) }
  m == Map#Empty() || (exists k, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Domain(m)) }
  Set#Card(Map#Domain(m)) == Map#Card(m));
axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Values(m)) }
  Set#Card(Map#Values(m)) <= Map#Card(m));
axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Items(m)) }
  Set#Card(Map#Items(m)) == Map#Card(m));

// The set of Values of a Map can be obtained by the function Map#Values, which is
// defined as follows.  Remember, a Set is defined by membership (using Boogie's
// square brackets) and Map#Card, so we need to define what these mean for the Set
// returned by Map#Values.

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
  Map#Values(m)[v] ==
	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
	  Map#Domain(m)[u] &&
    v == Map#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function Map#Items.  Again, we need to define membership of Set#Card for this
// set.  Everywhere else in this axiomatization, Map is parameterized by types U V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function Map#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of Map#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function Map#Items<U,V>(Map U V) : Set Box;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;
function _System.Tuple2._0(DatatypeType) : Box;
function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map Box Box, item: Box :: { Map#Items(m)[item] }
  Map#Items(m)[item] <==>
    Map#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    Map#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.

function Map#Empty<U, V>(): Map U V;
axiom (forall<U, V> u: U ::
        { Map#Domain(Map#Empty(): Map U V)[u] }
        !Map#Domain(Map#Empty(): Map U V)[u]);

function Map#Glue<U, V>([U]bool, [U]V, Ty): Map U V;
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { Map#Glue(a, b, TMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));


//Build is used in displays, and for map updates
function Map#Build<U, V>(Map U V, U, V): Map U V;
/*axiom (forall<U, V> m: Map U V, u: U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u] } { Map#Elements(Map#Build(m, u, v))[u] }
  Map#Domain(Map#Build(m, u, v))[u] && Map#Elements(Map#Build(m, u, v))[u] == v);*/

axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

// Map operations
function Map#Merge<U, V>(Map U V, Map U V): Map U V;
axiom (forall<U, V> m: Map U V, n: Map U V ::
  { Map#Domain(Map#Merge(m, n)) }
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));
axiom (forall<U, V> m: Map U V, n: Map U V, u: U ::
  { Map#Elements(Map#Merge(m, n))[u] }
  Map#Domain(Map#Merge(m, n))[u] ==>
    (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
    (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract<U, V>(Map U V, Set U): Map U V;
axiom (forall<U, V> m: Map U V, s: Set U ::
  { Map#Domain(Map#Subtract(m, s)) }
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));
axiom (forall<U, V> m: Map U V, s: Set U, u: U ::
  { Map#Elements(Map#Subtract(m, s))[u] }
  Map#Domain(Map#Subtract(m, s))[u] ==>
    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

//equality for maps
function Map#Equal<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));

// ---------------------------------------------------------------
// -- Axiomatization of IMaps ------------------------------------
// ---------------------------------------------------------------

type IMap U V;

// A IMap is defined by two functions, Map#Domain and Map#Elements.

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

axiom (forall<U, V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() || (exists k: U :: IMap#Domain(m)[k]));
axiom (forall<U, V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() || (exists v: V :: IMap#Values(m)[v]));
axiom (forall<U, V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() || (exists k, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U, V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());
axiom (forall<U, V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());
axiom (forall<U, V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

// The set of Values of a IMap can be obtained by the function IMap#Values, which is
// defined as follows.  Remember, a ISet is defined by membership (using Boogie's
// square brackets) so we need to define what these mean for the Set
// returned by Map#Values.

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V :: { IMap#Values(m)[v] }
  IMap#Values(m)[v] ==
	(exists u: U :: { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
	  IMap#Domain(m)[u] &&
    v == IMap#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function IMap#Items.
// Everywhere else in this axiomatization, IMap is parameterized by types U V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function IMap#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of IMap#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box :: { IMap#Items(m)[item] }
  IMap#Items(m)[item] <==>
    IMap#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    IMap#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.
function IMap#Empty<U, V>(): IMap U V;
axiom (forall<U, V> u: U ::
        { IMap#Domain(IMap#Empty(): IMap U V)[u] }
        !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U, V>([U] bool, [U]V, Ty): IMap U V;
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Domain(IMap#Glue(a, b, t)) }
  IMap#Domain(IMap#Glue(a, b, t)) == a);
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Elements(IMap#Glue(a, b, t)) }
  IMap#Elements(IMap#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { IMap#Glue(a, b, TIMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

//Build is used in displays
function IMap#Build<U, V>(IMap U V, U, V): IMap U V;
/*axiom (forall<U, V> m: IMap U V, u: U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u] } { IMap#Elements(IMap#Build(m, u, v))[u] }
  IMap#Domain(IMap#Build(m, u, v))[u] && IMap#Elements(IMap#Build(m, u, v))[u] == v);*/

axiom (forall<U, V> m: IMap U V, u: U, u': U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u'] } { IMap#Elements(IMap#Build(m, u, v))[u'] }
  (u' == u ==> IMap#Domain(IMap#Build(m, u, v))[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == v) &&
  (u' != u ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

//equality for imaps
function IMap#Equal<U, V>(IMap U V, IMap U V): bool;
axiom (forall<U, V> m: IMap U V, m': IMap U V::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') <==> (forall u : U :: IMap#Domain(m)[u] == IMap#Domain(m')[u]) &&
                          (forall u : U :: IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: IMap U V, m': IMap U V::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') ==> m == m');

// IMap operations
function IMap#Merge<U, V>(IMap U V, IMap U V): IMap U V;
axiom (forall<U, V> m: IMap U V, n: IMap U V ::
  { IMap#Domain(IMap#Merge(m, n)) }
  IMap#Domain(IMap#Merge(m, n)) == Set#Union(IMap#Domain(m), IMap#Domain(n)));
axiom (forall<U, V> m: IMap U V, n: IMap U V, u: U ::
  { IMap#Elements(IMap#Merge(m, n))[u] }
  IMap#Domain(IMap#Merge(m, n))[u] ==>
    (!IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u]) &&
    (IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract<U, V>(IMap U V, Set U): IMap U V;
axiom (forall<U, V> m: IMap U V, s: Set U ::
  { IMap#Domain(IMap#Subtract(m, s)) }
  IMap#Domain(IMap#Subtract(m, s)) == Set#Difference(IMap#Domain(m), s));
axiom (forall<U, V> m: IMap U V, s: Set U, u: U ::
  { IMap#Elements(IMap#Subtract(m, s))[u] }
  IMap#Domain(IMap#Subtract(m, s))[u] ==>
    IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);
