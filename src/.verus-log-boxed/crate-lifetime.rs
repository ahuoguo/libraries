#![feature(box_patterns)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unreachable_patterns)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unconditional_recursion)]
#![allow(unused_mut)]
#![allow(unused_labels)]
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;
fn op<A, B>(a: A) -> B { panic!() }
struct Tracked<A> { a: PhantomData<A> }
impl<A> Tracked<A> {
    pub fn get(self) -> A { panic!() }
    pub fn borrow(&self) -> &A { panic!() }
    pub fn borrow_mut(&mut self) -> &mut A { panic!() }
}
struct Ghost<A> { a: PhantomData<A> }
impl<A> Clone for Ghost<A> { fn clone(&self) -> Self { panic!() } }
impl<A> Copy for Ghost<A> { }
#[derive(Clone, Copy)] struct int;
#[derive(Clone, Copy)] struct nat;
struct FnSpec<Args, Output> { x: PhantomData<(Args, Output)> }
struct InvariantBlockGuard;
fn open_atomic_invariant_begin<'a, X, V>(_inv: &'a X) -> (&'a InvariantBlockGuard, V) { panic!(); }
fn open_local_invariant_begin<'a, X, V>(_inv: &'a X) -> (&'a InvariantBlockGuard, V) { panic!(); }
fn open_invariant_end<V>(_guard: &InvariantBlockGuard, _v: V) { panic!() }
fn index<'a, V, Idx, Output>(v: &'a V, index: Idx) -> &'a Output { panic!() }



fn f23_lemma_mul_distributes1(
)
{
}

fn f25_main(
)
{
}
