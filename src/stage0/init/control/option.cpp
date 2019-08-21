// Lean compiler output
// Module: init.control.option
// Imports: init.control.alternative init.control.lift init.control.except
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_OptionT_MonadRun___boxed(obj*, obj*);
obj* l_OptionT_pure(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_orelse___rarg(obj*, obj*, obj*, obj*);
obj* l_OptionT_fail(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__2(obj*);
obj* l_OptionT_Monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_monadMap___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_Monad___rarg(obj*);
obj* l_OptionT_pure___boxed(obj*);
obj* l_OptionT_Monad___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_OptionT_MonadExcept___boxed(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__5(obj*);
obj* l_OptionT_catch___rarg(obj*, obj*, obj*, obj*);
obj* l_OptionT_pure___rarg(obj*, obj*, obj*);
obj* l_OptionT_MonadExcept___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_OptionT_run___rarg___boxed(obj*);
obj* l_OptionT_MonadRun___rarg(obj*, obj*, obj*);
obj* l_OptionT_HasMonadLift(obj*);
obj* l_OptionT_lift(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_MonadFunctor(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__6(obj*);
obj* l_OptionT_bindCont(obj*);
obj* l_OptionT_catch___boxed(obj*);
obj* l_OptionT_HasMonadLift___rarg(obj*);
obj* l_OptionT_run___boxed(obj*, obj*);
obj* l_OptionT_monadMap___rarg(obj*, obj*);
obj* l_OptionT_Alternative(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__7___boxed(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__2___boxed(obj*);
obj* l_OptionT_orelse___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_OptionT_lift___boxed(obj*);
obj* l_OptionT_fail___boxed(obj*);
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_OptionT_MonadExcept___rarg(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__6___boxed(obj*);
obj* l_OptionT_Monad___rarg___lambda__5___boxed(obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_MonadExcept___rarg___lambda__1(obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__1___boxed(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__4(obj*);
obj* l_Function_const___rarg___boxed(obj*, obj*);
obj* l_OptionT_Monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_MonadRun(obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__7(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__3(obj*);
obj* l_OptionT_run___rarg(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__5___boxed(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_orelse___boxed(obj*);
obj* l_OptionT_HasMonadLift___boxed(obj*);
obj* l_OptionT_lift___rarg(obj*, obj*, obj*);
obj* l_OptionT_fail___rarg(obj*, obj*);
obj* l_OptionT_run(obj*, obj*);
extern obj* l_optional___rarg___closed__1;
obj* l_OptionT_catch___rarg___lambda__1(obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__3___boxed(obj*);
obj* l_OptionT_monadMap(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_Alternative___boxed(obj*);
obj* l_OptionT_Alternative___rarg(obj*);
obj* l_OptionT_Monad___boxed(obj*);
obj* l_OptionT_orelse___rarg___lambda__1(obj*, obj*, obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__1(obj*);
obj* l_OptionT_Monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_bind___boxed(obj*);
obj* l_OptionT_Monad___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_Monad___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_Monad___rarg___lambda__6(obj*, obj*, obj*);
obj* l_OptionT_bind___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_MonadExcept(obj*);
obj* l_OptionT_Monad(obj*);
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__4___boxed(obj*);
obj* l_OptionT_Monad___rarg___lambda__5(obj*, obj*, obj*);
obj* l_OptionT_catch(obj*);
obj* l_OptionT_bind(obj*);
obj* l_OptionT_bindCont___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_MonadFunctor___rarg(obj*, obj*);
obj* l_OptionT_orelse(obj*);
obj* l_OptionT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_OptionT_bindCont___boxed(obj*);
obj* l_OptionT_run___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_OptionT_run(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_run___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_OptionT_run___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_run___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_run___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_OptionT_run(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_OptionT_bindCont___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bind___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___rarg), 5, 4);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_5);
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_4, x_7);
return x_8;
}
}
obj* l_OptionT_bind(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bind___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bind___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bind(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_pure___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_OptionT_pure(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_pure___rarg), 3, 0);
return x_2;
}
}
obj* l_OptionT_pure___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_pure(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__2___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__3___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__4___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__5___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__6___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__6(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__6___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__7___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__7(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__7___rarg), 5, 0);
return x_2;
}
}
obj* l_OptionT_Monad___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_pure___rarg), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, lean::box(0));
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_7, 0, x_6);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__1___rarg), 5, 4);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_7);
x_10 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_5, x_9);
return x_10;
}
}
obj* l_OptionT_Monad___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_const___rarg___boxed), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_pure___rarg), 3, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, lean::box(0));
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_8, 0, x_7);
lean::closure_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__2___rarg), 5, 4);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, lean::box(0));
lean::closure_set(x_10, 2, lean::box(0));
lean::closure_set(x_10, 3, x_8);
x_11 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_5, x_10);
return x_11;
}
}
obj* l_OptionT_Monad___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_pure___rarg), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__3___rarg), 5, 4);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_5);
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_2, x_7);
return x_8;
}
}
obj* l_OptionT_Monad___rarg___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__4___rarg), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_6);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_8);
return x_9;
}
}
obj* l_OptionT_Monad___rarg___lambda__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_OptionT_Monad___rarg___lambda__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__5___boxed), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__5___rarg), 5, 4);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_4);
x_7 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_OptionT_Monad___rarg___lambda__7(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__6), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__6___rarg), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_6);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_8);
return x_9;
}
}
obj* l_OptionT_Monad___rarg___lambda__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bindCont___at_OptionT_Monad___spec__7___rarg), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_6);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_8);
return x_9;
}
}
obj* l_OptionT_Monad___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__1), 5, 1);
lean::closure_set(x_2, 0, x_1);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__2), 5, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_pure___rarg), 3, 1);
lean::closure_set(x_5, 0, x_1);
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__4), 5, 1);
lean::closure_set(x_6, 0, x_1);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__7), 5, 1);
lean::closure_set(x_7, 0, x_1);
lean::inc(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg___lambda__8), 5, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_bind___rarg), 5, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_OptionT_Monad(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Monad___rarg), 1, 0);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__3___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__3(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__4(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__5___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__5(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__6___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__6(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_bindCont___at_OptionT_Monad___spec__7___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_bindCont___at_OptionT_Monad___spec__7(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_Monad___rarg___lambda__5___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_OptionT_Monad___rarg___lambda__5(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_OptionT_Monad___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_Monad(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_orelse___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::apply_2(x_5, lean::box(0), x_3);
return x_6;
}
}
}
obj* l_OptionT_orelse___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_orelse___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_OptionT_orelse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_orelse___rarg), 4, 0);
return x_2;
}
}
obj* l_OptionT_orelse___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_OptionT_orelse___rarg___lambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_OptionT_orelse___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_orelse(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_fail___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::box(0);
x_6 = lean::apply_2(x_4, lean::box(0), x_5);
return x_6;
}
}
obj* l_OptionT_fail(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_fail___rarg), 2, 0);
return x_2;
}
}
obj* l_OptionT_fail___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_fail(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_Alternative___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_1);
x_2 = l_OptionT_Monad___rarg(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_fail___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_orelse___rarg), 4, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 2, x_5);
return x_6;
}
}
obj* l_OptionT_Alternative(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_Alternative___rarg), 1, 0);
return x_2;
}
}
obj* l_OptionT_Alternative___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_Alternative(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_lift___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = l_optional___rarg___closed__1;
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_7, x_3);
return x_8;
}
}
obj* l_OptionT_lift(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_lift___rarg), 3, 0);
return x_2;
}
}
obj* l_OptionT_lift___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_lift(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_HasMonadLift___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_lift___rarg), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_OptionT_HasMonadLift(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_HasMonadLift___rarg), 1, 0);
return x_2;
}
}
obj* l_OptionT_HasMonadLift___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_HasMonadLift(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_monadMap___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_OptionT_monadMap(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_monadMap___rarg), 2, 0);
return x_6;
}
}
obj* l_OptionT_monadMap___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_OptionT_monadMap(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_OptionT_MonadFunctor___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_OptionT_MonadFunctor(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_MonadFunctor___rarg), 2, 0);
return x_6;
}
}
obj* l_OptionT_MonadFunctor___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_OptionT_MonadFunctor(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_OptionT_catch___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
x_4 = lean::box(0);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
else
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
}
}
obj* l_OptionT_catch___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_catch___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_OptionT_catch(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_catch___rarg), 4, 0);
return x_2;
}
}
obj* l_OptionT_catch___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_catch(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_MonadExcept___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_OptionT_MonadExcept___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_MonadExcept___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_catch___rarg), 4, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_OptionT_MonadExcept(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_MonadExcept___rarg), 1, 0);
return x_2;
}
}
obj* l_OptionT_MonadExcept___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_OptionT_MonadExcept___rarg___lambda__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_OptionT_MonadExcept___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_OptionT_MonadExcept(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_OptionT_MonadRun___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_2(x_1, lean::box(0), x_3);
return x_4;
}
}
obj* l_OptionT_MonadRun(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_OptionT_MonadRun___rarg), 3, 0);
return x_3;
}
}
obj* l_OptionT_MonadRun___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_OptionT_MonadRun(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_control_lift(obj*);
obj* initialize_init_control_except(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_option(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_except(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
