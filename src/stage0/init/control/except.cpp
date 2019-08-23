// Lean compiler output
// Module: init.control.except
// Imports: init.control.alternative init.control.lift init.data.tostring init.control.monadfail
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
extern "C" {
obj* l_Except_MonadExcept___closed__2;
obj* l_ExceptT_HasMonadLift___boxed(obj*, obj*);
obj* l_ExceptT_lift___rarg___closed__1;
obj* l_Except_repr___rarg(obj*, obj*, obj*);
obj* l_ExceptT_MonadExceptAdapter___rarg(obj*, obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept(obj*, obj*);
obj* l_Except_toOption___rarg___boxed(obj*);
obj* l_ExceptT_pure___boxed(obj*, obj*);
obj* l_Except_Monad___closed__9;
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_toOption(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___boxed(obj*, obj*);
obj* l_ExceptT_MonadFail(obj*);
obj* l_Except_return(obj*, obj*);
obj* l_MonadExcept_liftExcept___boxed(obj*, obj*, obj*);
obj* l_ExceptT_run___boxed(obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(obj*, obj*);
obj* l_Except_repr(obj*, obj*);
obj* l_ExceptT_mk___rarg(obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_mapError(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__5(obj*, obj*, obj*);
obj* l_Except_Monad___closed__6;
obj* l_Except_toOption___rarg(obj*);
obj* l_ExceptT_MonadExcept(obj*, obj*);
obj* l_ExceptT_adapt(obj*, obj*);
obj* l_MonadExcept_orelse_x27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__6(obj*, obj*, obj*);
obj* l_ExceptT_HasMonadLift(obj*, obj*);
obj* l_ExceptT_run___rarg___boxed(obj*);
obj* l_ExceptT_catch___boxed(obj*, obj*);
obj* l_Except_HasToString(obj*, obj*);
obj* l_MonadExcept_orelse_x27___boxed(obj*, obj*);
obj* l_ExceptT_bind___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_mk___rarg___boxed(obj*);
obj* l_Except_MonadExcept(obj*);
obj* l_MonadExcept_liftExcept(obj*, obj*, obj*);
obj* l_Except_Monad___closed__10;
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_ExceptT_catch(obj*, obj*);
obj* l_Except_toBool___rarg___boxed(obj*);
obj* l_Except_map(obj*, obj*, obj*);
obj* l_ExceptT_mk___boxed(obj*, obj*, obj*);
obj* l_MonadExcept_orelse___rarg(obj*, obj*, obj*, obj*);
obj* l_Except_Monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_ExceptT_MonadExcept___rarg(obj*);
obj* l_MonadExcept_orelse_x27___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_ExceptT_adapt___boxed(obj*, obj*);
obj* l_Except_Monad___closed__7;
obj* l_ExceptT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Except_MonadExcept___lambda__1(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(obj*, obj*);
obj* l_Except_bind___rarg(obj*, obj*);
obj* l_ExceptT_MonadExcept___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Except_Monad___closed__4;
obj* l_ExceptT_Monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_toString___rarg(obj*, obj*, obj*);
obj* l_Except_toString___rarg___closed__2;
obj* l_Except_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept___boxed(obj*, obj*);
obj* l_ExceptT_bindCont(obj*, obj*);
obj* l_ExceptT_catch___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Except_map___rarg(obj*, obj*);
obj* lean_string_append(obj*, obj*);
obj* l_Except_HasRepr(obj*, obj*);
obj* l_monadExceptAdapterTrans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Except_bind(obj*, obj*, obj*);
obj* l_ExceptT_pure___rarg(obj*, obj*, obj*);
uint8 l_Except_toBool___rarg(obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___boxed(obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l_ExceptT_MonadExceptAdapter(obj*, obj*, obj*);
obj* l_Except_return___rarg(obj*);
obj* l_ExceptT_pure(obj*, obj*);
obj* l_Except_HasToString___rarg(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___boxed(obj*, obj*);
obj* l_Except_toBool(obj*, obj*);
obj* l_ExceptT_map(obj*, obj*);
obj* l_ExceptT_HasMonadLift___rarg(obj*);
obj* l_ExceptT_Monad___rarg___lambda__5___boxed(obj*, obj*, obj*);
obj* l_ExceptT_MonadFunctor___rarg(obj*, obj*);
obj* l_ExceptT_mk(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__9(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_run___rarg(obj*);
obj* l_ExceptT_map___rarg___lambda__1(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_ExceptT_MonadExcept___boxed(obj*, obj*);
obj* l_ExceptT_map___boxed(obj*, obj*);
obj* l_MonadExcept_orelse_x27___rarg___lambda__1(obj*, uint8, obj*, obj*);
obj* l_MonadExcept_orelse_x27(obj*, obj*);
obj* l_ExceptT_MonadFunctor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept___rarg(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__8(obj*, obj*);
obj* l_MonadExcept_orelse_x27___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_adapt___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_catch___rarg(obj*, obj*);
obj* l_Except_Inhabited___rarg(obj*);
obj* l_Except_Monad___closed__3;
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(obj*, obj*);
obj* l_Except_Inhabited(obj*, obj*);
obj* l_ExceptT_MonadRun(obj*, obj*, obj*);
obj* l_ExceptT_MonadRun___boxed(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(obj*, obj*);
obj* l_ExceptT_MonadFail___boxed(obj*);
obj* l_monadExceptAdapterTrans___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___boxed(obj*, obj*);
obj* l_ExceptT_lift___rarg(obj*, obj*, obj*);
obj* l_ExceptT_lift(obj*, obj*);
obj* l_Except_Monad___closed__5;
obj* l_ExceptT_bind(obj*, obj*);
obj* l_Except_MonadExcept___closed__3;
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Monad(obj*);
obj* l_ExceptT_MonadRun___rarg(obj*, obj*, obj*);
obj* l_ExceptT_bindCont___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_catch___rarg(obj*, obj*, obj*, obj*);
obj* l_MonadExcept_orelse___boxed(obj*, obj*);
obj* l_MonadExcept_orelse_x27___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*);
obj* l_ExceptT_MonadFail___rarg(obj*, obj*, obj*);
obj* l_ExceptT_lift___boxed(obj*, obj*);
obj* l_Except_toString(obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__1(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg(obj*);
obj* l_MonadExcept_orelse_x27___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_Monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Except_catch(obj*, obj*);
obj* l_MonadExcept_orelse(obj*, obj*);
obj* l_Except_Monad___closed__8;
obj* l_Except_Monad___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_HasRepr___rarg(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___boxed(obj*, obj*);
obj* l_ExceptT_Monad(obj*, obj*);
obj* l_Except_Monad___closed__1;
obj* l_monadExceptAdapterTrans___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_Except_Monad___closed__2;
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_map___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_Monad___boxed(obj*, obj*);
obj* l_Except_MonadExcept___closed__1;
obj* l_Except_mapError___rarg(obj*, obj*);
obj* l_ExceptT_MonadExceptAdapter___boxed(obj*, obj*, obj*);
obj* l_Except_toString___rarg___closed__1;
obj* l_monadFunctorTTrans___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_ExceptT_run(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_ExceptT_bind___boxed(obj*, obj*);
obj* l_MonadExcept_liftExcept___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Except_Inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Inhabited___rarg), 1, 0);
return x_3;
}
}
obj* _init_l_Except_toString___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("(error ");
return x_1;
}
}
obj* _init_l_Except_toString___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("(ok ");
return x_1;
}
}
obj* l_Except_toString___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Except_toString___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::apply_1(x_2, x_10);
x_12 = l_Except_toString___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean::dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
obj* l_Except_toString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toString___rarg), 3, 0);
return x_3;
}
}
obj* l_Except_repr___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Except_toString___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean::dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::apply_1(x_2, x_10);
x_12 = l_Except_toString___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean::dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
obj* l_Except_repr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_repr___rarg), 3, 0);
return x_3;
}
}
obj* l_Except_HasToString___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toString___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Except_HasToString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_HasToString___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_HasRepr___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_repr___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Except_HasRepr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_HasRepr___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_return___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Except_return(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_return___rarg), 1, 0);
return x_3;
}
}
obj* l_Except_map___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::apply_1(x_1, x_7);
lean::cnstr_set(x_2, 0, x_8);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::apply_1(x_1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
}
obj* l_Except_map(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_map___rarg), 2, 0);
return x_4;
}
}
obj* l_Except_mapError___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::apply_1(x_1, x_4);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::apply_1(x_1, x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8 x_9; 
lean::dec(x_1);
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
return x_2;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
}
obj* l_Except_mapError(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___rarg), 2, 0);
return x_4;
}
}
obj* l_Except_bind___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_2);
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::apply_1(x_2, x_6);
return x_7;
}
}
}
obj* l_Except_bind(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_bind___rarg), 2, 0);
return x_4;
}
}
uint8 l_Except_toBool___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Except_toBool(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toBool___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_Except_toBool___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Except_toBool___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Except_toOption___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
}
obj* l_Except_toOption(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toOption___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_Except_toOption___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toOption___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_catch___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Except_catch(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_catch___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_Monad___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
lean::dec(x_3);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_4, 0);
lean::dec(x_9);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
else
{
obj* x_10; 
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_3);
return x_10;
}
}
}
}
obj* l_Except_Monad___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; 
lean::dec(x_4);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_12 = !lean::is_exclusive(x_4);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_4, 0);
x_14 = lean::apply_1(x_11, x_13);
lean::cnstr_set(x_4, 0, x_14);
return x_4;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::apply_1(x_11, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
obj* l_Except_Monad___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; 
lean::dec(x_4);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_4);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_4, 0);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
lean::dec(x_3);
lean::cnstr_set(x_4, 0, x_13);
return x_4;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_4);
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
lean::dec(x_3);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
obj* l_Except_Monad___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean::dec(x_3);
lean::inc(x_4);
return x_4;
}
}
}
obj* _init_l_Except_Monad___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_map), 3, 1);
lean::closure_set(x_1, 0, lean::box(0));
return x_1;
}
}
obj* _init_l_Except_Monad___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__1), 4, 0);
return x_1;
}
}
obj* _init_l_Except_Monad___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Except_Monad___closed__1;
x_2 = l_Except_Monad___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Except_Monad___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_return), 2, 1);
lean::closure_set(x_1, 0, lean::box(0));
return x_1;
}
}
obj* _init_l_Except_Monad___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__2), 4, 0);
return x_1;
}
}
obj* _init_l_Except_Monad___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__3), 4, 0);
return x_1;
}
}
obj* _init_l_Except_Monad___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__4___boxed), 4, 0);
return x_1;
}
}
obj* _init_l_Except_Monad___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Except_Monad___closed__3;
x_2 = l_Except_Monad___closed__4;
x_3 = l_Except_Monad___closed__5;
x_4 = l_Except_Monad___closed__6;
x_5 = l_Except_Monad___closed__7;
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
lean::cnstr_set(x_6, 4, x_5);
return x_6;
}
}
obj* _init_l_Except_Monad___closed__9() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_bind), 3, 1);
lean::closure_set(x_1, 0, lean::box(0));
return x_1;
}
}
obj* _init_l_Except_Monad___closed__10() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Except_Monad___closed__8;
x_2 = l_Except_Monad___closed__9;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Except_Monad(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_Monad___closed__10;
return x_2;
}
}
obj* l_Except_Monad___lambda__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Except_Monad___lambda__4(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_ExceptT_mk___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_ExceptT_mk(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_mk___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_ExceptT_mk___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_mk___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_mk___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_mk(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_ExceptT_run___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_ExceptT_run(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_run___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_ExceptT_run___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_run___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_run___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_run(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_ExceptT_pure___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_ExceptT_pure(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_pure___rarg), 3, 0);
return x_3;
}
}
obj* l_ExceptT_pure___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_pure(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_bindCont___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_16 = lean::apply_1(x_4, x_15);
return x_16;
}
}
}
obj* l_ExceptT_bindCont(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_bindCont___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_bindCont(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_bind___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___rarg), 5, 4);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_5);
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_4, x_7);
return x_8;
}
}
obj* l_ExceptT_bind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bind___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_bind___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_bind(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_map___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
lean::dec(x_2);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_3, 0);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::apply_1(x_2, x_14);
lean::cnstr_set(x_3, 0, x_17);
x_18 = lean::apply_2(x_16, lean::box(0), x_3);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_22 = lean::apply_1(x_2, x_19);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::apply_2(x_21, lean::box(0), x_23);
return x_24;
}
}
}
}
obj* l_ExceptT_map___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_5, x_7);
return x_8;
}
}
obj* l_ExceptT_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_map___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_map(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_lift___rarg___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_ExceptT_lift___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
return x_1;
}
}
obj* l_ExceptT_lift___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_7 = l_ExceptT_lift___rarg___closed__1;
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_7, x_3);
return x_8;
}
}
obj* l_ExceptT_lift(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg), 3, 0);
return x_3;
}
}
obj* l_ExceptT_lift___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_lift(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_exceptTOfExcept___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::apply_2(x_5, lean::box(0), x_3);
return x_6;
}
}
obj* l_ExceptT_exceptTOfExcept(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_exceptTOfExcept___rarg), 3, 0);
return x_3;
}
}
obj* l_ExceptT_exceptTOfExcept___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_exceptTOfExcept(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_HasMonadLift___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_ExceptT_HasMonadLift(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_HasMonadLift___rarg), 1, 0);
return x_3;
}
}
obj* l_ExceptT_HasMonadLift___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_HasMonadLift(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_catch___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::apply_2(x_7, lean::box(0), x_3);
return x_8;
}
}
}
obj* l_ExceptT_catch___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_catch___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_ExceptT_catch(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_catch___rarg), 4, 0);
return x_3;
}
}
obj* l_ExceptT_catch___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_catch(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_MonadFunctor___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_ExceptT_MonadFunctor(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadFunctor___rarg), 2, 0);
return x_7;
}
}
obj* l_ExceptT_MonadFunctor___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_ExceptT_MonadFunctor(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_16 = lean::apply_1(x_4, x_15);
return x_16;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_16 = lean::apply_1(x_4, x_15);
return x_16;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_16 = lean::apply_1(x_4, x_15);
return x_16;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_16 = lean::apply_1(x_4, x_15);
return x_16;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_Monad___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
lean::dec(x_2);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_3, 0);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
lean::cnstr_set(x_3, 0, x_2);
x_17 = lean::apply_2(x_16, lean::box(0), x_3);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_2);
x_21 = lean::apply_2(x_19, lean::box(0), x_20);
return x_21;
}
}
}
}
obj* l_ExceptT_Monad___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_5, x_7);
return x_8;
}
}
obj* l_ExceptT_Monad___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_5);
return x_6;
}
}
obj* l_ExceptT_Monad___rarg___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_6);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_8);
return x_9;
}
}
obj* l_ExceptT_Monad___rarg___lambda__5(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_ExceptT_Monad___rarg___lambda__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__5___boxed), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg), 5, 4);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_4);
x_7 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_ExceptT_Monad___rarg___lambda__7(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__6), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_6);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_8);
return x_9;
}
}
obj* l_ExceptT_Monad___rarg___lambda__8(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_ExceptT_Monad___rarg___lambda__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_6);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_4, x_8);
return x_9;
}
}
obj* l_ExceptT_Monad___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg), 5, 1);
lean::closure_set(x_2, 0, x_1);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__2), 5, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_pure___rarg), 3, 1);
lean::closure_set(x_5, 0, x_1);
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__4), 5, 1);
lean::closure_set(x_6, 0, x_1);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__7), 5, 1);
lean::closure_set(x_7, 0, x_1);
lean::inc(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__9), 5, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bind___rarg), 5, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_ExceptT_Monad(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg), 1, 0);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_Monad___rarg___lambda__5___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_Monad___rarg___lambda__5(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_Monad___rarg___lambda__8(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_Monad___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_Monad(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_adapt___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___rarg), 2, 1);
lean::closure_set(x_9, 0, x_4);
x_10 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_9, x_5);
return x_10;
}
}
obj* l_ExceptT_adapt(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_adapt___rarg), 5, 0);
return x_3;
}
}
obj* l_ExceptT_adapt___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_adapt(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_MonadExcept_orelse___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_6, 0, x_4);
x_7 = lean::apply_3(x_5, lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_MonadExcept_orelse(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse___rarg), 4, 0);
return x_3;
}
}
obj* l_MonadExcept_orelse___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_MonadExcept_orelse(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_MonadExcept_orelse_x27___rarg___lambda__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
if (x_2 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::apply_2(x_5, lean::box(0), x_4);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::apply_2(x_7, lean::box(0), x_3);
return x_8;
}
}
}
obj* l_MonadExcept_orelse_x27___rarg___lambda__2(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::box(x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse_x27___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_6);
lean::closure_set(x_7, 2, x_5);
x_8 = lean::apply_3(x_3, lean::box(0), x_4, x_7);
return x_8;
}
}
obj* l_MonadExcept_orelse_x27___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::box(x_5);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse_x27___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_7);
lean::closure_set(x_8, 2, x_6);
lean::closure_set(x_8, 3, x_4);
x_9 = lean::apply_3(x_6, lean::box(0), x_3, x_8);
return x_9;
}
}
obj* l_MonadExcept_orelse_x27(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse_x27___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_MonadExcept_orelse_x27___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
lean::dec(x_2);
x_6 = l_MonadExcept_orelse_x27___rarg___lambda__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_MonadExcept_orelse_x27___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_MonadExcept_orelse_x27___rarg___lambda__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_MonadExcept_orelse_x27___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
lean::dec(x_5);
x_7 = l_MonadExcept_orelse_x27___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_MonadExcept_orelse_x27___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_MonadExcept_orelse_x27(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_MonadExcept_liftExcept___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::apply_1(x_2, x_6);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::apply_2(x_12, lean::box(0), x_10);
return x_13;
}
}
}
obj* l_MonadExcept_liftExcept(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_liftExcept___rarg), 5, 0);
return x_4;
}
}
obj* l_MonadExcept_liftExcept___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_MonadExcept_liftExcept(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_ExceptT_MonadExcept___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_ExceptT_MonadExcept___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadExcept___rarg___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_catch___rarg), 4, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_ExceptT_MonadExcept(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadExcept___rarg), 1, 0);
return x_3;
}
}
obj* l_ExceptT_MonadExcept___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_MonadExcept(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Except_MonadExcept___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Except_MonadExcept___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_catch), 2, 1);
lean::closure_set(x_1, 0, lean::box(0));
return x_1;
}
}
obj* _init_l_Except_MonadExcept___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_MonadExcept___lambda__1), 2, 0);
return x_1;
}
}
obj* _init_l_Except_MonadExcept___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Except_MonadExcept___closed__2;
x_2 = l_Except_MonadExcept___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Except_MonadExcept(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_MonadExcept___closed__3;
return x_2;
}
}
obj* l_monadExceptAdapterTrans___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monadFunctorTTrans___rarg___lambda__1), 4, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::apply_3(x_1, lean::box(0), x_6, x_5);
return x_7;
}
}
obj* l_monadExceptAdapterTrans(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_monadExceptAdapterTrans___rarg), 5, 0);
return x_7;
}
}
obj* l_monadExceptAdapterTrans___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_monadExceptAdapterTrans(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l_ExceptT_MonadExceptAdapter___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___rarg), 2, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_8, x_4);
return x_9;
}
}
obj* l_ExceptT_MonadExceptAdapter(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadExceptAdapter___rarg), 4, 0);
return x_4;
}
}
obj* l_ExceptT_MonadExceptAdapter___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_MonadExceptAdapter(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_ExceptT_MonadRun___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_2(x_1, lean::box(0), x_3);
return x_4;
}
}
obj* l_ExceptT_MonadRun(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadRun___rarg), 3, 0);
return x_4;
}
}
obj* l_ExceptT_MonadRun___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_MonadRun(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_ExceptT_MonadFail___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_ExceptT_MonadFail(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadFail___rarg), 3, 0);
return x_2;
}
}
obj* l_ExceptT_MonadFail___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_MonadFail(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_control_lift(obj*);
obj* initialize_init_data_tostring(obj*);
obj* initialize_init_control_monadfail(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_except(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_monadfail(w);
if (lean::io_result_is_error(w)) return w;
l_Except_toString___rarg___closed__1 = _init_l_Except_toString___rarg___closed__1();
lean::mark_persistent(l_Except_toString___rarg___closed__1);
l_Except_toString___rarg___closed__2 = _init_l_Except_toString___rarg___closed__2();
lean::mark_persistent(l_Except_toString___rarg___closed__2);
l_Except_Monad___closed__1 = _init_l_Except_Monad___closed__1();
lean::mark_persistent(l_Except_Monad___closed__1);
l_Except_Monad___closed__2 = _init_l_Except_Monad___closed__2();
lean::mark_persistent(l_Except_Monad___closed__2);
l_Except_Monad___closed__3 = _init_l_Except_Monad___closed__3();
lean::mark_persistent(l_Except_Monad___closed__3);
l_Except_Monad___closed__4 = _init_l_Except_Monad___closed__4();
lean::mark_persistent(l_Except_Monad___closed__4);
l_Except_Monad___closed__5 = _init_l_Except_Monad___closed__5();
lean::mark_persistent(l_Except_Monad___closed__5);
l_Except_Monad___closed__6 = _init_l_Except_Monad___closed__6();
lean::mark_persistent(l_Except_Monad___closed__6);
l_Except_Monad___closed__7 = _init_l_Except_Monad___closed__7();
lean::mark_persistent(l_Except_Monad___closed__7);
l_Except_Monad___closed__8 = _init_l_Except_Monad___closed__8();
lean::mark_persistent(l_Except_Monad___closed__8);
l_Except_Monad___closed__9 = _init_l_Except_Monad___closed__9();
lean::mark_persistent(l_Except_Monad___closed__9);
l_Except_Monad___closed__10 = _init_l_Except_Monad___closed__10();
lean::mark_persistent(l_Except_Monad___closed__10);
l_ExceptT_lift___rarg___closed__1 = _init_l_ExceptT_lift___rarg___closed__1();
lean::mark_persistent(l_ExceptT_lift___rarg___closed__1);
l_Except_MonadExcept___closed__1 = _init_l_Except_MonadExcept___closed__1();
lean::mark_persistent(l_Except_MonadExcept___closed__1);
l_Except_MonadExcept___closed__2 = _init_l_Except_MonadExcept___closed__2();
lean::mark_persistent(l_Except_MonadExcept___closed__2);
l_Except_MonadExcept___closed__3 = _init_l_Except_MonadExcept___closed__3();
lean::mark_persistent(l_Except_MonadExcept___closed__3);
return w;
}
}
