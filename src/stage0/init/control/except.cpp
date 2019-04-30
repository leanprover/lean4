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
obj* l_ExceptT_Monad___rarg___lambda__9___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_HasMonadLift___boxed(obj*, obj*);
obj* l_Except_HasRepr___boxed(obj*, obj*);
obj* l_ExceptT_lift___rarg___closed__1;
obj* l_Except_repr___rarg(obj*, obj*, obj*);
obj* l_ExceptT_MonadExceptAdapter___rarg(obj*, obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept(obj*, obj*);
obj* l_ExceptT_pure___boxed(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_MonadExcept___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_toOption(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___boxed(obj*, obj*);
uint8 l_Except_toBool___main___rarg(obj*);
obj* l_ExceptT_MonadFail(obj*);
obj* l_Except_return(obj*, obj*);
obj* l_MonadExcept_liftExcept___boxed(obj*, obj*, obj*);
obj* l_ExceptT_run___boxed(obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(obj*, obj*);
obj* l_Except_repr(obj*, obj*);
obj* l_ExceptT_mk___rarg(obj*);
obj* l_monadFunctorTTrans___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_return___boxed(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_mapError(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__5(obj*, obj*, obj*);
obj* l_Except_toOption___rarg(obj*);
obj* l_Except_repr___main(obj*, obj*);
obj* l_monadExceptAdapterTrans___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_MonadExcept(obj*, obj*);
obj* l_ExceptT_MonadFail___rarg___boxed(obj*, obj*, obj*);
obj* l_ExceptT_adapt(obj*, obj*);
obj* l_Except_Inhabited___boxed(obj*, obj*);
obj* l_ExceptT_bindCont___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_MonadExcept_orelse_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__6(obj*, obj*, obj*);
obj* l_ExceptT_HasMonadLift(obj*, obj*);
obj* l_ExceptT_run___rarg___boxed(obj*);
obj* l_Except_toOption___main(obj*, obj*);
obj* l_ExceptT_catch___boxed(obj*, obj*);
obj* l_Except_map___boxed(obj*, obj*, obj*);
obj* l_Except_HasToString(obj*, obj*);
obj* l_MonadExcept_orelse_x_27___boxed(obj*, obj*);
obj* l_ExceptT_bind___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_mk___rarg___boxed(obj*);
obj* l_Except_MonadExcept(obj*);
obj* l_MonadExcept_liftExcept(obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept___rarg___boxed(obj*, obj*, obj*);
obj* l_Except_bind___boxed(obj*, obj*, obj*);
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_ExceptT_adapt___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_catch(obj*, obj*);
obj* l_ExceptT_bindCont___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_toBool___rarg___boxed(obj*);
obj* l_Except_map(obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_mk___boxed(obj*, obj*, obj*);
obj* l_MonadExcept_orelse___rarg(obj*, obj*, obj*, obj*);
obj* l_Except_Monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_ExceptT_MonadExcept___rarg(obj*);
obj* l_Except_map___main___rarg(obj*, obj*);
obj* l_MonadExcept_orelse_x_27___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Except_repr___boxed(obj*, obj*);
obj* l_ExceptT_adapt___boxed(obj*, obj*);
obj* l_Except_toBool___boxed(obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___main___boxed(obj*, obj*);
obj* l_Except_MonadExcept___lambda__1(obj*, obj*);
obj* l_Except_repr___main___rarg(obj*, obj*, obj*);
obj* l_Except_toBool___main___boxed(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(obj*, obj*);
obj* l_MonadExcept_liftExcept___main___boxed(obj*, obj*, obj*);
obj* l_Except_bind___rarg(obj*, obj*);
obj* l_ExceptT_MonadExcept___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Except_MonadExcept___boxed(obj*);
obj* l_ExceptT_Monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_toString___rarg(obj*, obj*, obj*);
obj* l_Except_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_toString___main___boxed(obj*, obj*);
obj* l_Except_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept___boxed(obj*, obj*);
obj* l_ExceptT_bindCont(obj*, obj*);
obj* l_ExceptT_catch___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Except_map___rarg(obj*, obj*);
obj* l_Except_repr___main___boxed(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Except_HasRepr(obj*, obj*);
obj* l_monadExceptAdapterTrans(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Except_bind(obj*, obj*, obj*);
obj* l_ExceptT_pure___rarg(obj*, obj*, obj*);
obj* l_ExceptT_catch___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_Except_toBool___rarg(obj*);
obj* l_Except_toBool___main___rarg___boxed(obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___boxed(obj*, obj*);
obj* l_Except_toOption___main___boxed(obj*, obj*);
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
obj* l_MonadExcept_liftExcept___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__5___boxed(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_toString___main___rarg___closed__2;
obj* l_ExceptT_MonadFunctor___rarg(obj*, obj*);
obj* l_Except_toString___main(obj*, obj*);
obj* l_ExceptT_mk(obj*, obj*, obj*);
obj* l_Except_catch___boxed(obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__9(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_lift___rarg___boxed(obj*, obj*, obj*);
obj* l_ExceptT_run___rarg(obj*);
obj* l_ExceptT_map___rarg___lambda__1(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_ExceptT_MonadExcept___boxed(obj*, obj*);
obj* l_ExceptT_map___boxed(obj*, obj*);
obj* l_Except_map___main(obj*, obj*, obj*);
obj* l_Except_MonadExcept___lambda__1___boxed(obj*, obj*);
obj* l_MonadExcept_orelse_x_27___rarg___lambda__1(obj*, uint8, obj*, obj*);
obj* l_Except_toString___boxed(obj*, obj*);
obj* l_ExceptT_MonadRun___rarg___boxed(obj*, obj*, obj*);
obj* l_Except_mapError___main___rarg(obj*, obj*);
obj* l_Except_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_map___main___boxed(obj*, obj*, obj*);
obj* l_MonadExcept_orelse_x_27(obj*, obj*);
obj* l_ExceptT_MonadFunctor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_exceptTOfExcept___rarg(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__8(obj*, obj*);
obj* l_MonadExcept_orelse_x_27___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_adapt___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_catch___rarg(obj*, obj*);
obj* l_Except_Inhabited___rarg(obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(obj*, obj*);
obj* l_ExceptT_bind___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Inhabited(obj*, obj*);
obj* l_ExceptT_MonadRun(obj*, obj*, obj*);
obj* l_Except_mapError___main(obj*, obj*, obj*);
obj* l_ExceptT_MonadRun___boxed(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___main(obj*, obj*);
obj* l_Except_toString___main___rarg___closed__1;
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(obj*, obj*);
obj* l_Except_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_toOption___main___rarg(obj*);
obj* l_ExceptT_MonadFail___boxed(obj*);
obj* l_monadExceptAdapterTrans___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___boxed(obj*, obj*);
obj* l_ExceptT_lift___rarg(obj*, obj*, obj*);
obj* l_Except_mapError___boxed(obj*, obj*, obj*);
obj* l_MonadExcept_liftExcept___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_lift(obj*, obj*);
obj* l_Except_mapError___main___boxed(obj*, obj*, obj*);
obj* l_ExceptT_bind(obj*, obj*);
obj* l_ExceptT_pure___rarg___boxed(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Monad(obj*);
obj* l_ExceptT_MonadRun___rarg(obj*, obj*, obj*);
obj* l_ExceptT_bindCont___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_catch___rarg(obj*, obj*, obj*, obj*);
obj* l_Except_Monad___boxed(obj*);
obj* l_MonadExcept_orelse___boxed(obj*, obj*);
obj* l_MonadExcept_orelse_x_27___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*);
obj* l_ExceptT_MonadFail___rarg(obj*, obj*, obj*);
obj* l_ExceptT_lift___boxed(obj*, obj*);
obj* l_Except_toString(obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__1(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg(obj*);
obj* l_Except_HasToString___boxed(obj*, obj*);
obj* l_MonadExcept_orelse___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_MonadExcept_orelse_x_27___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Except_Monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Except_toBool___main(obj*, obj*);
obj* l_Except_catch(obj*, obj*);
obj* l_MonadExcept_orelse(obj*, obj*);
obj* l_Except_Monad___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_MonadExcept_liftExcept___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_HasRepr___rarg(obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___boxed(obj*, obj*);
obj* l_Except_toString___main___rarg(obj*, obj*, obj*);
obj* l_ExceptT_Monad(obj*, obj*);
obj* l_Except_Monad___closed__1;
obj* l_ExceptT_MonadExceptAdapter___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_ExceptT_map___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_monadExceptAdapterTrans___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_map___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_Monad___boxed(obj*, obj*);
obj* l_Except_toOption___boxed(obj*, obj*);
obj* l_MonadExcept_liftExcept___main(obj*, obj*, obj*);
obj* l_Except_MonadExcept___closed__1;
obj* l_Except_mapError___rarg(obj*, obj*);
obj* l_ExceptT_MonadExceptAdapter___boxed(obj*, obj*, obj*);
obj* l_ExceptT_run(obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_ExceptT_bind___boxed(obj*, obj*);
obj* l_MonadExcept_liftExcept___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Except_Inhabited___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Except_Inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Inhabited___rarg), 1, 0);
return x_2;
}
}
obj* l_Except_Inhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_Inhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Except_toString___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(error ");
return x_0;
}
}
obj* _init_l_Except_toString___main___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(ok ");
return x_0;
}
}
obj* l_Except_toString___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_Except_toString___main___rarg___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::apply_1(x_1, x_14);
x_18 = l_Except_toString___main___rarg___closed__2;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = l_Option_HasRepr___rarg___closed__3;
x_22 = lean::string_append(x_19, x_21);
return x_22;
}
}
}
obj* l_Except_toString___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toString___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Except_toString___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toString___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_toString___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_toString___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Except_toString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toString___rarg), 3, 0);
return x_2;
}
}
obj* l_Except_toString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toString(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_repr___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_Except_toString___main___rarg___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::apply_1(x_1, x_14);
x_18 = l_Except_toString___main___rarg___closed__2;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = l_Option_HasRepr___rarg___closed__3;
x_22 = lean::string_append(x_19, x_21);
return x_22;
}
}
}
obj* l_Except_repr___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_repr___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Except_repr___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_repr___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_repr___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Except_repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_repr___rarg), 3, 0);
return x_2;
}
}
obj* l_Except_repr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_repr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_HasToString___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toString___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Except_HasToString(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_HasToString___rarg), 2, 0);
return x_2;
}
}
obj* l_Except_HasToString___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_HasToString(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_HasRepr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_repr___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Except_HasRepr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_HasRepr___rarg), 2, 0);
return x_2;
}
}
obj* l_Except_HasRepr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_HasRepr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_return___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Except_return(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_return___rarg), 1, 0);
return x_2;
}
}
obj* l_Except_return___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_return(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_map___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_0);
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_9 = x_1;
} else {
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
x_10 = lean::apply_1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_Except_map___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_map___main___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_map___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_map___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Except_map___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_0);
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_9 = x_1;
} else {
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
x_10 = lean::apply_1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_Except_map(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_map___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_map___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_map(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Except_mapError___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_10 = x_1;
} else {
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_Except_mapError___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___main___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_mapError___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_mapError___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Except_mapError___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_10 = x_1;
} else {
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_Except_mapError(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_mapError___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_mapError(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Except_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_5 = x_0;
} else {
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::apply_1(x_1, x_7);
return x_10;
}
}
}
obj* l_Except_bind(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_bind___rarg), 2, 0);
return x_3;
}
}
obj* l_Except_bind___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Except_bind(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Except_toBool___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Except_toBool___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toBool___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Except_toBool___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Except_toBool___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Except_toBool___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toBool___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Except_toBool___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Except_toBool(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toBool___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Except_toBool___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Except_toBool___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Except_toBool___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toBool(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_toOption___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
}
}
obj* l_Except_toOption___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toOption___main___rarg), 1, 0);
return x_2;
}
}
obj* l_Except_toOption___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toOption___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_toOption___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
}
}
obj* l_Except_toOption(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_toOption___rarg), 1, 0);
return x_2;
}
}
obj* l_Except_toOption___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_toOption(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_catch___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_1, x_2);
return x_5;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_Except_catch(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_catch___rarg), 2, 0);
return x_2;
}
}
obj* l_Except_catch___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_catch(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_Monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_10; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
} else {
 lean::dec(x_3);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_2);
return x_10;
}
}
}
obj* l_Except_Monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_12 = x_3;
} else {
 lean::inc(x_10);
 lean::dec(x_3);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_19 = x_3;
} else {
 lean::inc(x_17);
 lean::dec(x_3);
 x_19 = lean::box(0);
}
x_20 = lean::apply_1(x_14, x_17);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
}
obj* l_Except_Monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_12 = x_3;
} else {
 lean::inc(x_10);
 lean::dec(x_3);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_14 = x_3;
} else {
 lean::dec(x_3);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
}
}
}
obj* l_Except_Monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
else
{
lean::dec(x_2);
lean::inc(x_3);
return x_3;
}
}
}
obj* _init_l_Except_Monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_map___boxed), 3, 1);
lean::closure_set(x_0, 0, lean::box(0));
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__1___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_return___boxed), 2, 1);
lean::closure_set(x_3, 0, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__2___boxed), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__3___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_Monad___lambda__4___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_bind___boxed), 3, 1);
lean::closure_set(x_8, 0, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Except_Monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Except_Monad___closed__1;
return x_1;
}
}
obj* l_Except_Monad___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Except_Monad___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Except_Monad___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Except_Monad___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Except_Monad___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Except_Monad___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Except_Monad___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Except_Monad___lambda__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_Except_Monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Except_Monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ExceptT_mk___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_ExceptT_mk(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_mk___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_ExceptT_mk___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ExceptT_mk___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ExceptT_mk___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_mk(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_run___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_ExceptT_run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_run___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_ExceptT_run___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ExceptT_run___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ExceptT_run___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_run(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_pure___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_ExceptT_pure(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_pure___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_ExceptT_pure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_pure___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_pure___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_pure(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_bindCont___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_6);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_ExceptT_bindCont___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_bindCont___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bindCont___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bindCont___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bindCont___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_bindCont___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_6);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_ExceptT_bindCont(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_bindCont___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bindCont___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bindCont___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bindCont(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_bind___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___rarg___boxed), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_3, x_7);
return x_8;
}
}
obj* l_ExceptT_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bind___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_bind___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bind___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bind___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bind(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_map___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_4);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_15 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_17 = x_2;
} else {
 lean::inc(x_15);
 lean::dec(x_2);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_1(x_1, x_15);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::apply_2(x_21, lean::box(0), x_25);
return x_26;
}
}
}
obj* l_ExceptT_map___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_4, x_7);
return x_8;
}
}
obj* l_ExceptT_map(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_map___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_map___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_map___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_map(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_lift___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_ExceptT_lift___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_ExceptT_lift___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_ExceptT_lift___rarg___closed__1;
x_13 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_2);
return x_13;
}
}
obj* l_ExceptT_lift(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_ExceptT_lift___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_lift___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_lift___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_lift(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_exceptTOfExcept___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_6, lean::box(0), x_2);
return x_9;
}
}
obj* l_ExceptT_exceptTOfExcept(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_exceptTOfExcept___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_ExceptT_exceptTOfExcept___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_exceptTOfExcept___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_exceptTOfExcept___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_exceptTOfExcept(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_HasMonadLift___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_ExceptT_HasMonadLift(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_HasMonadLift___rarg), 1, 0);
return x_2;
}
}
obj* l_ExceptT_HasMonadLift___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_HasMonadLift(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_catch___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
return x_7;
}
else
{
obj* x_9; obj* x_12; obj* x_15; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::apply_2(x_12, lean::box(0), x_2);
return x_15;
}
}
}
obj* l_ExceptT_catch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_catch___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_0);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_ExceptT_catch(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_catch___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_ExceptT_catch___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_catch___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_ExceptT_catch___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_catch(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_MonadFunctor___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_ExceptT_MonadFunctor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadFunctor___rarg), 2, 0);
return x_6;
}
}
obj* l_ExceptT_MonadFunctor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_ExceptT_MonadFunctor(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_6);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_6);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_6);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_6);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::apply_1(x_3, x_18);
return x_21;
}
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_Monad___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_4);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_19; obj* x_22; obj* x_23; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_15 = x_2;
} else {
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_1);
x_23 = lean::apply_2(x_19, lean::box(0), x_22);
return x_23;
}
}
}
obj* l_ExceptT_Monad___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_4, x_7);
return x_8;
}
}
obj* l_ExceptT_Monad___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_1, x_5);
return x_6;
}
}
obj* l_ExceptT_Monad___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_6);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_ExceptT_Monad___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_ExceptT_Monad___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__5___boxed), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg___boxed), 5, 4);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, lean::box(0));
lean::closure_set(x_7, 3, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_7);
return x_8;
}
}
obj* l_ExceptT_Monad___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__6), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, lean::box(0));
lean::closure_set(x_9, 3, x_6);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* l_ExceptT_Monad___rarg___lambda__8(obj* x_0, obj* x_1) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_ExceptT_Monad___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg___boxed), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_3, x_8);
return x_9;
}
}
obj* l_ExceptT_Monad___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_map___rarg___boxed), 5, 1);
lean::closure_set(x_2, 0, x_0);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__2___boxed), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_pure___rarg___boxed), 3, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__4___boxed), 5, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__7___boxed), 5, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__9___boxed), 5, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_bind___rarg___boxed), 5, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_ExceptT_Monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg), 1, 0);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_bindCont___at_ExceptT_Monad___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_bindCont___at_ExceptT_Monad___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_Monad___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_Monad___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_Monad___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_Monad___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_Monad___rarg___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_Monad___rarg___lambda__5(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_Monad___rarg___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_Monad___rarg___lambda__7(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_Monad___rarg___lambda__8(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_Monad___rarg___lambda__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_Monad___rarg___lambda__9(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_Monad___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_Monad(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ExceptT_adapt___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___rarg), 2, 1);
lean::closure_set(x_14, 0, x_3);
x_15 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_14, x_4);
return x_15;
}
}
obj* l_ExceptT_adapt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_adapt___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ExceptT_adapt___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ExceptT_adapt___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_ExceptT_adapt___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_adapt(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_MonadExcept_orelse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::apply_3(x_4, lean::box(0), x_2, x_7);
return x_8;
}
}
obj* l_MonadExcept_orelse(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_MonadExcept_orelse___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_MonadExcept_orelse___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_MonadExcept_orelse___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_MonadExcept_orelse(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_MonadExcept_orelse_x_27___rarg___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (x_1 == 0)
{
obj* x_5; obj* x_8; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_2(x_5, lean::box(0), x_3);
return x_8;
}
else
{
obj* x_10; obj* x_13; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_2(x_10, lean::box(0), x_2);
return x_13;
}
}
}
obj* l_MonadExcept_orelse_x_27___rarg___lambda__2(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse_x_27___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::apply_3(x_2, lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_MonadExcept_orelse_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::box(x_4);
lean::inc(x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse_x_27___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_5);
lean::closure_set(x_9, 3, x_3);
x_10 = lean::apply_3(x_5, lean::box(0), x_2, x_9);
return x_10;
}
}
obj* l_MonadExcept_orelse_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_orelse_x_27___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_MonadExcept_orelse_x_27___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_MonadExcept_orelse_x_27___rarg___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_MonadExcept_orelse_x_27___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_MonadExcept_orelse_x_27___rarg___lambda__2(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_MonadExcept_orelse_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_MonadExcept_orelse_x_27___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_MonadExcept_orelse_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_MonadExcept_orelse_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_MonadExcept_liftExcept___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::apply_1(x_1, x_6);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_25; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::apply_2(x_22, lean::box(0), x_16);
return x_25;
}
}
}
obj* l_MonadExcept_liftExcept___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_liftExcept___main___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_MonadExcept_liftExcept___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_MonadExcept_liftExcept___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_MonadExcept_liftExcept___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_MonadExcept_liftExcept___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_MonadExcept_liftExcept___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::apply_1(x_1, x_6);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_25; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::apply_2(x_22, lean::box(0), x_16);
return x_25;
}
}
}
obj* l_MonadExcept_liftExcept(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_MonadExcept_liftExcept___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_MonadExcept_liftExcept___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_MonadExcept_liftExcept___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_MonadExcept_liftExcept___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_MonadExcept_liftExcept(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_MonadExcept___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_ExceptT_MonadExcept___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadExcept___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_catch___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_ExceptT_MonadExcept(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadExcept___rarg), 1, 0);
return x_2;
}
}
obj* l_ExceptT_MonadExcept___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_MonadExcept___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_MonadExcept___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ExceptT_MonadExcept(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Except_MonadExcept___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Except_MonadExcept___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_catch___boxed), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_MonadExcept___lambda__1___boxed), 2, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_Except_MonadExcept(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Except_MonadExcept___closed__1;
return x_1;
}
}
obj* l_Except_MonadExcept___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Except_MonadExcept___lambda__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Except_MonadExcept___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Except_MonadExcept(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_monadExceptAdapterTrans___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_monadFunctorTTrans___rarg___lambda__1___boxed), 4, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::apply_3(x_0, lean::box(0), x_5, x_4);
return x_6;
}
}
obj* l_monadExceptAdapterTrans(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_monadExceptAdapterTrans___rarg___boxed), 5, 0);
return x_6;
}
}
obj* l_monadExceptAdapterTrans___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_monadExceptAdapterTrans___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_monadExceptAdapterTrans___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_monadExceptAdapterTrans(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_ExceptT_MonadExceptAdapter___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Except_mapError___rarg), 2, 1);
lean::closure_set(x_13, 0, x_2);
x_14 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_3);
return x_14;
}
}
obj* l_ExceptT_MonadExceptAdapter(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadExceptAdapter___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_ExceptT_MonadExceptAdapter___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ExceptT_MonadExceptAdapter___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_ExceptT_MonadExceptAdapter___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_MonadExceptAdapter(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_MonadRun___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_ExceptT_MonadRun(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadRun___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_ExceptT_MonadRun___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_MonadRun___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_MonadRun___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_MonadRun(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_ExceptT_MonadFail___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_ExceptT_MonadFail(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_MonadFail___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_ExceptT_MonadFail___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_ExceptT_MonadFail___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_ExceptT_MonadFail___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ExceptT_MonadFail(x_0);
lean::dec(x_0);
return x_1;
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
if (io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_monadfail(w);
if (io_result_is_error(w)) return w;
 l_Except_toString___main___rarg___closed__1 = _init_l_Except_toString___main___rarg___closed__1();
lean::mark_persistent(l_Except_toString___main___rarg___closed__1);
 l_Except_toString___main___rarg___closed__2 = _init_l_Except_toString___main___rarg___closed__2();
lean::mark_persistent(l_Except_toString___main___rarg___closed__2);
 l_Except_Monad___closed__1 = _init_l_Except_Monad___closed__1();
lean::mark_persistent(l_Except_Monad___closed__1);
 l_ExceptT_lift___rarg___closed__1 = _init_l_ExceptT_lift___rarg___closed__1();
lean::mark_persistent(l_ExceptT_lift___rarg___closed__1);
 l_Except_MonadExcept___closed__1 = _init_l_Except_MonadExcept___closed__1();
lean::mark_persistent(l_Except_MonadExcept___closed__1);
return w;
}
