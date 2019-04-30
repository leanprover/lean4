// Lean compiler output
// Module: init.control.estate
// Imports: init.control.state init.control.except
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
obj* l_EState_modify___boxed(obj*, obj*);
obj* l_EState_seqRight___rarg(obj*, obj*, obj*);
obj* l_EState_resultOk_mk___rarg(obj*, obj*);
obj* l_EState_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_EState_HasRepr___rarg(obj*, obj*);
obj* l_EState_Monad(obj*, obj*);
obj* l_EState_MonadExcept___boxed(obj*, obj*);
obj* l_EState_Result_repr___main(obj*, obj*, obj*);
obj* l_EState_Result_toString___main___rarg___closed__1;
obj* l_EState_set(obj*, obj*);
obj* l_EState_resultOk_mk(obj*, obj*, obj*);
obj* l_EState_orelse_x_27___boxed(obj*, obj*, obj*);
obj* l_EState_HasOrelse___boxed(obj*, obj*, obj*);
obj* l_EState_map___rarg(obj*, obj*, obj*);
obj* l_EState_Monad___boxed(obj*, obj*);
obj* l_EState_orelse(obj*, obj*, obj*);
obj* l_EState_Result_toString___main___boxed(obj*, obj*, obj*);
obj* l_EState_Inhabited___boxed(obj*, obj*, obj*);
obj* l_EState_orelse_x_27(obj*, obj*, obj*);
obj* l_EState_unreachableError(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_EState_orelse_x_27___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_EState_Result_toString___main(obj*, obj*, obj*);
obj* l_EState_throw___boxed(obj*, obj*, obj*);
obj* l_EState_Result_toString___main___rarg(obj*, obj*, obj*);
obj* l_EState_HasToString___boxed(obj*, obj*, obj*);
obj* l_EState_throw___rarg(obj*, obj*);
obj* l_EState_Result_toString(obj*, obj*, obj*);
obj* l_EState_adaptExcept___rarg(obj*, obj*, obj*);
obj* l_EState_Result_toString___main___rarg___closed__2;
obj* l_EState_bind(obj*, obj*, obj*, obj*);
obj* l_EState_pure___boxed(obj*, obj*, obj*);
obj* l_EState_seqRight___boxed(obj*, obj*, obj*, obj*);
obj* l_EState_modify(obj*, obj*);
obj* l_EState_unreachableError___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_EState_Result_toString___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_EState_Result_repr___main___rarg(obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l_EState_HasOrelse___closed__1;
obj* l_EState_pure(obj*, obj*, obj*);
extern obj* l_Except_toString___main___rarg___closed__2;
obj* l_EState_HasOrelse(obj*, obj*, obj*);
obj* l_EState_Monad___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_EState_Result_repr___boxed(obj*, obj*, obj*);
obj* l_EState_modify___rarg(obj*, obj*);
obj* l_EState_catch___rarg(obj*, obj*, obj*);
obj* l_EState_set___boxed(obj*, obj*);
obj* l_EState_get(obj*, obj*);
obj* l_EState_HasRepr___boxed(obj*, obj*, obj*);
obj* l_EState_adaptExcept(obj*, obj*, obj*, obj*);
obj* l_EState_bind___boxed(obj*, obj*, obj*, obj*);
obj* l_EState_Monad___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_EState_HasRepr(obj*, obj*, obj*);
obj* l_EState_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_EState_catch___boxed(obj*, obj*, obj*);
obj* l_EState_adaptExcept___boxed(obj*, obj*, obj*, obj*);
obj* l_EState_bind___rarg(obj*, obj*, obj*);
obj* l_EState_Monad___lambda__3(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Except_toString___main___rarg___closed__1;
obj* l_EState_Result_repr___main___boxed(obj*, obj*, obj*);
obj* l_EState_Result_repr___rarg(obj*, obj*, obj*);
obj* l_EState_get___boxed(obj*, obj*);
obj* l_EState_orelse___rarg(obj*, obj*, obj*);
obj* l_EState_orelse___boxed(obj*, obj*, obj*);
obj* l_EState_seqRight(obj*, obj*, obj*, obj*);
obj* l_EState_MonadState(obj*, obj*);
obj* l_EState_pure___rarg(obj*, obj*);
obj* l_EState_HasToString(obj*, obj*, obj*);
obj* l_EState_Monad___closed__1;
obj* l_EState_HasToString___rarg(obj*, obj*);
obj* l_EState_map(obj*, obj*, obj*, obj*);
obj* l_EState_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_EState_orelse_x_27___rarg(obj*, obj*, uint8, obj*);
obj* l_EState_Inhabited(obj*, obj*, obj*);
obj* l_EState_MonadExcept___closed__1;
obj* l_EState_MonadExcept(obj*, obj*);
obj* l_EState_catch(obj*, obj*, obj*);
obj* l_EState_MonadState___closed__1;
obj* l_EState_map___boxed(obj*, obj*, obj*, obj*);
obj* l_EState_resultOk_mk___boxed(obj*, obj*, obj*);
obj* l_EState_Result_repr(obj*, obj*, obj*);
obj* l_EState_set___rarg(obj*, obj*);
obj* l_EState_Inhabited___rarg(obj*, obj*);
obj* l_EState_MonadState___boxed(obj*, obj*);
obj* l_EState_throw(obj*, obj*, obj*);
obj* l_EState_get___rarg(obj*);
obj* l_EState_Result_toString___rarg(obj*, obj*, obj*);
obj* l_EState_unreachableError(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
lean_unreachable();
}
}
obj* l_EState_unreachableError___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_EState_unreachableError(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_EState_resultOk_mk___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_EState_resultOk_mk(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_resultOk_mk___rarg), 2, 0);
return x_3;
}
}
obj* l_EState_resultOk_mk___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_resultOk_mk(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_EState_Result_toString___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ok: ");
return x_0;
}
}
obj* _init_l_EState_Result_toString___main___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("error: ");
return x_0;
}
}
obj* l_EState_Result_toString___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_1, x_4);
x_8 = l_EState_Result_toString___main___rarg___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
return x_9;
}
else
{
obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::apply_1(x_0, x_12);
x_16 = l_EState_Result_toString___main___rarg___closed__2;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
return x_17;
}
}
}
obj* l_EState_Result_toString___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Result_toString___main___rarg), 3, 0);
return x_3;
}
}
obj* l_EState_Result_toString___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Result_toString___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_Result_toString___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Result_toString___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_EState_Result_toString(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Result_toString___rarg), 3, 0);
return x_3;
}
}
obj* l_EState_Result_toString___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Result_toString(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_Result_repr___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_1, x_4);
x_8 = l_Except_toString___main___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_Option_HasRepr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::apply_1(x_0, x_14);
x_18 = l_Except_toString___main___rarg___closed__1;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = l_Option_HasRepr___rarg___closed__3;
x_22 = lean::string_append(x_19, x_21);
return x_22;
}
}
}
obj* l_EState_Result_repr___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Result_repr___main___rarg), 3, 0);
return x_3;
}
}
obj* l_EState_Result_repr___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Result_repr___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_Result_repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Result_repr___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_EState_Result_repr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Result_repr___rarg), 3, 0);
return x_3;
}
}
obj* l_EState_Result_repr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Result_repr(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_HasToString___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Result_toString___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_EState_HasToString(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_HasToString___rarg), 2, 0);
return x_3;
}
}
obj* l_EState_HasToString___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_HasToString(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_HasRepr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Result_repr___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_EState_HasRepr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_HasRepr___rarg), 2, 0);
return x_3;
}
}
obj* l_EState_HasRepr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_HasRepr(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_Inhabited___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
if (lean::is_scalar(x_4)) {
 x_5 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_5 = x_4;
 lean::cnstr_set_tag(x_4, 1);
}
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_EState_Inhabited(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Inhabited___rarg), 2, 0);
return x_3;
}
}
obj* l_EState_Inhabited___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_Inhabited(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_pure___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
if (lean::is_scalar(x_4)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_4;
}
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_EState_pure(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_pure___rarg), 2, 0);
return x_3;
}
}
obj* l_EState_pure___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_pure(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_set___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_2 = x_1;
} else {
 lean::dec(x_1);
 x_2 = lean::box(0);
}
x_3 = lean::box(0);
if (lean::is_scalar(x_2)) {
 x_4 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_4 = x_2;
}
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
return x_4;
}
}
obj* l_EState_set(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_set___rarg), 2, 0);
return x_2;
}
}
obj* l_EState_set___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_set(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_EState_get___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
lean::inc(x_1);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_EState_get(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_get___rarg), 1, 0);
return x_2;
}
}
obj* l_EState_get___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_get(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_EState_modify___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::apply_1(x_0, x_2);
x_6 = lean::box(0);
if (lean::is_scalar(x_4)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_4;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
obj* l_EState_modify(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_modify___rarg), 2, 0);
return x_2;
}
}
obj* l_EState_modify___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_modify(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_EState_throw___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
if (lean::is_scalar(x_4)) {
 x_5 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_5 = x_4;
 lean::cnstr_set_tag(x_4, 1);
}
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_EState_throw(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_throw___rarg), 2, 0);
return x_3;
}
}
obj* l_EState_throw___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_throw(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_catch___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
 lean::cnstr_set_tag(x_9, 0);
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
x_12 = lean::apply_2(x_1, x_5, x_11);
return x_12;
}
}
}
obj* l_EState_catch(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_catch___rarg), 3, 0);
return x_3;
}
}
obj* l_EState_catch___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_catch(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_orelse___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
 lean::cnstr_set_tag(x_7, 0);
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
x_10 = lean::apply_1(x_1, x_9);
return x_10;
}
}
}
obj* l_EState_orelse(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_orelse___rarg), 3, 0);
return x_3;
}
}
obj* l_EState_orelse___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_orelse(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_orelse_x_27___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_1(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_1);
return x_4;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_4, 0);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_10 = x_4;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
 lean::cnstr_set_tag(x_10, 0);
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::apply_1(x_1, x_12);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_6);
return x_13;
}
else
{
if (x_2 == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_6);
x_16 = lean::cnstr_get(x_13, 0);
x_18 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_20 = x_13;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_24 = x_13;
} else {
 lean::inc(x_22);
 lean::dec(x_13);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_6);
lean::cnstr_set(x_25, 1, x_22);
return x_25;
}
}
}
}
}
obj* l_EState_orelse_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_orelse_x_27___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_EState_orelse_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_EState_orelse_x_27___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_EState_orelse_x_27___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_orelse_x_27(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_EState_adaptExcept___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_0);
x_5 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_15 = x_3;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = lean::apply_1(x_0, x_11);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
return x_17;
}
}
}
obj* l_EState_adaptExcept(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_adaptExcept___rarg), 3, 0);
return x_4;
}
}
obj* l_EState_adaptExcept___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_EState_adaptExcept(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_EState_bind___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
x_11 = lean::apply_2(x_1, x_4, x_10);
return x_11;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_3, 0);
x_15 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_17 = x_3;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
}
obj* l_EState_bind(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 0);
return x_4;
}
}
obj* l_EState_bind___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_EState_bind(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_EState_map___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::apply_1(x_0, x_4);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_16 = x_3;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_3);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
}
}
obj* l_EState_map(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_map___rarg), 3, 0);
return x_4;
}
}
obj* l_EState_map___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_EState_map(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_EState_seqRight___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::apply_1(x_1, x_8);
return x_9;
}
else
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_15 = x_3;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
}
}
obj* l_EState_seqRight(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_seqRight___rarg), 3, 0);
return x_4;
}
}
obj* l_EState_seqRight___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_EState_seqRight(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_EState_Monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_1(x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
else
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_11 = lean::cnstr_get(x_5, 0);
x_13 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_15 = x_5;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_5);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
}
}
obj* l_EState_Monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_1(x_2, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::apply_1(x_3, x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_13, 0);
x_16 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_18 = x_13;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
x_19 = lean::apply_1(x_6, x_14);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_6);
x_22 = lean::cnstr_get(x_13, 0);
x_24 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_26 = x_13;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_13);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_22);
lean::cnstr_set(x_27, 1, x_24);
return x_27;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_3);
x_29 = lean::cnstr_get(x_5, 0);
x_31 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_33 = x_5;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_5);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
obj* l_EState_Monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_1(x_2, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::apply_1(x_3, x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_16 = x_13;
} else {
 lean::inc(x_14);
 lean::dec(x_13);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_13, 0);
x_21 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_23 = x_13;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_21);
return x_24;
}
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_3);
x_26 = lean::cnstr_get(x_5, 0);
x_28 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_30 = x_5;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_5);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
}
}
obj* _init_l_EState_Monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_map___boxed), 4, 2);
lean::closure_set(x_0, 0, lean::box(0));
lean::closure_set(x_0, 1, lean::box(0));
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Monad___lambda__1___boxed), 5, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_pure___boxed), 3, 2);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_seqRight___boxed), 4, 2);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Monad___lambda__2___boxed), 5, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_Monad___lambda__3___boxed), 5, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___boxed), 4, 2);
lean::closure_set(x_8, 0, lean::box(0));
lean::closure_set(x_8, 1, lean::box(0));
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_EState_Monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_Monad___closed__1;
return x_2;
}
}
obj* l_EState_Monad___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_EState_Monad___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_EState_Monad___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_EState_Monad___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_EState_Monad___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_EState_Monad___lambda__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_EState_Monad___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_Monad(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_EState_HasOrelse___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_orelse___rarg), 3, 0);
return x_0;
}
}
obj* l_EState_HasOrelse(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_HasOrelse___closed__1;
return x_3;
}
}
obj* l_EState_HasOrelse___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_EState_HasOrelse(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_EState_MonadState___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_get___rarg), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_set___rarg), 2, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_modify___rarg), 2, 0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_EState_MonadState(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_MonadState___closed__1;
return x_2;
}
}
obj* l_EState_MonadState___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_MonadState(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_EState_MonadExcept___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_throw___boxed), 3, 2);
lean::closure_set(x_0, 0, lean::box(0));
lean::closure_set(x_0, 1, lean::box(0));
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_catch___boxed), 3, 2);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_EState_MonadExcept(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_MonadExcept___closed__1;
return x_2;
}
}
obj* l_EState_MonadExcept___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_EState_MonadExcept(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_control_state(obj*);
obj* initialize_init_control_except(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_estate(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_except(w);
if (io_result_is_error(w)) return w;
 l_EState_Result_toString___main___rarg___closed__1 = _init_l_EState_Result_toString___main___rarg___closed__1();
lean::mark_persistent(l_EState_Result_toString___main___rarg___closed__1);
 l_EState_Result_toString___main___rarg___closed__2 = _init_l_EState_Result_toString___main___rarg___closed__2();
lean::mark_persistent(l_EState_Result_toString___main___rarg___closed__2);
 l_EState_Monad___closed__1 = _init_l_EState_Monad___closed__1();
lean::mark_persistent(l_EState_Monad___closed__1);
 l_EState_HasOrelse___closed__1 = _init_l_EState_HasOrelse___closed__1();
lean::mark_persistent(l_EState_HasOrelse___closed__1);
 l_EState_MonadState___closed__1 = _init_l_EState_MonadState___closed__1();
lean::mark_persistent(l_EState_MonadState___closed__1);
 l_EState_MonadExcept___closed__1 = _init_l_EState_MonadExcept___closed__1();
lean::mark_persistent(l_EState_MonadExcept___closed__1);
return w;
}
