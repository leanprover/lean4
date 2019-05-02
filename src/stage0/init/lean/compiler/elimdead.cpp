// Lean compiler output
// Module: init.lean.compiler.elimdead
// Imports: init.default init.lean.compiler.ir
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
obj* l_Lean_IR_FnBody_collectFreeVars(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(obj*, obj*);
obj* l_Lean_IR_reshapeWithoutDead(obj*, obj*);
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(obj*);
obj* l_Lean_IR_reshapeWithoutDeadAux(obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1___boxed(obj*);
obj* l_Lean_IR_FnBody_elimDead___main(obj*);
obj* l_Lean_IR_FnBody_freeVars(obj*);
obj* l_Lean_IR_reshapeWithoutDeadAux___main(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_Decl_elimDead(obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Lean_IR_FnBody_elimDead(obj*);
extern obj* l_Lean_IR_Inhabited;
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_sub(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean::array_get(x_5, x_0, x_3);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_IR_reshapeWithoutDeadAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Array_isEmpty___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(x_0);
x_5 = lean::array_pop(x_0);
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::inc(x_2);
x_9 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_2, x_6);
lean::dec(x_6);
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_4);
x_0 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_9);
lean::inc(x_4);
x_15 = l_Lean_IR_FnBody_collectFreeVars(x_4, x_2);
x_16 = l_Lean_IR_FnBody_setBody___main(x_4, x_1);
x_0 = x_5;
x_1 = x_16;
x_2 = x_15;
goto _start;
}
}
case 1:
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::inc(x_2);
x_21 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_2, x_18);
lean::dec(x_18);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_4);
x_0 = x_5;
goto _start;
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_21);
lean::inc(x_4);
x_27 = l_Lean_IR_FnBody_collectFreeVars(x_4, x_2);
x_28 = l_Lean_IR_FnBody_setBody___main(x_4, x_1);
x_0 = x_5;
x_1 = x_28;
x_2 = x_27;
goto _start;
}
}
case 12:
{
obj* x_30; obj* x_31; 
x_30 = l_Lean_IR_FnBody_collectFreeVars(x_4, x_2);
x_31 = l_Lean_IR_FnBody_setBody___main(x_4, x_1);
x_0 = x_5;
x_1 = x_31;
x_2 = x_30;
goto _start;
}
default:
{
obj* x_34; obj* x_35; 
lean::inc(x_4);
x_34 = l_Lean_IR_FnBody_collectFreeVars(x_4, x_2);
x_35 = l_Lean_IR_FnBody_setBody___main(x_4, x_1);
x_0 = x_5;
x_1 = x_35;
x_2 = x_34;
goto _start;
}
}
}
else
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_reshapeWithoutDeadAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_reshapeWithoutDeadAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_reshapeWithoutDead(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = l_Lean_IR_FnBody_freeVars(x_1);
x_4 = l_Lean_IR_reshapeWithoutDeadAux___main(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = lean::box(12);
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_0, x_9);
switch (lean::obj_tag(x_6)) {
case 1:
{
obj* x_11; obj* x_13; uint8 x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*4);
x_16 = lean::cnstr_get(x_6, 2);
x_18 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_20 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_6);
 x_20 = lean::box(0);
}
x_21 = l_Lean_IR_FnBody_elimDead___main(x_16);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 2, x_21);
lean::cnstr_set(x_22, 3, x_18);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_15);
x_23 = x_22;
x_24 = lean::array_fset(x_8, x_0, x_23);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_24;
goto _start;
}
default:
{
obj* x_27; 
x_27 = lean::array_fset(x_8, x_0, x_6);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_27;
goto _start;
}
}
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(12);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_0, x_9);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_15 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_6);
 x_15 = lean::box(0);
}
x_16 = l_Lean_IR_FnBody_elimDead___main(x_13);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::array_fset(x_8, x_0, x_17);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_18;
goto _start;
}
else
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_23 = x_6;
} else {
 lean::inc(x_21);
 lean::dec(x_6);
 x_23 = lean::box(0);
}
x_24 = l_Lean_IR_FnBody_elimDead___main(x_21);
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::array_fset(x_8, x_0, x_25);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_26;
goto _start;
}
}
}
}
obj* l_Lean_IR_FnBody_elimDead___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_1 = l_Lean_IR_FnBody_flatten(x_0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::mk_nat_obj(0ul);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(x_7, x_2);
switch (lean::obj_tag(x_4)) {
case 9:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 x_15 = x_4;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_4);
 x_15 = lean::box(0);
}
x_16 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(x_7, x_13);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_16);
x_18 = l_Lean_IR_reshapeWithoutDead(x_8, x_17);
return x_18;
}
default:
{
obj* x_19; 
x_19 = l_Lean_IR_reshapeWithoutDead(x_8, x_4);
return x_19;
}
}
}
}
obj* l_Lean_IR_FnBody_elimDead(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FnBody_elimDead___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_elimDead___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_FnBody_elimDead___main(x_6);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_3);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*3, x_5);
x_11 = x_10;
return x_11;
}
else
{
return x_0;
}
}
}
obj* l_Lean_IR_Decl_elimDead(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_elimDead___main(x_0);
return x_1;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_compiler_ir(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_elimdead(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1);
return w;
}
