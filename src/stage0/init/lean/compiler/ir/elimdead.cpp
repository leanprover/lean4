// Lean compiler output
// Module: init.lean.compiler.ir.elimdead
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.freevars
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
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(obj*, obj*);
obj* l_Lean_IR_reshapeWithoutDead(obj*, obj*);
obj* l_Lean_IR_FnBody_freeIndices(obj*);
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(obj*);
obj* l_Lean_IR_reshapeWithoutDeadAux(obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1___boxed(obj*);
obj* l_Lean_IR_FnBody_elimDead___main(obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(obj*, obj*);
obj* l_Lean_IR_reshapeWithoutDeadAux___main(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_Decl_elimDead(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_Lean_IR_FnBody_collectFreeIndices(obj*, obj*);
obj* l_Array_pop(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Lean_IR_FnBody_elimDead(obj*);
extern obj* l_Lean_IR_Inhabited;
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean::array_get(x_5, x_1, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_reshapeWithoutDeadAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_Array_isEmpty___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_12; 
x_5 = l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(x_1);
x_6 = lean::array_pop(x_1);
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_17; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_12 = x_17;
goto block_16;
}
case 1:
{
obj* x_18; 
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
x_12 = x_18;
goto block_16;
}
default: 
{
obj* x_19; 
x_19 = lean::box(0);
x_7 = x_19;
goto block_11;
}
}
block_11:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_7);
lean::inc(x_5);
x_8 = l_Lean_IR_FnBody_collectFreeIndices(x_5, x_3);
x_9 = l_Lean_IR_FnBody_setBody___main(x_5, x_2);
x_1 = x_6;
x_2 = x_9;
x_3 = x_8;
goto _start;
}
block_16:
{
obj* x_13; 
x_13 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_3, x_12);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
lean::dec(x_13);
lean::dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_13);
x_15 = lean::box(0);
x_7 = x_15;
goto block_11;
}
}
}
else
{
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_reshapeWithoutDeadAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_reshapeWithoutDeadAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_reshapeWithoutDead(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_2);
x_3 = l_Lean_IR_FnBody_freeIndices(x_2);
x_4 = l_Lean_IR_reshapeWithoutDeadAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::array_fget(x_2, x_1);
x_6 = lean::box(13);
x_7 = lean::array_fset(x_2, x_1, x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_1, x_8);
if (lean::obj_tag(x_5) == 1)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_5);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 2);
x_12 = l_Lean_IR_FnBody_elimDead___main(x_11);
lean::cnstr_set(x_5, 2, x_12);
x_13 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_5, 0);
x_16 = lean::cnstr_get(x_5, 1);
x_17 = lean::cnstr_get(x_5, 2);
x_18 = lean::cnstr_get(x_5, 3);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_5);
x_19 = l_Lean_IR_FnBody_elimDead___main(x_17);
x_20 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
lean::cnstr_set(x_20, 3, x_18);
x_21 = lean::array_fset(x_7, x_1, x_20);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_21;
goto _start;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_23;
goto _start;
}
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(13);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::array_fget(x_2, x_1);
x_6 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1;
x_7 = lean::array_fset(x_2, x_1, x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_1, x_8);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_5);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 1);
x_12 = l_Lean_IR_FnBody_elimDead___main(x_11);
lean::cnstr_set(x_5, 1, x_12);
x_13 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_5, 0);
x_16 = lean::cnstr_get(x_5, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_5);
x_17 = l_Lean_IR_FnBody_elimDead___main(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::array_fset(x_7, x_1, x_18);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_19;
goto _start;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_5);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_5, 0);
x_23 = l_Lean_IR_FnBody_elimDead___main(x_22);
lean::cnstr_set(x_5, 0, x_23);
x_24 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_24;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_5, 0);
lean::inc(x_26);
lean::dec(x_5);
x_27 = l_Lean_IR_FnBody_elimDead___main(x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::array_fset(x_7, x_1, x_28);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_29;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_FnBody_elimDead___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(x_5, x_3);
if (lean::obj_tag(x_4) == 10)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 2);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(x_5, x_8);
lean::cnstr_set(x_4, 2, x_9);
x_10 = l_Lean_IR_reshapeWithoutDead(x_6, x_4);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_4, 0);
x_12 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(x_5, x_13);
x_15 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_14);
x_16 = l_Lean_IR_reshapeWithoutDead(x_6, x_15);
return x_16;
}
}
else
{
obj* x_17; 
x_17 = l_Lean_IR_reshapeWithoutDead(x_6, x_4);
return x_17;
}
}
}
obj* l_Lean_IR_FnBody_elimDead(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_FnBody_elimDead___main(x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_elimDead___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 2);
x_4 = l_Lean_IR_FnBody_elimDead___main(x_3);
lean::cnstr_set(x_1, 2, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_9 = l_Lean_IR_FnBody_elimDead___main(x_8);
x_10 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*3, x_7);
return x_10;
}
}
else
{
return x_1;
}
}
}
obj* l_Lean_IR_Decl_elimDead(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Decl_elimDead___main(x_1);
return x_2;
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_freevars(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_elimdead(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (io_result_is_error(w)) return w;
l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2___closed__1);
return w;
}
