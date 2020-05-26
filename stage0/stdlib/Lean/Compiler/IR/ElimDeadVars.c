// Lean compiler output
// Module: Lean.Compiler.IR.ElimDeadVars
// Imports: Lean.Compiler.IR.Basic Lean.Compiler.IR.FreeVars
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_IR_FnBody_elimDead(lean_object*);
lean_object* l_RBNode_findCore___main___at___private_Lean_Compiler_IR_FreeVars_14__collectIndex___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
lean_object* l_Lean_IR_reshapeWithoutDeadAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_IR_reshapeWithoutDeadAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(lean_object*);
lean_object* l_Lean_IR_reshapeWithoutDead(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_IR_FnBody_elimDead___main(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_IR_reshapeWithoutDeadAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; 
x_5 = l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(x_1);
x_6 = lean_array_pop(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_12 = x_17;
goto block_16;
}
case 1:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_12 = x_18;
goto block_16;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
x_7 = x_19;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_inc(x_5);
x_8 = l_Lean_IR_FnBody_collectFreeIndices(x_5, x_3);
x_9 = l_Lean_IR_FnBody_setBody(x_5, x_2);
x_1 = x_6;
x_2 = x_9;
x_3 = x_8;
goto _start;
}
block_16:
{
lean_object* x_13; 
x_13 = l_RBNode_findCore___main___at___private_Lean_Compiler_IR_FreeVars_14__collectIndex___spec__1(x_3, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = lean_box(0);
x_7 = x_15;
goto block_11;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_reshapeWithoutDeadAux___main___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_reshapeWithoutDeadAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_reshapeWithoutDeadAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_reshapeWithoutDead(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_freeIndices(x_2);
x_4 = l_Lean_IR_reshapeWithoutDeadAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 2);
x_19 = l_Lean_IR_FnBody_elimDead___main(x_18);
lean_ctor_set(x_9, 2, x_19);
x_12 = x_9;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_24 = l_Lean_IR_FnBody_elimDead___main(x_22);
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_23);
x_12 = x_25;
goto block_16;
}
}
else
{
x_12 = x_9;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = x_12;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = l_Lean_IR_FnBody_elimDead___main(x_13);
lean_ctor_set(x_9, 1, x_14);
x_15 = x_9;
x_16 = lean_array_fset(x_8, x_1, x_15);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l_Lean_IR_FnBody_elimDead___main(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = x_21;
x_23 = lean_array_fset(x_8, x_1, x_22);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_23;
goto _start;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = l_Lean_IR_FnBody_elimDead___main(x_26);
lean_ctor_set(x_9, 0, x_27);
x_28 = x_9;
x_29 = lean_array_fset(x_8, x_1, x_28);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
x_32 = l_Lean_IR_FnBody_elimDead___main(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = x_33;
x_35 = lean_array_fset(x_8, x_1, x_34);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_35;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_FnBody_elimDead___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = x_3;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__1(x_6, x_5);
x_8 = x_7;
if (lean_obj_tag(x_4) == 10)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 3);
x_11 = x_10;
x_12 = l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(x_6, x_11);
x_13 = x_12;
lean_ctor_set(x_4, 3, x_13);
x_14 = l_Lean_IR_reshapeWithoutDead(x_8, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_19 = x_18;
x_20 = l_Array_umapMAux___main___at_Lean_IR_FnBody_elimDead___main___spec__2(x_6, x_19);
x_21 = x_20;
x_22 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_21);
x_23 = l_Lean_IR_reshapeWithoutDead(x_8, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = l_Lean_IR_reshapeWithoutDead(x_8, x_4);
return x_24;
}
}
}
lean_object* l_Lean_IR_FnBody_elimDead(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_FnBody_elimDead___main(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_elimDead(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_IR_FnBody_elimDead___main(x_3);
lean_ctor_set(x_1, 3, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = l_Lean_IR_FnBody_elimDead___main(x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
else
{
return x_1;
}
}
}
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
