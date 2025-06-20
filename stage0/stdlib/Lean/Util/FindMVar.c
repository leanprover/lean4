// Lean compiler output
// Module: Lean.Util.FindMVar
// Imports: Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findMVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_main___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasExprMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_FindMVar_main(x_1, x_2, x_3);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindMVar_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_10);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_10);
return x_3;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Lean_FindMVar_visit(x_1, x_14, x_3);
x_17 = l_Lean_FindMVar_visit(x_1, x_15, x_16);
lean_dec(x_16);
return x_17;
}
case 6:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_4 = x_18;
x_5 = x_19;
x_6 = x_3;
goto block_9;
}
case 7:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
x_4 = x_20;
x_5 = x_21;
x_6 = x_3;
goto block_9;
}
case 8:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
x_25 = l_Lean_FindMVar_visit(x_1, x_22, x_3);
lean_inc(x_1);
x_26 = l_Lean_FindMVar_visit(x_1, x_23, x_25);
lean_dec(x_25);
x_27 = l_Lean_FindMVar_visit(x_1, x_24, x_26);
lean_dec(x_26);
return x_27;
}
case 10:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_FindMVar_visit(x_1, x_28, x_3);
return x_29;
}
case 11:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_Lean_FindMVar_visit(x_1, x_30, x_3);
return x_31;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l_Lean_FindMVar_visit(x_1, x_4, x_6);
x_8 = l_Lean_FindMVar_visit(x_1, x_5, x_7);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindMVar_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_visit(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FindMVar_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findMVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main(x_2, x_1, x_3);
return x_4;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindMVar(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
