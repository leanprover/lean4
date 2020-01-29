// Lean compiler output
// Module: Init.Lean.Util.FindMVar
// Imports: Init.Lean.Expr
#include "runtime/lean.h"
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
lean_object* l_Lean_FindMVar_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_findMVar_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_3);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_FindMVar_main___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_1);
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_FindMVar_main___main(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec(x_1);
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_13;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_1);
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l_Lean_FindMVar_main___main(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
lean_dec(x_17);
lean_dec(x_1);
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
lean_dec(x_17);
lean_dec(x_1);
return x_21;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_24);
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_1);
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
lean_inc(x_1);
x_29 = l_Lean_FindMVar_main___main(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
lean_dec(x_25);
lean_dec(x_1);
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
lean_dec(x_25);
lean_dec(x_1);
return x_29;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
lean_dec(x_32);
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
lean_inc(x_1);
x_44 = l_Lean_FindMVar_main___main(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
return x_44;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_1);
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_1);
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
lean_dec(x_34);
lean_dec(x_1);
return x_35;
}
}
else
{
lean_object* x_39; 
lean_inc(x_1);
x_39 = l_Lean_FindMVar_main___main(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
lean_dec(x_34);
lean_dec(x_1);
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
lean_dec(x_34);
lean_dec(x_1);
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_dec(x_2);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_1);
return x_3;
}
else
{
x_2 = x_45;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_1);
return x_3;
}
else
{
x_2 = x_48;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_FindMVar_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_findMVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main(x_2, x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_FindMVar(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
