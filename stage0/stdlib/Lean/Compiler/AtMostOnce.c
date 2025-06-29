// Lean compiler output
// Module: Lean.Compiler.AtMostOnce
// Imports: Lean.Environment
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
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_at_most_once(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_instAndThenVisitor___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_atMostOnce___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_instAndThenVisitor;
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_seq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get_uint8(x_4, 1);
if (x_5 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_instAndThenVisitor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get_uint8(x_4, 1);
if (x_5 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_apply_2(x_2, x_6, x_4);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Compiler_atMostOnce_instAndThenVisitor() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_atMostOnce_instAndThenVisitor___lam__0), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_skip___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_atMostOnce_skip(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, 0);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, 1);
if (x_6 == 0)
{
lean_ctor_set_uint8(x_3, 0, x_6);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_name_eq(x_1, x_2);
lean_ctor_set_uint8(x_3, 0, x_7);
return x_3;
}
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_3, 1);
lean_dec(x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_name_eq(x_1, x_2);
x_11 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_11, 0, x_10);
lean_ctor_set_uint8(x_11, 1, x_8);
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, 1);
if (x_12 == 0)
{
return x_3;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_name_eq(x_1, x_2);
if (x_14 == 0)
{
lean_ctor_set_uint8(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(0);
lean_ctor_set_uint8(x_3, 0, x_12);
x_16 = lean_unbox(x_15);
lean_ctor_set_uint8(x_3, 1, x_16);
return x_3;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = lean_name_eq(x_1, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_18, 0, x_12);
lean_ctor_set_uint8(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_20, 0, x_12);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, 1, x_21);
return x_20;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visitFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visitFVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_3, 0);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_3, 1);
if (x_13 == 0)
{
lean_ctor_set_uint8(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_name_eq(x_14, x_1);
lean_ctor_set_uint8(x_3, 0, x_15);
return x_3;
}
}
else
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_3, 1);
lean_dec(x_3);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_name_eq(x_18, x_1);
x_20 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, 1, x_16);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = lean_ctor_get_uint8(x_3, 1);
if (x_21 == 0)
{
return x_3;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_name_eq(x_23, x_1);
if (x_24 == 0)
{
lean_ctor_set_uint8(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
lean_ctor_set_uint8(x_3, 0, x_21);
x_26 = lean_unbox(x_25);
lean_ctor_set_uint8(x_3, 1, x_26);
return x_3;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_name_eq(x_27, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_29, 0, x_21);
lean_ctor_set_uint8(x_29, 1, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_31, 0, x_21);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, 1, x_32);
return x_31;
}
}
}
}
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = l_Lean_Compiler_atMostOnce_visit(x_1, x_34, x_3);
x_36 = lean_ctor_get_uint8(x_35, 1);
if (x_36 == 0)
{
return x_35;
}
else
{
x_2 = x_33;
x_3 = x_35;
goto _start;
}
}
case 6:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 2);
x_4 = x_38;
x_5 = x_39;
x_6 = x_3;
goto block_10;
}
case 7:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_4 = x_40;
x_5 = x_41;
x_6 = x_3;
goto block_10;
}
case 8:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_ctor_get(x_2, 3);
x_45 = l_Lean_Compiler_atMostOnce_visit(x_1, x_42, x_3);
x_46 = lean_ctor_get_uint8(x_45, 1);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Compiler_atMostOnce_visit(x_1, x_43, x_45);
x_48 = lean_ctor_get_uint8(x_47, 1);
if (x_48 == 0)
{
return x_47;
}
else
{
x_2 = x_44;
x_3 = x_47;
goto _start;
}
}
}
case 10:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_2, 1);
x_2 = x_50;
goto _start;
}
case 11:
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_2, 2);
x_2 = x_52;
goto _start;
}
default: 
{
return x_3;
}
}
block_10:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Compiler_atMostOnce_visit(x_1, x_4, x_6);
x_8 = lean_ctor_get_uint8(x_7, 1);
if (x_8 == 0)
{
return x_7;
}
else
{
x_2 = x_5;
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_atMostOnce_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_atMostOnce___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 0, 2);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 1, x_5);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_at_most_once(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_atMostOnce___closed__0;
x_4 = l_Lean_Compiler_atMostOnce_visit(x_2, x_1, x_3);
lean_dec(x_1);
lean_dec(x_2);
x_5 = lean_ctor_get_uint8(x_4, 1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_atMostOnce___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_at_most_once(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_AtMostOnce(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_atMostOnce_instAndThenVisitor = _init_l_Lean_Compiler_atMostOnce_instAndThenVisitor();
lean_mark_persistent(l_Lean_Compiler_atMostOnce_instAndThenVisitor);
l_Lean_Compiler_atMostOnce___closed__0 = _init_l_Lean_Compiler_atMostOnce___closed__0();
lean_mark_persistent(l_Lean_Compiler_atMostOnce___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
