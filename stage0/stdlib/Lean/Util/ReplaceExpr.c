// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: Lean.Expr Lean.Util.PtrSet
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
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_replace_expr(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_replace_expr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_replace(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_8 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_2, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; size_t x_20; size_t x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_10);
lean_inc_ref(x_1);
x_13 = l_Lean_Expr_replaceNoCache(x_1, x_10);
lean_inc_ref(x_11);
x_14 = l_Lean_Expr_replaceNoCache(x_1, x_11);
x_20 = lean_ptr_addr(x_10);
lean_dec_ref(x_10);
x_21 = lean_ptr_addr(x_13);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_dec_ref(x_11);
x_15 = x_22;
goto block_19;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_ptr_addr(x_11);
lean_dec_ref(x_11);
x_24 = lean_ptr_addr(x_14);
x_25 = lean_usize_dec_eq(x_23, x_24);
x_15 = x_25;
goto block_19;
}
block_19:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_2);
x_16 = l_Lean_Expr_lam___override(x_9, x_13, x_14, x_12);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_2);
x_18 = l_Lean_Expr_lam___override(x_9, x_13, x_14, x_12);
return x_18;
}
else
{
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_9);
return x_2;
}
}
}
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; size_t x_37; size_t x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_28);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_27);
lean_inc_ref(x_1);
x_30 = l_Lean_Expr_replaceNoCache(x_1, x_27);
lean_inc_ref(x_28);
x_31 = l_Lean_Expr_replaceNoCache(x_1, x_28);
x_37 = lean_ptr_addr(x_27);
lean_dec_ref(x_27);
x_38 = lean_ptr_addr(x_30);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_dec_ref(x_28);
x_32 = x_39;
goto block_36;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_28);
lean_dec_ref(x_28);
x_41 = lean_ptr_addr(x_31);
x_42 = lean_usize_dec_eq(x_40, x_41);
x_32 = x_42;
goto block_36;
}
block_36:
{
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_2);
x_33 = l_Lean_Expr_forallE___override(x_26, x_30, x_31, x_29);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_29, x_29);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_2);
x_35 = l_Lean_Expr_forallE___override(x_26, x_30, x_31, x_29);
return x_35;
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_26);
return x_2;
}
}
}
}
case 8:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; size_t x_58; size_t x_59; uint8_t x_60; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_46);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc_ref(x_44);
lean_inc_ref(x_1);
x_48 = l_Lean_Expr_replaceNoCache(x_1, x_44);
lean_inc_ref(x_45);
lean_inc_ref(x_1);
x_49 = l_Lean_Expr_replaceNoCache(x_1, x_45);
lean_inc_ref(x_46);
x_50 = l_Lean_Expr_replaceNoCache(x_1, x_46);
x_58 = lean_ptr_addr(x_44);
lean_dec_ref(x_44);
x_59 = lean_ptr_addr(x_48);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_dec_ref(x_45);
x_51 = x_60;
goto block_57;
}
else
{
size_t x_61; size_t x_62; uint8_t x_63; 
x_61 = lean_ptr_addr(x_45);
lean_dec_ref(x_45);
x_62 = lean_ptr_addr(x_49);
x_63 = lean_usize_dec_eq(x_61, x_62);
x_51 = x_63;
goto block_57;
}
block_57:
{
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_46);
lean_dec_ref(x_2);
x_52 = l_Lean_Expr_letE___override(x_43, x_48, x_49, x_50, x_47);
return x_52;
}
else
{
size_t x_53; size_t x_54; uint8_t x_55; 
x_53 = lean_ptr_addr(x_46);
lean_dec_ref(x_46);
x_54 = lean_ptr_addr(x_50);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec_ref(x_2);
x_56 = l_Lean_Expr_letE___override(x_43, x_48, x_49, x_50, x_47);
return x_56;
}
else
{
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_43);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_64);
x_65 = l_Lean_Expr_replaceNoCache(x_1, x_64);
x_66 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_2, x_65);
return x_66;
}
case 11:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_67);
x_68 = l_Lean_Expr_replaceNoCache(x_1, x_67);
x_69 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_2, x_68);
return x_69;
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
else
{
lean_object* x_70; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
lean_dec_ref(x_3);
return x_70;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
