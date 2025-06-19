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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_replace_expr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
lean_inc(x_5);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_8 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = l_Lean_Expr_app___override(x_6, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_13 = lean_ptr_addr(x_7);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l_Lean_Expr_app___override(x_6, x_7);
return x_15;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_17);
lean_inc(x_1);
x_20 = l_Lean_Expr_replaceNoCache(x_1, x_17);
lean_inc(x_18);
x_21 = l_Lean_Expr_replaceNoCache(x_1, x_18);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_22 = l_Lean_Expr_lam___override(x_16, x_17, x_18, x_19);
x_23 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_24 = lean_ptr_addr(x_20);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_18);
x_26 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_26;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_28 = lean_ptr_addr(x_21);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
x_30 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_19, x_19);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
x_32 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_32;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
return x_22;
}
}
}
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_34);
lean_inc(x_1);
x_37 = l_Lean_Expr_replaceNoCache(x_1, x_34);
lean_inc(x_35);
x_38 = l_Lean_Expr_replaceNoCache(x_1, x_35);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_39 = l_Lean_Expr_forallE___override(x_33, x_34, x_35, x_36);
x_40 = lean_ptr_addr(x_34);
lean_dec(x_34);
x_41 = lean_ptr_addr(x_37);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_35);
x_43 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_43;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_45 = lean_ptr_addr(x_38);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
x_47 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_36, x_36);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_39);
x_49 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_49;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
return x_39;
}
}
}
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; uint8_t x_61; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_dec(x_2);
lean_inc(x_51);
lean_inc(x_1);
x_55 = l_Lean_Expr_replaceNoCache(x_1, x_51);
lean_inc(x_52);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceNoCache(x_1, x_52);
lean_inc(x_53);
x_57 = l_Lean_Expr_replaceNoCache(x_1, x_53);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_58 = l_Lean_Expr_letE___override(x_50, x_51, x_52, x_53, x_54);
x_59 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_60 = lean_ptr_addr(x_55);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_52);
x_62 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_62;
}
else
{
size_t x_63; size_t x_64; uint8_t x_65; 
x_63 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_64 = lean_ptr_addr(x_56);
x_65 = lean_usize_dec_eq(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_58);
lean_dec(x_53);
x_66 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_66;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_68 = lean_ptr_addr(x_57);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_58);
x_70 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_70;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_50);
return x_58;
}
}
}
}
case 10:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_inc(x_72);
x_73 = l_Lean_Expr_replaceNoCache(x_1, x_72);
x_74 = lean_ptr_addr(x_72);
lean_dec(x_72);
x_75 = lean_ptr_addr(x_73);
x_76 = lean_usize_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_2);
x_77 = l_Lean_Expr_mdata___override(x_71, x_73);
return x_77;
}
else
{
lean_dec(x_73);
lean_dec(x_71);
return x_2;
}
}
case 11:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
lean_inc(x_80);
x_81 = l_Lean_Expr_replaceNoCache(x_1, x_80);
x_82 = lean_ptr_addr(x_80);
lean_dec(x_80);
x_83 = lean_ptr_addr(x_81);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_2);
x_85 = l_Lean_Expr_proj___override(x_78, x_79, x_81);
return x_85;
}
else
{
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
return x_2;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_ctor_get(x_3, 0);
lean_inc(x_86);
lean_dec(x_3);
return x_86;
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
