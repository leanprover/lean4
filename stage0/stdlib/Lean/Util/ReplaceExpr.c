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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_11; size_t x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
lean_inc(x_5);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_11 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_12 = lean_ptr_addr(x_6);
x_13 = lean_usize_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_5);
x_8 = x_13;
goto block_10;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_15 = lean_ptr_addr(x_7);
x_16 = lean_usize_dec_eq(x_14, x_15);
x_8 = x_16;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Expr_app___override(x_6, x_7);
return x_9;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; size_t x_28; size_t x_29; uint8_t x_30; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_18);
lean_inc(x_1);
x_21 = l_Lean_Expr_replaceNoCache(x_1, x_18);
lean_inc(x_19);
x_22 = l_Lean_Expr_replaceNoCache(x_1, x_19);
x_28 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_29 = lean_ptr_addr(x_21);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_dec(x_19);
x_23 = x_30;
goto block_27;
}
else
{
size_t x_31; size_t x_32; uint8_t x_33; 
x_31 = lean_ptr_addr(x_19);
lean_dec(x_19);
x_32 = lean_ptr_addr(x_22);
x_33 = lean_usize_dec_eq(x_31, x_32);
x_23 = x_33;
goto block_27;
}
block_27:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = l_Lean_Expr_lam___override(x_17, x_21, x_22, x_20);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_20, x_20);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = l_Lean_Expr_lam___override(x_17, x_21, x_22, x_20);
return x_26;
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
return x_2;
}
}
}
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; size_t x_45; size_t x_46; uint8_t x_47; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_35);
lean_inc(x_1);
x_38 = l_Lean_Expr_replaceNoCache(x_1, x_35);
lean_inc(x_36);
x_39 = l_Lean_Expr_replaceNoCache(x_1, x_36);
x_45 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_46 = lean_ptr_addr(x_38);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_36);
x_40 = x_47;
goto block_44;
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = lean_ptr_addr(x_36);
lean_dec(x_36);
x_49 = lean_ptr_addr(x_39);
x_50 = lean_usize_dec_eq(x_48, x_49);
x_40 = x_50;
goto block_44;
}
block_44:
{
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_2);
x_41 = l_Lean_Expr_forallE___override(x_34, x_38, x_39, x_37);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_37, x_37);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = l_Lean_Expr_forallE___override(x_34, x_38, x_39, x_37);
return x_43;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
return x_2;
}
}
}
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; size_t x_66; size_t x_67; uint8_t x_68; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_52);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceNoCache(x_1, x_52);
lean_inc(x_53);
lean_inc(x_1);
x_57 = l_Lean_Expr_replaceNoCache(x_1, x_53);
lean_inc(x_54);
x_58 = l_Lean_Expr_replaceNoCache(x_1, x_54);
x_66 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_67 = lean_ptr_addr(x_56);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_dec(x_53);
x_59 = x_68;
goto block_65;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_70 = lean_ptr_addr(x_57);
x_71 = lean_usize_dec_eq(x_69, x_70);
x_59 = x_71;
goto block_65;
}
block_65:
{
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_2);
x_60 = l_Lean_Expr_letE___override(x_51, x_56, x_57, x_58, x_55);
return x_60;
}
else
{
size_t x_61; size_t x_62; uint8_t x_63; 
x_61 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_62 = lean_ptr_addr(x_58);
x_63 = lean_usize_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_2);
x_64 = l_Lean_Expr_letE___override(x_51, x_56, x_57, x_58, x_55);
return x_64;
}
else
{
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_51);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
lean_inc(x_73);
x_74 = l_Lean_Expr_replaceNoCache(x_1, x_73);
x_75 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_76 = lean_ptr_addr(x_74);
x_77 = lean_usize_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_2);
x_78 = l_Lean_Expr_mdata___override(x_72, x_74);
return x_78;
}
else
{
lean_dec(x_74);
lean_dec(x_72);
return x_2;
}
}
case 11:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
lean_inc(x_81);
x_82 = l_Lean_Expr_replaceNoCache(x_1, x_81);
x_83 = lean_ptr_addr(x_81);
lean_dec(x_81);
x_84 = lean_ptr_addr(x_82);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_2);
x_86 = l_Lean_Expr_proj___override(x_79, x_80, x_82);
return x_86;
}
else
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
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
lean_object* x_87; 
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_3, 0);
lean_inc(x_87);
lean_dec(x_3);
return x_87;
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
