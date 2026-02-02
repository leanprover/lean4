// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: public import Lean.Expr public import Lean.Util.PtrSet
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
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
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
case 7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_15; size_t x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_8 = l_Lean_Expr_replaceNoCache(x_1, x_5);
lean_inc_ref(x_6);
x_9 = l_Lean_Expr_replaceNoCache(x_1, x_6);
x_15 = lean_ptr_addr(x_5);
x_16 = lean_ptr_addr(x_8);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
x_10 = x_17;
goto block_14;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_6);
x_19 = lean_ptr_addr(x_9);
x_20 = lean_usize_dec_eq(x_18, x_19);
x_10 = x_20;
goto block_14;
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_4);
lean_dec_ref(x_2);
x_11 = l_Lean_Expr_forallE___override(x_4, x_8, x_9, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_instBEqBinderInfo_beq(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_4);
lean_dec_ref(x_2);
x_13 = l_Lean_Expr_forallE___override(x_4, x_8, x_9, x_7);
return x_13;
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_2;
}
}
}
}
case 6:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; size_t x_32; size_t x_33; uint8_t x_34; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_22);
lean_inc_ref(x_1);
x_25 = l_Lean_Expr_replaceNoCache(x_1, x_22);
lean_inc_ref(x_23);
x_26 = l_Lean_Expr_replaceNoCache(x_1, x_23);
x_32 = lean_ptr_addr(x_22);
x_33 = lean_ptr_addr(x_25);
x_34 = lean_usize_dec_eq(x_32, x_33);
if (x_34 == 0)
{
x_27 = x_34;
goto block_31;
}
else
{
size_t x_35; size_t x_36; uint8_t x_37; 
x_35 = lean_ptr_addr(x_23);
x_36 = lean_ptr_addr(x_26);
x_37 = lean_usize_dec_eq(x_35, x_36);
x_27 = x_37;
goto block_31;
}
block_31:
{
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_21);
lean_dec_ref(x_2);
x_28 = l_Lean_Expr_lam___override(x_21, x_25, x_26, x_24);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_instBEqBinderInfo_beq(x_24, x_24);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_21);
lean_dec_ref(x_2);
x_30 = l_Lean_Expr_lam___override(x_21, x_25, x_26, x_24);
return x_30;
}
else
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_39);
x_40 = l_Lean_Expr_replaceNoCache(x_1, x_39);
x_41 = lean_ptr_addr(x_39);
x_42 = lean_ptr_addr(x_40);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_inc(x_38);
lean_dec_ref(x_2);
x_44 = l_Lean_Expr_mdata___override(x_38, x_40);
return x_44;
}
else
{
lean_dec_ref(x_40);
return x_2;
}
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; size_t x_60; size_t x_61; uint8_t x_62; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc_ref(x_46);
lean_inc_ref(x_1);
x_50 = l_Lean_Expr_replaceNoCache(x_1, x_46);
lean_inc_ref(x_47);
lean_inc_ref(x_1);
x_51 = l_Lean_Expr_replaceNoCache(x_1, x_47);
lean_inc_ref(x_48);
x_52 = l_Lean_Expr_replaceNoCache(x_1, x_48);
x_60 = lean_ptr_addr(x_46);
x_61 = lean_ptr_addr(x_50);
x_62 = lean_usize_dec_eq(x_60, x_61);
if (x_62 == 0)
{
x_53 = x_62;
goto block_59;
}
else
{
size_t x_63; size_t x_64; uint8_t x_65; 
x_63 = lean_ptr_addr(x_47);
x_64 = lean_ptr_addr(x_51);
x_65 = lean_usize_dec_eq(x_63, x_64);
x_53 = x_65;
goto block_59;
}
block_59:
{
if (x_53 == 0)
{
lean_object* x_54; 
lean_inc(x_45);
lean_dec_ref(x_2);
x_54 = l_Lean_Expr_letE___override(x_45, x_50, x_51, x_52, x_49);
return x_54;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = lean_ptr_addr(x_48);
x_56 = lean_ptr_addr(x_52);
x_57 = lean_usize_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_inc(x_45);
lean_dec_ref(x_2);
x_58 = l_Lean_Expr_letE___override(x_45, x_50, x_51, x_52, x_49);
return x_58;
}
else
{
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
return x_2;
}
}
}
}
case 5:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; size_t x_73; size_t x_74; uint8_t x_75; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_66);
lean_inc_ref(x_1);
x_68 = l_Lean_Expr_replaceNoCache(x_1, x_66);
lean_inc_ref(x_67);
x_69 = l_Lean_Expr_replaceNoCache(x_1, x_67);
x_73 = lean_ptr_addr(x_66);
x_74 = lean_ptr_addr(x_68);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
x_70 = x_75;
goto block_72;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_67);
x_77 = lean_ptr_addr(x_69);
x_78 = lean_usize_dec_eq(x_76, x_77);
x_70 = x_78;
goto block_72;
}
block_72:
{
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec_ref(x_2);
x_71 = l_Lean_Expr_app___override(x_68, x_69);
return x_71;
}
else
{
lean_dec_ref(x_69);
lean_dec_ref(x_68);
return x_2;
}
}
}
case 11:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get(x_2, 1);
x_81 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_81);
x_82 = l_Lean_Expr_replaceNoCache(x_1, x_81);
x_83 = lean_ptr_addr(x_81);
x_84 = lean_ptr_addr(x_82);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_inc(x_80);
lean_inc(x_79);
lean_dec_ref(x_2);
x_86 = l_Lean_Expr_proj___override(x_79, x_80, x_82);
return x_86;
}
else
{
lean_dec_ref(x_82);
return x_2;
}
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
lean_object* x_87; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_3, 0);
lean_inc(x_87);
lean_dec_ref(x_3);
return x_87;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
