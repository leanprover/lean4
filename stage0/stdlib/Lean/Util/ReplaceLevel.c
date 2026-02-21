// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: public import Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0;
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0 = (const lean_object*)&l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr = (const lean_object*)&l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value;
lean_object* lean_usize_to_nat(size_t);
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
static const lean_string_object l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = (const lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = (const lean_object*)&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_value;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5;
static lean_once_cell_t l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_6 = l_Lean_Level_replace(x_1, x_4);
x_7 = l_Lean_Level_replace(x_1, x_5);
x_8 = l_Lean_mkLevelMax_x27(x_6, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_11 = l_Lean_Level_replace(x_1, x_9);
x_12 = l_Lean_Level_replace(x_1, x_10);
x_13 = l_Lean_mkLevelIMax_x27(x_11, x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Lean_Level_replace(x_1, x_14);
x_16 = l_Lean_Level_succ___override(x_15);
return x_16;
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
lean_object* x_17; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec_ref(x_3);
return x_17;
}
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 8192;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize(void) {
_start:
{
size_t x_1; 
x_1 = lean_usize_once(&l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0, &l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_uset(x_6, x_1, x_2);
lean_inc_ref(x_3);
x_9 = lean_array_uset(x_7, x_1, x_3);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_array_uset(x_11, x_1, x_2);
lean_inc_ref(x_3);
x_14 = lean_array_uset(x_12, x_1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceLevelImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_8 = l_Lean_Level_replace(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc_ref(x_1);
x_12 = l_Lean_Level_replace(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ptr_addr(x_3);
x_8 = lean_usize_mod(x_7, x_2);
x_9 = lean_array_uget_borrowed(x_5, x_8);
x_10 = lean_ptr_addr(x_9);
x_11 = lean_usize_dec_eq(x_10, x_7);
if (x_11 == 0)
{
switch (lean_obj_tag(x_3)) {
case 7:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; size_t x_30; size_t x_31; uint8_t x_32; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc_ref(x_13);
lean_inc_ref(x_1);
x_16 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_13, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
lean_inc_ref(x_14);
x_19 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_14, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_30 = lean_ptr_addr(x_13);
x_31 = lean_ptr_addr(x_17);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
x_22 = x_32;
goto block_29;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_14);
x_34 = lean_ptr_addr(x_20);
x_35 = lean_usize_dec_eq(x_33, x_34);
x_22 = x_35;
goto block_29;
}
block_29:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_12);
x_23 = l_Lean_Expr_forallE___override(x_12, x_17, x_20, x_15);
x_24 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_23, x_21);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_Lean_instBEqBinderInfo_beq(x_15, x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_inc(x_12);
x_26 = l_Lean_Expr_forallE___override(x_12, x_17, x_20, x_15);
x_27 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_17);
lean_inc_ref(x_3);
x_28 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_21);
return x_28;
}
}
}
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; size_t x_54; size_t x_55; uint8_t x_56; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
x_38 = lean_ctor_get(x_3, 2);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_40 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_37, x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
lean_inc_ref(x_38);
x_43 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_38, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_54 = lean_ptr_addr(x_37);
x_55 = lean_ptr_addr(x_41);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
x_46 = x_56;
goto block_53;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_38);
x_58 = lean_ptr_addr(x_44);
x_59 = lean_usize_dec_eq(x_57, x_58);
x_46 = x_59;
goto block_53;
}
block_53:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_inc(x_36);
x_47 = l_Lean_Expr_lam___override(x_36, x_41, x_44, x_39);
x_48 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_47, x_45);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = l_Lean_instBEqBinderInfo_beq(x_39, x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_inc(x_36);
x_50 = l_Lean_Expr_lam___override(x_36, x_41, x_44, x_39);
x_51 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_50, x_45);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_41);
lean_inc_ref(x_3);
x_52 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_45);
return x_52;
}
}
}
}
case 10:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_3, 0);
x_61 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_61);
x_62 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_61, x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_ptr_addr(x_61);
x_66 = lean_ptr_addr(x_63);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_inc(x_60);
x_68 = l_Lean_Expr_mdata___override(x_60, x_63);
x_69 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_68, x_64);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_63);
lean_inc_ref(x_3);
x_70 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_64);
return x_70;
}
}
case 8:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; size_t x_95; size_t x_96; uint8_t x_97; 
x_71 = lean_ctor_get(x_3, 0);
x_72 = lean_ctor_get(x_3, 1);
x_73 = lean_ctor_get(x_3, 2);
x_74 = lean_ctor_get(x_3, 3);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc_ref(x_72);
lean_inc_ref(x_1);
x_76 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_72, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
lean_inc_ref(x_73);
lean_inc_ref(x_1);
x_79 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_73, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
lean_inc_ref(x_74);
x_82 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_74, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_95 = lean_ptr_addr(x_72);
x_96 = lean_ptr_addr(x_77);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
x_85 = x_97;
goto block_94;
}
else
{
size_t x_98; size_t x_99; uint8_t x_100; 
x_98 = lean_ptr_addr(x_73);
x_99 = lean_ptr_addr(x_80);
x_100 = lean_usize_dec_eq(x_98, x_99);
x_85 = x_100;
goto block_94;
}
block_94:
{
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_inc(x_71);
x_86 = l_Lean_Expr_letE___override(x_71, x_77, x_80, x_83, x_75);
x_87 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_86, x_84);
return x_87;
}
else
{
size_t x_88; size_t x_89; uint8_t x_90; 
x_88 = lean_ptr_addr(x_74);
x_89 = lean_ptr_addr(x_83);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_inc(x_71);
x_91 = l_Lean_Expr_letE___override(x_71, x_77, x_80, x_83, x_75);
x_92 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_91, x_84);
return x_92;
}
else
{
lean_object* x_93; 
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_77);
lean_inc_ref(x_3);
x_93 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_84);
return x_93;
}
}
}
}
case 5:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; size_t x_114; size_t x_115; uint8_t x_116; 
x_101 = lean_ctor_get(x_3, 0);
x_102 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_101);
lean_inc_ref(x_1);
x_103 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_101, x_4);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
lean_inc_ref(x_102);
x_106 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_102, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_114 = lean_ptr_addr(x_101);
x_115 = lean_ptr_addr(x_104);
x_116 = lean_usize_dec_eq(x_114, x_115);
if (x_116 == 0)
{
x_109 = x_116;
goto block_113;
}
else
{
size_t x_117; size_t x_118; uint8_t x_119; 
x_117 = lean_ptr_addr(x_102);
x_118 = lean_ptr_addr(x_107);
x_119 = lean_usize_dec_eq(x_117, x_118);
x_109 = x_119;
goto block_113;
}
block_113:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Lean_Expr_app___override(x_104, x_107);
x_111 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_110, x_108);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_107);
lean_dec(x_104);
lean_inc_ref(x_3);
x_112 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_108);
return x_112;
}
}
}
case 11:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; size_t x_126; size_t x_127; uint8_t x_128; 
x_120 = lean_ctor_get(x_3, 0);
x_121 = lean_ctor_get(x_3, 1);
x_122 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_122);
x_123 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_122, x_4);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_ptr_addr(x_122);
x_127 = lean_ptr_addr(x_124);
x_128 = lean_usize_dec_eq(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_inc(x_121);
lean_inc(x_120);
x_129 = l_Lean_Expr_proj___override(x_120, x_121, x_124);
x_130 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_129, x_125);
return x_130;
}
else
{
lean_object* x_131; 
lean_dec(x_124);
lean_inc_ref(x_3);
x_131 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_125);
return x_131;
}
}
case 3:
{
lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_3, 0);
lean_inc(x_132);
x_133 = l_Lean_Level_replace(x_1, x_132);
x_134 = lean_ptr_addr(x_132);
x_135 = lean_ptr_addr(x_133);
x_136 = lean_usize_dec_eq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Lean_Expr_sort___override(x_133);
x_138 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_137, x_4);
return x_138;
}
else
{
lean_object* x_139; 
lean_dec(x_133);
lean_inc_ref(x_3);
x_139 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_4);
return x_139;
}
}
case 4:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_3, 0);
x_141 = lean_ctor_get(x_3, 1);
x_142 = lean_box(0);
lean_inc(x_141);
x_143 = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_141, x_142);
x_144 = l_ptrEqList___redArg(x_141, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_inc(x_140);
x_145 = l_Lean_Expr_const___override(x_140, x_143);
x_146 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_145, x_4);
return x_146;
}
else
{
lean_object* x_147; 
lean_dec(x_143);
lean_inc_ref(x_3);
x_147 = l_Lean_Expr_ReplaceLevelImpl_cache(x_8, x_3, x_3, x_4);
return x_147;
}
}
default: 
{
lean_object* x_148; 
lean_dec_ref(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_4);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_149 = lean_array_uget(x_6, x_8);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_4);
return x_150;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0(void) {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = lean_usize_once(&l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0, &l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0);
x_2 = lean_usize_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr));
x_2 = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4);
x_2 = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5);
x_2 = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6, &l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6_once, _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_usize_once(&l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0, &l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once, _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0);
x_4 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_5 = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_14; size_t x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_7 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_4);
lean_inc_ref(x_5);
x_8 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_5);
x_14 = lean_ptr_addr(x_4);
x_15 = lean_ptr_addr(x_7);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
x_9 = x_16;
goto block_13;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_5);
x_18 = lean_ptr_addr(x_8);
x_19 = lean_usize_dec_eq(x_17, x_18);
x_9 = x_19;
goto block_13;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_3);
lean_dec_ref(x_2);
x_10 = l_Lean_Expr_forallE___override(x_3, x_7, x_8, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Lean_instBEqBinderInfo_beq(x_6, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_3);
lean_dec_ref(x_2);
x_12 = l_Lean_Expr_forallE___override(x_3, x_7, x_8, x_6);
return x_12;
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_2;
}
}
}
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; size_t x_31; size_t x_32; uint8_t x_33; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
x_24 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_21);
lean_inc_ref(x_22);
x_25 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_22);
x_31 = lean_ptr_addr(x_21);
x_32 = lean_ptr_addr(x_24);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
x_26 = x_33;
goto block_30;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_22);
x_35 = lean_ptr_addr(x_25);
x_36 = lean_usize_dec_eq(x_34, x_35);
x_26 = x_36;
goto block_30;
}
block_30:
{
if (x_26 == 0)
{
lean_object* x_27; 
lean_inc(x_20);
lean_dec_ref(x_2);
x_27 = l_Lean_Expr_lam___override(x_20, x_24, x_25, x_23);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Lean_instBEqBinderInfo_beq(x_23, x_23);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc(x_20);
lean_dec_ref(x_2);
x_29 = l_Lean_Expr_lam___override(x_20, x_24, x_25, x_23);
return x_29;
}
else
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_38);
x_39 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_38);
x_40 = lean_ptr_addr(x_38);
x_41 = lean_ptr_addr(x_39);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_37);
lean_dec_ref(x_2);
x_43 = l_Lean_Expr_mdata___override(x_37, x_39);
return x_43;
}
else
{
lean_dec_ref(x_39);
return x_2;
}
}
case 8:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; size_t x_59; size_t x_60; uint8_t x_61; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 2);
x_47 = lean_ctor_get(x_2, 3);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc_ref(x_45);
lean_inc_ref(x_1);
x_49 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_45);
lean_inc_ref(x_46);
lean_inc_ref(x_1);
x_50 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_46);
lean_inc_ref(x_47);
x_51 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_47);
x_59 = lean_ptr_addr(x_45);
x_60 = lean_ptr_addr(x_49);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
x_52 = x_61;
goto block_58;
}
else
{
size_t x_62; size_t x_63; uint8_t x_64; 
x_62 = lean_ptr_addr(x_46);
x_63 = lean_ptr_addr(x_50);
x_64 = lean_usize_dec_eq(x_62, x_63);
x_52 = x_64;
goto block_58;
}
block_58:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_44);
lean_dec_ref(x_2);
x_53 = l_Lean_Expr_letE___override(x_44, x_49, x_50, x_51, x_48);
return x_53;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = lean_ptr_addr(x_47);
x_55 = lean_ptr_addr(x_51);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_inc(x_44);
lean_dec_ref(x_2);
x_57 = l_Lean_Expr_letE___override(x_44, x_49, x_50, x_51, x_48);
return x_57;
}
else
{
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
return x_2;
}
}
}
}
case 5:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; size_t x_72; size_t x_73; uint8_t x_74; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_65);
lean_inc_ref(x_1);
x_67 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_65);
lean_inc_ref(x_66);
x_68 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_66);
x_72 = lean_ptr_addr(x_65);
x_73 = lean_ptr_addr(x_67);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
x_69 = x_74;
goto block_71;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = lean_ptr_addr(x_66);
x_76 = lean_ptr_addr(x_68);
x_77 = lean_usize_dec_eq(x_75, x_76);
x_69 = x_77;
goto block_71;
}
block_71:
{
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec_ref(x_2);
x_70 = l_Lean_Expr_app___override(x_67, x_68);
return x_70;
}
else
{
lean_dec_ref(x_68);
lean_dec_ref(x_67);
return x_2;
}
}
}
case 11:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
x_80 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_80);
x_81 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_80);
x_82 = lean_ptr_addr(x_80);
x_83 = lean_ptr_addr(x_81);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_inc(x_79);
lean_inc(x_78);
lean_dec_ref(x_2);
x_85 = l_Lean_Expr_proj___override(x_78, x_79, x_81);
return x_85;
}
else
{
lean_dec_ref(x_81);
return x_2;
}
}
case 3:
{
lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
x_87 = l_Lean_Level_replace(x_1, x_86);
x_88 = lean_ptr_addr(x_86);
x_89 = lean_ptr_addr(x_87);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec_ref(x_2);
x_91 = l_Lean_Expr_sort___override(x_87);
return x_91;
}
else
{
lean_dec(x_87);
return x_2;
}
}
case 4:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_2, 0);
x_93 = lean_ctor_get(x_2, 1);
x_94 = lean_box(0);
lean_inc(x_93);
x_95 = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_93, x_94);
x_96 = l_ptrEqList___redArg(x_93, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_inc(x_92);
lean_dec_ref(x_2);
x_97 = l_Lean_Expr_const___override(x_92, x_95);
return x_97;
}
else
{
lean_dec(x_95);
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
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
