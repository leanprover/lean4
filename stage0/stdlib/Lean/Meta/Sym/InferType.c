// Lean compiler output
// Module: Lean.Meta.Sym.InferType
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_keyedConfig_7_; uint8_t v_trackZetaDelta_8_; lean_object* v_zetaDeltaSet_9_; lean_object* v_lctx_10_; lean_object* v_localInstances_11_; lean_object* v_defEqCtx_x3f_12_; lean_object* v_synthPendingDepth_13_; lean_object* v_canUnfold_x3f_14_; uint8_t v_univApprox_15_; uint8_t v_inTypeClassResolution_16_; uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_keyedConfig_7_ = lean_ctor_get(v_a_2_, 0);
v_trackZetaDelta_8_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7);
v_zetaDeltaSet_9_ = lean_ctor_get(v_a_2_, 1);
v_lctx_10_ = lean_ctor_get(v_a_2_, 2);
v_localInstances_11_ = lean_ctor_get(v_a_2_, 3);
v_defEqCtx_x3f_12_ = lean_ctor_get(v_a_2_, 4);
v_synthPendingDepth_13_ = lean_ctor_get(v_a_2_, 5);
v_canUnfold_x3f_14_ = lean_ctor_get(v_a_2_, 6);
v_univApprox_15_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_16_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 2);
v___x_17_ = 0;
lean_inc(v_canUnfold_x3f_14_);
lean_inc(v_synthPendingDepth_13_);
lean_inc(v_defEqCtx_x3f_12_);
lean_inc_ref(v_localInstances_11_);
lean_inc_ref(v_lctx_10_);
lean_inc(v_zetaDeltaSet_9_);
lean_inc_ref(v_keyedConfig_7_);
v___x_18_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_18_, 0, v_keyedConfig_7_);
lean_ctor_set(v___x_18_, 1, v_zetaDeltaSet_9_);
lean_ctor_set(v___x_18_, 2, v_lctx_10_);
lean_ctor_set(v___x_18_, 3, v_localInstances_11_);
lean_ctor_set(v___x_18_, 4, v_defEqCtx_x3f_12_);
lean_ctor_set(v___x_18_, 5, v_synthPendingDepth_13_);
lean_ctor_set(v___x_18_, 6, v_canUnfold_x3f_14_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*7, v_trackZetaDelta_8_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*7 + 1, v_univApprox_15_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*7 + 2, v_inTypeClassResolution_16_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*7 + 3, v___x_17_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_19_ = lean_infer_type(v_e_1_, v___x_18_, v_a_3_, v_a_4_, v_a_5_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache___boxed(lean_object* v_e_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(lean_object* v_type_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_keyedConfig_33_; uint8_t v_trackZetaDelta_34_; lean_object* v_zetaDeltaSet_35_; lean_object* v_lctx_36_; lean_object* v_localInstances_37_; lean_object* v_defEqCtx_x3f_38_; lean_object* v_synthPendingDepth_39_; lean_object* v_canUnfold_x3f_40_; uint8_t v_univApprox_41_; uint8_t v_inTypeClassResolution_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_keyedConfig_33_ = lean_ctor_get(v_a_28_, 0);
v_trackZetaDelta_34_ = lean_ctor_get_uint8(v_a_28_, sizeof(void*)*7);
v_zetaDeltaSet_35_ = lean_ctor_get(v_a_28_, 1);
v_lctx_36_ = lean_ctor_get(v_a_28_, 2);
v_localInstances_37_ = lean_ctor_get(v_a_28_, 3);
v_defEqCtx_x3f_38_ = lean_ctor_get(v_a_28_, 4);
v_synthPendingDepth_39_ = lean_ctor_get(v_a_28_, 5);
v_canUnfold_x3f_40_ = lean_ctor_get(v_a_28_, 6);
v_univApprox_41_ = lean_ctor_get_uint8(v_a_28_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_42_ = lean_ctor_get_uint8(v_a_28_, sizeof(void*)*7 + 2);
v___x_43_ = 0;
lean_inc(v_canUnfold_x3f_40_);
lean_inc(v_synthPendingDepth_39_);
lean_inc(v_defEqCtx_x3f_38_);
lean_inc_ref(v_localInstances_37_);
lean_inc_ref(v_lctx_36_);
lean_inc(v_zetaDeltaSet_35_);
lean_inc_ref(v_keyedConfig_33_);
v___x_44_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_44_, 0, v_keyedConfig_33_);
lean_ctor_set(v___x_44_, 1, v_zetaDeltaSet_35_);
lean_ctor_set(v___x_44_, 2, v_lctx_36_);
lean_ctor_set(v___x_44_, 3, v_localInstances_37_);
lean_ctor_set(v___x_44_, 4, v_defEqCtx_x3f_38_);
lean_ctor_set(v___x_44_, 5, v_synthPendingDepth_39_);
lean_ctor_set(v___x_44_, 6, v_canUnfold_x3f_40_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*7, v_trackZetaDelta_34_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*7 + 1, v_univApprox_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*7 + 2, v_inTypeClassResolution_42_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*7 + 3, v___x_43_);
v___x_45_ = l_Lean_Meta_getLevel(v_type_27_, v___x_44_, v_a_29_, v_a_30_, v_a_31_);
lean_dec_ref(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache___boxed(lean_object* v_type_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_53_, lean_object* v_vals_54_, lean_object* v_i_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_get_size(v_keys_53_);
v___x_58_ = lean_nat_dec_lt(v_i_55_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
lean_dec(v_i_55_);
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
lean_object* v_k_x27_60_; uint8_t v___x_61_; 
v_k_x27_60_ = lean_array_fget_borrowed(v_keys_53_, v_i_55_);
v___x_61_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_56_, v_k_x27_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_i_55_, v___x_62_);
lean_dec(v_i_55_);
v_i_55_ = v___x_63_;
goto _start;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_array_fget_borrowed(v_vals_54_, v_i_55_);
lean_dec(v_i_55_);
lean_inc(v___x_65_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_67_, lean_object* v_vals_68_, lean_object* v_i_69_, lean_object* v_k_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_67_, v_vals_68_, v_i_69_, v_k_70_);
lean_dec_ref(v_k_70_);
lean_dec_ref(v_vals_68_);
lean_dec_ref(v_keys_67_);
return v_res_71_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; 
v___x_72_ = ((size_t)5ULL);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_shift_left(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; 
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0);
v___x_77_ = lean_usize_sub(v___x_76_, v___x_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(lean_object* v_x_78_, size_t v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v_es_81_; lean_object* v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v_j_86_; lean_object* v___x_87_; 
v_es_81_ = lean_ctor_get(v_x_78_, 0);
v___x_82_ = lean_box(2);
v___x_83_ = ((size_t)5ULL);
v___x_84_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
v___x_85_ = lean_usize_land(v_x_79_, v___x_84_);
v_j_86_ = lean_usize_to_nat(v___x_85_);
v___x_87_ = lean_array_get_borrowed(v___x_82_, v_es_81_, v_j_86_);
lean_dec(v_j_86_);
switch(lean_obj_tag(v___x_87_))
{
case 0:
{
lean_object* v_key_88_; lean_object* v_val_89_; uint8_t v___x_90_; 
v_key_88_ = lean_ctor_get(v___x_87_, 0);
v_val_89_ = lean_ctor_get(v___x_87_, 1);
v___x_90_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_80_, v_key_88_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v___x_92_; 
lean_inc(v_val_89_);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v_val_89_);
return v___x_92_;
}
}
case 1:
{
lean_object* v_node_93_; size_t v___x_94_; 
v_node_93_ = lean_ctor_get(v___x_87_, 0);
v___x_94_ = lean_usize_shift_right(v_x_79_, v___x_83_);
v_x_78_ = v_node_93_;
v_x_79_ = v___x_94_;
goto _start;
}
default: 
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
else
{
lean_object* v_ks_97_; lean_object* v_vs_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_ks_97_ = lean_ctor_get(v_x_78_, 0);
v_vs_98_ = lean_ctor_get(v_x_78_, 1);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_97_, v_vs_98_, v___x_99_, v_x_80_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
size_t v_x_2882__boxed_104_; lean_object* v_res_105_; 
v_x_2882__boxed_104_ = lean_unbox_usize(v_x_102_);
lean_dec(v_x_102_);
v_res_105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_101_, v_x_2882__boxed_104_, v_x_103_);
lean_dec_ref(v_x_103_);
lean_dec_ref(v_x_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint64_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___x_108_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_107_);
v___x_109_ = lean_uint64_to_usize(v___x_108_);
v___x_110_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_106_, v___x_109_, v_x_107_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_111_, v_x_112_);
lean_dec_ref(v_x_112_);
lean_dec_ref(v_x_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_ks_118_; lean_object* v_vs_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v_ks_118_ = lean_ctor_get(v_x_114_, 0);
v_vs_119_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v_x_114_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_vs_119_);
lean_inc(v_ks_118_);
lean_dec(v_x_114_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_array_get_size(v_ks_118_);
v___x_124_ = lean_nat_dec_lt(v_x_115_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_x_115_);
v___x_125_ = lean_array_push(v_ks_118_, v_x_116_);
v___x_126_ = lean_array_push(v_vs_119_, v_x_117_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_126_);
lean_ctor_set(v___x_121_, 0, v___x_125_);
v___x_128_ = v___x_121_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v_k_x27_130_; uint8_t v___x_131_; 
v_k_x27_130_ = lean_array_fget_borrowed(v_ks_118_, v_x_115_);
v___x_131_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_116_, v_k_x27_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_133_; 
if (v_isShared_122_ == 0)
{
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_ks_118_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_vs_119_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_x_115_, v___x_134_);
lean_dec(v_x_115_);
v_x_114_ = v___x_133_;
v_x_115_ = v___x_135_;
goto _start;
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = lean_array_fset(v_ks_118_, v_x_115_, v_x_116_);
v___x_139_ = lean_array_fset(v_vs_119_, v_x_115_, v_x_117_);
lean_dec(v_x_115_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_139_);
lean_ctor_set(v___x_121_, 0, v___x_138_);
v___x_141_ = v___x_121_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(lean_object* v_n_144_, lean_object* v_k_145_, lean_object* v_v_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_n_144_, v___x_147_, v_k_145_, v_v_146_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object* v_x_150_, size_t v_x_151_, size_t v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v_es_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; lean_object* v_j_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_es_155_ = lean_ctor_get(v_x_150_, 0);
v___x_156_ = ((size_t)5ULL);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
v___x_159_ = lean_usize_land(v_x_151_, v___x_158_);
v_j_160_ = lean_usize_to_nat(v___x_159_);
v___x_161_ = lean_array_get_size(v_es_155_);
v___x_162_ = lean_nat_dec_lt(v_j_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_dec(v_j_160_);
lean_dec(v_x_154_);
lean_dec_ref(v_x_153_);
return v_x_150_;
}
else
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_199_; 
lean_inc_ref(v_es_155_);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_x_150_, 0);
lean_dec(v_unused_200_);
v___x_164_ = v_x_150_;
v_isShared_165_ = v_isSharedCheck_199_;
goto v_resetjp_163_;
}
else
{
lean_dec(v_x_150_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_199_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_v_166_; lean_object* v___x_167_; lean_object* v_xs_x27_168_; lean_object* v___y_170_; 
v_v_166_ = lean_array_fget(v_es_155_, v_j_160_);
v___x_167_ = lean_box(0);
v_xs_x27_168_ = lean_array_fset(v_es_155_, v_j_160_, v___x_167_);
switch(lean_obj_tag(v_v_166_))
{
case 0:
{
lean_object* v_key_175_; lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_key_175_ = lean_ctor_get(v_v_166_, 0);
v_val_176_ = lean_ctor_get(v_v_166_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_v_166_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v_v_166_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_inc(v_key_175_);
lean_dec(v_v_166_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v___x_180_; 
v___x_180_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_153_, v_key_175_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_del_object(v___x_178_);
v___x_181_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_175_, v_val_176_, v_x_153_, v_x_154_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
v___y_170_ = v___x_182_;
goto v___jp_169_;
}
else
{
lean_object* v___x_184_; 
lean_dec(v_val_176_);
lean_dec(v_key_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_x_154_);
lean_ctor_set(v___x_178_, 0, v_x_153_);
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_x_153_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_x_154_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
v___y_170_ = v___x_184_;
goto v___jp_169_;
}
}
}
}
case 1:
{
lean_object* v_node_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v_node_187_ = lean_ctor_get(v_v_166_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_v_166_);
if (v_isSharedCheck_197_ == 0)
{
v___x_189_ = v_v_166_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_node_187_);
lean_dec(v_v_166_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_191_ = lean_usize_shift_right(v_x_151_, v___x_156_);
v___x_192_ = lean_usize_add(v_x_152_, v___x_157_);
v___x_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_187_, v___x_191_, v___x_192_, v_x_153_, v_x_154_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_193_);
v___x_195_ = v___x_189_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v___y_170_ = v___x_195_;
goto v___jp_169_;
}
}
}
default: 
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_x_153_);
lean_ctor_set(v___x_198_, 1, v_x_154_);
v___y_170_ = v___x_198_;
goto v___jp_169_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_array_fset(v_xs_x27_168_, v_j_160_, v___y_170_);
lean_dec(v_j_160_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_173_ = v___x_164_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
else
{
lean_object* v_ks_201_; lean_object* v_vs_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_222_; 
v_ks_201_ = lean_ctor_get(v_x_150_, 0);
v_vs_202_ = lean_ctor_get(v_x_150_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_222_ == 0)
{
v___x_204_ = v_x_150_;
v_isShared_205_ = v_isSharedCheck_222_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_vs_202_);
lean_inc(v_ks_201_);
lean_dec(v_x_150_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_222_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_ks_201_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_vs_202_);
v___x_207_ = v_reuseFailAlloc_221_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v_newNode_208_; uint8_t v___y_210_; size_t v___x_216_; uint8_t v___x_217_; 
v_newNode_208_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_207_, v_x_153_, v_x_154_);
v___x_216_ = ((size_t)7ULL);
v___x_217_ = lean_usize_dec_le(v___x_216_, v_x_152_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_208_);
v___x_219_ = lean_unsigned_to_nat(4u);
v___x_220_ = lean_nat_dec_lt(v___x_218_, v___x_219_);
lean_dec(v___x_218_);
v___y_210_ = v___x_220_;
goto v___jp_209_;
}
else
{
v___y_210_ = v___x_217_;
goto v___jp_209_;
}
v___jp_209_:
{
if (v___y_210_ == 0)
{
lean_object* v_ks_211_; lean_object* v_vs_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_ks_211_ = lean_ctor_get(v_newNode_208_, 0);
lean_inc_ref(v_ks_211_);
v_vs_212_ = lean_ctor_get(v_newNode_208_, 1);
lean_inc_ref(v_vs_212_);
lean_dec_ref(v_newNode_208_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
v___x_215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_152_, v_ks_211_, v_vs_212_, v___x_213_, v___x_214_);
lean_dec_ref(v_vs_212_);
lean_dec_ref(v_ks_211_);
return v___x_215_;
}
else
{
return v_newNode_208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t v_depth_223_, lean_object* v_keys_224_, lean_object* v_vals_225_, lean_object* v_i_226_, lean_object* v_entries_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_array_get_size(v_keys_224_);
v___x_229_ = lean_nat_dec_lt(v_i_226_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v_i_226_);
return v_entries_227_;
}
else
{
lean_object* v_k_230_; lean_object* v_v_231_; uint64_t v___x_232_; size_t v_h_233_; size_t v___x_234_; lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v_h_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_k_230_ = lean_array_fget_borrowed(v_keys_224_, v_i_226_);
v_v_231_ = lean_array_fget_borrowed(v_vals_225_, v_i_226_);
v___x_232_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_230_);
v_h_233_ = lean_uint64_to_usize(v___x_232_);
v___x_234_ = ((size_t)5ULL);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v_depth_223_, v___x_236_);
v___x_238_ = lean_usize_mul(v___x_234_, v___x_237_);
v_h_239_ = lean_usize_shift_right(v_h_233_, v___x_238_);
v___x_240_ = lean_nat_add(v_i_226_, v___x_235_);
lean_dec(v_i_226_);
lean_inc(v_v_231_);
lean_inc(v_k_230_);
v___x_241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_227_, v_h_239_, v_depth_223_, v_k_230_, v_v_231_);
v_i_226_ = v___x_240_;
v_entries_227_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_243_, lean_object* v_keys_244_, lean_object* v_vals_245_, lean_object* v_i_246_, lean_object* v_entries_247_){
_start:
{
size_t v_depth_boxed_248_; lean_object* v_res_249_; 
v_depth_boxed_248_ = lean_unbox_usize(v_depth_243_);
lean_dec(v_depth_243_);
v_res_249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_boxed_248_, v_keys_244_, v_vals_245_, v_i_246_, v_entries_247_);
lean_dec_ref(v_vals_245_);
lean_dec_ref(v_keys_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
size_t v_x_3029__boxed_255_; size_t v_x_3030__boxed_256_; lean_object* v_res_257_; 
v_x_3029__boxed_255_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_x_3030__boxed_256_ = lean_unbox_usize(v_x_252_);
lean_dec(v_x_252_);
v_res_257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_250_, v_x_3029__boxed_255_, v_x_3030__boxed_256_, v_x_253_, v_x_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
uint64_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_261_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_259_);
v___x_262_ = lean_uint64_to_usize(v___x_261_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_258_, v___x_262_, v___x_263_, v_x_259_, v_x_260_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_inferType_273_; lean_object* v___x_274_; 
v___x_272_ = lean_st_ref_get(v_a_266_);
v_inferType_273_ = lean_ctor_get(v___x_272_, 3);
lean_inc_ref(v_inferType_273_);
lean_dec(v___x_272_);
v___x_274_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_273_, v_e_265_);
lean_dec_ref(v_inferType_273_);
if (lean_obj_tag(v___x_274_) == 1)
{
lean_object* v_val_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_e_265_);
v_val_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_val_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 0);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_val_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v___x_274_);
lean_inc_ref(v_e_265_);
v___x_283_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_265_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v___x_283_);
v___x_285_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_284_, v_a_266_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_314_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_314_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_314_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_314_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v_share_291_; lean_object* v_maxFVar_292_; lean_object* v_proofInstInfo_293_; lean_object* v_inferType_294_; lean_object* v_getLevel_295_; lean_object* v_congrInfo_296_; lean_object* v_defEqI_297_; lean_object* v_extensions_298_; lean_object* v_issues_299_; lean_object* v_canon_300_; uint8_t v_debug_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_313_; 
v___x_290_ = lean_st_ref_take(v_a_266_);
v_share_291_ = lean_ctor_get(v___x_290_, 0);
v_maxFVar_292_ = lean_ctor_get(v___x_290_, 1);
v_proofInstInfo_293_ = lean_ctor_get(v___x_290_, 2);
v_inferType_294_ = lean_ctor_get(v___x_290_, 3);
v_getLevel_295_ = lean_ctor_get(v___x_290_, 4);
v_congrInfo_296_ = lean_ctor_get(v___x_290_, 5);
v_defEqI_297_ = lean_ctor_get(v___x_290_, 6);
v_extensions_298_ = lean_ctor_get(v___x_290_, 7);
v_issues_299_ = lean_ctor_get(v___x_290_, 8);
v_canon_300_ = lean_ctor_get(v___x_290_, 9);
v_debug_301_ = lean_ctor_get_uint8(v___x_290_, sizeof(void*)*10);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_313_ == 0)
{
v___x_303_ = v___x_290_;
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_canon_300_);
lean_inc(v_issues_299_);
lean_inc(v_extensions_298_);
lean_inc(v_defEqI_297_);
lean_inc(v_congrInfo_296_);
lean_inc(v_getLevel_295_);
lean_inc(v_inferType_294_);
lean_inc(v_proofInstInfo_293_);
lean_inc(v_maxFVar_292_);
lean_inc(v_share_291_);
lean_dec(v___x_290_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
lean_inc(v_a_286_);
v___x_305_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_294_, v_e_265_, v_a_286_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 3, v___x_305_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_share_291_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_maxFVar_292_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_proofInstInfo_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_getLevel_295_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_congrInfo_296_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_defEqI_297_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_extensions_298_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_issues_299_);
lean_ctor_set(v_reuseFailAlloc_312_, 9, v_canon_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*10, v_debug_301_);
v___x_307_ = v_reuseFailAlloc_312_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_st_ref_set(v_a_266_, v___x_307_);
if (v_isShared_289_ == 0)
{
v___x_310_ = v___x_288_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_286_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_265_);
return v___x_285_;
}
}
else
{
lean_dec_ref(v_e_265_);
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg___boxed(lean_object* v_e_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_Sym_inferType___redArg(v_e_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType(lean_object* v_e_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Sym_inferType___redArg(v_e_323_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_Sym_inferType(v_e_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object* v_00_u03b2_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object* v_00_u03b2_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(v_00_u03b2_345_, v_x_346_, v_x_347_);
lean_dec_ref(v_x_347_);
lean_dec_ref(v_x_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object* v_00_u03b2_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_x_350_, v_x_351_, v_x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object* v_00_u03b2_354_, lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_355_, v_x_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_3287__boxed_363_; lean_object* v_res_364_; 
v_x_3287__boxed_363_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_359_, v_x_360_, v_x_3287__boxed_363_, v_x_362_);
lean_dec_ref(v_x_362_);
lean_dec_ref(v_x_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, size_t v_x_367_, size_t v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_366_, v_x_367_, v_x_368_, v_x_369_, v_x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_3298__boxed_378_; size_t v_x_3299__boxed_379_; lean_object* v_res_380_; 
v_x_3298__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_x_3299__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_res_380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_372_, v_x_373_, v_x_3298__boxed_378_, v_x_3299__boxed_379_, v_x_376_, v_x_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_381_, lean_object* v_keys_382_, lean_object* v_vals_383_, lean_object* v_heq_384_, lean_object* v_i_385_, lean_object* v_k_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_382_, v_vals_383_, v_i_385_, v_k_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_388_, lean_object* v_keys_389_, lean_object* v_vals_390_, lean_object* v_heq_391_, lean_object* v_i_392_, lean_object* v_k_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_388_, v_keys_389_, v_vals_390_, v_heq_391_, v_i_392_, v_k_393_);
lean_dec_ref(v_k_393_);
lean_dec_ref(v_vals_390_);
lean_dec_ref(v_keys_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_395_, lean_object* v_n_396_, lean_object* v_k_397_, lean_object* v_v_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_396_, v_k_397_, v_v_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_400_, size_t v_depth_401_, lean_object* v_keys_402_, lean_object* v_vals_403_, lean_object* v_heq_404_, lean_object* v_i_405_, lean_object* v_entries_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_401_, v_keys_402_, v_vals_403_, v_i_405_, v_entries_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_408_, lean_object* v_depth_409_, lean_object* v_keys_410_, lean_object* v_vals_411_, lean_object* v_heq_412_, lean_object* v_i_413_, lean_object* v_entries_414_){
_start:
{
size_t v_depth_boxed_415_; lean_object* v_res_416_; 
v_depth_boxed_415_ = lean_unbox_usize(v_depth_409_);
lean_dec(v_depth_409_);
v_res_416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_408_, v_depth_boxed_415_, v_keys_410_, v_vals_411_, v_heq_412_, v_i_413_, v_entries_414_);
lean_dec_ref(v_vals_411_);
lean_dec_ref(v_keys_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_418_, v_x_419_, v_x_420_, v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object* v_type_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_getLevel_431_; lean_object* v___x_432_; 
v___x_430_ = lean_st_ref_get(v_a_424_);
v_getLevel_431_ = lean_ctor_get(v___x_430_, 4);
lean_inc_ref(v_getLevel_431_);
lean_dec(v___x_430_);
v___x_432_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_431_, v_type_423_);
lean_dec_ref(v_getLevel_431_);
if (lean_obj_tag(v___x_432_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v_type_423_);
v_val_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_val_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set_tag(v___x_435_, 0);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_val_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v___x_432_);
lean_inc_ref(v_type_423_);
v___x_441_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_423_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_470_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_470_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_470_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_470_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v_share_447_; lean_object* v_maxFVar_448_; lean_object* v_proofInstInfo_449_; lean_object* v_inferType_450_; lean_object* v_getLevel_451_; lean_object* v_congrInfo_452_; lean_object* v_defEqI_453_; lean_object* v_extensions_454_; lean_object* v_issues_455_; lean_object* v_canon_456_; uint8_t v_debug_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
v___x_446_ = lean_st_ref_take(v_a_424_);
v_share_447_ = lean_ctor_get(v___x_446_, 0);
v_maxFVar_448_ = lean_ctor_get(v___x_446_, 1);
v_proofInstInfo_449_ = lean_ctor_get(v___x_446_, 2);
v_inferType_450_ = lean_ctor_get(v___x_446_, 3);
v_getLevel_451_ = lean_ctor_get(v___x_446_, 4);
v_congrInfo_452_ = lean_ctor_get(v___x_446_, 5);
v_defEqI_453_ = lean_ctor_get(v___x_446_, 6);
v_extensions_454_ = lean_ctor_get(v___x_446_, 7);
v_issues_455_ = lean_ctor_get(v___x_446_, 8);
v_canon_456_ = lean_ctor_get(v___x_446_, 9);
v_debug_457_ = lean_ctor_get_uint8(v___x_446_, sizeof(void*)*10);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_469_ == 0)
{
v___x_459_ = v___x_446_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_canon_456_);
lean_inc(v_issues_455_);
lean_inc(v_extensions_454_);
lean_inc(v_defEqI_453_);
lean_inc(v_congrInfo_452_);
lean_inc(v_getLevel_451_);
lean_inc(v_inferType_450_);
lean_inc(v_proofInstInfo_449_);
lean_inc(v_maxFVar_448_);
lean_inc(v_share_447_);
lean_dec(v___x_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_inc(v_a_442_);
v___x_461_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_451_, v_type_423_, v_a_442_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 4, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_share_447_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_maxFVar_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_proofInstInfo_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_inferType_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_congrInfo_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_defEqI_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_extensions_454_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_issues_455_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_canon_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*10, v_debug_457_);
v___x_463_ = v_reuseFailAlloc_468_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_st_ref_set(v_a_424_, v___x_463_);
if (v_isShared_445_ == 0)
{
v___x_466_ = v___x_444_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_442_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_423_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object* v_type_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel(lean_object* v_type_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_479_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object* v_type_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_Sym_getLevel(v_type_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object* v_e_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; 
lean_inc_ref(v_e_502_);
v___x_509_ = l_Lean_Meta_Sym_inferType___redArg(v_e_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_n(v_a_510_, 2);
lean_dec_ref(v___x_509_);
v___x_511_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_510_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_524_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_524_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_516_ = ((lean_object*)(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2));
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_512_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_mkConst(v___x_516_, v___x_518_);
v___x_520_ = l_Lean_mkAppB(v___x_519_, v_a_510_, v_e_502_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_520_);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_510_);
lean_dec_ref(v_e_502_);
v_a_525_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_511_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_511_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_dec_ref(v_e_502_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___boxed(lean_object* v_e_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object* v_e_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_541_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object* v_e_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_Sym_mkEqRefl(v_e_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_558_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_InferType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_InferType(builtin);
}
#ifdef __cplusplus
}
#endif
