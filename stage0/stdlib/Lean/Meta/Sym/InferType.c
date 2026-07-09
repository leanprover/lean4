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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_mkEqRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_mkEqRefl___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkEqRefl___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_mkEqRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Sym_mkEqRefl___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkEqRefl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_mkEqRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_mkEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_mkEqRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_mkEqRefl___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_mkEqRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Sym_mkEqRefl___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_mkEqRefl___closed__2_value;
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
lean_dec_ref_known(v___x_44_, 7);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(lean_object* v_x_72_, size_t v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v_es_75_; lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_j_79_; lean_object* v___x_80_; 
v_es_75_ = lean_ctor_get(v_x_72_, 0);
v___x_76_ = lean_box(2);
v___x_77_ = ((size_t)31ULL);
v___x_78_ = lean_usize_land(v_x_73_, v___x_77_);
v_j_79_ = lean_usize_to_nat(v___x_78_);
v___x_80_ = lean_array_get_borrowed(v___x_76_, v_es_75_, v_j_79_);
lean_dec(v_j_79_);
switch(lean_obj_tag(v___x_80_))
{
case 0:
{
lean_object* v_key_81_; lean_object* v_val_82_; uint8_t v___x_83_; 
v_key_81_ = lean_ctor_get(v___x_80_, 0);
v_val_82_ = lean_ctor_get(v___x_80_, 1);
v___x_83_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_74_, v_key_81_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
lean_inc(v_val_82_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_val_82_);
return v___x_85_;
}
}
case 1:
{
lean_object* v_node_86_; size_t v___x_87_; size_t v___x_88_; 
v_node_86_ = lean_ctor_get(v___x_80_, 0);
v___x_87_ = ((size_t)5ULL);
v___x_88_ = lean_usize_shift_right(v_x_73_, v___x_87_);
v_x_72_ = v_node_86_;
v_x_73_ = v___x_88_;
goto _start;
}
default: 
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
}
else
{
lean_object* v_ks_91_; lean_object* v_vs_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_ks_91_ = lean_ctor_get(v_x_72_, 0);
v_vs_92_ = lean_ctor_get(v_x_72_, 1);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_91_, v_vs_92_, v___x_93_, v_x_74_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
size_t v_x_2862__boxed_98_; lean_object* v_res_99_; 
v_x_2862__boxed_98_ = lean_unbox_usize(v_x_96_);
lean_dec(v_x_96_);
v_res_99_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_95_, v_x_2862__boxed_98_, v_x_97_);
lean_dec_ref(v_x_97_);
lean_dec_ref(v_x_95_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint64_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
v___x_102_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_101_);
v___x_103_ = lean_uint64_to_usize(v___x_102_);
v___x_104_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_100_, v___x_103_, v_x_101_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_105_, v_x_106_);
lean_dec_ref(v_x_106_);
lean_dec_ref(v_x_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_ks_112_; lean_object* v_vs_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_137_; 
v_ks_112_ = lean_ctor_get(v_x_108_, 0);
v_vs_113_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_137_ == 0)
{
v___x_115_ = v_x_108_;
v_isShared_116_ = v_isSharedCheck_137_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_vs_113_);
lean_inc(v_ks_112_);
lean_dec(v_x_108_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_137_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_array_get_size(v_ks_112_);
v___x_118_ = lean_nat_dec_lt(v_x_109_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
lean_dec(v_x_109_);
v___x_119_ = lean_array_push(v_ks_112_, v_x_110_);
v___x_120_ = lean_array_push(v_vs_113_, v_x_111_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_120_);
lean_ctor_set(v___x_115_, 0, v___x_119_);
v___x_122_ = v___x_115_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
else
{
lean_object* v_k_x27_124_; uint8_t v___x_125_; 
v_k_x27_124_ = lean_array_fget_borrowed(v_ks_112_, v_x_109_);
v___x_125_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_110_, v_k_x27_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_127_; 
if (v_isShared_116_ == 0)
{
v___x_127_ = v___x_115_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_ks_112_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_vs_113_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_x_109_, v___x_128_);
lean_dec(v_x_109_);
v_x_108_ = v___x_127_;
v_x_109_ = v___x_129_;
goto _start;
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = lean_array_fset(v_ks_112_, v_x_109_, v_x_110_);
v___x_133_ = lean_array_fset(v_vs_113_, v_x_109_, v_x_111_);
lean_dec(v_x_109_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_133_);
lean_ctor_set(v___x_115_, 0, v___x_132_);
v___x_135_ = v___x_115_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(lean_object* v_n_138_, lean_object* v_k_139_, lean_object* v_v_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_n_138_, v___x_141_, v_k_139_, v_v_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object* v_x_144_, size_t v_x_145_, size_t v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v_es_149_; size_t v___x_150_; size_t v___x_151_; lean_object* v_j_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_es_149_ = lean_ctor_get(v_x_144_, 0);
v___x_150_ = ((size_t)31ULL);
v___x_151_ = lean_usize_land(v_x_145_, v___x_150_);
v_j_152_ = lean_usize_to_nat(v___x_151_);
v___x_153_ = lean_array_get_size(v_es_149_);
v___x_154_ = lean_nat_dec_lt(v_j_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_j_152_);
lean_dec(v_x_148_);
lean_dec_ref(v_x_147_);
return v_x_144_;
}
else
{
lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_193_; 
lean_inc_ref(v_es_149_);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v_x_144_, 0);
lean_dec(v_unused_194_);
v___x_156_ = v_x_144_;
v_isShared_157_ = v_isSharedCheck_193_;
goto v_resetjp_155_;
}
else
{
lean_dec(v_x_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_193_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_v_158_; lean_object* v___x_159_; lean_object* v_xs_x27_160_; lean_object* v___y_162_; 
v_v_158_ = lean_array_fget(v_es_149_, v_j_152_);
v___x_159_ = lean_box(0);
v_xs_x27_160_ = lean_array_fset(v_es_149_, v_j_152_, v___x_159_);
switch(lean_obj_tag(v_v_158_))
{
case 0:
{
lean_object* v_key_167_; lean_object* v_val_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_178_; 
v_key_167_ = lean_ctor_get(v_v_158_, 0);
v_val_168_ = lean_ctor_get(v_v_158_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_v_158_);
if (v_isSharedCheck_178_ == 0)
{
v___x_170_ = v_v_158_;
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_val_168_);
lean_inc(v_key_167_);
lean_dec(v_v_158_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___x_172_; 
v___x_172_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_147_, v_key_167_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_del_object(v___x_170_);
v___x_173_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_167_, v_val_168_, v_x_147_, v_x_148_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
v___y_162_ = v___x_174_;
goto v___jp_161_;
}
else
{
lean_object* v___x_176_; 
lean_dec(v_val_168_);
lean_dec(v_key_167_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v_x_148_);
lean_ctor_set(v___x_170_, 0, v_x_147_);
v___x_176_ = v___x_170_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_x_147_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_x_148_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
v___y_162_ = v___x_176_;
goto v___jp_161_;
}
}
}
}
case 1:
{
lean_object* v_node_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_191_; 
v_node_179_ = lean_ctor_get(v_v_158_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_v_158_);
if (v_isSharedCheck_191_ == 0)
{
v___x_181_ = v_v_158_;
v_isShared_182_ = v_isSharedCheck_191_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_node_179_);
lean_dec(v_v_158_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_191_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_usize_shift_right(v_x_145_, v___x_183_);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_x_146_, v___x_185_);
v___x_187_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_179_, v___x_184_, v___x_186_, v_x_147_, v_x_148_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_187_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v___y_162_ = v___x_189_;
goto v___jp_161_;
}
}
}
default: 
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_x_147_);
lean_ctor_set(v___x_192_, 1, v_x_148_);
v___y_162_ = v___x_192_;
goto v___jp_161_;
}
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_array_fset(v_xs_x27_160_, v_j_152_, v___y_162_);
lean_dec(v_j_152_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_163_);
v___x_165_ = v___x_156_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
else
{
lean_object* v_ks_195_; lean_object* v_vs_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_216_; 
v_ks_195_ = lean_ctor_get(v_x_144_, 0);
v_vs_196_ = lean_ctor_get(v_x_144_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_216_ == 0)
{
v___x_198_ = v_x_144_;
v_isShared_199_ = v_isSharedCheck_216_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_vs_196_);
lean_inc(v_ks_195_);
lean_dec(v_x_144_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_216_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_ks_195_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_vs_196_);
v___x_201_ = v_reuseFailAlloc_215_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v_newNode_202_; uint8_t v___y_204_; size_t v___x_210_; uint8_t v___x_211_; 
v_newNode_202_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_201_, v_x_147_, v_x_148_);
v___x_210_ = ((size_t)7ULL);
v___x_211_ = lean_usize_dec_le(v___x_210_, v_x_146_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_212_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_202_);
v___x_213_ = lean_unsigned_to_nat(4u);
v___x_214_ = lean_nat_dec_lt(v___x_212_, v___x_213_);
lean_dec(v___x_212_);
v___y_204_ = v___x_214_;
goto v___jp_203_;
}
else
{
v___y_204_ = v___x_211_;
goto v___jp_203_;
}
v___jp_203_:
{
if (v___y_204_ == 0)
{
lean_object* v_ks_205_; lean_object* v_vs_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_ks_205_ = lean_ctor_get(v_newNode_202_, 0);
lean_inc_ref(v_ks_205_);
v_vs_206_ = lean_ctor_get(v_newNode_202_, 1);
lean_inc_ref(v_vs_206_);
lean_dec_ref(v_newNode_202_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
v___x_209_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_146_, v_ks_205_, v_vs_206_, v___x_207_, v___x_208_);
lean_dec_ref(v_vs_206_);
lean_dec_ref(v_ks_205_);
return v___x_209_;
}
else
{
return v_newNode_202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t v_depth_217_, lean_object* v_keys_218_, lean_object* v_vals_219_, lean_object* v_i_220_, lean_object* v_entries_221_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_array_get_size(v_keys_218_);
v___x_223_ = lean_nat_dec_lt(v_i_220_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v_i_220_);
return v_entries_221_;
}
else
{
lean_object* v_k_224_; lean_object* v_v_225_; uint64_t v___x_226_; size_t v_h_227_; size_t v___x_228_; lean_object* v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v_h_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_k_224_ = lean_array_fget_borrowed(v_keys_218_, v_i_220_);
v_v_225_ = lean_array_fget_borrowed(v_vals_219_, v_i_220_);
v___x_226_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_224_);
v_h_227_ = lean_uint64_to_usize(v___x_226_);
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_sub(v_depth_217_, v___x_230_);
v___x_232_ = lean_usize_mul(v___x_228_, v___x_231_);
v_h_233_ = lean_usize_shift_right(v_h_227_, v___x_232_);
v___x_234_ = lean_nat_add(v_i_220_, v___x_229_);
lean_dec(v_i_220_);
lean_inc(v_v_225_);
lean_inc(v_k_224_);
v___x_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_221_, v_h_233_, v_depth_217_, v_k_224_, v_v_225_);
v_i_220_ = v___x_234_;
v_entries_221_ = v___x_235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_237_, lean_object* v_keys_238_, lean_object* v_vals_239_, lean_object* v_i_240_, lean_object* v_entries_241_){
_start:
{
size_t v_depth_boxed_242_; lean_object* v_res_243_; 
v_depth_boxed_242_ = lean_unbox_usize(v_depth_237_);
lean_dec(v_depth_237_);
v_res_243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_boxed_242_, v_keys_238_, v_vals_239_, v_i_240_, v_entries_241_);
lean_dec_ref(v_vals_239_);
lean_dec_ref(v_keys_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
size_t v_x_2997__boxed_249_; size_t v_x_2998__boxed_250_; lean_object* v_res_251_; 
v_x_2997__boxed_249_ = lean_unbox_usize(v_x_245_);
lean_dec(v_x_245_);
v_x_2998__boxed_250_ = lean_unbox_usize(v_x_246_);
lean_dec(v_x_246_);
v_res_251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_244_, v_x_2997__boxed_249_, v_x_2998__boxed_250_, v_x_247_, v_x_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
uint64_t v___x_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; 
v___x_255_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_253_);
v___x_256_ = lean_uint64_to_usize(v___x_255_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_252_, v___x_256_, v___x_257_, v_x_253_, v_x_254_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType(lean_object* v_e_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_inferType_268_; lean_object* v___x_269_; 
v___x_267_ = lean_st_ref_get(v_a_261_);
v_inferType_268_ = lean_ctor_get(v___x_267_, 3);
lean_inc_ref(v_inferType_268_);
lean_dec(v___x_267_);
v___x_269_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_268_, v_e_259_);
lean_dec_ref(v_inferType_268_);
if (lean_obj_tag(v___x_269_) == 1)
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_e_259_);
v_val_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_val_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v___x_278_; 
lean_dec(v___x_269_);
lean_inc_ref(v_e_259_);
v___x_278_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_259_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = l_Lean_Meta_Sym_shareCommonInc(v_a_279_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_309_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_309_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_309_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_309_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v_share_286_; lean_object* v_maxFVar_287_; lean_object* v_proofInstInfo_288_; lean_object* v_inferType_289_; lean_object* v_getLevel_290_; lean_object* v_congrInfo_291_; lean_object* v_defEqI_292_; lean_object* v_extensions_293_; lean_object* v_issues_294_; lean_object* v_canon_295_; uint8_t v_debug_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_308_; 
v___x_285_ = lean_st_ref_take(v_a_261_);
v_share_286_ = lean_ctor_get(v___x_285_, 0);
v_maxFVar_287_ = lean_ctor_get(v___x_285_, 1);
v_proofInstInfo_288_ = lean_ctor_get(v___x_285_, 2);
v_inferType_289_ = lean_ctor_get(v___x_285_, 3);
v_getLevel_290_ = lean_ctor_get(v___x_285_, 4);
v_congrInfo_291_ = lean_ctor_get(v___x_285_, 5);
v_defEqI_292_ = lean_ctor_get(v___x_285_, 6);
v_extensions_293_ = lean_ctor_get(v___x_285_, 7);
v_issues_294_ = lean_ctor_get(v___x_285_, 8);
v_canon_295_ = lean_ctor_get(v___x_285_, 9);
v_debug_296_ = lean_ctor_get_uint8(v___x_285_, sizeof(void*)*10);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_308_ == 0)
{
v___x_298_ = v___x_285_;
v_isShared_299_ = v_isSharedCheck_308_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_canon_295_);
lean_inc(v_issues_294_);
lean_inc(v_extensions_293_);
lean_inc(v_defEqI_292_);
lean_inc(v_congrInfo_291_);
lean_inc(v_getLevel_290_);
lean_inc(v_inferType_289_);
lean_inc(v_proofInstInfo_288_);
lean_inc(v_maxFVar_287_);
lean_inc(v_share_286_);
lean_dec(v___x_285_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_308_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_inc(v_a_281_);
v___x_300_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_289_, v_e_259_, v_a_281_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 3, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_share_286_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_maxFVar_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_proofInstInfo_288_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_getLevel_290_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_congrInfo_291_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_defEqI_292_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_extensions_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_issues_294_);
lean_ctor_set(v_reuseFailAlloc_307_, 9, v_canon_295_);
lean_ctor_set_uint8(v_reuseFailAlloc_307_, sizeof(void*)*10, v_debug_296_);
v___x_302_ = v_reuseFailAlloc_307_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_st_ref_set(v_a_261_, v___x_302_);
if (v_isShared_284_ == 0)
{
v___x_305_ = v___x_283_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_281_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_259_);
return v___x_280_;
}
}
else
{
lean_dec_ref(v_e_259_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object* v_e_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Meta_Sym_inferType(v_e_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_320_, v_x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(v_00_u03b2_323_, v_x_324_, v_x_325_);
lean_dec_ref(v_x_325_);
lean_dec_ref(v_x_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object* v_00_u03b2_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_x_328_, v_x_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object* v_00_u03b2_332_, lean_object* v_x_333_, size_t v_x_334_, lean_object* v_x_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_333_, v_x_334_, v_x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
size_t v_x_3250__boxed_341_; lean_object* v_res_342_; 
v_x_3250__boxed_341_ = lean_unbox_usize(v_x_339_);
lean_dec(v_x_339_);
v_res_342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_337_, v_x_338_, v_x_3250__boxed_341_, v_x_340_);
lean_dec_ref(v_x_340_);
lean_dec_ref(v_x_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object* v_00_u03b2_343_, lean_object* v_x_344_, size_t v_x_345_, size_t v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_344_, v_x_345_, v_x_346_, v_x_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
size_t v_x_3261__boxed_356_; size_t v_x_3262__boxed_357_; lean_object* v_res_358_; 
v_x_3261__boxed_356_ = lean_unbox_usize(v_x_352_);
lean_dec(v_x_352_);
v_x_3262__boxed_357_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_res_358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_350_, v_x_351_, v_x_3261__boxed_356_, v_x_3262__boxed_357_, v_x_354_, v_x_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_359_, lean_object* v_keys_360_, lean_object* v_vals_361_, lean_object* v_heq_362_, lean_object* v_i_363_, lean_object* v_k_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_360_, v_vals_361_, v_i_363_, v_k_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_366_, lean_object* v_keys_367_, lean_object* v_vals_368_, lean_object* v_heq_369_, lean_object* v_i_370_, lean_object* v_k_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_366_, v_keys_367_, v_vals_368_, v_heq_369_, v_i_370_, v_k_371_);
lean_dec_ref(v_k_371_);
lean_dec_ref(v_vals_368_);
lean_dec_ref(v_keys_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_373_, lean_object* v_n_374_, lean_object* v_k_375_, lean_object* v_v_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_374_, v_k_375_, v_v_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_378_, size_t v_depth_379_, lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_heq_382_, lean_object* v_i_383_, lean_object* v_entries_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_379_, v_keys_380_, v_vals_381_, v_i_383_, v_entries_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_386_, lean_object* v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_heq_390_, lean_object* v_i_391_, lean_object* v_entries_392_){
_start:
{
size_t v_depth_boxed_393_; lean_object* v_res_394_; 
v_depth_boxed_393_ = lean_unbox_usize(v_depth_387_);
lean_dec(v_depth_387_);
v_res_394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_386_, v_depth_boxed_393_, v_keys_388_, v_vals_389_, v_heq_390_, v_i_391_, v_entries_392_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_396_, v_x_397_, v_x_398_, v_x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object* v_type_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; lean_object* v_getLevel_409_; lean_object* v___x_410_; 
v___x_408_ = lean_st_ref_get(v_a_402_);
v_getLevel_409_ = lean_ctor_get(v___x_408_, 4);
lean_inc_ref(v_getLevel_409_);
lean_dec(v___x_408_);
v___x_410_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_409_, v_type_401_);
lean_dec_ref(v_getLevel_409_);
if (lean_obj_tag(v___x_410_) == 1)
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v_type_401_);
v_val_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 0);
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_val_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v___x_410_);
lean_inc_ref(v_type_401_);
v___x_419_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_401_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_448_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_448_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_448_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_448_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_share_425_; lean_object* v_maxFVar_426_; lean_object* v_proofInstInfo_427_; lean_object* v_inferType_428_; lean_object* v_getLevel_429_; lean_object* v_congrInfo_430_; lean_object* v_defEqI_431_; lean_object* v_extensions_432_; lean_object* v_issues_433_; lean_object* v_canon_434_; uint8_t v_debug_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_447_; 
v___x_424_ = lean_st_ref_take(v_a_402_);
v_share_425_ = lean_ctor_get(v___x_424_, 0);
v_maxFVar_426_ = lean_ctor_get(v___x_424_, 1);
v_proofInstInfo_427_ = lean_ctor_get(v___x_424_, 2);
v_inferType_428_ = lean_ctor_get(v___x_424_, 3);
v_getLevel_429_ = lean_ctor_get(v___x_424_, 4);
v_congrInfo_430_ = lean_ctor_get(v___x_424_, 5);
v_defEqI_431_ = lean_ctor_get(v___x_424_, 6);
v_extensions_432_ = lean_ctor_get(v___x_424_, 7);
v_issues_433_ = lean_ctor_get(v___x_424_, 8);
v_canon_434_ = lean_ctor_get(v___x_424_, 9);
v_debug_435_ = lean_ctor_get_uint8(v___x_424_, sizeof(void*)*10);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_447_ == 0)
{
v___x_437_ = v___x_424_;
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_canon_434_);
lean_inc(v_issues_433_);
lean_inc(v_extensions_432_);
lean_inc(v_defEqI_431_);
lean_inc(v_congrInfo_430_);
lean_inc(v_getLevel_429_);
lean_inc(v_inferType_428_);
lean_inc(v_proofInstInfo_427_);
lean_inc(v_maxFVar_426_);
lean_inc(v_share_425_);
lean_dec(v___x_424_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_inc(v_a_420_);
v___x_439_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_429_, v_type_401_, v_a_420_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 4, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_share_425_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_maxFVar_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_proofInstInfo_427_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_inferType_428_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v_congrInfo_430_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_defEqI_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_extensions_432_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v_issues_433_);
lean_ctor_set(v_reuseFailAlloc_446_, 9, v_canon_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_446_, sizeof(void*)*10, v_debug_435_);
v___x_441_ = v_reuseFailAlloc_446_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_st_ref_set(v_a_402_, v___x_441_);
if (v_isShared_423_ == 0)
{
v___x_444_ = v___x_422_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_420_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_401_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object* v_type_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel(lean_object* v_type_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_457_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object* v_type_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Sym_getLevel(v_type_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object* v_e_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
lean_inc_ref(v_e_480_);
v___x_488_ = l_Lean_Meta_Sym_inferType(v_e_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc_n(v_a_489_, 2);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_489_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_503_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_503_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_503_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_503_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_495_ = ((lean_object*)(l_Lean_Meta_Sym_mkEqRefl___closed__2));
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v_a_491_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = l_Lean_mkConst(v___x_495_, v___x_497_);
v___x_499_ = l_Lean_mkAppB(v___x_498_, v_a_489_, v_e_480_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_499_);
v___x_501_ = v___x_493_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec(v_a_489_);
lean_dec_ref(v_e_480_);
v_a_504_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_490_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_490_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_dec_ref(v_e_480_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object* v_e_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_Sym_mkEqRefl(v_e_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_520_;
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
