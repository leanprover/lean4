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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_keyedConfig_7_; uint8_t v_trackZetaDelta_8_; lean_object* v_zetaDeltaSet_9_; lean_object* v_lctx_10_; lean_object* v_localInstances_11_; lean_object* v_defEqCtx_x3f_12_; lean_object* v_synthPendingDepth_13_; lean_object* v_customCanUnfoldPredicate_x3f_14_; uint8_t v_univApprox_15_; uint8_t v_inTypeClassResolution_16_; uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_keyedConfig_7_ = lean_ctor_get(v_a_2_, 0);
v_trackZetaDelta_8_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7);
v_zetaDeltaSet_9_ = lean_ctor_get(v_a_2_, 1);
v_lctx_10_ = lean_ctor_get(v_a_2_, 2);
v_localInstances_11_ = lean_ctor_get(v_a_2_, 3);
v_defEqCtx_x3f_12_ = lean_ctor_get(v_a_2_, 4);
v_synthPendingDepth_13_ = lean_ctor_get(v_a_2_, 5);
v_customCanUnfoldPredicate_x3f_14_ = lean_ctor_get(v_a_2_, 6);
v_univApprox_15_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_16_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 2);
v___x_17_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_14_);
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
lean_ctor_set(v___x_18_, 6, v_customCanUnfoldPredicate_x3f_14_);
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
lean_object* v_keyedConfig_33_; uint8_t v_trackZetaDelta_34_; lean_object* v_zetaDeltaSet_35_; lean_object* v_lctx_36_; lean_object* v_localInstances_37_; lean_object* v_defEqCtx_x3f_38_; lean_object* v_synthPendingDepth_39_; lean_object* v_customCanUnfoldPredicate_x3f_40_; uint8_t v_univApprox_41_; uint8_t v_inTypeClassResolution_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_keyedConfig_33_ = lean_ctor_get(v_a_28_, 0);
v_trackZetaDelta_34_ = lean_ctor_get_uint8(v_a_28_, sizeof(void*)*7);
v_zetaDeltaSet_35_ = lean_ctor_get(v_a_28_, 1);
v_lctx_36_ = lean_ctor_get(v_a_28_, 2);
v_localInstances_37_ = lean_ctor_get(v_a_28_, 3);
v_defEqCtx_x3f_38_ = lean_ctor_get(v_a_28_, 4);
v_synthPendingDepth_39_ = lean_ctor_get(v_a_28_, 5);
v_customCanUnfoldPredicate_x3f_40_ = lean_ctor_get(v_a_28_, 6);
v_univApprox_41_ = lean_ctor_get_uint8(v_a_28_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_42_ = lean_ctor_get_uint8(v_a_28_, sizeof(void*)*7 + 2);
v___x_43_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_40_);
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
lean_ctor_set(v___x_44_, 6, v_customCanUnfoldPredicate_x3f_40_);
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
lean_object* v_k_x27_60_; size_t v___x_61_; size_t v___x_62_; uint8_t v___x_63_; 
v_k_x27_60_ = lean_array_fget_borrowed(v_keys_53_, v_i_55_);
v___x_61_ = lean_ptr_addr(v_k_56_);
v___x_62_ = lean_ptr_addr(v_k_x27_60_);
v___x_63_ = lean_usize_dec_eq(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_i_55_, v___x_64_);
lean_dec(v_i_55_);
v_i_55_ = v___x_65_;
goto _start;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_array_fget_borrowed(v_vals_54_, v_i_55_);
lean_dec(v_i_55_);
lean_inc(v___x_67_);
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_69_, lean_object* v_vals_70_, lean_object* v_i_71_, lean_object* v_k_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_69_, v_vals_70_, v_i_71_, v_k_72_);
lean_dec_ref(v_k_72_);
lean_dec_ref(v_vals_70_);
lean_dec_ref(v_keys_69_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(lean_object* v_x_74_, size_t v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_es_77_; lean_object* v___x_78_; size_t v___x_79_; size_t v___x_80_; lean_object* v_j_81_; lean_object* v___x_82_; 
v_es_77_ = lean_ctor_get(v_x_74_, 0);
v___x_78_ = lean_box(2);
v___x_79_ = ((size_t)31ULL);
v___x_80_ = lean_usize_land(v_x_75_, v___x_79_);
v_j_81_ = lean_usize_to_nat(v___x_80_);
v___x_82_ = lean_array_get_borrowed(v___x_78_, v_es_77_, v_j_81_);
lean_dec(v_j_81_);
switch(lean_obj_tag(v___x_82_))
{
case 0:
{
lean_object* v_key_83_; lean_object* v_val_84_; size_t v___x_85_; size_t v___x_86_; uint8_t v___x_87_; 
v_key_83_ = lean_ctor_get(v___x_82_, 0);
v_val_84_ = lean_ctor_get(v___x_82_, 1);
v___x_85_ = lean_ptr_addr(v_x_76_);
v___x_86_ = lean_ptr_addr(v_key_83_);
v___x_87_ = lean_usize_dec_eq(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
else
{
lean_object* v___x_89_; 
lean_inc(v_val_84_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_val_84_);
return v___x_89_;
}
}
case 1:
{
lean_object* v_node_90_; size_t v___x_91_; size_t v___x_92_; 
v_node_90_ = lean_ctor_get(v___x_82_, 0);
v___x_91_ = ((size_t)5ULL);
v___x_92_ = lean_usize_shift_right(v_x_75_, v___x_91_);
v_x_74_ = v_node_90_;
v_x_75_ = v___x_92_;
goto _start;
}
default: 
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
}
else
{
lean_object* v_ks_95_; lean_object* v_vs_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_ks_95_ = lean_ctor_get(v_x_74_, 0);
v_vs_96_ = lean_ctor_get(v_x_74_, 1);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_95_, v_vs_96_, v___x_97_, v_x_76_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
size_t v_x_3005__boxed_102_; lean_object* v_res_103_; 
v_x_3005__boxed_102_ = lean_unbox_usize(v_x_100_);
lean_dec(v_x_100_);
v_res_103_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_99_, v_x_3005__boxed_102_, v_x_101_);
lean_dec_ref(v_x_101_);
lean_dec_ref(v_x_99_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; uint64_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_106_ = lean_ptr_addr(v_x_105_);
v___x_107_ = ((size_t)3ULL);
v___x_108_ = lean_usize_shift_right(v___x_106_, v___x_107_);
v___x_109_ = lean_usize_to_uint64(v___x_108_);
v___x_110_ = lean_uint64_to_usize(v___x_109_);
v___x_111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_104_, v___x_110_, v_x_105_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_112_, v_x_113_);
lean_dec_ref(v_x_113_);
lean_dec_ref(v_x_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_ks_119_; lean_object* v_vs_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_146_; 
v_ks_119_ = lean_ctor_get(v_x_115_, 0);
v_vs_120_ = lean_ctor_get(v_x_115_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_146_ == 0)
{
v___x_122_ = v_x_115_;
v_isShared_123_ = v_isSharedCheck_146_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_vs_120_);
lean_inc(v_ks_119_);
lean_dec(v_x_115_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_146_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_array_get_size(v_ks_119_);
v___x_125_ = lean_nat_dec_lt(v_x_116_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
lean_dec(v_x_116_);
v___x_126_ = lean_array_push(v_ks_119_, v_x_117_);
v___x_127_ = lean_array_push(v_vs_120_, v_x_118_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_127_);
lean_ctor_set(v___x_122_, 0, v___x_126_);
v___x_129_ = v___x_122_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v_k_x27_131_; size_t v___x_132_; size_t v___x_133_; uint8_t v___x_134_; 
v_k_x27_131_ = lean_array_fget_borrowed(v_ks_119_, v_x_116_);
v___x_132_ = lean_ptr_addr(v_x_117_);
v___x_133_ = lean_ptr_addr(v_k_x27_131_);
v___x_134_ = lean_usize_dec_eq(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_136_; 
if (v_isShared_123_ == 0)
{
v___x_136_ = v___x_122_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_ks_119_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_vs_120_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_x_116_, v___x_137_);
lean_dec(v_x_116_);
v_x_115_ = v___x_136_;
v_x_116_ = v___x_138_;
goto _start;
}
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_141_ = lean_array_fset(v_ks_119_, v_x_116_, v_x_117_);
v___x_142_ = lean_array_fset(v_vs_120_, v_x_116_, v_x_118_);
lean_dec(v_x_116_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_142_);
lean_ctor_set(v___x_122_, 0, v___x_141_);
v___x_144_ = v___x_122_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(lean_object* v_n_147_, lean_object* v_k_148_, lean_object* v_v_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_n_147_, v___x_150_, v_k_148_, v_v_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object* v_x_153_, size_t v_x_154_, size_t v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v_es_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v_j_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_es_158_ = lean_ctor_get(v_x_153_, 0);
v___x_159_ = ((size_t)31ULL);
v___x_160_ = lean_usize_land(v_x_154_, v___x_159_);
v_j_161_ = lean_usize_to_nat(v___x_160_);
v___x_162_ = lean_array_get_size(v_es_158_);
v___x_163_ = lean_nat_dec_lt(v_j_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v_j_161_);
lean_dec(v_x_157_);
lean_dec_ref(v_x_156_);
return v_x_153_;
}
else
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_204_; 
lean_inc_ref(v_es_158_);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_x_153_, 0);
lean_dec(v_unused_205_);
v___x_165_ = v_x_153_;
v_isShared_166_ = v_isSharedCheck_204_;
goto v_resetjp_164_;
}
else
{
lean_dec(v_x_153_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_204_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_v_167_; lean_object* v___x_168_; lean_object* v_xs_x27_169_; lean_object* v___y_171_; 
v_v_167_ = lean_array_fget(v_es_158_, v_j_161_);
v___x_168_ = lean_box(0);
v_xs_x27_169_ = lean_array_fset(v_es_158_, v_j_161_, v___x_168_);
switch(lean_obj_tag(v_v_167_))
{
case 0:
{
lean_object* v_key_176_; lean_object* v_val_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_189_; 
v_key_176_ = lean_ctor_get(v_v_167_, 0);
v_val_177_ = lean_ctor_get(v_v_167_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_v_167_);
if (v_isSharedCheck_189_ == 0)
{
v___x_179_ = v_v_167_;
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_val_177_);
lean_inc(v_key_176_);
lean_dec(v_v_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
size_t v___x_181_; size_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_ptr_addr(v_x_156_);
v___x_182_ = lean_ptr_addr(v_key_176_);
v___x_183_ = lean_usize_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_del_object(v___x_179_);
v___x_184_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_176_, v_val_177_, v_x_156_, v_x_157_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
v___y_171_ = v___x_185_;
goto v___jp_170_;
}
else
{
lean_object* v___x_187_; 
lean_dec(v_val_177_);
lean_dec(v_key_176_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_x_157_);
lean_ctor_set(v___x_179_, 0, v_x_156_);
v___x_187_ = v___x_179_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_x_156_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_x_157_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v___y_171_ = v___x_187_;
goto v___jp_170_;
}
}
}
}
case 1:
{
lean_object* v_node_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_202_; 
v_node_190_ = lean_ctor_get(v_v_167_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_v_167_);
if (v_isSharedCheck_202_ == 0)
{
v___x_192_ = v_v_167_;
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_node_190_);
lean_dec(v_v_167_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_194_ = ((size_t)5ULL);
v___x_195_ = lean_usize_shift_right(v_x_154_, v___x_194_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_x_155_, v___x_196_);
v___x_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_190_, v___x_195_, v___x_197_, v_x_156_, v_x_157_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_198_);
v___x_200_ = v___x_192_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v___y_171_ = v___x_200_;
goto v___jp_170_;
}
}
}
default: 
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_x_156_);
lean_ctor_set(v___x_203_, 1, v_x_157_);
v___y_171_ = v___x_203_;
goto v___jp_170_;
}
}
v___jp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_array_fset(v_xs_x27_169_, v_j_161_, v___y_171_);
lean_dec(v_j_161_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_172_);
v___x_174_ = v___x_165_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
else
{
lean_object* v_ks_206_; lean_object* v_vs_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_225_; 
v_ks_206_ = lean_ctor_get(v_x_153_, 0);
v_vs_207_ = lean_ctor_get(v_x_153_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_225_ == 0)
{
v___x_209_ = v_x_153_;
v_isShared_210_ = v_isSharedCheck_225_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_vs_207_);
lean_inc(v_ks_206_);
lean_dec(v_x_153_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_225_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_ks_206_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_vs_207_);
v___x_212_ = v_reuseFailAlloc_224_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v_newNode_213_; size_t v___x_214_; uint8_t v___x_215_; 
v_newNode_213_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_212_, v_x_156_, v_x_157_);
v___x_214_ = ((size_t)7ULL);
v___x_215_ = lean_usize_dec_le(v___x_214_, v_x_155_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_213_);
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
if (v___x_218_ == 0)
{
lean_object* v_ks_219_; lean_object* v_vs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_ks_219_ = lean_ctor_get(v_newNode_213_, 0);
lean_inc_ref(v_ks_219_);
v_vs_220_ = lean_ctor_get(v_newNode_213_, 1);
lean_inc_ref(v_vs_220_);
lean_dec_ref(v_newNode_213_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
v___x_223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_155_, v_ks_219_, v_vs_220_, v___x_221_, v___x_222_);
lean_dec_ref(v_vs_220_);
lean_dec_ref(v_ks_219_);
return v___x_223_;
}
else
{
return v_newNode_213_;
}
}
else
{
return v_newNode_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t v_depth_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_i_229_, lean_object* v_entries_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_keys_227_);
v___x_232_ = lean_nat_dec_lt(v_i_229_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v_i_229_);
return v_entries_230_;
}
else
{
lean_object* v_k_233_; lean_object* v_v_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; uint64_t v___x_238_; size_t v_h_239_; size_t v___x_240_; lean_object* v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v_h_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_k_233_ = lean_array_fget_borrowed(v_keys_227_, v_i_229_);
v_v_234_ = lean_array_fget_borrowed(v_vals_228_, v_i_229_);
v___x_235_ = lean_ptr_addr(v_k_233_);
v___x_236_ = ((size_t)3ULL);
v___x_237_ = lean_usize_shift_right(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_to_uint64(v___x_237_);
v_h_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = ((size_t)5ULL);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v_depth_226_, v___x_242_);
v___x_244_ = lean_usize_mul(v___x_240_, v___x_243_);
v_h_245_ = lean_usize_shift_right(v_h_239_, v___x_244_);
v___x_246_ = lean_nat_add(v_i_229_, v___x_241_);
lean_dec(v_i_229_);
lean_inc(v_v_234_);
lean_inc(v_k_233_);
v___x_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_230_, v_h_245_, v_depth_226_, v_k_233_, v_v_234_);
v_i_229_ = v___x_246_;
v_entries_230_ = v___x_247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_249_, lean_object* v_keys_250_, lean_object* v_vals_251_, lean_object* v_i_252_, lean_object* v_entries_253_){
_start:
{
size_t v_depth_boxed_254_; lean_object* v_res_255_; 
v_depth_boxed_254_ = lean_unbox_usize(v_depth_249_);
lean_dec(v_depth_249_);
v_res_255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_boxed_254_, v_keys_250_, v_vals_251_, v_i_252_, v_entries_253_);
lean_dec_ref(v_vals_251_);
lean_dec_ref(v_keys_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
size_t v_x_3157__boxed_261_; size_t v_x_3158__boxed_262_; lean_object* v_res_263_; 
v_x_3157__boxed_261_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_3158__boxed_262_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_256_, v_x_3157__boxed_261_, v_x_3158__boxed_262_, v_x_259_, v_x_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; uint64_t v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_ptr_addr(v_x_265_);
v___x_268_ = ((size_t)3ULL);
v___x_269_ = lean_usize_shift_right(v___x_267_, v___x_268_);
v___x_270_ = lean_usize_to_uint64(v___x_269_);
v___x_271_ = lean_uint64_to_usize(v___x_270_);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_264_, v___x_271_, v___x_272_, v_x_265_, v_x_266_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType(lean_object* v_e_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; lean_object* v_inferType_283_; lean_object* v___x_284_; 
v___x_282_ = lean_st_ref_get(v_a_276_);
v_inferType_283_ = lean_ctor_get(v___x_282_, 4);
lean_inc_ref(v_inferType_283_);
lean_dec(v___x_282_);
v___x_284_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_283_, v_e_274_);
lean_dec_ref(v_inferType_283_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_e_274_);
v_val_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 0);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_val_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v___x_293_; 
lean_dec(v___x_284_);
lean_inc_ref(v_e_274_);
v___x_293_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_274_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = l_Lean_Meta_Sym_shareCommonInc(v_a_294_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_326_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_326_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_326_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_326_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v_share_301_; lean_object* v_maxFVar_302_; lean_object* v_proofInstInfo_303_; lean_object* v_proofInstInfoFVar_304_; lean_object* v_inferType_305_; lean_object* v_getLevel_306_; lean_object* v_congrInfo_307_; lean_object* v_defEqI_308_; lean_object* v_extensions_309_; lean_object* v_issues_310_; lean_object* v_canon_311_; lean_object* v_instanceOverrides_312_; uint8_t v_debug_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_325_; 
v___x_300_ = lean_st_ref_take(v_a_276_);
v_share_301_ = lean_ctor_get(v___x_300_, 0);
v_maxFVar_302_ = lean_ctor_get(v___x_300_, 1);
v_proofInstInfo_303_ = lean_ctor_get(v___x_300_, 2);
v_proofInstInfoFVar_304_ = lean_ctor_get(v___x_300_, 3);
v_inferType_305_ = lean_ctor_get(v___x_300_, 4);
v_getLevel_306_ = lean_ctor_get(v___x_300_, 5);
v_congrInfo_307_ = lean_ctor_get(v___x_300_, 6);
v_defEqI_308_ = lean_ctor_get(v___x_300_, 7);
v_extensions_309_ = lean_ctor_get(v___x_300_, 8);
v_issues_310_ = lean_ctor_get(v___x_300_, 9);
v_canon_311_ = lean_ctor_get(v___x_300_, 10);
v_instanceOverrides_312_ = lean_ctor_get(v___x_300_, 11);
v_debug_313_ = lean_ctor_get_uint8(v___x_300_, sizeof(void*)*12);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_325_ == 0)
{
v___x_315_ = v___x_300_;
v_isShared_316_ = v_isSharedCheck_325_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_instanceOverrides_312_);
lean_inc(v_canon_311_);
lean_inc(v_issues_310_);
lean_inc(v_extensions_309_);
lean_inc(v_defEqI_308_);
lean_inc(v_congrInfo_307_);
lean_inc(v_getLevel_306_);
lean_inc(v_inferType_305_);
lean_inc(v_proofInstInfoFVar_304_);
lean_inc(v_proofInstInfo_303_);
lean_inc(v_maxFVar_302_);
lean_inc(v_share_301_);
lean_dec(v___x_300_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_325_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_inc(v_a_296_);
v___x_317_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_305_, v_e_274_, v_a_296_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 4, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_share_301_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_maxFVar_302_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_proofInstInfo_303_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_proofInstInfoFVar_304_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_324_, 5, v_getLevel_306_);
lean_ctor_set(v_reuseFailAlloc_324_, 6, v_congrInfo_307_);
lean_ctor_set(v_reuseFailAlloc_324_, 7, v_defEqI_308_);
lean_ctor_set(v_reuseFailAlloc_324_, 8, v_extensions_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 9, v_issues_310_);
lean_ctor_set(v_reuseFailAlloc_324_, 10, v_canon_311_);
lean_ctor_set(v_reuseFailAlloc_324_, 11, v_instanceOverrides_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*12, v_debug_313_);
v___x_319_ = v_reuseFailAlloc_324_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_st_ref_put(v_a_276_, v___x_319_);
if (v_isShared_299_ == 0)
{
v___x_322_ = v___x_298_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_296_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_274_);
return v___x_295_;
}
}
else
{
lean_dec_ref(v_e_274_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_Sym_inferType(v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object* v_00_u03b2_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(v_00_u03b2_340_, v_x_341_, v_x_342_);
lean_dec_ref(v_x_342_);
lean_dec_ref(v_x_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_x_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object* v_00_u03b2_349_, lean_object* v_x_350_, size_t v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_350_, v_x_351_, v_x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
size_t v_x_3419__boxed_358_; lean_object* v_res_359_; 
v_x_3419__boxed_358_ = lean_unbox_usize(v_x_356_);
lean_dec(v_x_356_);
v_res_359_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_354_, v_x_355_, v_x_3419__boxed_358_, v_x_357_);
lean_dec_ref(v_x_357_);
lean_dec_ref(v_x_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object* v_00_u03b2_360_, lean_object* v_x_361_, size_t v_x_362_, size_t v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_361_, v_x_362_, v_x_363_, v_x_364_, v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
size_t v_x_3430__boxed_373_; size_t v_x_3431__boxed_374_; lean_object* v_res_375_; 
v_x_3430__boxed_373_ = lean_unbox_usize(v_x_369_);
lean_dec(v_x_369_);
v_x_3431__boxed_374_ = lean_unbox_usize(v_x_370_);
lean_dec(v_x_370_);
v_res_375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_367_, v_x_368_, v_x_3430__boxed_373_, v_x_3431__boxed_374_, v_x_371_, v_x_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_376_, lean_object* v_keys_377_, lean_object* v_vals_378_, lean_object* v_heq_379_, lean_object* v_i_380_, lean_object* v_k_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_377_, v_vals_378_, v_i_380_, v_k_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_383_, lean_object* v_keys_384_, lean_object* v_vals_385_, lean_object* v_heq_386_, lean_object* v_i_387_, lean_object* v_k_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_383_, v_keys_384_, v_vals_385_, v_heq_386_, v_i_387_, v_k_388_);
lean_dec_ref(v_k_388_);
lean_dec_ref(v_vals_385_);
lean_dec_ref(v_keys_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_390_, lean_object* v_n_391_, lean_object* v_k_392_, lean_object* v_v_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_391_, v_k_392_, v_v_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_395_, size_t v_depth_396_, lean_object* v_keys_397_, lean_object* v_vals_398_, lean_object* v_heq_399_, lean_object* v_i_400_, lean_object* v_entries_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_396_, v_keys_397_, v_vals_398_, v_i_400_, v_entries_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_403_, lean_object* v_depth_404_, lean_object* v_keys_405_, lean_object* v_vals_406_, lean_object* v_heq_407_, lean_object* v_i_408_, lean_object* v_entries_409_){
_start:
{
size_t v_depth_boxed_410_; lean_object* v_res_411_; 
v_depth_boxed_410_ = lean_unbox_usize(v_depth_404_);
lean_dec(v_depth_404_);
v_res_411_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_403_, v_depth_boxed_410_, v_keys_405_, v_vals_406_, v_heq_407_, v_i_408_, v_entries_409_);
lean_dec_ref(v_vals_406_);
lean_dec_ref(v_keys_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_413_, v_x_414_, v_x_415_, v_x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object* v_type_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_getLevel_426_; lean_object* v___x_427_; 
v___x_425_ = lean_st_ref_get(v_a_419_);
v_getLevel_426_ = lean_ctor_get(v___x_425_, 5);
lean_inc_ref(v_getLevel_426_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_426_, v_type_418_);
lean_dec_ref(v_getLevel_426_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_type_418_);
v_val_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_val_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_val_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v___x_436_; 
lean_dec(v___x_427_);
lean_inc_ref(v_type_418_);
v___x_436_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_418_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_467_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_share_442_; lean_object* v_maxFVar_443_; lean_object* v_proofInstInfo_444_; lean_object* v_proofInstInfoFVar_445_; lean_object* v_inferType_446_; lean_object* v_getLevel_447_; lean_object* v_congrInfo_448_; lean_object* v_defEqI_449_; lean_object* v_extensions_450_; lean_object* v_issues_451_; lean_object* v_canon_452_; lean_object* v_instanceOverrides_453_; uint8_t v_debug_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_466_; 
v___x_441_ = lean_st_ref_take(v_a_419_);
v_share_442_ = lean_ctor_get(v___x_441_, 0);
v_maxFVar_443_ = lean_ctor_get(v___x_441_, 1);
v_proofInstInfo_444_ = lean_ctor_get(v___x_441_, 2);
v_proofInstInfoFVar_445_ = lean_ctor_get(v___x_441_, 3);
v_inferType_446_ = lean_ctor_get(v___x_441_, 4);
v_getLevel_447_ = lean_ctor_get(v___x_441_, 5);
v_congrInfo_448_ = lean_ctor_get(v___x_441_, 6);
v_defEqI_449_ = lean_ctor_get(v___x_441_, 7);
v_extensions_450_ = lean_ctor_get(v___x_441_, 8);
v_issues_451_ = lean_ctor_get(v___x_441_, 9);
v_canon_452_ = lean_ctor_get(v___x_441_, 10);
v_instanceOverrides_453_ = lean_ctor_get(v___x_441_, 11);
v_debug_454_ = lean_ctor_get_uint8(v___x_441_, sizeof(void*)*12);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_466_ == 0)
{
v___x_456_ = v___x_441_;
v_isShared_457_ = v_isSharedCheck_466_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_instanceOverrides_453_);
lean_inc(v_canon_452_);
lean_inc(v_issues_451_);
lean_inc(v_extensions_450_);
lean_inc(v_defEqI_449_);
lean_inc(v_congrInfo_448_);
lean_inc(v_getLevel_447_);
lean_inc(v_inferType_446_);
lean_inc(v_proofInstInfoFVar_445_);
lean_inc(v_proofInstInfo_444_);
lean_inc(v_maxFVar_443_);
lean_inc(v_share_442_);
lean_dec(v___x_441_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_466_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_inc(v_a_437_);
v___x_458_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_447_, v_type_418_, v_a_437_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 5, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_share_442_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_maxFVar_443_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_proofInstInfo_444_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_proofInstInfoFVar_445_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_inferType_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_congrInfo_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_defEqI_449_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_extensions_450_);
lean_ctor_set(v_reuseFailAlloc_465_, 9, v_issues_451_);
lean_ctor_set(v_reuseFailAlloc_465_, 10, v_canon_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 11, v_instanceOverrides_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_465_, sizeof(void*)*12, v_debug_454_);
v___x_460_ = v_reuseFailAlloc_465_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_st_ref_put(v_a_419_, v___x_460_);
if (v_isShared_440_ == 0)
{
v___x_463_ = v___x_439_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_437_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_418_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object* v_type_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel(lean_object* v_type_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_476_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object* v_type_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Meta_Sym_getLevel(v_type_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object* v_e_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
lean_inc_ref(v_e_499_);
v___x_507_ = l_Lean_Meta_Sym_inferType(v_e_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_n(v_a_508_, 2);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_508_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_522_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_522_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_Sym_mkEqRefl___closed__2));
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v_a_510_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_mkConst(v___x_514_, v___x_516_);
v___x_518_ = l_Lean_mkAppB(v___x_517_, v_a_508_, v_e_499_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_518_);
v___x_520_ = v___x_512_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_508_);
lean_dec_ref(v_e_499_);
v_a_523_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_509_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_509_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_dec_ref(v_e_499_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object* v_e_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Meta_Sym_mkEqRefl(v_e_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_539_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
