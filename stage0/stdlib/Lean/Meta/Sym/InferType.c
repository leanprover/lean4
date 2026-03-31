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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
v_es_81_ = lean_ctor_get(v_x_78_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_102_ == 0)
{
v___x_83_ = v_x_78_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_es_81_);
lean_dec(v_x_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; lean_object* v_j_89_; lean_object* v___x_90_; 
v___x_85_ = lean_box(2);
v___x_86_ = ((size_t)5ULL);
v___x_87_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
v___x_88_ = lean_usize_land(v_x_79_, v___x_87_);
v_j_89_ = lean_usize_to_nat(v___x_88_);
v___x_90_ = lean_array_get(v___x_85_, v_es_81_, v_j_89_);
lean_dec(v_j_89_);
lean_dec_ref(v_es_81_);
switch(lean_obj_tag(v___x_90_))
{
case 0:
{
lean_object* v_key_91_; lean_object* v_val_92_; uint8_t v___x_93_; 
v_key_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_key_91_);
v_val_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_val_92_);
lean_dec_ref(v___x_90_);
v___x_93_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_80_, v_key_91_);
lean_dec(v_key_91_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v_val_92_);
lean_del_object(v___x_83_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_96_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 0, v_val_92_);
v___x_96_ = v___x_83_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_val_92_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
case 1:
{
lean_object* v_node_98_; size_t v___x_99_; 
lean_del_object(v___x_83_);
v_node_98_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_node_98_);
lean_dec_ref(v___x_90_);
v___x_99_ = lean_usize_shift_right(v_x_79_, v___x_86_);
v_x_78_ = v_node_98_;
v_x_79_ = v___x_99_;
goto _start;
}
default: 
{
lean_object* v___x_101_; 
lean_del_object(v___x_83_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
}
}
}
else
{
lean_object* v_ks_103_; lean_object* v_vs_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_ks_103_ = lean_ctor_get(v_x_78_, 0);
lean_inc_ref(v_ks_103_);
v_vs_104_ = lean_ctor_get(v_x_78_, 1);
lean_inc_ref(v_vs_104_);
lean_dec_ref(v_x_78_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_103_, v_vs_104_, v___x_105_, v_x_80_);
lean_dec_ref(v_vs_104_);
lean_dec_ref(v_ks_103_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
size_t v_x_2882__boxed_110_; lean_object* v_res_111_; 
v_x_2882__boxed_110_ = lean_unbox_usize(v_x_108_);
lean_dec(v_x_108_);
v_res_111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_107_, v_x_2882__boxed_110_, v_x_109_);
lean_dec_ref(v_x_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint64_t v___x_114_; size_t v___x_115_; lean_object* v___x_116_; 
v___x_114_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_113_);
v___x_115_ = lean_uint64_to_usize(v___x_114_);
v___x_116_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_112_, v___x_115_, v_x_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_117_, v_x_118_);
lean_dec_ref(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
lean_object* v_ks_124_; lean_object* v_vs_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_149_; 
v_ks_124_ = lean_ctor_get(v_x_120_, 0);
v_vs_125_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_149_ == 0)
{
v___x_127_ = v_x_120_;
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_vs_125_);
lean_inc(v_ks_124_);
lean_dec(v_x_120_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_array_get_size(v_ks_124_);
v___x_130_ = lean_nat_dec_lt(v_x_121_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
lean_dec(v_x_121_);
v___x_131_ = lean_array_push(v_ks_124_, v_x_122_);
v___x_132_ = lean_array_push(v_vs_125_, v_x_123_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_132_);
lean_ctor_set(v___x_127_, 0, v___x_131_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v_k_x27_136_; uint8_t v___x_137_; 
v_k_x27_136_ = lean_array_fget_borrowed(v_ks_124_, v_x_121_);
v___x_137_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_122_, v_k_x27_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; 
if (v_isShared_128_ == 0)
{
v___x_139_ = v___x_127_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_ks_124_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_vs_125_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_x_121_, v___x_140_);
lean_dec(v_x_121_);
v_x_120_ = v___x_139_;
v_x_121_ = v___x_141_;
goto _start;
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_array_fset(v_ks_124_, v_x_121_, v_x_122_);
v___x_145_ = lean_array_fset(v_vs_125_, v_x_121_, v_x_123_);
lean_dec(v_x_121_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_145_);
lean_ctor_set(v___x_127_, 0, v___x_144_);
v___x_147_ = v___x_127_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(lean_object* v_n_150_, lean_object* v_k_151_, lean_object* v_v_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_n_150_, v___x_153_, v_k_151_, v_v_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object* v_x_156_, size_t v_x_157_, size_t v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v_es_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v_j_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_es_161_ = lean_ctor_get(v_x_156_, 0);
v___x_162_ = ((size_t)5ULL);
v___x_163_ = ((size_t)1ULL);
v___x_164_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
v___x_165_ = lean_usize_land(v_x_157_, v___x_164_);
v_j_166_ = lean_usize_to_nat(v___x_165_);
v___x_167_ = lean_array_get_size(v_es_161_);
v___x_168_ = lean_nat_dec_lt(v_j_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec(v_j_166_);
lean_dec(v_x_160_);
lean_dec_ref(v_x_159_);
return v_x_156_;
}
else
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_205_; 
lean_inc_ref(v_es_161_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_x_156_, 0);
lean_dec(v_unused_206_);
v___x_170_ = v_x_156_;
v_isShared_171_ = v_isSharedCheck_205_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_x_156_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_205_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_v_172_; lean_object* v___x_173_; lean_object* v_xs_x27_174_; lean_object* v___y_176_; 
v_v_172_ = lean_array_fget(v_es_161_, v_j_166_);
v___x_173_ = lean_box(0);
v_xs_x27_174_ = lean_array_fset(v_es_161_, v_j_166_, v___x_173_);
switch(lean_obj_tag(v_v_172_))
{
case 0:
{
lean_object* v_key_181_; lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_192_; 
v_key_181_ = lean_ctor_get(v_v_172_, 0);
v_val_182_ = lean_ctor_get(v_v_172_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_v_172_);
if (v_isSharedCheck_192_ == 0)
{
v___x_184_ = v_v_172_;
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_inc(v_key_181_);
lean_dec(v_v_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
uint8_t v___x_186_; 
v___x_186_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_159_, v_key_181_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_del_object(v___x_184_);
v___x_187_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_181_, v_val_182_, v_x_159_, v_x_160_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___y_176_ = v___x_188_;
goto v___jp_175_;
}
else
{
lean_object* v___x_190_; 
lean_dec(v_val_182_);
lean_dec(v_key_181_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_x_160_);
lean_ctor_set(v___x_184_, 0, v_x_159_);
v___x_190_ = v___x_184_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_x_159_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_x_160_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v___y_176_ = v___x_190_;
goto v___jp_175_;
}
}
}
}
case 1:
{
lean_object* v_node_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_203_; 
v_node_193_ = lean_ctor_get(v_v_172_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_v_172_);
if (v_isSharedCheck_203_ == 0)
{
v___x_195_ = v_v_172_;
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_node_193_);
lean_dec(v_v_172_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_197_ = lean_usize_shift_right(v_x_157_, v___x_162_);
v___x_198_ = lean_usize_add(v_x_158_, v___x_163_);
v___x_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_193_, v___x_197_, v___x_198_, v_x_159_, v_x_160_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_199_);
v___x_201_ = v___x_195_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v___y_176_ = v___x_201_;
goto v___jp_175_;
}
}
}
default: 
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_x_159_);
lean_ctor_set(v___x_204_, 1, v_x_160_);
v___y_176_ = v___x_204_;
goto v___jp_175_;
}
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_array_fset(v_xs_x27_174_, v_j_166_, v___y_176_);
lean_dec(v_j_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_177_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
else
{
lean_object* v_ks_207_; lean_object* v_vs_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_228_; 
v_ks_207_ = lean_ctor_get(v_x_156_, 0);
v_vs_208_ = lean_ctor_get(v_x_156_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_228_ == 0)
{
v___x_210_ = v_x_156_;
v_isShared_211_ = v_isSharedCheck_228_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_vs_208_);
lean_inc(v_ks_207_);
lean_dec(v_x_156_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_228_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_ks_207_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_vs_208_);
v___x_213_ = v_reuseFailAlloc_227_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v_newNode_214_; uint8_t v___y_216_; size_t v___x_222_; uint8_t v___x_223_; 
v_newNode_214_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_213_, v_x_159_, v_x_160_);
v___x_222_ = ((size_t)7ULL);
v___x_223_ = lean_usize_dec_le(v___x_222_, v_x_158_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_214_);
v___x_225_ = lean_unsigned_to_nat(4u);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
lean_dec(v___x_224_);
v___y_216_ = v___x_226_;
goto v___jp_215_;
}
else
{
v___y_216_ = v___x_223_;
goto v___jp_215_;
}
v___jp_215_:
{
if (v___y_216_ == 0)
{
lean_object* v_ks_217_; lean_object* v_vs_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_ks_217_ = lean_ctor_get(v_newNode_214_, 0);
lean_inc_ref(v_ks_217_);
v_vs_218_ = lean_ctor_get(v_newNode_214_, 1);
lean_inc_ref(v_vs_218_);
lean_dec_ref(v_newNode_214_);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
v___x_221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_158_, v_ks_217_, v_vs_218_, v___x_219_, v___x_220_);
lean_dec_ref(v_vs_218_);
lean_dec_ref(v_ks_217_);
return v___x_221_;
}
else
{
return v_newNode_214_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t v_depth_229_, lean_object* v_keys_230_, lean_object* v_vals_231_, lean_object* v_i_232_, lean_object* v_entries_233_){
_start:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_array_get_size(v_keys_230_);
v___x_235_ = lean_nat_dec_lt(v_i_232_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v_i_232_);
return v_entries_233_;
}
else
{
lean_object* v_k_236_; lean_object* v_v_237_; uint64_t v___x_238_; size_t v_h_239_; size_t v___x_240_; lean_object* v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v_h_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_k_236_ = lean_array_fget_borrowed(v_keys_230_, v_i_232_);
v_v_237_ = lean_array_fget_borrowed(v_vals_231_, v_i_232_);
v___x_238_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_236_);
v_h_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = ((size_t)5ULL);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v_depth_229_, v___x_242_);
v___x_244_ = lean_usize_mul(v___x_240_, v___x_243_);
v_h_245_ = lean_usize_shift_right(v_h_239_, v___x_244_);
v___x_246_ = lean_nat_add(v_i_232_, v___x_241_);
lean_dec(v_i_232_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
v___x_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_233_, v_h_245_, v_depth_229_, v_k_236_, v_v_237_);
v_i_232_ = v___x_246_;
v_entries_233_ = v___x_247_;
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
size_t v_x_3041__boxed_261_; size_t v_x_3042__boxed_262_; lean_object* v_res_263_; 
v_x_3041__boxed_261_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_3042__boxed_262_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_256_, v_x_3041__boxed_261_, v_x_3042__boxed_262_, v_x_259_, v_x_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint64_t v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_267_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_265_);
v___x_268_ = lean_uint64_to_usize(v___x_267_);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_264_, v___x_268_, v___x_269_, v_x_265_, v_x_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; lean_object* v_inferType_279_; lean_object* v___x_280_; 
v___x_278_ = lean_st_ref_get(v_a_272_);
v_inferType_279_ = lean_ctor_get(v___x_278_, 3);
lean_inc_ref(v_inferType_279_);
lean_dec(v___x_278_);
v___x_280_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_279_, v_e_271_);
if (lean_obj_tag(v___x_280_) == 1)
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_e_271_);
v_val_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 0);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_val_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v___x_289_; 
lean_dec(v___x_280_);
lean_inc_ref(v_e_271_);
v___x_289_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_271_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref(v___x_289_);
v___x_291_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_290_, v_a_272_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_320_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_320_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_320_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_320_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v_share_297_; lean_object* v_maxFVar_298_; lean_object* v_proofInstInfo_299_; lean_object* v_inferType_300_; lean_object* v_getLevel_301_; lean_object* v_congrInfo_302_; lean_object* v_defEqI_303_; lean_object* v_extensions_304_; lean_object* v_issues_305_; lean_object* v_canon_306_; uint8_t v_debug_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_319_; 
v___x_296_ = lean_st_ref_take(v_a_272_);
v_share_297_ = lean_ctor_get(v___x_296_, 0);
v_maxFVar_298_ = lean_ctor_get(v___x_296_, 1);
v_proofInstInfo_299_ = lean_ctor_get(v___x_296_, 2);
v_inferType_300_ = lean_ctor_get(v___x_296_, 3);
v_getLevel_301_ = lean_ctor_get(v___x_296_, 4);
v_congrInfo_302_ = lean_ctor_get(v___x_296_, 5);
v_defEqI_303_ = lean_ctor_get(v___x_296_, 6);
v_extensions_304_ = lean_ctor_get(v___x_296_, 7);
v_issues_305_ = lean_ctor_get(v___x_296_, 8);
v_canon_306_ = lean_ctor_get(v___x_296_, 9);
v_debug_307_ = lean_ctor_get_uint8(v___x_296_, sizeof(void*)*10);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_319_ == 0)
{
v___x_309_ = v___x_296_;
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_canon_306_);
lean_inc(v_issues_305_);
lean_inc(v_extensions_304_);
lean_inc(v_defEqI_303_);
lean_inc(v_congrInfo_302_);
lean_inc(v_getLevel_301_);
lean_inc(v_inferType_300_);
lean_inc(v_proofInstInfo_299_);
lean_inc(v_maxFVar_298_);
lean_inc(v_share_297_);
lean_dec(v___x_296_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_inc(v_a_292_);
v___x_311_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_300_, v_e_271_, v_a_292_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v___x_311_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_share_297_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_maxFVar_298_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_proofInstInfo_299_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v_getLevel_301_);
lean_ctor_set(v_reuseFailAlloc_318_, 5, v_congrInfo_302_);
lean_ctor_set(v_reuseFailAlloc_318_, 6, v_defEqI_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 7, v_extensions_304_);
lean_ctor_set(v_reuseFailAlloc_318_, 8, v_issues_305_);
lean_ctor_set(v_reuseFailAlloc_318_, 9, v_canon_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*10, v_debug_307_);
v___x_313_ = v_reuseFailAlloc_318_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = lean_st_ref_set(v_a_272_, v___x_313_);
if (v_isShared_295_ == 0)
{
v___x_316_ = v___x_294_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_292_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_271_);
return v___x_291_;
}
}
else
{
lean_dec_ref(v_e_271_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg___boxed(lean_object* v_e_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_Sym_inferType___redArg(v_e_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType(lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Sym_inferType___redArg(v_e_329_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object* v_e_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Sym_inferType(v_e_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object* v_00_u03b2_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_348_, v_x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object* v_00_u03b2_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(v_00_u03b2_351_, v_x_352_, v_x_353_);
lean_dec_ref(v_x_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object* v_00_u03b2_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_x_356_, v_x_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object* v_00_u03b2_360_, lean_object* v_x_361_, size_t v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_361_, v_x_362_, v_x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
size_t v_x_3299__boxed_369_; lean_object* v_res_370_; 
v_x_3299__boxed_369_ = lean_unbox_usize(v_x_367_);
lean_dec(v_x_367_);
v_res_370_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_365_, v_x_366_, v_x_3299__boxed_369_, v_x_368_);
lean_dec_ref(v_x_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object* v_00_u03b2_371_, lean_object* v_x_372_, size_t v_x_373_, size_t v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_372_, v_x_373_, v_x_374_, v_x_375_, v_x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
size_t v_x_3310__boxed_384_; size_t v_x_3311__boxed_385_; lean_object* v_res_386_; 
v_x_3310__boxed_384_ = lean_unbox_usize(v_x_380_);
lean_dec(v_x_380_);
v_x_3311__boxed_385_ = lean_unbox_usize(v_x_381_);
lean_dec(v_x_381_);
v_res_386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_378_, v_x_379_, v_x_3310__boxed_384_, v_x_3311__boxed_385_, v_x_382_, v_x_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_heq_390_, lean_object* v_i_391_, lean_object* v_k_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_388_, v_vals_389_, v_i_391_, v_k_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_394_, lean_object* v_keys_395_, lean_object* v_vals_396_, lean_object* v_heq_397_, lean_object* v_i_398_, lean_object* v_k_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_394_, v_keys_395_, v_vals_396_, v_heq_397_, v_i_398_, v_k_399_);
lean_dec_ref(v_k_399_);
lean_dec_ref(v_vals_396_);
lean_dec_ref(v_keys_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_401_, lean_object* v_n_402_, lean_object* v_k_403_, lean_object* v_v_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_402_, v_k_403_, v_v_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_406_, size_t v_depth_407_, lean_object* v_keys_408_, lean_object* v_vals_409_, lean_object* v_heq_410_, lean_object* v_i_411_, lean_object* v_entries_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_407_, v_keys_408_, v_vals_409_, v_i_411_, v_entries_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_414_, lean_object* v_depth_415_, lean_object* v_keys_416_, lean_object* v_vals_417_, lean_object* v_heq_418_, lean_object* v_i_419_, lean_object* v_entries_420_){
_start:
{
size_t v_depth_boxed_421_; lean_object* v_res_422_; 
v_depth_boxed_421_ = lean_unbox_usize(v_depth_415_);
lean_dec(v_depth_415_);
v_res_422_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_414_, v_depth_boxed_421_, v_keys_416_, v_vals_417_, v_heq_418_, v_i_419_, v_entries_420_);
lean_dec_ref(v_vals_417_);
lean_dec_ref(v_keys_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_424_, v_x_425_, v_x_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object* v_type_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; lean_object* v_getLevel_437_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_get(v_a_430_);
v_getLevel_437_ = lean_ctor_get(v___x_436_, 4);
lean_inc_ref(v_getLevel_437_);
lean_dec(v___x_436_);
v___x_438_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_437_, v_type_429_);
if (lean_obj_tag(v___x_438_) == 1)
{
lean_object* v_val_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_type_429_);
v_val_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_val_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 0);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_val_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_447_; 
lean_dec(v___x_438_);
lean_inc_ref(v_type_429_);
v___x_447_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_476_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_476_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v_share_453_; lean_object* v_maxFVar_454_; lean_object* v_proofInstInfo_455_; lean_object* v_inferType_456_; lean_object* v_getLevel_457_; lean_object* v_congrInfo_458_; lean_object* v_defEqI_459_; lean_object* v_extensions_460_; lean_object* v_issues_461_; lean_object* v_canon_462_; uint8_t v_debug_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_475_; 
v___x_452_ = lean_st_ref_take(v_a_430_);
v_share_453_ = lean_ctor_get(v___x_452_, 0);
v_maxFVar_454_ = lean_ctor_get(v___x_452_, 1);
v_proofInstInfo_455_ = lean_ctor_get(v___x_452_, 2);
v_inferType_456_ = lean_ctor_get(v___x_452_, 3);
v_getLevel_457_ = lean_ctor_get(v___x_452_, 4);
v_congrInfo_458_ = lean_ctor_get(v___x_452_, 5);
v_defEqI_459_ = lean_ctor_get(v___x_452_, 6);
v_extensions_460_ = lean_ctor_get(v___x_452_, 7);
v_issues_461_ = lean_ctor_get(v___x_452_, 8);
v_canon_462_ = lean_ctor_get(v___x_452_, 9);
v_debug_463_ = lean_ctor_get_uint8(v___x_452_, sizeof(void*)*10);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_475_ == 0)
{
v___x_465_ = v___x_452_;
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_canon_462_);
lean_inc(v_issues_461_);
lean_inc(v_extensions_460_);
lean_inc(v_defEqI_459_);
lean_inc(v_congrInfo_458_);
lean_inc(v_getLevel_457_);
lean_inc(v_inferType_456_);
lean_inc(v_proofInstInfo_455_);
lean_inc(v_maxFVar_454_);
lean_inc(v_share_453_);
lean_dec(v___x_452_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_a_448_);
v___x_467_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_457_, v_type_429_, v_a_448_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 4, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_share_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_maxFVar_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_proofInstInfo_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_inferType_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_congrInfo_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_defEqI_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_extensions_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_issues_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_canon_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*10, v_debug_463_);
v___x_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_st_ref_set(v_a_430_, v___x_469_);
if (v_isShared_451_ == 0)
{
v___x_472_ = v___x_450_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_448_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_429_);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object* v_type_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel(lean_object* v_type_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_485_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object* v_type_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_Sym_getLevel(v_type_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object* v_e_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; 
lean_inc_ref(v_e_508_);
v___x_515_ = l_Lean_Meta_Sym_inferType___redArg(v_e_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_n(v_a_516_, 2);
lean_dec_ref(v___x_515_);
v___x_517_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_516_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_530_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_522_ = ((lean_object*)(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2));
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v_a_518_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_mkConst(v___x_522_, v___x_524_);
v___x_526_ = l_Lean_mkAppB(v___x_525_, v_a_516_, v_e_508_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_526_);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_516_);
lean_dec_ref(v_e_508_);
v_a_531_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_517_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_517_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_dec_ref(v_e_508_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___boxed(lean_object* v_e_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_547_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_Sym_mkEqRefl(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_564_;
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
