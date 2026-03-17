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
lean_object* v_keyedConfig_7_; uint8_t v_trackZetaDelta_8_; lean_object* v_zetaDeltaSet_9_; lean_object* v_lctx_10_; lean_object* v_localInstances_11_; lean_object* v_defEqCtx_x3f_12_; lean_object* v_synthPendingDepth_13_; lean_object* v_canUnfold_x3f_14_; uint8_t v_univApprox_15_; uint8_t v_inTypeClassResolution_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_25_; 
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
v_isSharedCheck_25_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_25_ == 0)
{
v___x_18_ = v_a_2_;
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_canUnfold_x3f_14_);
lean_inc(v_synthPendingDepth_13_);
lean_inc(v_defEqCtx_x3f_12_);
lean_inc(v_localInstances_11_);
lean_inc(v_lctx_10_);
lean_inc(v_zetaDeltaSet_9_);
lean_inc(v_keyedConfig_7_);
lean_dec(v_a_2_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; lean_object* v___x_22_; 
v___x_20_ = 0;
if (v_isShared_19_ == 0)
{
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_keyedConfig_7_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_zetaDeltaSet_9_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v_lctx_10_);
lean_ctor_set(v_reuseFailAlloc_24_, 3, v_localInstances_11_);
lean_ctor_set(v_reuseFailAlloc_24_, 4, v_defEqCtx_x3f_12_);
lean_ctor_set(v_reuseFailAlloc_24_, 5, v_synthPendingDepth_13_);
lean_ctor_set(v_reuseFailAlloc_24_, 6, v_canUnfold_x3f_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, sizeof(void*)*7, v_trackZetaDelta_8_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, sizeof(void*)*7 + 1, v_univApprox_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, sizeof(void*)*7 + 2, v_inTypeClassResolution_16_);
v___x_22_ = v_reuseFailAlloc_24_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; 
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*7 + 3, v___x_20_);
v___x_23_ = lean_infer_type(v_e_1_, v___x_22_, v_a_3_, v_a_4_, v_a_5_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache___boxed(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(lean_object* v_type_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_keyedConfig_39_; uint8_t v_trackZetaDelta_40_; lean_object* v_zetaDeltaSet_41_; lean_object* v_lctx_42_; lean_object* v_localInstances_43_; lean_object* v_defEqCtx_x3f_44_; lean_object* v_synthPendingDepth_45_; lean_object* v_canUnfold_x3f_46_; uint8_t v_univApprox_47_; uint8_t v_inTypeClassResolution_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_57_; 
v_keyedConfig_39_ = lean_ctor_get(v_a_34_, 0);
v_trackZetaDelta_40_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7);
v_zetaDeltaSet_41_ = lean_ctor_get(v_a_34_, 1);
v_lctx_42_ = lean_ctor_get(v_a_34_, 2);
v_localInstances_43_ = lean_ctor_get(v_a_34_, 3);
v_defEqCtx_x3f_44_ = lean_ctor_get(v_a_34_, 4);
v_synthPendingDepth_45_ = lean_ctor_get(v_a_34_, 5);
v_canUnfold_x3f_46_ = lean_ctor_get(v_a_34_, 6);
v_univApprox_47_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_48_ = lean_ctor_get_uint8(v_a_34_, sizeof(void*)*7 + 2);
v_isSharedCheck_57_ = !lean_is_exclusive(v_a_34_);
if (v_isSharedCheck_57_ == 0)
{
v___x_50_ = v_a_34_;
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_canUnfold_x3f_46_);
lean_inc(v_synthPendingDepth_45_);
lean_inc(v_defEqCtx_x3f_44_);
lean_inc(v_localInstances_43_);
lean_inc(v_lctx_42_);
lean_inc(v_zetaDeltaSet_41_);
lean_inc(v_keyedConfig_39_);
lean_dec(v_a_34_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
uint8_t v___x_52_; lean_object* v___x_54_; 
v___x_52_ = 0;
if (v_isShared_51_ == 0)
{
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_keyedConfig_39_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_zetaDeltaSet_41_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v_lctx_42_);
lean_ctor_set(v_reuseFailAlloc_56_, 3, v_localInstances_43_);
lean_ctor_set(v_reuseFailAlloc_56_, 4, v_defEqCtx_x3f_44_);
lean_ctor_set(v_reuseFailAlloc_56_, 5, v_synthPendingDepth_45_);
lean_ctor_set(v_reuseFailAlloc_56_, 6, v_canUnfold_x3f_46_);
lean_ctor_set_uint8(v_reuseFailAlloc_56_, sizeof(void*)*7, v_trackZetaDelta_40_);
lean_ctor_set_uint8(v_reuseFailAlloc_56_, sizeof(void*)*7 + 1, v_univApprox_47_);
lean_ctor_set_uint8(v_reuseFailAlloc_56_, sizeof(void*)*7 + 2, v_inTypeClassResolution_48_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; 
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*7 + 3, v___x_52_);
v___x_55_ = l_Lean_Meta_getLevel(v_type_33_, v___x_54_, v_a_35_, v_a_36_, v_a_37_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache___boxed(lean_object* v_type_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_65_, lean_object* v_vals_66_, lean_object* v_i_67_, lean_object* v_k_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_array_get_size(v_keys_65_);
v___x_70_ = lean_nat_dec_lt(v_i_67_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v_i_67_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v_k_x27_72_; uint8_t v___x_73_; 
v_k_x27_72_ = lean_array_fget_borrowed(v_keys_65_, v_i_67_);
v___x_73_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_68_, v_k_x27_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_i_67_, v___x_74_);
lean_dec(v_i_67_);
v_i_67_ = v___x_75_;
goto _start;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_array_fget_borrowed(v_vals_66_, v_i_67_);
lean_dec(v_i_67_);
lean_inc(v___x_77_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_79_, lean_object* v_vals_80_, lean_object* v_i_81_, lean_object* v_k_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_79_, v_vals_80_, v_i_81_, v_k_82_);
lean_dec_ref(v_k_82_);
lean_dec_ref(v_vals_80_);
lean_dec_ref(v_keys_79_);
return v_res_83_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; 
v___x_84_ = ((size_t)5ULL);
v___x_85_ = ((size_t)1ULL);
v___x_86_ = lean_usize_shift_left(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; 
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0);
v___x_89_ = lean_usize_sub(v___x_88_, v___x_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(lean_object* v_x_90_, size_t v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v_es_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_114_; 
v_es_93_ = lean_ctor_get(v_x_90_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_114_ == 0)
{
v___x_95_ = v_x_90_;
v_isShared_96_ = v_isSharedCheck_114_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_es_93_);
lean_dec(v_x_90_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_114_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; lean_object* v_j_101_; lean_object* v___x_102_; 
v___x_97_ = lean_box(2);
v___x_98_ = ((size_t)5ULL);
v___x_99_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
v___x_100_ = lean_usize_land(v_x_91_, v___x_99_);
v_j_101_ = lean_usize_to_nat(v___x_100_);
v___x_102_ = lean_array_get(v___x_97_, v_es_93_, v_j_101_);
lean_dec(v_j_101_);
lean_dec_ref(v_es_93_);
switch(lean_obj_tag(v___x_102_))
{
case 0:
{
lean_object* v_key_103_; lean_object* v_val_104_; uint8_t v___x_105_; 
v_key_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_key_103_);
v_val_104_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_val_104_);
lean_dec_ref(v___x_102_);
v___x_105_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_92_, v_key_103_);
lean_dec(v_key_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_dec(v_val_104_);
lean_del_object(v___x_95_);
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
lean_object* v___x_108_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 1);
lean_ctor_set(v___x_95_, 0, v_val_104_);
v___x_108_ = v___x_95_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_val_104_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
case 1:
{
lean_object* v_node_110_; size_t v___x_111_; 
lean_del_object(v___x_95_);
v_node_110_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_node_110_);
lean_dec_ref(v___x_102_);
v___x_111_ = lean_usize_shift_right(v_x_91_, v___x_98_);
v_x_90_ = v_node_110_;
v_x_91_ = v___x_111_;
goto _start;
}
default: 
{
lean_object* v___x_113_; 
lean_del_object(v___x_95_);
v___x_113_ = lean_box(0);
return v___x_113_;
}
}
}
}
else
{
lean_object* v_ks_115_; lean_object* v_vs_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_ks_115_ = lean_ctor_get(v_x_90_, 0);
lean_inc_ref(v_ks_115_);
v_vs_116_ = lean_ctor_get(v_x_90_, 1);
lean_inc_ref(v_vs_116_);
lean_dec_ref(v_x_90_);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_115_, v_vs_116_, v___x_117_, v_x_92_);
lean_dec_ref(v_vs_116_);
lean_dec_ref(v_ks_115_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
size_t v_x_2829__boxed_122_; lean_object* v_res_123_; 
v_x_2829__boxed_122_ = lean_unbox_usize(v_x_120_);
lean_dec(v_x_120_);
v_res_123_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_119_, v_x_2829__boxed_122_, v_x_121_);
lean_dec_ref(v_x_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
uint64_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_124_, v___x_127_, v_x_125_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_129_, v_x_130_);
lean_dec_ref(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
lean_object* v_ks_136_; lean_object* v_vs_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_161_; 
v_ks_136_ = lean_ctor_get(v_x_132_, 0);
v_vs_137_ = lean_ctor_get(v_x_132_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_161_ == 0)
{
v___x_139_ = v_x_132_;
v_isShared_140_ = v_isSharedCheck_161_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_vs_137_);
lean_inc(v_ks_136_);
lean_dec(v_x_132_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_161_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_array_get_size(v_ks_136_);
v___x_142_ = lean_nat_dec_lt(v_x_133_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_x_133_);
v___x_143_ = lean_array_push(v_ks_136_, v_x_134_);
v___x_144_ = lean_array_push(v_vs_137_, v_x_135_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_144_);
lean_ctor_set(v___x_139_, 0, v___x_143_);
v___x_146_ = v___x_139_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v_k_x27_148_; uint8_t v___x_149_; 
v_k_x27_148_ = lean_array_fget_borrowed(v_ks_136_, v_x_133_);
v___x_149_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_134_, v_k_x27_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_151_; 
if (v_isShared_140_ == 0)
{
v___x_151_ = v___x_139_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_ks_136_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_vs_137_);
v___x_151_ = v_reuseFailAlloc_155_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_add(v_x_133_, v___x_152_);
lean_dec(v_x_133_);
v_x_132_ = v___x_151_;
v_x_133_ = v___x_153_;
goto _start;
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_156_ = lean_array_fset(v_ks_136_, v_x_133_, v_x_134_);
v___x_157_ = lean_array_fset(v_vs_137_, v_x_133_, v_x_135_);
lean_dec(v_x_133_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_157_);
lean_ctor_set(v___x_139_, 0, v___x_156_);
v___x_159_ = v___x_139_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(lean_object* v_n_162_, lean_object* v_k_163_, lean_object* v_v_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_n_162_, v___x_165_, v_k_163_, v_v_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object* v_x_168_, size_t v_x_169_, size_t v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_es_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; lean_object* v_j_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_es_173_ = lean_ctor_get(v_x_168_, 0);
v___x_174_ = ((size_t)5ULL);
v___x_175_ = ((size_t)1ULL);
v___x_176_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
v___x_177_ = lean_usize_land(v_x_169_, v___x_176_);
v_j_178_ = lean_usize_to_nat(v___x_177_);
v___x_179_ = lean_array_get_size(v_es_173_);
v___x_180_ = lean_nat_dec_lt(v_j_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_j_178_);
lean_dec(v_x_172_);
lean_dec_ref(v_x_171_);
return v_x_168_;
}
else
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_217_; 
lean_inc_ref(v_es_173_);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_x_168_, 0);
lean_dec(v_unused_218_);
v___x_182_ = v_x_168_;
v_isShared_183_ = v_isSharedCheck_217_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_x_168_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_217_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_v_184_; lean_object* v___x_185_; lean_object* v_xs_x27_186_; lean_object* v___y_188_; 
v_v_184_ = lean_array_fget(v_es_173_, v_j_178_);
v___x_185_ = lean_box(0);
v_xs_x27_186_ = lean_array_fset(v_es_173_, v_j_178_, v___x_185_);
switch(lean_obj_tag(v_v_184_))
{
case 0:
{
lean_object* v_key_193_; lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_204_; 
v_key_193_ = lean_ctor_get(v_v_184_, 0);
v_val_194_ = lean_ctor_get(v_v_184_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_v_184_);
if (v_isSharedCheck_204_ == 0)
{
v___x_196_ = v_v_184_;
v_isShared_197_ = v_isSharedCheck_204_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_inc(v_key_193_);
lean_dec(v_v_184_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_204_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
uint8_t v___x_198_; 
v___x_198_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_171_, v_key_193_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_del_object(v___x_196_);
v___x_199_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_193_, v_val_194_, v_x_171_, v_x_172_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
v___y_188_ = v___x_200_;
goto v___jp_187_;
}
else
{
lean_object* v___x_202_; 
lean_dec(v_val_194_);
lean_dec(v_key_193_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v_x_172_);
lean_ctor_set(v___x_196_, 0, v_x_171_);
v___x_202_ = v___x_196_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_x_171_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_x_172_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
v___y_188_ = v___x_202_;
goto v___jp_187_;
}
}
}
}
case 1:
{
lean_object* v_node_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_215_; 
v_node_205_ = lean_ctor_get(v_v_184_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_v_184_);
if (v_isSharedCheck_215_ == 0)
{
v___x_207_ = v_v_184_;
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_node_205_);
lean_dec(v_v_184_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_209_ = lean_usize_shift_right(v_x_169_, v___x_174_);
v___x_210_ = lean_usize_add(v_x_170_, v___x_175_);
v___x_211_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_205_, v___x_209_, v___x_210_, v_x_171_, v_x_172_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_211_);
v___x_213_ = v___x_207_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v___y_188_ = v___x_213_;
goto v___jp_187_;
}
}
}
default: 
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_x_171_);
lean_ctor_set(v___x_216_, 1, v_x_172_);
v___y_188_ = v___x_216_;
goto v___jp_187_;
}
}
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_array_fset(v_xs_x27_186_, v_j_178_, v___y_188_);
lean_dec(v_j_178_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_189_);
v___x_191_ = v___x_182_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
else
{
lean_object* v_ks_219_; lean_object* v_vs_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_240_; 
v_ks_219_ = lean_ctor_get(v_x_168_, 0);
v_vs_220_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_240_ == 0)
{
v___x_222_ = v_x_168_;
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_vs_220_);
lean_inc(v_ks_219_);
lean_dec(v_x_168_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_ks_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_vs_220_);
v___x_225_ = v_reuseFailAlloc_239_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v_newNode_226_; uint8_t v___y_228_; size_t v___x_234_; uint8_t v___x_235_; 
v_newNode_226_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_225_, v_x_171_, v_x_172_);
v___x_234_ = ((size_t)7ULL);
v___x_235_ = lean_usize_dec_le(v___x_234_, v_x_170_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_226_);
v___x_237_ = lean_unsigned_to_nat(4u);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
v___y_228_ = v___x_238_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___x_235_;
goto v___jp_227_;
}
v___jp_227_:
{
if (v___y_228_ == 0)
{
lean_object* v_ks_229_; lean_object* v_vs_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_ks_229_ = lean_ctor_get(v_newNode_226_, 0);
lean_inc_ref(v_ks_229_);
v_vs_230_ = lean_ctor_get(v_newNode_226_, 1);
lean_inc_ref(v_vs_230_);
lean_dec_ref(v_newNode_226_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
v___x_233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_170_, v_ks_229_, v_vs_230_, v___x_231_, v___x_232_);
lean_dec_ref(v_vs_230_);
lean_dec_ref(v_ks_229_);
return v___x_233_;
}
else
{
return v_newNode_226_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t v_depth_241_, lean_object* v_keys_242_, lean_object* v_vals_243_, lean_object* v_i_244_, lean_object* v_entries_245_){
_start:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_array_get_size(v_keys_242_);
v___x_247_ = lean_nat_dec_lt(v_i_244_, v___x_246_);
if (v___x_247_ == 0)
{
lean_dec(v_i_244_);
return v_entries_245_;
}
else
{
lean_object* v_k_248_; lean_object* v_v_249_; uint64_t v___x_250_; size_t v_h_251_; size_t v___x_252_; lean_object* v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v_h_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_k_248_ = lean_array_fget_borrowed(v_keys_242_, v_i_244_);
v_v_249_ = lean_array_fget_borrowed(v_vals_243_, v_i_244_);
v___x_250_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_248_);
v_h_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = ((size_t)5ULL);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v_depth_241_, v___x_254_);
v___x_256_ = lean_usize_mul(v___x_252_, v___x_255_);
v_h_257_ = lean_usize_shift_right(v_h_251_, v___x_256_);
v___x_258_ = lean_nat_add(v_i_244_, v___x_253_);
lean_dec(v_i_244_);
lean_inc(v_v_249_);
lean_inc(v_k_248_);
v___x_259_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_245_, v_h_257_, v_depth_241_, v_k_248_, v_v_249_);
v_i_244_ = v___x_258_;
v_entries_245_ = v___x_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_261_, lean_object* v_keys_262_, lean_object* v_vals_263_, lean_object* v_i_264_, lean_object* v_entries_265_){
_start:
{
size_t v_depth_boxed_266_; lean_object* v_res_267_; 
v_depth_boxed_266_ = lean_unbox_usize(v_depth_261_);
lean_dec(v_depth_261_);
v_res_267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_boxed_266_, v_keys_262_, v_vals_263_, v_i_264_, v_entries_265_);
lean_dec_ref(v_vals_263_);
lean_dec_ref(v_keys_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
size_t v_x_2988__boxed_273_; size_t v_x_2989__boxed_274_; lean_object* v_res_275_; 
v_x_2988__boxed_273_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_x_2989__boxed_274_ = lean_unbox_usize(v_x_270_);
lean_dec(v_x_270_);
v_res_275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_268_, v_x_2988__boxed_273_, v_x_2989__boxed_274_, v_x_271_, v_x_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint64_t v___x_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v___x_279_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_277_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_276_, v___x_280_, v___x_281_, v_x_277_, v_x_278_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object* v_e_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; lean_object* v_inferType_291_; lean_object* v___x_292_; 
v___x_290_ = lean_st_ref_get(v_a_284_);
v_inferType_291_ = lean_ctor_get(v___x_290_, 3);
lean_inc_ref(v_inferType_291_);
lean_dec(v___x_290_);
v___x_292_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_291_, v_e_283_);
if (lean_obj_tag(v___x_292_) == 1)
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_e_283_);
v_val_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 0);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_val_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_object* v___x_301_; 
lean_dec(v___x_292_);
lean_inc_ref(v_e_283_);
v___x_301_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_283_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_303_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref(v___x_301_);
v___x_303_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_302_, v_a_284_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_329_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_329_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_329_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_329_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v_share_309_; lean_object* v_maxFVar_310_; lean_object* v_proofInstInfo_311_; lean_object* v_inferType_312_; lean_object* v_getLevel_313_; lean_object* v_congrInfo_314_; lean_object* v_defEqI_315_; uint8_t v_debug_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_328_; 
v___x_308_ = lean_st_ref_take(v_a_284_);
v_share_309_ = lean_ctor_get(v___x_308_, 0);
v_maxFVar_310_ = lean_ctor_get(v___x_308_, 1);
v_proofInstInfo_311_ = lean_ctor_get(v___x_308_, 2);
v_inferType_312_ = lean_ctor_get(v___x_308_, 3);
v_getLevel_313_ = lean_ctor_get(v___x_308_, 4);
v_congrInfo_314_ = lean_ctor_get(v___x_308_, 5);
v_defEqI_315_ = lean_ctor_get(v___x_308_, 6);
v_debug_316_ = lean_ctor_get_uint8(v___x_308_, sizeof(void*)*7);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_328_ == 0)
{
v___x_318_ = v___x_308_;
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_defEqI_315_);
lean_inc(v_congrInfo_314_);
lean_inc(v_getLevel_313_);
lean_inc(v_inferType_312_);
lean_inc(v_proofInstInfo_311_);
lean_inc(v_maxFVar_310_);
lean_inc(v_share_309_);
lean_dec(v___x_308_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_inc(v_a_304_);
v___x_320_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_312_, v_e_283_, v_a_304_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 3, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_share_309_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_maxFVar_310_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_proofInstInfo_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_getLevel_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_congrInfo_314_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_defEqI_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*7, v_debug_316_);
v___x_322_ = v_reuseFailAlloc_327_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_st_ref_set(v_a_284_, v___x_322_);
if (v_isShared_307_ == 0)
{
v___x_325_ = v___x_306_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_304_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_283_);
return v___x_303_;
}
}
else
{
lean_dec_ref(v_e_283_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___redArg___boxed(lean_object* v_e_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Sym_inferType___redArg(v_e_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_331_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType(lean_object* v_e_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_Sym_inferType___redArg(v_e_338_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Meta_Sym_inferType(v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object* v_00_u03b2_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object* v_00_u03b2_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(v_00_u03b2_360_, v_x_361_, v_x_362_);
lean_dec_ref(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_x_365_, v_x_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object* v_00_u03b2_369_, lean_object* v_x_370_, size_t v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_370_, v_x_371_, v_x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_3279__boxed_378_; lean_object* v_res_379_; 
v_x_3279__boxed_378_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_374_, v_x_375_, v_x_3279__boxed_378_, v_x_377_);
lean_dec_ref(v_x_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object* v_00_u03b2_380_, lean_object* v_x_381_, size_t v_x_382_, size_t v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_381_, v_x_382_, v_x_383_, v_x_384_, v_x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
size_t v_x_3290__boxed_393_; size_t v_x_3291__boxed_394_; lean_object* v_res_395_; 
v_x_3290__boxed_393_ = lean_unbox_usize(v_x_389_);
lean_dec(v_x_389_);
v_x_3291__boxed_394_ = lean_unbox_usize(v_x_390_);
lean_dec(v_x_390_);
v_res_395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_387_, v_x_388_, v_x_3290__boxed_393_, v_x_3291__boxed_394_, v_x_391_, v_x_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_396_, lean_object* v_keys_397_, lean_object* v_vals_398_, lean_object* v_heq_399_, lean_object* v_i_400_, lean_object* v_k_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_397_, v_vals_398_, v_i_400_, v_k_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_403_, lean_object* v_keys_404_, lean_object* v_vals_405_, lean_object* v_heq_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_403_, v_keys_404_, v_vals_405_, v_heq_406_, v_i_407_, v_k_408_);
lean_dec_ref(v_k_408_);
lean_dec_ref(v_vals_405_);
lean_dec_ref(v_keys_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_410_, lean_object* v_n_411_, lean_object* v_k_412_, lean_object* v_v_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_411_, v_k_412_, v_v_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_415_, size_t v_depth_416_, lean_object* v_keys_417_, lean_object* v_vals_418_, lean_object* v_heq_419_, lean_object* v_i_420_, lean_object* v_entries_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_416_, v_keys_417_, v_vals_418_, v_i_420_, v_entries_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_423_, lean_object* v_depth_424_, lean_object* v_keys_425_, lean_object* v_vals_426_, lean_object* v_heq_427_, lean_object* v_i_428_, lean_object* v_entries_429_){
_start:
{
size_t v_depth_boxed_430_; lean_object* v_res_431_; 
v_depth_boxed_430_ = lean_unbox_usize(v_depth_424_);
lean_dec(v_depth_424_);
v_res_431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_423_, v_depth_boxed_430_, v_keys_425_, v_vals_426_, v_heq_427_, v_i_428_, v_entries_429_);
lean_dec_ref(v_vals_426_);
lean_dec_ref(v_keys_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_433_, v_x_434_, v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object* v_type_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_getLevel_446_; lean_object* v___x_447_; 
v___x_445_ = lean_st_ref_get(v_a_439_);
v_getLevel_446_ = lean_ctor_get(v___x_445_, 4);
lean_inc_ref(v_getLevel_446_);
lean_dec(v___x_445_);
v___x_447_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_446_, v_type_438_);
if (lean_obj_tag(v___x_447_) == 1)
{
lean_object* v_val_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec_ref(v_type_438_);
v_val_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_val_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_val_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v___x_447_);
lean_inc_ref(v_type_438_);
v___x_456_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_438_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_482_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_482_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_482_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_482_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v_share_462_; lean_object* v_maxFVar_463_; lean_object* v_proofInstInfo_464_; lean_object* v_inferType_465_; lean_object* v_getLevel_466_; lean_object* v_congrInfo_467_; lean_object* v_defEqI_468_; uint8_t v_debug_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v___x_461_ = lean_st_ref_take(v_a_439_);
v_share_462_ = lean_ctor_get(v___x_461_, 0);
v_maxFVar_463_ = lean_ctor_get(v___x_461_, 1);
v_proofInstInfo_464_ = lean_ctor_get(v___x_461_, 2);
v_inferType_465_ = lean_ctor_get(v___x_461_, 3);
v_getLevel_466_ = lean_ctor_get(v___x_461_, 4);
v_congrInfo_467_ = lean_ctor_get(v___x_461_, 5);
v_defEqI_468_ = lean_ctor_get(v___x_461_, 6);
v_debug_469_ = lean_ctor_get_uint8(v___x_461_, sizeof(void*)*7);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v___x_461_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_defEqI_468_);
lean_inc(v_congrInfo_467_);
lean_inc(v_getLevel_466_);
lean_inc(v_inferType_465_);
lean_inc(v_proofInstInfo_464_);
lean_inc(v_maxFVar_463_);
lean_inc(v_share_462_);
lean_dec(v___x_461_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
lean_inc(v_a_457_);
v___x_473_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_466_, v_type_438_, v_a_457_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_share_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_maxFVar_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_proofInstInfo_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_inferType_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_congrInfo_467_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_defEqI_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_480_, sizeof(void*)*7, v_debug_469_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_st_ref_set(v_a_439_, v___x_475_);
if (v_isShared_460_ == 0)
{
v___x_478_ = v___x_459_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_457_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_438_);
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object* v_type_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel(lean_object* v_type_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_491_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object* v_type_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_Sym_getLevel(v_type_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object* v_e_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; 
lean_inc(v_a_519_);
lean_inc_ref(v_a_518_);
lean_inc(v_a_517_);
lean_inc_ref(v_a_516_);
lean_inc_ref(v_e_514_);
v___x_521_ = l_Lean_Meta_Sym_inferType___redArg(v_e_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
lean_inc(v_a_522_);
v___x_523_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_522_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_536_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_536_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_528_ = ((lean_object*)(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2));
v___x_529_ = lean_box(0);
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v_a_524_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_mkConst(v___x_528_, v___x_530_);
v___x_532_ = l_Lean_mkAppB(v___x_531_, v_a_522_, v_e_514_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_532_);
v___x_534_ = v___x_526_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_522_);
lean_dec_ref(v_e_514_);
v_a_537_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_523_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_523_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec_ref(v_e_514_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg___boxed(lean_object* v_e_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object* v_e_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_553_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object* v_e_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Sym_mkEqRefl(v_e_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_570_;
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
