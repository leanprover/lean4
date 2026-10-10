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
lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_20_;
v_res_20_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache___boxed(lean_object* v_e_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
return v_res_27_;
}
}
lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(lean_object* v_type_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_keyedConfig_34_; uint8_t v_trackZetaDelta_35_; lean_object* v_zetaDeltaSet_36_; lean_object* v_lctx_37_; lean_object* v_localInstances_38_; lean_object* v_defEqCtx_x3f_39_; lean_object* v_synthPendingDepth_40_; lean_object* v_customCanUnfoldPredicate_x3f_41_; uint8_t v_univApprox_42_; uint8_t v_inTypeClassResolution_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_keyedConfig_34_ = lean_ctor_get(v_a_29_, 0);
v_trackZetaDelta_35_ = lean_ctor_get_uint8(v_a_29_, sizeof(void*)*7);
v_zetaDeltaSet_36_ = lean_ctor_get(v_a_29_, 1);
v_lctx_37_ = lean_ctor_get(v_a_29_, 2);
v_localInstances_38_ = lean_ctor_get(v_a_29_, 3);
v_defEqCtx_x3f_39_ = lean_ctor_get(v_a_29_, 4);
v_synthPendingDepth_40_ = lean_ctor_get(v_a_29_, 5);
v_customCanUnfoldPredicate_x3f_41_ = lean_ctor_get(v_a_29_, 6);
v_univApprox_42_ = lean_ctor_get_uint8(v_a_29_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_43_ = lean_ctor_get_uint8(v_a_29_, sizeof(void*)*7 + 2);
v___x_44_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_41_);
lean_inc(v_synthPendingDepth_40_);
lean_inc(v_defEqCtx_x3f_39_);
lean_inc_ref(v_localInstances_38_);
lean_inc_ref(v_lctx_37_);
lean_inc(v_zetaDeltaSet_36_);
lean_inc_ref(v_keyedConfig_34_);
v___x_45_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_45_, 0, v_keyedConfig_34_);
lean_ctor_set(v___x_45_, 1, v_zetaDeltaSet_36_);
lean_ctor_set(v___x_45_, 2, v_lctx_37_);
lean_ctor_set(v___x_45_, 3, v_localInstances_38_);
lean_ctor_set(v___x_45_, 4, v_defEqCtx_x3f_39_);
lean_ctor_set(v___x_45_, 5, v_synthPendingDepth_40_);
lean_ctor_set(v___x_45_, 6, v_customCanUnfoldPredicate_x3f_41_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7, v_trackZetaDelta_35_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7 + 1, v_univApprox_42_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7 + 2, v_inTypeClassResolution_43_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7 + 3, v___x_44_);
v___x_46_ = l_Lean_Meta_getLevel(v_type_28_, v___x_45_, v_a_30_, v_a_31_, v_a_32_);
lean_dec_ref_known(v___x_45_, 7);
return v___x_46_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_28_ = stack[0].m_obj;
lean_object* v_a_29_ = stack[1].m_obj;
lean_object* v_a_30_ = stack[2].m_obj;
lean_object* v_a_31_ = stack[3].m_obj;
lean_object* v_a_32_ = stack[4].m_obj;
lean_object* v_res_47_;
v_res_47_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache___boxed(lean_object* v_type_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_55_, lean_object* v_vals_56_, lean_object* v_i_57_, lean_object* v_k_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_keys_55_);
v___x_60_ = lean_nat_dec_lt(v_i_57_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v_i_57_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v_k_x27_62_; size_t v___x_63_; size_t v___x_64_; uint8_t v___x_65_; 
v_k_x27_62_ = lean_array_fget_borrowed(v_keys_55_, v_i_57_);
v___x_63_ = lean_ptr_addr(v_k_58_);
v___x_64_ = lean_ptr_addr(v_k_x27_62_);
v___x_65_ = lean_usize_dec_eq(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_i_57_, v___x_66_);
lean_dec(v_i_57_);
v_i_57_ = v___x_67_;
goto _start;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_array_fget_borrowed(v_vals_56_, v_i_57_);
lean_dec(v_i_57_);
lean_inc(v___x_69_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_71_, lean_object* v_vals_72_, lean_object* v_i_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_71_, v_vals_72_, v_i_73_, v_k_74_);
lean_dec_ref(v_k_74_);
lean_dec_ref(v_vals_72_);
lean_dec_ref(v_keys_71_);
return v_res_75_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(lean_object* v_x_76_, size_t v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_es_79_; lean_object* v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v_j_83_; lean_object* v___x_84_; 
v_es_79_ = lean_ctor_get(v_x_76_, 0);
v___x_80_ = lean_box(2);
v___x_81_ = ((size_t)31ULL);
v___x_82_ = lean_usize_land(v_x_77_, v___x_81_);
v_j_83_ = lean_usize_to_nat(v___x_82_);
v___x_84_ = lean_array_get_borrowed(v___x_80_, v_es_79_, v_j_83_);
lean_dec(v_j_83_);
switch(lean_obj_tag(v___x_84_))
{
case 0:
{
lean_object* v_key_85_; lean_object* v_val_86_; size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v_key_85_ = lean_ctor_get(v___x_84_, 0);
v_val_86_ = lean_ctor_get(v___x_84_, 1);
v___x_87_ = lean_ptr_addr(v_x_78_);
v___x_88_ = lean_ptr_addr(v_key_85_);
v___x_89_ = lean_usize_dec_eq(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_inc(v_val_86_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_val_86_);
return v___x_91_;
}
}
case 1:
{
lean_object* v_node_92_; size_t v___x_93_; size_t v___x_94_; 
v_node_92_ = lean_ctor_get(v___x_84_, 0);
v___x_93_ = ((size_t)5ULL);
v___x_94_ = lean_usize_shift_right(v_x_77_, v___x_93_);
v_x_76_ = v_node_92_;
v_x_77_ = v___x_94_;
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
v_ks_97_ = lean_ctor_get(v_x_76_, 0);
v_vs_98_ = lean_ctor_get(v_x_76_, 1);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_97_, v_vs_98_, v___x_99_, v_x_78_);
return v___x_100_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_76_ = stack[0].m_obj;
size_t v_x_77_ = stack[1].m_num;
lean_object* v_x_78_ = stack[2].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_76_, v_x_77_, v_x_78_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
size_t v_x_3016__boxed_105_; lean_object* v_res_106_; 
v_x_3016__boxed_105_ = lean_unbox_usize(v_x_103_);
lean_dec(v_x_103_);
v_res_106_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_102_, v_x_3016__boxed_105_, v_x_104_);
lean_dec_ref(v_x_104_);
lean_dec_ref(v_x_102_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; uint64_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v___x_109_ = lean_ptr_addr(v_x_108_);
v___x_110_ = ((size_t)3ULL);
v___x_111_ = lean_usize_shift_right(v___x_109_, v___x_110_);
v___x_112_ = lean_usize_to_uint64(v___x_111_);
v___x_113_ = lean_uint64_to_usize(v___x_112_);
v___x_114_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_107_, v___x_113_, v_x_108_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_115_, v_x_116_);
lean_dec_ref(v_x_116_);
lean_dec_ref(v_x_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_ks_122_; lean_object* v_vs_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_149_; 
v_ks_122_ = lean_ctor_get(v_x_118_, 0);
v_vs_123_ = lean_ctor_get(v_x_118_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_118_);
if (v_isSharedCheck_149_ == 0)
{
v___x_125_ = v_x_118_;
v_isShared_126_ = v_isSharedCheck_149_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_vs_123_);
lean_inc(v_ks_122_);
lean_dec(v_x_118_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_149_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_array_get_size(v_ks_122_);
v___x_128_ = lean_nat_dec_lt(v_x_119_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
lean_dec(v_x_119_);
v___x_129_ = lean_array_push(v_ks_122_, v_x_120_);
v___x_130_ = lean_array_push(v_vs_123_, v_x_121_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_130_);
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v_k_x27_134_; size_t v___x_135_; size_t v___x_136_; uint8_t v___x_137_; 
v_k_x27_134_ = lean_array_fget_borrowed(v_ks_122_, v_x_119_);
v___x_135_ = lean_ptr_addr(v_x_120_);
v___x_136_ = lean_ptr_addr(v_k_x27_134_);
v___x_137_ = lean_usize_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; 
if (v_isShared_126_ == 0)
{
v___x_139_ = v___x_125_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_ks_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_vs_123_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_x_119_, v___x_140_);
lean_dec(v_x_119_);
v_x_118_ = v___x_139_;
v_x_119_ = v___x_141_;
goto _start;
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_array_fset(v_ks_122_, v_x_119_, v_x_120_);
v___x_145_ = lean_array_fset(v_vs_123_, v_x_119_, v_x_121_);
lean_dec(v_x_119_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_145_);
lean_ctor_set(v___x_125_, 0, v___x_144_);
v___x_147_ = v___x_125_;
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
v___x_155_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_155_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(lean_object* v_x_156_, size_t v_x_157_, size_t v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v_es_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v_j_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_es_161_ = lean_ctor_get(v_x_156_, 0);
v___x_162_ = ((size_t)31ULL);
v___x_163_ = lean_usize_land(v_x_157_, v___x_162_);
v_j_164_ = lean_usize_to_nat(v___x_163_);
v___x_165_ = lean_array_get_size(v_es_161_);
v___x_166_ = lean_nat_dec_lt(v_j_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_j_164_);
lean_dec(v_x_160_);
lean_dec_ref(v_x_159_);
return v_x_156_;
}
else
{
lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_es_161_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_x_156_, 0);
lean_dec(v_unused_208_);
v___x_168_ = v_x_156_;
v_isShared_169_ = v_isSharedCheck_207_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_x_156_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_207_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_v_170_; lean_object* v___x_171_; lean_object* v_xs_x27_172_; lean_object* v___y_174_; 
v_v_170_ = lean_array_fget(v_es_161_, v_j_164_);
v___x_171_ = lean_box(0);
v_xs_x27_172_ = lean_array_fset(v_es_161_, v_j_164_, v___x_171_);
switch(lean_obj_tag(v_v_170_))
{
case 0:
{
lean_object* v_key_179_; lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_192_; 
v_key_179_ = lean_ctor_get(v_v_170_, 0);
v_val_180_ = lean_ctor_get(v_v_170_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_v_170_);
if (v_isSharedCheck_192_ == 0)
{
v___x_182_ = v_v_170_;
v_isShared_183_ = v_isSharedCheck_192_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_inc(v_key_179_);
lean_dec(v_v_170_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_192_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
size_t v___x_184_; size_t v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_ptr_addr(v_x_159_);
v___x_185_ = lean_ptr_addr(v_key_179_);
v___x_186_ = lean_usize_dec_eq(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_del_object(v___x_182_);
v___x_187_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_179_, v_val_180_, v_x_159_, v_x_160_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___y_174_ = v___x_188_;
goto v___jp_173_;
}
else
{
lean_object* v___x_190_; 
lean_dec(v_val_180_);
lean_dec(v_key_179_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_x_160_);
lean_ctor_set(v___x_182_, 0, v_x_159_);
v___x_190_ = v___x_182_;
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
v___y_174_ = v___x_190_;
goto v___jp_173_;
}
}
}
}
case 1:
{
lean_object* v_node_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_205_; 
v_node_193_ = lean_ctor_get(v_v_170_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_v_170_);
if (v_isSharedCheck_205_ == 0)
{
v___x_195_ = v_v_170_;
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_node_193_);
lean_dec(v_v_170_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_197_ = ((size_t)5ULL);
v___x_198_ = lean_usize_shift_right(v_x_157_, v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_x_158_, v___x_199_);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_193_, v___x_198_, v___x_200_, v_x_159_, v_x_160_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_203_ = v___x_195_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v___y_174_ = v___x_203_;
goto v___jp_173_;
}
}
}
default: 
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_x_159_);
lean_ctor_set(v___x_206_, 1, v_x_160_);
v___y_174_ = v___x_206_;
goto v___jp_173_;
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_array_fset(v_xs_x27_172_, v_j_164_, v___y_174_);
lean_dec(v_j_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_175_);
v___x_177_ = v___x_168_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v_ks_209_; lean_object* v_vs_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_228_; 
v_ks_209_ = lean_ctor_get(v_x_156_, 0);
v_vs_210_ = lean_ctor_get(v_x_156_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_228_ == 0)
{
v___x_212_ = v_x_156_;
v_isShared_213_ = v_isSharedCheck_228_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_vs_210_);
lean_inc(v_ks_209_);
lean_dec(v_x_156_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_228_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_ks_209_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_vs_210_);
v___x_215_ = v_reuseFailAlloc_227_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v_newNode_216_; size_t v___x_217_; uint8_t v___x_218_; 
v_newNode_216_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_215_, v_x_159_, v_x_160_);
v___x_217_ = ((size_t)7ULL);
v___x_218_ = lean_usize_dec_le(v___x_217_, v_x_158_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_216_);
v___x_220_ = lean_unsigned_to_nat(4u);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v_ks_222_; lean_object* v_vs_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_ks_222_ = lean_ctor_get(v_newNode_216_, 0);
lean_inc_ref(v_ks_222_);
v_vs_223_ = lean_ctor_get(v_newNode_216_, 1);
lean_inc_ref(v_vs_223_);
lean_dec_ref(v_newNode_216_);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
v___x_226_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_158_, v_ks_222_, v_vs_223_, v___x_224_, v___x_225_);
lean_dec_ref(v_vs_223_);
lean_dec_ref(v_ks_222_);
return v___x_226_;
}
else
{
return v_newNode_216_;
}
}
else
{
return v_newNode_216_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_156_ = stack[0].m_obj;
size_t v_x_157_ = stack[1].m_num;
size_t v_x_158_ = stack[2].m_num;
lean_object* v_x_159_ = stack[3].m_obj;
lean_object* v_x_160_ = stack[4].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_156_, v_x_157_, v_x_158_, v_x_159_, v_x_160_);
stack->m_obj
 = v_res_229_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(size_t v_depth_230_, lean_object* v_keys_231_, lean_object* v_vals_232_, lean_object* v_i_233_, lean_object* v_entries_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_keys_231_);
v___x_236_ = lean_nat_dec_lt(v_i_233_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_i_233_);
return v_entries_234_;
}
else
{
lean_object* v_k_237_; lean_object* v_v_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; uint64_t v___x_242_; size_t v_h_243_; size_t v___x_244_; lean_object* v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v_h_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_k_237_ = lean_array_fget_borrowed(v_keys_231_, v_i_233_);
v_v_238_ = lean_array_fget_borrowed(v_vals_232_, v_i_233_);
v___x_239_ = lean_ptr_addr(v_k_237_);
v___x_240_ = ((size_t)3ULL);
v___x_241_ = lean_usize_shift_right(v___x_239_, v___x_240_);
v___x_242_ = lean_usize_to_uint64(v___x_241_);
v_h_243_ = lean_uint64_to_usize(v___x_242_);
v___x_244_ = ((size_t)5ULL);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v_depth_230_, v___x_246_);
v___x_248_ = lean_usize_mul(v___x_244_, v___x_247_);
v_h_249_ = lean_usize_shift_right(v_h_243_, v___x_248_);
v___x_250_ = lean_nat_add(v_i_233_, v___x_245_);
lean_dec(v_i_233_);
lean_inc(v_v_238_);
lean_inc(v_k_237_);
v___x_251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_234_, v_h_249_, v_depth_230_, v_k_237_, v_v_238_);
v_i_233_ = v___x_250_;
v_entries_234_ = v___x_251_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_230_ = stack[0].m_num;
lean_object* v_keys_231_ = stack[1].m_obj;
lean_object* v_vals_232_ = stack[2].m_obj;
lean_object* v_i_233_ = stack[3].m_obj;
lean_object* v_entries_234_ = stack[4].m_obj;
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_230_, v_keys_231_, v_vals_232_, v_i_233_, v_entries_234_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_254_, lean_object* v_keys_255_, lean_object* v_vals_256_, lean_object* v_i_257_, lean_object* v_entries_258_){
_start:
{
size_t v_depth_boxed_259_; lean_object* v_res_260_; 
v_depth_boxed_259_ = lean_unbox_usize(v_depth_254_);
lean_dec(v_depth_254_);
v_res_260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_boxed_259_, v_keys_255_, v_vals_256_, v_i_257_, v_entries_258_);
lean_dec_ref(v_vals_256_);
lean_dec_ref(v_keys_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
size_t v_x_3238__boxed_266_; size_t v_x_3239__boxed_267_; lean_object* v_res_268_; 
v_x_3238__boxed_266_ = lean_unbox_usize(v_x_262_);
lean_dec(v_x_262_);
v_x_3239__boxed_267_ = lean_unbox_usize(v_x_263_);
lean_dec(v_x_263_);
v_res_268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_261_, v_x_3238__boxed_266_, v_x_3239__boxed_267_, v_x_264_, v_x_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; uint64_t v___x_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v___x_272_ = lean_ptr_addr(v_x_270_);
v___x_273_ = ((size_t)3ULL);
v___x_274_ = lean_usize_shift_right(v___x_272_, v___x_273_);
v___x_275_ = lean_usize_to_uint64(v___x_274_);
v___x_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_269_, v___x_276_, v___x_277_, v_x_270_, v_x_271_);
return v___x_278_;
}
}
lean_object* l_Lean_Meta_Sym_inferType(lean_object* v_e_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_inferType_288_; lean_object* v___x_289_; 
v___x_287_ = lean_st_ref_get(v_a_281_);
v_inferType_288_ = lean_ctor_get(v___x_287_, 4);
lean_inc_ref(v_inferType_288_);
lean_dec(v___x_287_);
v___x_289_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_288_, v_e_279_);
lean_dec_ref(v_inferType_288_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_e_279_);
v_val_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_val_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 0);
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_val_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v___x_298_; 
lean_dec(v___x_289_);
lean_inc_ref(v_e_279_);
v___x_298_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(v_e_279_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = l_Lean_Meta_Sym_shareCommonInc(v_a_299_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_331_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_331_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_share_306_; lean_object* v_maxFVar_307_; lean_object* v_proofInstInfo_308_; lean_object* v_proofInstInfoFVar_309_; lean_object* v_inferType_310_; lean_object* v_getLevel_311_; lean_object* v_congrInfo_312_; lean_object* v_defEqI_313_; lean_object* v_extensions_314_; lean_object* v_issues_315_; lean_object* v_canon_316_; lean_object* v_instanceOverrides_317_; uint8_t v_debug_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_330_; 
v___x_305_ = lean_st_ref_take(v_a_281_);
v_share_306_ = lean_ctor_get(v___x_305_, 0);
v_maxFVar_307_ = lean_ctor_get(v___x_305_, 1);
v_proofInstInfo_308_ = lean_ctor_get(v___x_305_, 2);
v_proofInstInfoFVar_309_ = lean_ctor_get(v___x_305_, 3);
v_inferType_310_ = lean_ctor_get(v___x_305_, 4);
v_getLevel_311_ = lean_ctor_get(v___x_305_, 5);
v_congrInfo_312_ = lean_ctor_get(v___x_305_, 6);
v_defEqI_313_ = lean_ctor_get(v___x_305_, 7);
v_extensions_314_ = lean_ctor_get(v___x_305_, 8);
v_issues_315_ = lean_ctor_get(v___x_305_, 9);
v_canon_316_ = lean_ctor_get(v___x_305_, 10);
v_instanceOverrides_317_ = lean_ctor_get(v___x_305_, 11);
v_debug_318_ = lean_ctor_get_uint8(v___x_305_, sizeof(void*)*12);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_330_ == 0)
{
v___x_320_ = v___x_305_;
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_instanceOverrides_317_);
lean_inc(v_canon_316_);
lean_inc(v_issues_315_);
lean_inc(v_extensions_314_);
lean_inc(v_defEqI_313_);
lean_inc(v_congrInfo_312_);
lean_inc(v_getLevel_311_);
lean_inc(v_inferType_310_);
lean_inc(v_proofInstInfoFVar_309_);
lean_inc(v_proofInstInfo_308_);
lean_inc(v_maxFVar_307_);
lean_inc(v_share_306_);
lean_dec(v___x_305_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_a_301_);
v___x_322_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_310_, v_e_279_, v_a_301_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_share_306_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_maxFVar_307_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_proofInstInfo_308_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_proofInstInfoFVar_309_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 5, v_getLevel_311_);
lean_ctor_set(v_reuseFailAlloc_329_, 6, v_congrInfo_312_);
lean_ctor_set(v_reuseFailAlloc_329_, 7, v_defEqI_313_);
lean_ctor_set(v_reuseFailAlloc_329_, 8, v_extensions_314_);
lean_ctor_set(v_reuseFailAlloc_329_, 9, v_issues_315_);
lean_ctor_set(v_reuseFailAlloc_329_, 10, v_canon_316_);
lean_ctor_set(v_reuseFailAlloc_329_, 11, v_instanceOverrides_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_329_, sizeof(void*)*12, v_debug_318_);
v___x_324_ = v_reuseFailAlloc_329_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_st_ref_put(v_a_281_, v___x_324_);
if (v_isShared_304_ == 0)
{
v___x_327_ = v___x_303_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_301_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_279_);
return v___x_300_;
}
}
else
{
lean_dec_ref(v_e_279_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_inferType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_279_ = stack[0].m_obj;
lean_object* v_a_280_ = stack[1].m_obj;
lean_object* v_a_281_ = stack[2].m_obj;
lean_object* v_a_282_ = stack[3].m_obj;
lean_object* v_a_283_ = stack[4].m_obj;
lean_object* v_a_284_ = stack[5].m_obj;
lean_object* v_a_285_ = stack[6].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_Meta_Sym_inferType(v_e_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_inferType___boxed(lean_object* v_e_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Sym_inferType(v_e_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(lean_object* v_00_u03b2_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_x_343_, v_x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(lean_object* v_00_u03b2_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(v_00_u03b2_346_, v_x_347_, v_x_348_);
lean_dec_ref(v_x_348_);
lean_dec_ref(v_x_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_x_351_, v_x_352_, v_x_353_);
return v___x_354_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_object* v_00_u03b2_355_, lean_object* v_x_356_, size_t v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_356_, v_x_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_356_ = stack[1].m_obj;
size_t v_x_357_ = stack[2].m_num;
lean_object* v_x_358_ = stack[3].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(lean_box(0), v_x_356_, v_x_357_, v_x_358_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
size_t v_x_3641__boxed_365_; lean_object* v_res_366_; 
v_x_3641__boxed_365_ = lean_unbox_usize(v_x_363_);
lean_dec(v_x_363_);
v_res_366_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_361_, v_x_362_, v_x_3641__boxed_365_, v_x_364_);
lean_dec_ref(v_x_364_);
lean_dec_ref(v_x_362_);
return v_res_366_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_object* v_00_u03b2_367_, lean_object* v_x_368_, size_t v_x_369_, size_t v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_368_, v_x_369_, v_x_370_, v_x_371_, v_x_372_);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_368_ = stack[1].m_obj;
size_t v_x_369_ = stack[2].m_num;
size_t v_x_370_ = stack[3].m_num;
lean_object* v_x_371_ = stack[4].m_obj;
lean_object* v_x_372_ = stack[5].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(lean_box(0), v_x_368_, v_x_369_, v_x_370_, v_x_371_, v_x_372_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(lean_object* v_00_u03b2_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
size_t v_x_3659__boxed_381_; size_t v_x_3660__boxed_382_; lean_object* v_res_383_; 
v_x_3659__boxed_381_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_x_3660__boxed_382_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_res_383_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_375_, v_x_376_, v_x_3659__boxed_381_, v_x_3660__boxed_382_, v_x_379_, v_x_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_384_, lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_heq_387_, lean_object* v_i_388_, lean_object* v_k_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_385_, v_vals_386_, v_i_388_, v_k_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_391_, lean_object* v_keys_392_, lean_object* v_vals_393_, lean_object* v_heq_394_, lean_object* v_i_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_391_, v_keys_392_, v_vals_393_, v_heq_394_, v_i_395_, v_k_396_);
lean_dec_ref(v_k_396_);
lean_dec_ref(v_vals_393_);
lean_dec_ref(v_keys_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_398_, lean_object* v_n_399_, lean_object* v_k_400_, lean_object* v_v_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_399_, v_k_400_, v_v_401_);
return v___x_402_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_403_, size_t v_depth_404_, lean_object* v_keys_405_, lean_object* v_vals_406_, lean_object* v_heq_407_, lean_object* v_i_408_, lean_object* v_entries_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_404_, v_keys_405_, v_vals_406_, v_i_408_, v_entries_409_);
return v___x_410_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_404_ = stack[1].m_num;
lean_object* v_keys_405_ = stack[2].m_obj;
lean_object* v_vals_406_ = stack[3].m_obj;
lean_object* v_i_408_ = stack[5].m_obj;
lean_object* v_entries_409_ = stack[6].m_obj;
lean_object* v_res_411_;
v_res_411_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(lean_box(0), v_depth_404_, v_keys_405_, v_vals_406_, lean_box(0), v_i_408_, v_entries_409_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_412_, lean_object* v_depth_413_, lean_object* v_keys_414_, lean_object* v_vals_415_, lean_object* v_heq_416_, lean_object* v_i_417_, lean_object* v_entries_418_){
_start:
{
size_t v_depth_boxed_419_; lean_object* v_res_420_; 
v_depth_boxed_419_ = lean_unbox_usize(v_depth_413_);
lean_dec(v_depth_413_);
v_res_420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_412_, v_depth_boxed_419_, v_keys_414_, v_vals_415_, v_heq_416_, v_i_417_, v_entries_418_);
lean_dec_ref(v_vals_415_);
lean_dec_ref(v_keys_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_421_, lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_422_, v_x_423_, v_x_424_, v_x_425_);
return v___x_426_;
}
}
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object* v_type_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; lean_object* v_getLevel_435_; lean_object* v___x_436_; 
v___x_434_ = lean_st_ref_get(v_a_428_);
v_getLevel_435_ = lean_ctor_get(v___x_434_, 5);
lean_inc_ref(v_getLevel_435_);
lean_dec(v___x_434_);
v___x_436_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_435_, v_type_427_);
lean_dec_ref(v_getLevel_435_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v_val_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v_type_427_);
v_val_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_val_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 0);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_val_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v___x_445_; 
lean_dec(v___x_436_);
lean_inc_ref(v_type_427_);
v___x_445_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(v_type_427_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_476_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_476_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_476_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_476_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v_share_451_; lean_object* v_maxFVar_452_; lean_object* v_proofInstInfo_453_; lean_object* v_proofInstInfoFVar_454_; lean_object* v_inferType_455_; lean_object* v_getLevel_456_; lean_object* v_congrInfo_457_; lean_object* v_defEqI_458_; lean_object* v_extensions_459_; lean_object* v_issues_460_; lean_object* v_canon_461_; lean_object* v_instanceOverrides_462_; uint8_t v_debug_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_475_; 
v___x_450_ = lean_st_ref_take(v_a_428_);
v_share_451_ = lean_ctor_get(v___x_450_, 0);
v_maxFVar_452_ = lean_ctor_get(v___x_450_, 1);
v_proofInstInfo_453_ = lean_ctor_get(v___x_450_, 2);
v_proofInstInfoFVar_454_ = lean_ctor_get(v___x_450_, 3);
v_inferType_455_ = lean_ctor_get(v___x_450_, 4);
v_getLevel_456_ = lean_ctor_get(v___x_450_, 5);
v_congrInfo_457_ = lean_ctor_get(v___x_450_, 6);
v_defEqI_458_ = lean_ctor_get(v___x_450_, 7);
v_extensions_459_ = lean_ctor_get(v___x_450_, 8);
v_issues_460_ = lean_ctor_get(v___x_450_, 9);
v_canon_461_ = lean_ctor_get(v___x_450_, 10);
v_instanceOverrides_462_ = lean_ctor_get(v___x_450_, 11);
v_debug_463_ = lean_ctor_get_uint8(v___x_450_, sizeof(void*)*12);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_475_ == 0)
{
v___x_465_ = v___x_450_;
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_instanceOverrides_462_);
lean_inc(v_canon_461_);
lean_inc(v_issues_460_);
lean_inc(v_extensions_459_);
lean_inc(v_defEqI_458_);
lean_inc(v_congrInfo_457_);
lean_inc(v_getLevel_456_);
lean_inc(v_inferType_455_);
lean_inc(v_proofInstInfoFVar_454_);
lean_inc(v_proofInstInfo_453_);
lean_inc(v_maxFVar_452_);
lean_inc(v_share_451_);
lean_dec(v___x_450_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_a_446_);
v___x_467_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_456_, v_type_427_, v_a_446_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 5, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_share_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_maxFVar_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_proofInstInfo_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_proofInstInfoFVar_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_inferType_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_congrInfo_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_defEqI_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_extensions_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_issues_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 10, v_canon_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 11, v_instanceOverrides_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*12, v_debug_463_);
v___x_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_st_ref_put(v_a_428_, v___x_469_);
if (v_isShared_449_ == 0)
{
v___x_472_ = v___x_448_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_446_);
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
lean_dec_ref(v_type_427_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getLevel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_427_ = stack[0].m_obj;
lean_object* v_a_428_ = stack[1].m_obj;
lean_object* v_a_429_ = stack[2].m_obj;
lean_object* v_a_430_ = stack[3].m_obj;
lean_object* v_a_431_ = stack[4].m_obj;
lean_object* v_a_432_ = stack[5].m_obj;
lean_object* v_res_477_;
v_res_477_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
stack->m_obj
 = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___redArg___boxed(lean_object* v_type_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
return v_res_485_;
}
}
lean_object* l_Lean_Meta_Sym_getLevel(lean_object* v_type_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_486_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
return v___x_494_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_486_ = stack[0].m_obj;
lean_object* v_a_487_ = stack[1].m_obj;
lean_object* v_a_488_ = stack[2].m_obj;
lean_object* v_a_489_ = stack[3].m_obj;
lean_object* v_a_490_ = stack[4].m_obj;
lean_object* v_a_491_ = stack[5].m_obj;
lean_object* v_a_492_ = stack[6].m_obj;
lean_object* v_res_495_;
v_res_495_ = l_Lean_Meta_Sym_getLevel(v_type_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getLevel___boxed(lean_object* v_type_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Sym_getLevel(v_type_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_504_;
}
}
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object* v_e_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
lean_inc_ref(v_e_510_);
v___x_518_ = l_Lean_Meta_Sym_inferType(v_e_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc_n(v_a_519_, 2);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_519_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_533_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_525_ = ((lean_object*)(l_Lean_Meta_Sym_mkEqRefl___closed__2));
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_521_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_mkConst(v___x_525_, v___x_527_);
v___x_529_ = l_Lean_mkAppB(v___x_528_, v_a_519_, v_e_510_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_529_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_a_519_);
lean_dec_ref(v_e_510_);
v_a_534_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_520_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_520_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_dec_ref(v_e_510_);
return v___x_518_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkEqRefl_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_510_ = stack[0].m_obj;
lean_object* v_a_511_ = stack[1].m_obj;
lean_object* v_a_512_ = stack[2].m_obj;
lean_object* v_a_513_ = stack[3].m_obj;
lean_object* v_a_514_ = stack[4].m_obj;
lean_object* v_a_515_ = stack[5].m_obj;
lean_object* v_a_516_ = stack[6].m_obj;
lean_object* v_res_542_;
v_res_542_ = l_Lean_Meta_Sym_mkEqRefl(v_e_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkEqRefl___boxed(lean_object* v_e_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Sym_mkEqRefl(v_e_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_551_;
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
