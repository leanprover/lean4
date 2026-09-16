// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: public import Lean.HeadIndex public import Lean.Meta.Basic
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object* v_p_1_, lean_object* v_occs_2_, lean_object* v_pHeadIdx_3_, lean_object* v_pNumArgs_4_, lean_object* v_e_5_, lean_object* v_offset_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; uint8_t v___x_197_; 
v___x_197_ = l_Lean_Expr_hasLooseBVars(v_e_5_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
lean_inc_ref(v_e_5_);
v___x_198_ = l_Lean_Expr_toHeadIndex(v_e_5_);
v___x_199_ = l_Lean_instBEqHeadIndex_beq(v___x_198_, v_pHeadIdx_3_);
lean_dec(v___x_198_);
if (v___x_199_ == 0)
{
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
else
{
if (v___x_197_ == 0)
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = l_Lean_Expr_headNumArgs(v_e_5_);
v___x_201_ = lean_nat_dec_eq(v___x_200_, v_pNumArgs_4_);
lean_dec(v___x_200_);
if (v___x_201_ == 0)
{
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
else
{
if (v___x_197_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_st_ref_get(v_a_9_);
lean_inc_ref(v_p_1_);
lean_inc_ref(v_e_5_);
v___x_203_ = l_Lean_Meta_isExprDefEq(v_e_5_, v_p_1_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_233_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_233_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_233_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_233_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
uint8_t v___x_208_; 
v___x_208_ = lean_unbox(v_a_204_);
lean_dec(v_a_204_);
if (v___x_208_ == 0)
{
lean_del_object(v___x_206_);
lean_dec(v___x_202_);
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_209_ = lean_st_ref_get(v_a_7_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v___x_209_, v___x_210_);
v___x_212_ = lean_st_ref_swap(v_a_7_, v___x_211_);
lean_dec(v___x_212_);
v___x_213_ = l_Lean_Meta_Occurrences_contains(v_occs_2_, v___x_209_);
lean_dec(v___x_209_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v_mctx_215_; lean_object* v_cache_216_; lean_object* v_zetaDeltaFVarIds_217_; lean_object* v_postponed_218_; lean_object* v_diag_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
lean_del_object(v___x_206_);
v___x_214_ = lean_st_ref_take(v_a_9_);
v_mctx_215_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_mctx_215_);
lean_dec(v___x_202_);
v_cache_216_ = lean_ctor_get(v___x_214_, 1);
v_zetaDeltaFVarIds_217_ = lean_ctor_get(v___x_214_, 2);
v_postponed_218_ = lean_ctor_get(v___x_214_, 3);
v_diag_219_ = lean_ctor_get(v___x_214_, 4);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v___x_214_, 0);
lean_dec(v_unused_228_);
v___x_221_ = v___x_214_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_diag_219_);
lean_inc(v_postponed_218_);
lean_inc(v_zetaDeltaFVarIds_217_);
lean_inc(v_cache_216_);
lean_dec(v___x_214_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_mctx_215_);
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_mctx_215_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_cache_216_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_zetaDeltaFVarIds_217_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_postponed_218_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_diag_219_);
v___x_224_ = v_reuseFailAlloc_226_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; 
v___x_225_ = lean_st_ref_put(v_a_9_, v___x_224_);
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v___x_202_);
lean_dec_ref(v_e_5_);
lean_dec_ref(v_p_1_);
v___x_229_ = l_Lean_mkBVar(v_offset_6_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_229_);
v___x_231_ = v___x_206_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v___x_202_);
lean_dec(v_offset_6_);
lean_dec_ref(v_e_5_);
lean_dec_ref(v_p_1_);
v_a_234_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_203_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_203_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
}
}
else
{
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
}
}
else
{
v___y_14_ = v_a_7_;
v___y_15_ = v_a_8_;
v___y_16_ = v_a_9_;
v___y_17_ = v_a_10_;
v___y_18_ = v_a_11_;
goto v___jp_13_;
}
v___jp_13_:
{
switch(lean_obj_tag(v_e_5_))
{
case 5:
{
lean_object* v_fn_19_; lean_object* v_arg_20_; lean_object* v___x_21_; 
v_fn_19_ = lean_ctor_get(v_e_5_, 0);
v_arg_20_ = lean_ctor_get(v_e_5_, 1);
lean_inc(v_offset_6_);
lean_inc_ref(v_fn_19_);
lean_inc_ref(v_p_1_);
v___x_21_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_fn_19_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v___x_21_, 1);
lean_inc_ref(v_arg_20_);
v___x_23_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_arg_20_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_45_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_45_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_45_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_45_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
size_t v___x_28_; size_t v___x_29_; uint8_t v___x_30_; 
v___x_28_ = lean_ptr_addr(v_fn_19_);
v___x_29_ = lean_ptr_addr(v_a_22_);
v___x_30_ = lean_usize_dec_eq(v___x_28_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_33_; 
lean_dec_ref_known(v_e_5_, 2);
v___x_31_ = l_Lean_Expr_app___override(v_a_22_, v_a_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_31_);
v___x_33_ = v___x_26_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
size_t v___x_35_; size_t v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_ptr_addr(v_arg_20_);
v___x_36_ = lean_ptr_addr(v_a_24_);
v___x_37_ = lean_usize_dec_eq(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_dec_ref_known(v_e_5_, 2);
v___x_38_ = l_Lean_Expr_app___override(v_a_22_, v_a_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_38_);
v___x_40_ = v___x_26_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v_a_24_);
lean_dec(v_a_22_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v_e_5_);
v___x_43_ = v___x_26_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_e_5_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
else
{
lean_dec(v_a_22_);
lean_dec_ref_known(v_e_5_, 2);
return v___x_23_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 2);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_21_;
}
}
case 10:
{
lean_object* v_data_46_; lean_object* v_expr_47_; lean_object* v___x_48_; 
v_data_46_ = lean_ctor_get(v_e_5_, 0);
v_expr_47_ = lean_ctor_get(v_e_5_, 1);
lean_inc_ref(v_expr_47_);
v___x_48_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_expr_47_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_63_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_63_ == 0)
{
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_63_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_63_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
size_t v___x_53_; size_t v___x_54_; uint8_t v___x_55_; 
v___x_53_ = lean_ptr_addr(v_expr_47_);
v___x_54_ = lean_ptr_addr(v_a_49_);
v___x_55_ = lean_usize_dec_eq(v___x_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_inc(v_data_46_);
lean_dec_ref_known(v_e_5_, 2);
v___x_56_ = l_Lean_Expr_mdata___override(v_data_46_, v_a_49_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_56_);
v___x_58_ = v___x_51_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
lean_object* v___x_61_; 
lean_dec(v_a_49_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v_e_5_);
v___x_61_ = v___x_51_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_e_5_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_5_, 2);
return v___x_48_;
}
}
case 11:
{
lean_object* v_typeName_64_; lean_object* v_idx_65_; lean_object* v_struct_66_; lean_object* v___x_67_; 
v_typeName_64_ = lean_ctor_get(v_e_5_, 0);
v_idx_65_ = lean_ctor_get(v_e_5_, 1);
v_struct_66_ = lean_ctor_get(v_e_5_, 2);
lean_inc_ref(v_struct_66_);
v___x_67_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_struct_66_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_82_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_82_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_82_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_82_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
size_t v___x_72_; size_t v___x_73_; uint8_t v___x_74_; 
v___x_72_ = lean_ptr_addr(v_struct_66_);
v___x_73_ = lean_ptr_addr(v_a_68_);
v___x_74_ = lean_usize_dec_eq(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_77_; 
lean_inc(v_idx_65_);
lean_inc(v_typeName_64_);
lean_dec_ref_known(v_e_5_, 3);
v___x_75_ = l_Lean_Expr_proj___override(v_typeName_64_, v_idx_65_, v_a_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_75_);
v___x_77_ = v___x_70_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v_a_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_e_5_);
v___x_80_ = v___x_70_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_e_5_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_5_, 3);
return v___x_67_;
}
}
case 8:
{
lean_object* v_declName_83_; lean_object* v_type_84_; lean_object* v_value_85_; lean_object* v_body_86_; uint8_t v_nondep_87_; lean_object* v___x_88_; 
v_declName_83_ = lean_ctor_get(v_e_5_, 0);
v_type_84_ = lean_ctor_get(v_e_5_, 1);
v_value_85_ = lean_ctor_get(v_e_5_, 2);
v_body_86_ = lean_ctor_get(v_e_5_, 3);
v_nondep_87_ = lean_ctor_get_uint8(v_e_5_, sizeof(void*)*4 + 8);
lean_inc(v_offset_6_);
lean_inc_ref(v_type_84_);
lean_inc_ref(v_p_1_);
v___x_88_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_type_84_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
lean_inc(v_offset_6_);
lean_inc_ref(v_value_85_);
lean_inc_ref(v_p_1_);
v___x_90_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_value_85_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_offset_6_, v___x_92_);
lean_dec(v_offset_6_);
lean_inc_ref(v_body_86_);
v___x_94_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_body_86_, v___x_93_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_123_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_123_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_123_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_123_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
size_t v___x_99_; size_t v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_ptr_addr(v_type_84_);
v___x_100_ = lean_ptr_addr(v_a_89_);
v___x_101_ = lean_usize_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_104_; 
lean_inc(v_declName_83_);
lean_dec_ref_known(v_e_5_, 4);
v___x_102_ = l_Lean_Expr_letE___override(v_declName_83_, v_a_89_, v_a_91_, v_a_95_, v_nondep_87_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_102_);
v___x_104_ = v___x_97_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
size_t v___x_106_; size_t v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_ptr_addr(v_value_85_);
v___x_107_ = lean_ptr_addr(v_a_91_);
v___x_108_ = lean_usize_dec_eq(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_inc(v_declName_83_);
lean_dec_ref_known(v_e_5_, 4);
v___x_109_ = l_Lean_Expr_letE___override(v_declName_83_, v_a_89_, v_a_91_, v_a_95_, v_nondep_87_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_109_);
v___x_111_ = v___x_97_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
else
{
size_t v___x_113_; size_t v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_ptr_addr(v_body_86_);
v___x_114_ = lean_ptr_addr(v_a_95_);
v___x_115_ = lean_usize_dec_eq(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_118_; 
lean_inc(v_declName_83_);
lean_dec_ref_known(v_e_5_, 4);
v___x_116_ = l_Lean_Expr_letE___override(v_declName_83_, v_a_89_, v_a_91_, v_a_95_, v_nondep_87_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_116_);
v___x_118_ = v___x_97_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v_a_95_);
lean_dec(v_a_91_);
lean_dec(v_a_89_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v_e_5_);
v___x_121_ = v___x_97_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_e_5_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
}
else
{
lean_dec(v_a_91_);
lean_dec(v_a_89_);
lean_dec_ref_known(v_e_5_, 4);
return v___x_94_;
}
}
else
{
lean_dec(v_a_89_);
lean_dec_ref_known(v_e_5_, 4);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_90_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 4);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_88_;
}
}
case 6:
{
lean_object* v_binderName_124_; lean_object* v_binderType_125_; lean_object* v_body_126_; uint8_t v_binderInfo_127_; lean_object* v___x_128_; 
v_binderName_124_ = lean_ctor_get(v_e_5_, 0);
v_binderType_125_ = lean_ctor_get(v_e_5_, 1);
v_body_126_ = lean_ctor_get(v_e_5_, 2);
v_binderInfo_127_ = lean_ctor_get_uint8(v_e_5_, sizeof(void*)*3 + 8);
lean_inc(v_offset_6_);
lean_inc_ref(v_binderType_125_);
lean_inc_ref(v_p_1_);
v___x_128_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_binderType_125_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_add(v_offset_6_, v___x_130_);
lean_dec(v_offset_6_);
lean_inc_ref(v_body_126_);
v___x_132_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_body_126_, v___x_131_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_159_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_159_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
size_t v___x_137_; size_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_ptr_addr(v_binderType_125_);
v___x_138_ = lean_ptr_addr(v_a_129_);
v___x_139_ = lean_usize_dec_eq(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_binderName_124_);
lean_dec_ref_known(v_e_5_, 3);
v___x_140_ = l_Lean_Expr_lam___override(v_binderName_124_, v_a_129_, v_a_133_, v_binderInfo_127_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_140_);
v___x_142_ = v___x_135_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
else
{
size_t v___x_144_; size_t v___x_145_; uint8_t v___x_146_; 
v___x_144_ = lean_ptr_addr(v_body_126_);
v___x_145_ = lean_ptr_addr(v_a_133_);
v___x_146_ = lean_usize_dec_eq(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_inc(v_binderName_124_);
lean_dec_ref_known(v_e_5_, 3);
v___x_147_ = l_Lean_Expr_lam___override(v_binderName_124_, v_a_129_, v_a_133_, v_binderInfo_127_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_147_);
v___x_149_ = v___x_135_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_127_, v_binderInfo_127_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_154_; 
lean_inc(v_binderName_124_);
lean_dec_ref_known(v_e_5_, 3);
v___x_152_ = l_Lean_Expr_lam___override(v_binderName_124_, v_a_129_, v_a_133_, v_binderInfo_127_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_152_);
v___x_154_ = v___x_135_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v_a_133_);
lean_dec(v_a_129_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v_e_5_);
v___x_157_ = v___x_135_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_e_5_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
else
{
lean_dec(v_a_129_);
lean_dec_ref_known(v_e_5_, 3);
return v___x_132_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 3);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_128_;
}
}
case 7:
{
lean_object* v_binderName_160_; lean_object* v_binderType_161_; lean_object* v_body_162_; uint8_t v_binderInfo_163_; lean_object* v___x_164_; 
v_binderName_160_ = lean_ctor_get(v_e_5_, 0);
v_binderType_161_ = lean_ctor_get(v_e_5_, 1);
v_body_162_ = lean_ctor_get(v_e_5_, 2);
v_binderInfo_163_ = lean_ctor_get_uint8(v_e_5_, sizeof(void*)*3 + 8);
lean_inc(v_offset_6_);
lean_inc_ref(v_binderType_161_);
lean_inc_ref(v_p_1_);
v___x_164_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_binderType_161_, v_offset_6_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_offset_6_, v___x_166_);
lean_dec(v_offset_6_);
lean_inc_ref(v_body_162_);
v___x_168_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_body_162_, v___x_167_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_195_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_195_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_195_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_195_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
size_t v___x_173_; size_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_ptr_addr(v_binderType_161_);
v___x_174_ = lean_ptr_addr(v_a_165_);
v___x_175_ = lean_usize_dec_eq(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_178_; 
lean_inc(v_binderName_160_);
lean_dec_ref_known(v_e_5_, 3);
v___x_176_ = l_Lean_Expr_forallE___override(v_binderName_160_, v_a_165_, v_a_169_, v_binderInfo_163_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_176_);
v___x_178_ = v___x_171_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
else
{
size_t v___x_180_; size_t v___x_181_; uint8_t v___x_182_; 
v___x_180_ = lean_ptr_addr(v_body_162_);
v___x_181_ = lean_ptr_addr(v_a_169_);
v___x_182_ = lean_usize_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_185_; 
lean_inc(v_binderName_160_);
lean_dec_ref_known(v_e_5_, 3);
v___x_183_ = l_Lean_Expr_forallE___override(v_binderName_160_, v_a_165_, v_a_169_, v_binderInfo_163_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_183_);
v___x_185_ = v___x_171_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
uint8_t v___x_187_; 
v___x_187_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_163_, v_binderInfo_163_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_binderName_160_);
lean_dec_ref_known(v_e_5_, 3);
v___x_188_ = l_Lean_Expr_forallE___override(v_binderName_160_, v_a_165_, v_a_169_, v_binderInfo_163_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_188_);
v___x_190_ = v___x_171_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_193_; 
lean_dec(v_a_169_);
lean_dec(v_a_165_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_e_5_);
v___x_193_ = v___x_171_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_e_5_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
else
{
lean_dec(v_a_165_);
lean_dec_ref_known(v_e_5_, 3);
return v___x_168_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 3);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_164_;
}
}
default: 
{
lean_object* v___x_196_; 
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_e_5_);
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object* v_p_242_, lean_object* v_occs_243_, lean_object* v_pHeadIdx_244_, lean_object* v_pNumArgs_245_, lean_object* v_e_246_, lean_object* v_offset_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_242_, v_occs_243_, v_pHeadIdx_244_, v_pNumArgs_245_, v_e_246_, v_offset_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec(v_pNumArgs_245_);
lean_dec(v_pHeadIdx_244_);
lean_dec(v_occs_243_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object* v_e_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Expr_hasMVar(v_e_255_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_e_255_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v_mctx_261_; lean_object* v___x_262_; lean_object* v_fst_263_; lean_object* v_snd_264_; lean_object* v___x_265_; lean_object* v_cache_266_; lean_object* v_zetaDeltaFVarIds_267_; lean_object* v_postponed_268_; lean_object* v_diag_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
v___x_260_ = lean_st_ref_get(v___y_256_);
v_mctx_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_mctx_261_);
lean_dec(v___x_260_);
v___x_262_ = l_Lean_instantiateMVarsCore(v_mctx_261_, v_e_255_);
v_fst_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_fst_263_);
v_snd_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_snd_264_);
lean_dec_ref(v___x_262_);
v___x_265_ = lean_st_ref_take(v___y_256_);
v_cache_266_ = lean_ctor_get(v___x_265_, 1);
v_zetaDeltaFVarIds_267_ = lean_ctor_get(v___x_265_, 2);
v_postponed_268_ = lean_ctor_get(v___x_265_, 3);
v_diag_269_ = lean_ctor_get(v___x_265_, 4);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_265_, 0);
lean_dec(v_unused_279_);
v___x_271_ = v___x_265_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_diag_269_);
lean_inc(v_postponed_268_);
lean_inc(v_zetaDeltaFVarIds_267_);
lean_inc(v_cache_266_);
lean_dec(v___x_265_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v_snd_264_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_snd_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_cache_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_zetaDeltaFVarIds_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_postponed_268_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_diag_269_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_st_ref_put(v___y_256_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_fst_263_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object* v_e_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_280_, v___y_281_);
lean_dec(v___y_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object* v_e_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_284_, v___y_286_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object* v_e_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(v_e_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* v_e_298_, lean_object* v_p_299_, lean_object* v_occs_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_338_; 
v___x_306_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_298_, v_a_302_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_338_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_338_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_338_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___y_312_; uint8_t v___x_335_; 
v___x_335_ = l_Lean_Expr_isFVar(v_p_299_);
if (v___x_335_ == 0)
{
v___y_312_ = v___x_335_;
goto v___jp_311_;
}
else
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_box(0);
lean_inc(v_occs_300_);
v___x_337_ = l_Lean_Meta_instBEqOccurrences_beq(v_occs_300_, v___x_336_);
v___y_312_ = v___x_337_;
goto v___jp_311_;
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_del_object(v___x_309_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_st_mk_ref(v___x_313_);
lean_inc_ref(v_p_299_);
v___x_315_ = l_Lean_Expr_toHeadIndex(v_p_299_);
v___x_316_ = l_Lean_Expr_headNumArgs(v_p_299_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_299_, v_occs_300_, v___x_315_, v___x_316_, v_a_307_, v___x_317_, v___x_314_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v___x_316_);
lean_dec(v___x_315_);
lean_dec(v_occs_300_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_st_ref_get(v___x_314_);
lean_dec(v___x_314_);
lean_dec(v___x_323_);
if (v_isShared_322_ == 0)
{
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_319_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_dec(v___x_314_);
return v___x_318_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v_occs_300_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_array_push(v___x_329_, v_p_299_);
v___x_331_ = lean_expr_abstract(v_a_307_, v___x_330_);
lean_dec_ref(v___x_330_);
lean_dec(v_a_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_331_);
v___x_333_ = v___x_309_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* v_e_339_, lean_object* v_p_340_, lean_object* v_occs_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_kabstract(v_e_339_, v_p_340_, v_occs_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_KAbstract(builtin);
}
#ifdef __cplusplus
}
#endif
