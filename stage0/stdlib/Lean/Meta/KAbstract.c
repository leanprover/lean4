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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_14_; lean_object* v___y_15_; uint8_t v___y_16_; lean_object* v___y_21_; lean_object* v___y_22_; uint8_t v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v___y_37_; lean_object* v___y_38_; uint8_t v___y_39_; lean_object* v___y_40_; uint8_t v___y_41_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___y_51_; uint8_t v___y_52_; uint8_t v___y_53_; lean_object* v___y_61_; lean_object* v___y_62_; lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___y_65_; uint8_t v___x_167_; 
v___x_167_ = l_Lean_Expr_hasLooseBVars(v_e_5_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; uint8_t v___x_170_; 
lean_inc_ref(v_e_5_);
v___x_168_ = l_Lean_Expr_toHeadIndex(v_e_5_);
v___x_169_ = l_Lean_instBEqHeadIndex_beq(v___x_168_, v_pHeadIdx_3_);
lean_dec(v___x_168_);
v___x_170_ = lean_bool_not(v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; 
v___x_171_ = l_Lean_Expr_headNumArgs(v_e_5_);
v___x_172_ = lean_nat_dec_eq(v___x_171_, v_pNumArgs_4_);
lean_dec(v___x_171_);
v___x_173_ = lean_bool_not(v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_st_ref_get(v_a_9_);
lean_inc_ref(v_p_1_);
lean_inc_ref(v_e_5_);
v___x_175_ = l_Lean_Meta_isExprDefEq(v_e_5_, v_p_1_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_205_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_205_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_205_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_205_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v___x_180_; 
v___x_180_ = lean_unbox(v_a_176_);
lean_dec(v_a_176_);
if (v___x_180_ == 0)
{
lean_del_object(v___x_178_);
lean_dec(v___x_174_);
v___y_61_ = v_a_7_;
v___y_62_ = v_a_8_;
v___y_63_ = v_a_9_;
v___y_64_ = v_a_10_;
v___y_65_ = v_a_11_;
goto v___jp_60_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_181_ = lean_st_ref_get(v_a_7_);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v___x_181_, v___x_182_);
v___x_184_ = lean_st_ref_set(v_a_7_, v___x_183_);
v___x_185_ = l_Lean_Meta_Occurrences_contains(v_occs_2_, v___x_181_);
lean_dec(v___x_181_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v_mctx_187_; lean_object* v_cache_188_; lean_object* v_zetaDeltaFVarIds_189_; lean_object* v_postponed_190_; lean_object* v_diag_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
lean_del_object(v___x_178_);
v___x_186_ = lean_st_ref_take(v_a_9_);
v_mctx_187_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_mctx_187_);
lean_dec(v___x_174_);
v_cache_188_ = lean_ctor_get(v___x_186_, 1);
v_zetaDeltaFVarIds_189_ = lean_ctor_get(v___x_186_, 2);
v_postponed_190_ = lean_ctor_get(v___x_186_, 3);
v_diag_191_ = lean_ctor_get(v___x_186_, 4);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v___x_186_, 0);
lean_dec(v_unused_200_);
v___x_193_ = v___x_186_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_diag_191_);
lean_inc(v_postponed_190_);
lean_inc(v_zetaDeltaFVarIds_189_);
lean_inc(v_cache_188_);
lean_dec(v___x_186_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v_mctx_187_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_mctx_187_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_cache_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_zetaDeltaFVarIds_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_postponed_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v_diag_191_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = lean_st_ref_set(v_a_9_, v___x_196_);
v___y_61_ = v_a_7_;
v___y_62_ = v_a_8_;
v___y_63_ = v_a_9_;
v___y_64_ = v_a_10_;
v___y_65_ = v_a_11_;
goto v___jp_60_;
}
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_203_; 
lean_dec(v___x_174_);
lean_dec_ref(v_e_5_);
lean_dec_ref(v_p_1_);
v___x_201_ = l_Lean_mkBVar(v_offset_6_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_201_);
v___x_203_ = v___x_178_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v___x_174_);
lean_dec(v_offset_6_);
lean_dec_ref(v_e_5_);
lean_dec_ref(v_p_1_);
v_a_206_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_175_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_175_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
v___y_61_ = v_a_7_;
v___y_62_ = v_a_8_;
v___y_63_ = v_a_9_;
v___y_64_ = v_a_10_;
v___y_65_ = v_a_11_;
goto v___jp_60_;
}
}
else
{
v___y_61_ = v_a_7_;
v___y_62_ = v_a_8_;
v___y_63_ = v_a_9_;
v___y_64_ = v_a_10_;
v___y_65_ = v_a_11_;
goto v___jp_60_;
}
}
else
{
v___y_61_ = v_a_7_;
v___y_62_ = v_a_8_;
v___y_63_ = v_a_9_;
v___y_64_ = v_a_10_;
v___y_65_ = v_a_11_;
goto v___jp_60_;
}
v___jp_13_:
{
if (v___y_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec_ref(v_e_5_);
v___x_17_ = l_Lean_Expr_app___override(v___y_14_, v___y_15_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; 
lean_dec_ref(v___y_15_);
lean_dec_ref(v___y_14_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v_e_5_);
return v___x_19_;
}
}
v___jp_20_:
{
if (v___y_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec_ref(v___y_22_);
lean_dec_ref(v_e_5_);
v___x_28_ = l_Lean_Expr_letE___override(v___y_21_, v___y_26_, v___y_25_, v___y_24_, v___y_23_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
else
{
size_t v___x_30_; size_t v___x_31_; uint8_t v___x_32_; 
v___x_30_ = lean_ptr_addr(v___y_22_);
lean_dec_ref(v___y_22_);
v___x_31_ = lean_ptr_addr(v___y_24_);
v___x_32_ = lean_usize_dec_eq(v___x_30_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec_ref(v_e_5_);
v___x_33_ = l_Lean_Expr_letE___override(v___y_21_, v___y_26_, v___y_25_, v___y_24_, v___y_23_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
lean_dec_ref(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_21_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v_e_5_);
return v___x_35_;
}
}
}
v___jp_36_:
{
if (v___y_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec_ref(v_e_5_);
v___x_42_ = l_Lean_Expr_lam___override(v___y_38_, v___y_37_, v___y_40_, v___y_39_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = l_Lean_instBEqBinderInfo_beq(v___y_39_, v___y_39_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec_ref(v_e_5_);
v___x_45_ = l_Lean_Expr_lam___override(v___y_38_, v___y_37_, v___y_40_, v___y_39_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; 
lean_dec_ref(v___y_40_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v_e_5_);
return v___x_47_;
}
}
}
v___jp_48_:
{
if (v___y_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v_e_5_);
v___x_54_ = l_Lean_Expr_forallE___override(v___y_51_, v___y_49_, v___y_50_, v___y_52_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = l_Lean_instBEqBinderInfo_beq(v___y_52_, v___y_52_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref(v_e_5_);
v___x_57_ = l_Lean_Expr_forallE___override(v___y_51_, v___y_49_, v___y_50_, v___y_52_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; 
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec_ref(v___y_49_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v_e_5_);
return v___x_59_;
}
}
}
v___jp_60_:
{
switch(lean_obj_tag(v_e_5_))
{
case 5:
{
lean_object* v_fn_66_; lean_object* v_arg_67_; lean_object* v___x_68_; 
v_fn_66_ = lean_ctor_get(v_e_5_, 0);
v_arg_67_ = lean_ctor_get(v_e_5_, 1);
lean_inc(v_offset_6_);
lean_inc_ref(v_fn_66_);
lean_inc_ref(v_p_1_);
v___x_68_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_fn_66_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_68_, 1);
lean_inc_ref(v_arg_67_);
v___x_70_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_arg_67_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; size_t v___x_72_; size_t v___x_73_; uint8_t v___x_74_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = lean_ptr_addr(v_fn_66_);
v___x_73_ = lean_ptr_addr(v_a_69_);
v___x_74_ = lean_usize_dec_eq(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
v___y_14_ = v_a_69_;
v___y_15_ = v_a_71_;
v___y_16_ = v___x_74_;
goto v___jp_13_;
}
else
{
size_t v___x_75_; size_t v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_ptr_addr(v_arg_67_);
v___x_76_ = lean_ptr_addr(v_a_71_);
v___x_77_ = lean_usize_dec_eq(v___x_75_, v___x_76_);
v___y_14_ = v_a_69_;
v___y_15_ = v_a_71_;
v___y_16_ = v___x_77_;
goto v___jp_13_;
}
}
else
{
lean_dec(v_a_69_);
lean_dec_ref_known(v_e_5_, 2);
return v___x_70_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 2);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_68_;
}
}
case 10:
{
lean_object* v_data_78_; lean_object* v_expr_79_; lean_object* v___x_80_; 
v_data_78_ = lean_ctor_get(v_e_5_, 0);
v_expr_79_ = lean_ctor_get(v_e_5_, 1);
lean_inc_ref(v_expr_79_);
v___x_80_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_expr_79_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_95_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_95_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_95_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_95_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
size_t v___x_85_; size_t v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_ptr_addr(v_expr_79_);
v___x_86_ = lean_ptr_addr(v_a_81_);
v___x_87_ = lean_usize_dec_eq(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_inc(v_data_78_);
lean_dec_ref_known(v_e_5_, 2);
v___x_88_ = l_Lean_Expr_mdata___override(v_data_78_, v_a_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_88_);
v___x_90_ = v___x_83_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
else
{
lean_object* v___x_93_; 
lean_dec(v_a_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_e_5_);
v___x_93_ = v___x_83_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_e_5_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_5_, 2);
return v___x_80_;
}
}
case 11:
{
lean_object* v_typeName_96_; lean_object* v_idx_97_; lean_object* v_struct_98_; lean_object* v___x_99_; 
v_typeName_96_ = lean_ctor_get(v_e_5_, 0);
v_idx_97_ = lean_ctor_get(v_e_5_, 1);
v_struct_98_ = lean_ctor_get(v_e_5_, 2);
lean_inc_ref(v_struct_98_);
v___x_99_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_struct_98_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_114_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_114_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_114_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_114_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
size_t v___x_104_; size_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_ptr_addr(v_struct_98_);
v___x_105_ = lean_ptr_addr(v_a_100_);
v___x_106_ = lean_usize_dec_eq(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_109_; 
lean_inc(v_idx_97_);
lean_inc(v_typeName_96_);
lean_dec_ref_known(v_e_5_, 3);
v___x_107_ = l_Lean_Expr_proj___override(v_typeName_96_, v_idx_97_, v_a_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_107_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec(v_a_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_e_5_);
v___x_112_ = v___x_102_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_e_5_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_5_, 3);
return v___x_99_;
}
}
case 8:
{
lean_object* v_declName_115_; lean_object* v_type_116_; lean_object* v_value_117_; lean_object* v_body_118_; uint8_t v_nondep_119_; lean_object* v___x_120_; 
v_declName_115_ = lean_ctor_get(v_e_5_, 0);
v_type_116_ = lean_ctor_get(v_e_5_, 1);
v_value_117_ = lean_ctor_get(v_e_5_, 2);
v_body_118_ = lean_ctor_get(v_e_5_, 3);
v_nondep_119_ = lean_ctor_get_uint8(v_e_5_, sizeof(void*)*4 + 8);
lean_inc(v_offset_6_);
lean_inc_ref(v_type_116_);
lean_inc_ref(v_p_1_);
v___x_120_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_type_116_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_120_, 1);
lean_inc(v_offset_6_);
lean_inc_ref(v_value_117_);
lean_inc_ref(v_p_1_);
v___x_122_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_value_117_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_offset_6_, v___x_124_);
lean_dec(v_offset_6_);
lean_inc_ref(v_body_118_);
v___x_126_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_body_118_, v___x_125_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; size_t v___x_128_; size_t v___x_129_; uint8_t v___x_130_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = lean_ptr_addr(v_type_116_);
v___x_129_ = lean_ptr_addr(v_a_121_);
v___x_130_ = lean_usize_dec_eq(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_inc_ref(v_body_118_);
lean_inc(v_declName_115_);
v___y_21_ = v_declName_115_;
v___y_22_ = v_body_118_;
v___y_23_ = v_nondep_119_;
v___y_24_ = v_a_127_;
v___y_25_ = v_a_123_;
v___y_26_ = v_a_121_;
v___y_27_ = v___x_130_;
goto v___jp_20_;
}
else
{
size_t v___x_131_; size_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_ptr_addr(v_value_117_);
v___x_132_ = lean_ptr_addr(v_a_123_);
v___x_133_ = lean_usize_dec_eq(v___x_131_, v___x_132_);
lean_inc_ref(v_body_118_);
lean_inc(v_declName_115_);
v___y_21_ = v_declName_115_;
v___y_22_ = v_body_118_;
v___y_23_ = v_nondep_119_;
v___y_24_ = v_a_127_;
v___y_25_ = v_a_123_;
v___y_26_ = v_a_121_;
v___y_27_ = v___x_133_;
goto v___jp_20_;
}
}
else
{
lean_dec(v_a_123_);
lean_dec(v_a_121_);
lean_dec_ref_known(v_e_5_, 4);
return v___x_126_;
}
}
else
{
lean_dec(v_a_121_);
lean_dec_ref_known(v_e_5_, 4);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_122_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 4);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_120_;
}
}
case 6:
{
lean_object* v_binderName_134_; lean_object* v_binderType_135_; lean_object* v_body_136_; uint8_t v_binderInfo_137_; lean_object* v___x_138_; 
v_binderName_134_ = lean_ctor_get(v_e_5_, 0);
v_binderType_135_ = lean_ctor_get(v_e_5_, 1);
v_body_136_ = lean_ctor_get(v_e_5_, 2);
v_binderInfo_137_ = lean_ctor_get_uint8(v_e_5_, sizeof(void*)*3 + 8);
lean_inc(v_offset_6_);
lean_inc_ref(v_binderType_135_);
lean_inc_ref(v_p_1_);
v___x_138_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_binderType_135_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_offset_6_, v___x_140_);
lean_dec(v_offset_6_);
lean_inc_ref(v_body_136_);
v___x_142_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_body_136_, v___x_141_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; size_t v___x_144_; size_t v___x_145_; uint8_t v___x_146_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_142_, 1);
v___x_144_ = lean_ptr_addr(v_binderType_135_);
v___x_145_ = lean_ptr_addr(v_a_139_);
v___x_146_ = lean_usize_dec_eq(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_inc(v_binderName_134_);
v___y_37_ = v_a_139_;
v___y_38_ = v_binderName_134_;
v___y_39_ = v_binderInfo_137_;
v___y_40_ = v_a_143_;
v___y_41_ = v___x_146_;
goto v___jp_36_;
}
else
{
size_t v___x_147_; size_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_ptr_addr(v_body_136_);
v___x_148_ = lean_ptr_addr(v_a_143_);
v___x_149_ = lean_usize_dec_eq(v___x_147_, v___x_148_);
lean_inc(v_binderName_134_);
v___y_37_ = v_a_139_;
v___y_38_ = v_binderName_134_;
v___y_39_ = v_binderInfo_137_;
v___y_40_ = v_a_143_;
v___y_41_ = v___x_149_;
goto v___jp_36_;
}
}
else
{
lean_dec(v_a_139_);
lean_dec_ref_known(v_e_5_, 3);
return v___x_142_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 3);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_138_;
}
}
case 7:
{
lean_object* v_binderName_150_; lean_object* v_binderType_151_; lean_object* v_body_152_; uint8_t v_binderInfo_153_; lean_object* v___x_154_; 
v_binderName_150_ = lean_ctor_get(v_e_5_, 0);
v_binderType_151_ = lean_ctor_get(v_e_5_, 1);
v_body_152_ = lean_ctor_get(v_e_5_, 2);
v_binderInfo_153_ = lean_ctor_get_uint8(v_e_5_, sizeof(void*)*3 + 8);
lean_inc(v_offset_6_);
lean_inc_ref(v_binderType_151_);
lean_inc_ref(v_p_1_);
v___x_154_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_binderType_151_, v_offset_6_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_add(v_offset_6_, v___x_156_);
lean_dec(v_offset_6_);
lean_inc_ref(v_body_152_);
v___x_158_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_1_, v_occs_2_, v_pHeadIdx_3_, v_pNumArgs_4_, v_body_152_, v___x_157_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; size_t v___x_160_; size_t v___x_161_; uint8_t v___x_162_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = lean_ptr_addr(v_binderType_151_);
v___x_161_ = lean_ptr_addr(v_a_155_);
v___x_162_ = lean_usize_dec_eq(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_inc(v_binderName_150_);
v___y_49_ = v_a_155_;
v___y_50_ = v_a_159_;
v___y_51_ = v_binderName_150_;
v___y_52_ = v_binderInfo_153_;
v___y_53_ = v___x_162_;
goto v___jp_48_;
}
else
{
size_t v___x_163_; size_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_ptr_addr(v_body_152_);
v___x_164_ = lean_ptr_addr(v_a_159_);
v___x_165_ = lean_usize_dec_eq(v___x_163_, v___x_164_);
lean_inc(v_binderName_150_);
v___y_49_ = v_a_155_;
v___y_50_ = v_a_159_;
v___y_51_ = v_binderName_150_;
v___y_52_ = v_binderInfo_153_;
v___y_53_ = v___x_165_;
goto v___jp_48_;
}
}
else
{
lean_dec(v_a_155_);
lean_dec_ref_known(v_e_5_, 3);
return v___x_158_;
}
}
else
{
lean_dec_ref_known(v_e_5_, 3);
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
return v___x_154_;
}
}
default: 
{
lean_object* v___x_166_; 
lean_dec(v_offset_6_);
lean_dec_ref(v_p_1_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v_e_5_);
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object* v_p_214_, lean_object* v_occs_215_, lean_object* v_pHeadIdx_216_, lean_object* v_pNumArgs_217_, lean_object* v_e_218_, lean_object* v_offset_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_214_, v_occs_215_, v_pHeadIdx_216_, v_pNumArgs_217_, v_e_218_, v_offset_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec(v_pNumArgs_217_);
lean_dec(v_pHeadIdx_216_);
lean_dec(v_occs_215_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object* v_e_227_, lean_object* v___y_228_){
_start:
{
uint8_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = l_Lean_Expr_hasMVar(v_e_227_);
v___x_231_ = lean_bool_not(v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v_mctx_233_; lean_object* v___x_234_; lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v___x_237_; lean_object* v_cache_238_; lean_object* v_zetaDeltaFVarIds_239_; lean_object* v_postponed_240_; lean_object* v_diag_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_250_; 
v___x_232_ = lean_st_ref_get(v___y_228_);
v_mctx_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_mctx_233_);
lean_dec(v___x_232_);
v___x_234_ = l_Lean_instantiateMVarsCore(v_mctx_233_, v_e_227_);
v_fst_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_fst_235_);
v_snd_236_ = lean_ctor_get(v___x_234_, 1);
lean_inc(v_snd_236_);
lean_dec_ref(v___x_234_);
v___x_237_ = lean_st_ref_take(v___y_228_);
v_cache_238_ = lean_ctor_get(v___x_237_, 1);
v_zetaDeltaFVarIds_239_ = lean_ctor_get(v___x_237_, 2);
v_postponed_240_ = lean_ctor_get(v___x_237_, 3);
v_diag_241_ = lean_ctor_get(v___x_237_, 4);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_251_);
v___x_243_ = v___x_237_;
v_isShared_244_ = v_isSharedCheck_250_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_diag_241_);
lean_inc(v_postponed_240_);
lean_inc(v_zetaDeltaFVarIds_239_);
lean_inc(v_cache_238_);
lean_dec(v___x_237_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_250_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_snd_236_);
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_snd_236_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_cache_238_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_zetaDeltaFVarIds_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_postponed_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_diag_241_);
v___x_246_ = v_reuseFailAlloc_249_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_st_ref_set(v___y_228_, v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v_fst_235_);
return v___x_248_;
}
}
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v_e_227_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object* v_e_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_253_, v___y_254_);
lean_dec(v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object* v_e_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_257_, v___y_259_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object* v_e_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(v_e_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* v_e_271_, lean_object* v_p_272_, lean_object* v_occs_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_311_; 
v___x_279_ = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(v_e_271_, v_a_275_);
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_311_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_311_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_311_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
uint8_t v___y_285_; uint8_t v___x_308_; 
v___x_308_ = l_Lean_Expr_isFVar(v_p_272_);
if (v___x_308_ == 0)
{
v___y_285_ = v___x_308_;
goto v___jp_284_;
}
else
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_box(0);
lean_inc(v_occs_273_);
v___x_310_ = l_Lean_Meta_instBEqOccurrences_beq(v_occs_273_, v___x_309_);
v___y_285_ = v___x_310_;
goto v___jp_284_;
}
v___jp_284_:
{
if (v___y_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_del_object(v___x_282_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_st_mk_ref(v___x_286_);
lean_inc_ref(v_p_272_);
v___x_288_ = l_Lean_Expr_toHeadIndex(v_p_272_);
v___x_289_ = l_Lean_Expr_headNumArgs(v_p_272_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(v_p_272_, v_occs_273_, v___x_288_, v___x_289_, v_a_280_, v___x_290_, v___x_287_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v___x_289_);
lean_dec(v___x_288_);
lean_dec(v_occs_273_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_st_ref_get(v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_296_);
if (v_isShared_295_ == 0)
{
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_292_);
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
lean_dec(v___x_287_);
return v___x_291_;
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
lean_dec(v_occs_273_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_301_);
v___x_303_ = lean_array_push(v___x_302_, v_p_272_);
v___x_304_ = lean_expr_abstract(v_a_280_, v___x_303_);
lean_dec_ref(v___x_303_);
lean_dec(v_a_280_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_304_);
v___x_306_ = v___x_282_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* v_e_312_, lean_object* v_p_313_, lean_object* v_occs_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_kabstract(v_e_312_, v_p_313_, v_occs_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_320_;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
