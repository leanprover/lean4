// Lean compiler output
// Module: Std.Sat.AIG.Cached
// Imports: public import Std.Sat.AIG.Lemmas import Init.Omega
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
uint8_t l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instHashableDecl_hash___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_1_, v_a_2_, v_b_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_mkAtomCached___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_b_3_ = stack[2].m_obj;
uint8_t v_res_5_;
v_res_5_ = l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(v_inst_1_, v_a_2_, v_b_3_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object* v_inst_6_, lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(v_inst_6_, v_a_7_, v_b_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_aig_13_, lean_object* v_n_14_){
_start:
{
lean_object* v_decls_15_; lean_object* v_cache_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_41_; 
v_decls_15_ = lean_ctor_get(v_aig_13_, 0);
v_cache_16_ = lean_ctor_get(v_aig_13_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_aig_13_);
if (v_isSharedCheck_41_ == 0)
{
v___x_18_ = v_aig_13_;
v_isShared_19_ = v_isSharedCheck_41_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_cache_16_);
lean_inc(v_decls_15_);
lean_dec(v_aig_13_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_41_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___f_20_; lean_object* v_decl_21_; lean_object* v___x_22_; lean_object* v___f_23_; lean_object* v___x_24_; 
v___f_20_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_20_, 0, v_inst_12_);
v_decl_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_21_, 0, v_n_14_);
v___x_22_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_22_, 0, lean_box(0));
lean_closure_set(v___x_22_, 1, v_inst_11_);
v___f_23_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_23_, 0, v___f_20_);
lean_inc_ref(v_decl_21_);
lean_inc_ref(v___x_22_);
lean_inc_ref(v___f_23_);
v___x_24_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_23_, v___x_22_, v_cache_16_, v_decl_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_g_25_; lean_object* v_cache_26_; lean_object* v_decls_27_; lean_object* v___x_29_; 
v_g_25_ = lean_array_get_size(v_decls_15_);
lean_inc_ref(v_decl_21_);
v_cache_26_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_23_, v___x_22_, v_cache_16_, v_decl_21_, v_g_25_);
v_decls_27_ = lean_array_push(v_decls_15_, v_decl_21_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v_cache_26_);
lean_ctor_set(v___x_18_, 0, v_decls_27_);
v___x_29_ = v___x_18_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_decls_27_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_cache_26_);
v___x_29_ = v_reuseFailAlloc_33_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_31_, 0, v_g_25_);
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*1, v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_29_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
}
else
{
lean_object* v_val_34_; lean_object* v___x_36_; 
lean_dec_ref(v___f_23_);
lean_dec_ref(v___x_22_);
lean_dec_ref_known(v_decl_21_, 1);
v_val_34_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v___x_24_, 1);
if (v_isShared_19_ == 0)
{
v___x_36_ = v___x_18_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_decls_15_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_cache_16_);
v___x_36_ = v_reuseFailAlloc_40_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
uint8_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = 0;
v___x_38_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_38_, 0, v_val_34_);
lean_ctor_set_uint8(v___x_38_, sizeof(void*)*1, v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_36_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
return v___x_39_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_aig_45_, lean_object* v_n_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Sat_AIG_mkAtomCached___redArg(v_inst_43_, v_inst_44_, v_aig_45_, v_n_46_);
return v___x_47_;
}
}
lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t v_val_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*1, v_val_48_);
return v___x_50_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_mkConstCached___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_48_ = stack[0].m_num;
lean_object* v_res_51_;
v_res_51_ = l_Std_Sat_AIG_mkConstCached___redArg(v_val_48_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object* v_val_52_){
_start:
{
uint8_t v_val_boxed_53_; lean_object* v_res_54_; 
v_val_boxed_53_ = lean_unbox(v_val_52_);
v_res_54_ = l_Std_Sat_AIG_mkConstCached___redArg(v_val_boxed_53_);
return v_res_54_;
}
}
lean_object* l_Std_Sat_AIG_mkConstCached(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_aig_58_, uint8_t v_val_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set_uint8(v___x_61_, sizeof(void*)*1, v_val_59_);
return v___x_61_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_mkConstCached_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_56_ = stack[1].m_obj;
lean_object* v_inst_57_ = stack[2].m_obj;
lean_object* v_aig_58_ = stack[3].m_obj;
uint8_t v_val_59_ = stack[4].m_num;
lean_object* v_res_62_;
v_res_62_ = l_Std_Sat_AIG_mkConstCached(lean_box(0), v_inst_56_, v_inst_57_, v_aig_58_, v_val_59_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_aig_66_, lean_object* v_val_67_){
_start:
{
uint8_t v_val_boxed_68_; lean_object* v_res_69_; 
v_val_boxed_68_ = lean_unbox(v_val_67_);
v_res_69_ = l_Std_Sat_AIG_mkConstCached(v_00_u03b1_63_, v_inst_64_, v_inst_65_, v_aig_66_, v_val_boxed_68_);
lean_dec_ref(v_aig_66_);
lean_dec_ref(v_inst_65_);
lean_dec_ref(v_inst_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_aig_75_, lean_object* v_input_76_){
_start:
{
lean_object* v_lhs_77_; lean_object* v_rhs_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_164_; 
v_lhs_77_ = lean_ctor_get(v_input_76_, 0);
v_rhs_78_ = lean_ctor_get(v_input_76_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_input_76_);
if (v_isSharedCheck_164_ == 0)
{
v___x_80_ = v_input_76_;
v_isShared_81_ = v_isSharedCheck_164_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_rhs_78_);
lean_inc(v_lhs_77_);
lean_dec(v_input_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_164_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_decls_82_; lean_object* v_cache_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_163_; 
v_decls_82_ = lean_ctor_get(v_aig_75_, 0);
v_cache_83_ = lean_ctor_get(v_aig_75_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_aig_75_);
if (v_isSharedCheck_163_ == 0)
{
v___x_85_ = v_aig_75_;
v_isShared_86_ = v_isSharedCheck_163_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_cache_83_);
lean_inc(v_decls_82_);
lean_dec(v_aig_75_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_163_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v_gate_87_; uint8_t v_invert_88_; lean_object* v_gate_89_; uint8_t v_invert_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_decl_100_; 
v_gate_87_ = lean_ctor_get(v_lhs_77_, 0);
lean_inc(v_gate_87_);
v_invert_88_ = lean_ctor_get_uint8(v_lhs_77_, sizeof(void*)*1);
v_gate_89_ = lean_ctor_get(v_rhs_78_, 0);
v_invert_90_ = lean_ctor_get_uint8(v_rhs_78_, sizeof(void*)*1);
v___f_91_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_91_, 0, v_inst_74_);
v___x_92_ = lean_unsigned_to_nat(2u);
v___x_93_ = lean_nat_mul(v_gate_87_, v___x_92_);
v___x_94_ = l_Bool_toNat(v_invert_88_);
v___x_95_ = lean_nat_lor(v___x_93_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_nat_mul(v_gate_89_, v___x_92_);
v___x_97_ = l_Bool_toNat(v_invert_90_);
v___x_98_ = lean_nat_lor(v___x_96_, v___x_97_);
lean_dec(v___x_97_);
lean_dec(v___x_96_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 2);
lean_ctor_set(v___x_80_, 1, v___x_98_);
lean_ctor_set(v___x_80_, 0, v___x_95_);
v_decl_100_ = v___x_80_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_98_);
v_decl_100_ = v_reuseFailAlloc_162_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___x_103_; 
v___x_101_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, v_inst_73_);
v___f_102_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_102_, 0, v___f_91_);
lean_inc_ref(v_decl_100_);
lean_inc_ref(v___x_101_);
lean_inc_ref(v___f_102_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_102_, v___x_101_, v_cache_83_, v_decl_100_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_105_; 
lean_inc(v_gate_89_);
lean_inc_ref(v_cache_83_);
lean_inc_ref(v_decls_82_);
if (v_isShared_86_ == 0)
{
v___x_105_ = v___x_85_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_decls_82_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_cache_83_);
v___x_105_ = v_reuseFailAlloc_147_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
uint8_t v___y_107_; uint8_t v___y_112_; lean_object* v_lhsVal_121_; lean_object* v_rhsVal_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_145_; 
v_lhsVal_121_ = l_Std_Sat_AIG_getConstant___redArg(v___x_105_, v_lhs_77_);
lean_dec_ref(v_lhs_77_);
v_rhsVal_122_ = l_Std_Sat_AIG_getConstant___redArg(v___x_105_, v_rhs_78_);
v_isSharedCheck_145_ = !lean_is_exclusive(v_rhs_78_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_rhs_78_, 0);
lean_dec(v_unused_146_);
v___x_124_ = v_rhs_78_;
v_isShared_125_ = v_isSharedCheck_145_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_rhs_78_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_145_;
goto v_resetjp_123_;
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v_ref_109_; lean_object* v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v_ref_109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_109_, 0, v___x_108_);
lean_ctor_set_uint8(v_ref_109_, sizeof(void*)*1, v___y_107_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_105_);
lean_ctor_set(v___x_110_, 1, v_ref_109_);
return v___x_110_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
lean_dec(v_gate_87_);
v___y_107_ = v___y_112_;
goto v___jp_106_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_113_, 0, v_gate_87_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v_invert_88_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_105_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
}
v___jp_115_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_116_, 0, v_gate_89_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*1, v_invert_90_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_105_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
return v___x_117_;
}
v___jp_118_:
{
lean_object* v_ref_119_; lean_object* v___x_120_; 
v_ref_119_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0));
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_105_);
lean_ctor_set(v___x_120_, 1, v_ref_119_);
return v___x_120_;
}
v_resetjp_123_:
{
if (lean_obj_tag(v_lhsVal_121_) == 1)
{
lean_object* v_val_126_; uint8_t v___x_127_; 
lean_del_object(v___x_124_);
lean_dec_ref(v___f_102_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_decl_100_);
lean_dec(v_gate_87_);
lean_dec_ref(v_cache_83_);
lean_dec_ref(v_decls_82_);
v_val_126_ = lean_ctor_get(v_lhsVal_121_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v_lhsVal_121_, 1);
v___x_127_ = lean_unbox(v_val_126_);
lean_dec(v_val_126_);
if (v___x_127_ == 0)
{
lean_dec(v_rhsVal_122_);
lean_dec(v_gate_89_);
goto v___jp_118_;
}
else
{
if (lean_obj_tag(v_rhsVal_122_) == 1)
{
lean_object* v_val_128_; uint8_t v___x_129_; 
v_val_128_ = lean_ctor_get(v_rhsVal_122_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v_rhsVal_122_, 1);
v___x_129_ = lean_unbox(v_val_128_);
lean_dec(v_val_128_);
if (v___x_129_ == 0)
{
lean_dec(v_gate_89_);
goto v___jp_118_;
}
else
{
goto v___jp_115_;
}
}
else
{
lean_dec(v_rhsVal_122_);
goto v___jp_115_;
}
}
}
else
{
lean_dec(v_lhsVal_121_);
if (lean_obj_tag(v_rhsVal_122_) == 1)
{
lean_object* v_val_130_; uint8_t v___x_131_; 
lean_dec_ref(v___f_102_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_decl_100_);
lean_dec(v_gate_89_);
lean_dec_ref(v_cache_83_);
lean_dec_ref(v_decls_82_);
v_val_130_ = lean_ctor_get(v_rhsVal_122_, 0);
lean_inc(v_val_130_);
lean_dec_ref_known(v_rhsVal_122_, 1);
v___x_131_ = lean_unbox(v_val_130_);
lean_dec(v_val_130_);
if (v___x_131_ == 0)
{
lean_del_object(v___x_124_);
lean_dec(v_gate_87_);
goto v___jp_118_;
}
else
{
lean_object* v___x_133_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_gate_87_);
v___x_133_ = v___x_124_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_gate_87_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v_invert_88_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_105_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
return v___x_134_;
}
}
}
else
{
uint8_t v___x_136_; 
lean_dec(v_rhsVal_122_);
v___x_136_ = lean_nat_dec_eq(v_gate_87_, v_gate_89_);
lean_dec(v_gate_89_);
if (v___x_136_ == 0)
{
lean_object* v_g_137_; lean_object* v_cache_138_; lean_object* v_decls_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
lean_dec_ref(v___x_105_);
lean_dec(v_gate_87_);
v_g_137_ = lean_array_get_size(v_decls_82_);
lean_inc_ref(v_decl_100_);
v_cache_138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_102_, v___x_101_, v_cache_83_, v_decl_100_, v_g_137_);
v_decls_139_ = lean_array_push(v_decls_82_, v_decl_100_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_decls_139_);
lean_ctor_set(v___x_140_, 1, v_cache_138_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_g_137_);
v___x_142_ = v___x_124_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_g_137_);
v___x_142_ = v_reuseFailAlloc_144_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; 
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_136_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_140_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
return v___x_143_;
}
}
else
{
lean_del_object(v___x_124_);
lean_dec_ref(v___f_102_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_decl_100_);
lean_dec_ref(v_cache_83_);
lean_dec_ref(v_decls_82_);
if (v_invert_90_ == 0)
{
if (v_invert_88_ == 0)
{
v___y_112_ = v___x_136_;
goto v___jp_111_;
}
else
{
lean_dec(v_gate_87_);
v___y_107_ = v_invert_90_;
goto v___jp_106_;
}
}
else
{
v___y_112_ = v_invert_88_;
goto v___jp_111_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v___f_102_);
lean_dec_ref(v___x_101_);
lean_dec_ref(v_decl_100_);
lean_dec(v_gate_87_);
lean_dec_ref(v_lhs_77_);
v_isSharedCheck_160_ = !lean_is_exclusive(v_rhs_78_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_rhs_78_, 0);
lean_dec(v_unused_161_);
v___x_149_ = v_rhs_78_;
v_isShared_150_ = v_isSharedCheck_160_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_rhs_78_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_160_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_val_151_; lean_object* v___x_153_; 
v_val_151_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v___x_103_, 1);
if (v_isShared_86_ == 0)
{
v___x_153_ = v___x_85_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_decls_82_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_cache_83_);
v___x_153_ = v_reuseFailAlloc_159_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
uint8_t v___x_154_; lean_object* v___x_156_; 
v___x_154_ = 0;
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v_val_151_);
v___x_156_ = v___x_149_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_val_151_);
v___x_156_ = v_reuseFailAlloc_158_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_154_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_153_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
return v___x_157_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_aig_168_, lean_object* v_input_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_166_, v_inst_167_, v_aig_168_, v_input_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_aig_173_, lean_object* v_input_174_){
_start:
{
lean_object* v_lhs_175_; lean_object* v_rhs_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_191_; 
v_lhs_175_ = lean_ctor_get(v_input_174_, 0);
v_rhs_176_ = lean_ctor_get(v_input_174_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_input_174_);
if (v_isSharedCheck_191_ == 0)
{
v___x_178_ = v_input_174_;
v_isShared_179_ = v_isSharedCheck_191_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_rhs_176_);
lean_inc(v_lhs_175_);
lean_dec(v_input_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_191_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_gate_180_; lean_object* v_gate_181_; uint8_t v___x_182_; 
v_gate_180_ = lean_ctor_get(v_lhs_175_, 0);
v_gate_181_ = lean_ctor_get(v_rhs_176_, 0);
v___x_182_ = lean_nat_dec_lt(v_gate_180_, v_gate_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_lhs_175_);
lean_ctor_set(v___x_178_, 0, v_rhs_176_);
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_rhs_176_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_lhs_175_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_171_, v_inst_172_, v_aig_173_, v___x_184_);
return v___x_185_;
}
}
else
{
lean_object* v___x_188_; 
if (v_isShared_179_ == 0)
{
v___x_188_ = v___x_178_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_lhs_175_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_rhs_176_);
v___x_188_ = v_reuseFailAlloc_190_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_171_, v_inst_172_, v_aig_173_, v___x_188_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object* v_00_u03b1_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_aig_195_, lean_object* v_input_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_193_, v_inst_194_, v_aig_195_, v_input_196_);
return v___x_197_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_Cached(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_Cached(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_Cached(builtin);
}
#ifdef __cplusplus
}
#endif
