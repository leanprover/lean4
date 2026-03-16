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
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_1_, v_a_2_, v_b_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object* v_inst_5_, lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(v_inst_5_, v_a_6_, v_b_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_aig_12_, lean_object* v_n_13_){
_start:
{
lean_object* v_decls_14_; lean_object* v_cache_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_40_; 
v_decls_14_ = lean_ctor_get(v_aig_12_, 0);
v_cache_15_ = lean_ctor_get(v_aig_12_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_aig_12_);
if (v_isSharedCheck_40_ == 0)
{
v___x_17_ = v_aig_12_;
v_isShared_18_ = v_isSharedCheck_40_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_cache_15_);
lean_inc(v_decls_14_);
lean_dec(v_aig_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_40_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___f_19_; lean_object* v_decl_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v___f_19_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_19_, 0, v_inst_11_);
v_decl_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_decl_20_, 0, v_n_13_);
v___x_21_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_21_, 0, lean_box(0));
lean_closure_set(v___x_21_, 1, v_inst_10_);
v___f_22_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_22_, 0, v___f_19_);
lean_inc_ref(v_decl_20_);
lean_inc_ref(v___x_21_);
lean_inc_ref(v___f_22_);
v___x_23_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_22_, v___x_21_, v_cache_15_, v_decl_20_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_g_24_; lean_object* v_cache_25_; lean_object* v_decls_26_; lean_object* v___x_28_; 
v_g_24_ = lean_array_get_size(v_decls_14_);
lean_inc_ref(v_decl_20_);
v_cache_25_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_22_, v___x_21_, v_cache_15_, v_decl_20_, v_g_24_);
v_decls_26_ = lean_array_push(v_decls_14_, v_decl_20_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v_cache_25_);
lean_ctor_set(v___x_17_, 0, v_decls_26_);
v___x_28_ = v___x_17_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_decls_26_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_cache_25_);
v___x_28_ = v_reuseFailAlloc_32_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = 0;
v___x_30_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_30_, 0, v_g_24_);
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_28_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
return v___x_31_;
}
}
else
{
lean_object* v_val_33_; lean_object* v___x_35_; 
lean_dec_ref(v___f_22_);
lean_dec_ref(v___x_21_);
lean_dec_ref(v_decl_20_);
v_val_33_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_val_33_);
lean_dec_ref(v___x_23_);
if (v_isShared_18_ == 0)
{
v___x_35_ = v___x_17_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_decls_14_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_cache_15_);
v___x_35_ = v_reuseFailAlloc_39_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = 0;
v___x_37_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_37_, 0, v_val_33_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*1, v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_35_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_aig_44_, lean_object* v_n_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Sat_AIG_mkAtomCached___redArg(v_inst_42_, v_inst_43_, v_aig_44_, v_n_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t v_val_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*1, v_val_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object* v_val_50_){
_start:
{
uint8_t v_val_boxed_51_; lean_object* v_res_52_; 
v_val_boxed_51_ = lean_unbox(v_val_50_);
v_res_52_ = l_Std_Sat_AIG_mkConstCached___redArg(v_val_boxed_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_aig_56_, uint8_t v_val_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v_val_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_aig_63_, lean_object* v_val_64_){
_start:
{
uint8_t v_val_boxed_65_; lean_object* v_res_66_; 
v_val_boxed_65_ = lean_unbox(v_val_64_);
v_res_66_ = l_Std_Sat_AIG_mkConstCached(v_00_u03b1_60_, v_inst_61_, v_inst_62_, v_aig_63_, v_val_boxed_65_);
lean_dec_ref(v_aig_63_);
lean_dec_ref(v_inst_62_);
lean_dec_ref(v_inst_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_aig_72_, lean_object* v_input_73_){
_start:
{
lean_object* v_lhs_74_; lean_object* v_rhs_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_161_; 
v_lhs_74_ = lean_ctor_get(v_input_73_, 0);
v_rhs_75_ = lean_ctor_get(v_input_73_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_input_73_);
if (v_isSharedCheck_161_ == 0)
{
v___x_77_ = v_input_73_;
v_isShared_78_ = v_isSharedCheck_161_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_rhs_75_);
lean_inc(v_lhs_74_);
lean_dec(v_input_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_161_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_decls_79_; lean_object* v_cache_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_160_; 
v_decls_79_ = lean_ctor_get(v_aig_72_, 0);
v_cache_80_ = lean_ctor_get(v_aig_72_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_aig_72_);
if (v_isSharedCheck_160_ == 0)
{
v___x_82_ = v_aig_72_;
v_isShared_83_ = v_isSharedCheck_160_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_cache_80_);
lean_inc(v_decls_79_);
lean_dec(v_aig_72_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_160_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v_gate_84_; uint8_t v_invert_85_; lean_object* v_gate_86_; uint8_t v_invert_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_decl_97_; 
v_gate_84_ = lean_ctor_get(v_lhs_74_, 0);
lean_inc(v_gate_84_);
v_invert_85_ = lean_ctor_get_uint8(v_lhs_74_, sizeof(void*)*1);
v_gate_86_ = lean_ctor_get(v_rhs_75_, 0);
v_invert_87_ = lean_ctor_get_uint8(v_rhs_75_, sizeof(void*)*1);
v___f_88_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_88_, 0, v_inst_71_);
v___x_89_ = lean_unsigned_to_nat(2u);
v___x_90_ = lean_nat_mul(v_gate_84_, v___x_89_);
v___x_91_ = l_Bool_toNat(v_invert_85_);
v___x_92_ = lean_nat_lor(v___x_90_, v___x_91_);
lean_dec(v___x_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_nat_mul(v_gate_86_, v___x_89_);
v___x_94_ = l_Bool_toNat(v_invert_87_);
v___x_95_ = lean_nat_lor(v___x_93_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_93_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 2);
lean_ctor_set(v___x_77_, 1, v___x_95_);
lean_ctor_set(v___x_77_, 0, v___x_92_);
v_decl_97_ = v___x_77_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_95_);
v_decl_97_ = v_reuseFailAlloc_159_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___x_100_; 
v___x_98_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, v_inst_70_);
v___f_99_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_99_, 0, v___f_88_);
lean_inc_ref(v_decl_97_);
lean_inc_ref(v___x_98_);
lean_inc_ref(v___f_99_);
v___x_100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_99_, v___x_98_, v_cache_80_, v_decl_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_102_; 
lean_inc(v_gate_86_);
lean_inc_ref(v_cache_80_);
lean_inc_ref(v_decls_79_);
if (v_isShared_83_ == 0)
{
v___x_102_ = v___x_82_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_decls_79_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_cache_80_);
v___x_102_ = v_reuseFailAlloc_144_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
uint8_t v___y_104_; uint8_t v___y_109_; lean_object* v_lhsVal_118_; lean_object* v_rhsVal_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_142_; 
v_lhsVal_118_ = l_Std_Sat_AIG_getConstant___redArg(v___x_102_, v_lhs_74_);
lean_dec_ref(v_lhs_74_);
v_rhsVal_119_ = l_Std_Sat_AIG_getConstant___redArg(v___x_102_, v_rhs_75_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_rhs_75_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_rhs_75_, 0);
lean_dec(v_unused_143_);
v___x_121_ = v_rhs_75_;
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
else
{
lean_dec(v_rhs_75_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v_ref_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v_ref_106_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_106_, 0, v___x_105_);
lean_ctor_set_uint8(v_ref_106_, sizeof(void*)*1, v___y_104_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_102_);
lean_ctor_set(v___x_107_, 1, v_ref_106_);
return v___x_107_;
}
v___jp_108_:
{
if (v___y_109_ == 0)
{
lean_dec(v_gate_84_);
v___y_104_ = v___y_109_;
goto v___jp_103_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_110_, 0, v_gate_84_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v_invert_85_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_102_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
return v___x_111_;
}
}
v___jp_112_:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_113_, 0, v_gate_86_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v_invert_87_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_102_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
v___jp_115_:
{
lean_object* v_ref_116_; lean_object* v___x_117_; 
v_ref_116_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0));
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_102_);
lean_ctor_set(v___x_117_, 1, v_ref_116_);
return v___x_117_;
}
v_resetjp_120_:
{
if (lean_obj_tag(v_lhsVal_118_) == 1)
{
lean_object* v_val_123_; uint8_t v___x_124_; 
lean_del_object(v___x_121_);
lean_dec_ref(v___f_99_);
lean_dec_ref(v___x_98_);
lean_dec_ref(v_decl_97_);
lean_dec(v_gate_84_);
lean_dec_ref(v_cache_80_);
lean_dec_ref(v_decls_79_);
v_val_123_ = lean_ctor_get(v_lhsVal_118_, 0);
lean_inc(v_val_123_);
lean_dec_ref(v_lhsVal_118_);
v___x_124_ = lean_unbox(v_val_123_);
lean_dec(v_val_123_);
if (v___x_124_ == 0)
{
lean_dec(v_rhsVal_119_);
lean_dec(v_gate_86_);
goto v___jp_115_;
}
else
{
if (lean_obj_tag(v_rhsVal_119_) == 1)
{
lean_object* v_val_125_; uint8_t v___x_126_; 
v_val_125_ = lean_ctor_get(v_rhsVal_119_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v_rhsVal_119_);
v___x_126_ = lean_unbox(v_val_125_);
lean_dec(v_val_125_);
if (v___x_126_ == 0)
{
lean_dec(v_gate_86_);
goto v___jp_115_;
}
else
{
goto v___jp_112_;
}
}
else
{
lean_dec(v_rhsVal_119_);
goto v___jp_112_;
}
}
}
else
{
lean_dec(v_lhsVal_118_);
if (lean_obj_tag(v_rhsVal_119_) == 1)
{
lean_object* v_val_127_; uint8_t v___x_128_; 
lean_dec_ref(v___f_99_);
lean_dec_ref(v___x_98_);
lean_dec_ref(v_decl_97_);
lean_dec(v_gate_86_);
lean_dec_ref(v_cache_80_);
lean_dec_ref(v_decls_79_);
v_val_127_ = lean_ctor_get(v_rhsVal_119_, 0);
lean_inc(v_val_127_);
lean_dec_ref(v_rhsVal_119_);
v___x_128_ = lean_unbox(v_val_127_);
lean_dec(v_val_127_);
if (v___x_128_ == 0)
{
lean_del_object(v___x_121_);
lean_dec(v_gate_84_);
goto v___jp_115_;
}
else
{
lean_object* v___x_130_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_gate_84_);
v___x_130_ = v___x_121_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_gate_84_);
v___x_130_ = v_reuseFailAlloc_132_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; 
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v_invert_85_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_102_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
}
else
{
uint8_t v___x_133_; 
lean_dec(v_rhsVal_119_);
v___x_133_ = lean_nat_dec_eq(v_gate_84_, v_gate_86_);
lean_dec(v_gate_86_);
if (v___x_133_ == 0)
{
lean_object* v_g_134_; lean_object* v_cache_135_; lean_object* v_decls_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
lean_dec_ref(v___x_102_);
lean_dec(v_gate_84_);
v_g_134_ = lean_array_get_size(v_decls_79_);
lean_inc_ref(v_decl_97_);
v_cache_135_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_99_, v___x_98_, v_cache_80_, v_decl_97_, v_g_134_);
v_decls_136_ = lean_array_push(v_decls_79_, v_decl_97_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_decls_136_);
lean_ctor_set(v___x_137_, 1, v_cache_135_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_g_134_);
v___x_139_ = v___x_121_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_g_134_);
v___x_139_ = v_reuseFailAlloc_141_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; 
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_133_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_137_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
return v___x_140_;
}
}
else
{
lean_del_object(v___x_121_);
lean_dec_ref(v___f_99_);
lean_dec_ref(v___x_98_);
lean_dec_ref(v_decl_97_);
lean_dec_ref(v_cache_80_);
lean_dec_ref(v_decls_79_);
if (v_invert_85_ == 0)
{
if (v_invert_87_ == 0)
{
v___y_109_ = v___x_133_;
goto v___jp_108_;
}
else
{
lean_dec(v_gate_84_);
v___y_104_ = v_invert_85_;
goto v___jp_103_;
}
}
else
{
v___y_109_ = v_invert_87_;
goto v___jp_108_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_157_; 
lean_dec_ref(v___f_99_);
lean_dec_ref(v___x_98_);
lean_dec_ref(v_decl_97_);
lean_dec(v_gate_84_);
lean_dec_ref(v_lhs_74_);
v_isSharedCheck_157_ = !lean_is_exclusive(v_rhs_75_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v_rhs_75_, 0);
lean_dec(v_unused_158_);
v___x_146_ = v_rhs_75_;
v_isShared_147_ = v_isSharedCheck_157_;
goto v_resetjp_145_;
}
else
{
lean_dec(v_rhs_75_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_157_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_val_148_; lean_object* v___x_150_; 
v_val_148_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_148_);
lean_dec_ref(v___x_100_);
if (v_isShared_83_ == 0)
{
v___x_150_ = v___x_82_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_decls_79_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_cache_80_);
v___x_150_ = v_reuseFailAlloc_156_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
uint8_t v___x_151_; lean_object* v___x_153_; 
v___x_151_ = 0;
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v_val_148_);
v___x_153_ = v___x_146_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_val_148_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_151_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_150_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
return v___x_154_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object* v_00_u03b1_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_aig_165_, lean_object* v_input_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_163_, v_inst_164_, v_aig_165_, v_input_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_aig_170_, lean_object* v_input_171_){
_start:
{
lean_object* v_lhs_172_; lean_object* v_rhs_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_188_; 
v_lhs_172_ = lean_ctor_get(v_input_171_, 0);
v_rhs_173_ = lean_ctor_get(v_input_171_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_input_171_);
if (v_isSharedCheck_188_ == 0)
{
v___x_175_ = v_input_171_;
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_rhs_173_);
lean_inc(v_lhs_172_);
lean_dec(v_input_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_gate_177_; lean_object* v_gate_178_; uint8_t v___x_179_; 
v_gate_177_ = lean_ctor_get(v_lhs_172_, 0);
v_gate_178_ = lean_ctor_get(v_rhs_173_, 0);
v___x_179_ = lean_nat_dec_lt(v_gate_177_, v_gate_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_181_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_lhs_172_);
lean_ctor_set(v___x_175_, 0, v_rhs_173_);
v___x_181_ = v___x_175_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_rhs_173_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_lhs_172_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_168_, v_inst_169_, v_aig_170_, v___x_181_);
return v___x_182_;
}
}
else
{
lean_object* v___x_185_; 
if (v_isShared_176_ == 0)
{
v___x_185_ = v___x_175_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_lhs_172_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_rhs_173_);
v___x_185_ = v_reuseFailAlloc_187_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_168_, v_inst_169_, v_aig_170_, v___x_185_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object* v_00_u03b1_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_aig_192_, lean_object* v_input_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_190_, v_inst_191_, v_aig_192_, v_input_193_);
return v___x_194_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_Cached(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
