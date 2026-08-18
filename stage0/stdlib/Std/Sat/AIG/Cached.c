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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_decls_14_; lean_object* v_cache_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_105_; 
v_decls_14_ = lean_ctor_get(v_aig_12_, 0);
v_cache_15_ = lean_ctor_get(v_aig_12_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_aig_12_);
if (v_isSharedCheck_105_ == 0)
{
v___x_17_ = v_aig_12_;
v_isShared_18_ = v_isSharedCheck_105_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_cache_15_);
lean_inc(v_decls_14_);
lean_dec(v_aig_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_105_;
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
lean_object* v_g_24_; lean_object* v___y_26_; lean_object* v___y_35_; lean_object* v_i_36_; lean_object* v___y_42_; lean_object* v_i_43_; lean_object* v___y_49_; lean_object* v___x_68_; 
v_g_24_ = lean_array_get_size(v_decls_14_);
lean_inc_ref(v_decl_20_);
lean_inc_ref(v___x_21_);
lean_inc_ref(v___f_22_);
v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_22_, v___x_21_, v_cache_15_, v_decl_20_);
switch(lean_obj_tag(v___x_68_))
{
case 0:
{
lean_object* v_index_69_; lean_object* v_size_70_; lean_object* v___x_71_; 
lean_dec_ref(v___f_22_);
lean_dec_ref(v___x_21_);
v_index_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_index_69_);
lean_dec_ref_known(v___x_68_, 3);
v_size_70_ = lean_ctor_get(v_cache_15_, 0);
lean_inc(v_size_70_);
lean_inc_ref(v_decl_20_);
v___x_71_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_15_, v_size_70_, v_index_69_, v_decl_20_, v_g_24_);
lean_dec(v_index_69_);
v___y_26_ = v___x_71_;
goto v___jp_25_;
}
case 1:
{
lean_object* v_index_72_; lean_object* v_size_73_; lean_object* v_keyArray_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_index_72_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_index_72_);
lean_dec_ref_known(v___x_68_, 1);
v_size_73_ = lean_ctor_get(v_cache_15_, 0);
v_keyArray_74_ = lean_ctor_get(v_cache_15_, 1);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_add(v_size_73_, v___x_75_);
v___x_77_ = lean_array_get_size(v_keyArray_74_);
v___x_78_ = lean_nat_dec_lt(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_dec(v___x_76_);
lean_dec(v_index_72_);
goto v___jp_58_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_79_ = lean_unsigned_to_nat(4u);
v___x_80_ = lean_nat_mul(v___x_76_, v___x_79_);
v___x_81_ = lean_unsigned_to_nat(3u);
v___x_82_ = lean_nat_mul(v___x_77_, v___x_81_);
v___x_83_ = lean_nat_dec_le(v___x_80_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_80_);
if (v___x_83_ == 0)
{
lean_dec(v___x_76_);
lean_dec(v_index_72_);
goto v___jp_58_;
}
else
{
lean_object* v___x_84_; 
lean_dec_ref(v___f_22_);
lean_dec_ref(v___x_21_);
lean_inc_ref(v_decl_20_);
v___x_84_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_15_, v___x_76_, v_index_72_, v_decl_20_, v_g_24_);
lean_dec(v_index_72_);
v___y_26_ = v___x_84_;
goto v___jp_25_;
}
}
}
default: 
{
lean_object* v_size_85_; lean_object* v_keyArray_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_size_85_ = lean_ctor_get(v_cache_15_, 0);
v_keyArray_86_ = lean_ctor_get(v_cache_15_, 1);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_size_85_, v___x_87_);
v___x_89_ = lean_array_get_size(v_keyArray_86_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v___x_88_);
lean_inc_ref(v___x_21_);
lean_inc_ref(v___f_22_);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_22_, v___x_21_, v_cache_15_);
v___y_49_ = v___x_91_;
goto v___jp_48_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_92_ = lean_unsigned_to_nat(4u);
v___x_93_ = lean_nat_mul(v___x_88_, v___x_92_);
lean_dec(v___x_88_);
v___x_94_ = lean_unsigned_to_nat(3u);
v___x_95_ = lean_nat_mul(v___x_89_, v___x_94_);
v___x_96_ = lean_nat_dec_le(v___x_93_, v___x_95_);
lean_dec(v___x_95_);
lean_dec(v___x_93_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_inc_ref(v___x_21_);
lean_inc_ref(v___f_22_);
v___x_97_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_22_, v___x_21_, v_cache_15_);
v___y_49_ = v___x_97_;
goto v___jp_48_;
}
else
{
v___y_49_ = v_cache_15_;
goto v___jp_48_;
}
}
}
}
v___jp_25_:
{
lean_object* v_decls_27_; lean_object* v___x_29_; 
v_decls_27_ = lean_array_push(v_decls_14_, v_decl_20_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___y_26_);
lean_ctor_set(v___x_17_, 0, v_decls_27_);
v___x_29_ = v___x_17_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_decls_27_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___y_26_);
v___x_29_ = v_reuseFailAlloc_33_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_31_, 0, v_g_24_);
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*1, v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_29_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
}
v___jp_34_:
{
lean_object* v_size_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_size_37_ = lean_ctor_get(v___y_35_, 0);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_size_37_, v___x_38_);
lean_inc_ref(v_decl_20_);
v___x_40_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_35_, v___x_39_, v_i_36_, v_decl_20_, v_g_24_);
lean_dec(v_i_36_);
v___y_26_ = v___x_40_;
goto v___jp_25_;
}
v___jp_41_:
{
lean_object* v_size_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_size_44_ = lean_ctor_get(v___y_42_, 0);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_add(v_size_44_, v___x_45_);
lean_inc_ref(v_decl_20_);
v___x_47_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_42_, v___x_46_, v_i_43_, v_decl_20_, v_g_24_);
lean_dec(v_i_43_);
v___y_26_ = v___x_47_;
goto v___jp_25_;
}
v___jp_48_:
{
lean_object* v___x_50_; 
lean_inc_ref(v_decl_20_);
v___x_50_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_22_, v___x_21_, v___y_49_, v_decl_20_);
switch(lean_obj_tag(v___x_50_))
{
case 0:
{
lean_object* v_index_51_; lean_object* v_size_52_; lean_object* v___x_53_; 
v_index_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_index_51_);
lean_dec_ref_known(v___x_50_, 3);
v_size_52_ = lean_ctor_get(v___y_49_, 0);
lean_inc(v_size_52_);
lean_inc_ref(v_decl_20_);
v___x_53_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_49_, v_size_52_, v_index_51_, v_decl_20_, v_g_24_);
lean_dec(v_index_51_);
v___y_26_ = v___x_53_;
goto v___jp_25_;
}
case 1:
{
lean_object* v_index_54_; 
v_index_54_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_index_54_);
lean_dec_ref_known(v___x_50_, 1);
v___y_42_ = v___y_49_;
v_i_43_ = v_index_54_;
goto v___jp_41_;
}
default: 
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_49_, v___x_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_index_57_; 
v_index_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_index_57_);
lean_dec_ref_known(v___x_56_, 1);
v___y_42_ = v___y_49_;
v_i_43_ = v_index_57_;
goto v___jp_41_;
}
else
{
v___y_26_ = v___y_49_;
goto v___jp_25_;
}
}
}
}
v___jp_58_:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_inc_ref(v___x_21_);
lean_inc_ref(v___f_22_);
v___x_59_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_22_, v___x_21_, v_cache_15_);
lean_inc_ref(v_decl_20_);
v___x_60_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_22_, v___x_21_, v___x_59_, v_decl_20_);
switch(lean_obj_tag(v___x_60_))
{
case 0:
{
lean_object* v_index_61_; lean_object* v_size_62_; lean_object* v___x_63_; 
v_index_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_index_61_);
lean_dec_ref_known(v___x_60_, 3);
v_size_62_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_size_62_);
lean_inc_ref(v_decl_20_);
v___x_63_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_59_, v_size_62_, v_index_61_, v_decl_20_, v_g_24_);
lean_dec(v_index_61_);
v___y_26_ = v___x_63_;
goto v___jp_25_;
}
case 1:
{
lean_object* v_index_64_; 
v_index_64_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_index_64_);
lean_dec_ref_known(v___x_60_, 1);
v___y_35_ = v___x_59_;
v_i_36_ = v_index_64_;
goto v___jp_34_;
}
default: 
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_59_, v___x_65_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_index_67_; 
v_index_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_index_67_);
lean_dec_ref_known(v___x_66_, 1);
v___y_35_ = v___x_59_;
v_i_36_ = v_index_67_;
goto v___jp_34_;
}
else
{
v___y_26_ = v___x_59_;
goto v___jp_25_;
}
}
}
}
}
else
{
lean_object* v_val_98_; lean_object* v___x_100_; 
lean_dec_ref(v___f_22_);
lean_dec_ref(v___x_21_);
lean_dec_ref_known(v_decl_20_, 1);
v_val_98_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_val_98_);
lean_dec_ref_known(v___x_23_, 1);
if (v_isShared_18_ == 0)
{
v___x_100_ = v___x_17_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_decls_14_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_cache_15_);
v___x_100_ = v_reuseFailAlloc_104_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_102_, 0, v_val_98_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_100_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_aig_109_, lean_object* v_n_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Sat_AIG_mkAtomCached___redArg(v_inst_107_, v_inst_108_, v_aig_109_, v_n_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(uint8_t v_val_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v_val_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object* v_val_115_){
_start:
{
uint8_t v_val_boxed_116_; lean_object* v_res_117_; 
v_val_boxed_116_ = lean_unbox(v_val_115_);
v_res_117_ = l_Std_Sat_AIG_mkConstCached___redArg(v_val_boxed_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object* v_00_u03b1_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_aig_121_, uint8_t v_val_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_124_, sizeof(void*)*1, v_val_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object* v_00_u03b1_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_aig_128_, lean_object* v_val_129_){
_start:
{
uint8_t v_val_boxed_130_; lean_object* v_res_131_; 
v_val_boxed_130_ = lean_unbox(v_val_129_);
v_res_131_ = l_Std_Sat_AIG_mkConstCached(v_00_u03b1_125_, v_inst_126_, v_inst_127_, v_aig_128_, v_val_boxed_130_);
lean_dec_ref(v_aig_128_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_aig_137_, lean_object* v_input_138_){
_start:
{
lean_object* v_lhs_139_; lean_object* v_rhs_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_291_; 
v_lhs_139_ = lean_ctor_get(v_input_138_, 0);
v_rhs_140_ = lean_ctor_get(v_input_138_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_input_138_);
if (v_isSharedCheck_291_ == 0)
{
v___x_142_ = v_input_138_;
v_isShared_143_ = v_isSharedCheck_291_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_rhs_140_);
lean_inc(v_lhs_139_);
lean_dec(v_input_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_291_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_decls_144_; lean_object* v_cache_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_290_; 
v_decls_144_ = lean_ctor_get(v_aig_137_, 0);
v_cache_145_ = lean_ctor_get(v_aig_137_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v_aig_137_);
if (v_isSharedCheck_290_ == 0)
{
v___x_147_ = v_aig_137_;
v_isShared_148_ = v_isSharedCheck_290_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_cache_145_);
lean_inc(v_decls_144_);
lean_dec(v_aig_137_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_290_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_gate_149_; uint8_t v_invert_150_; lean_object* v_gate_151_; uint8_t v_invert_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_decl_162_; 
v_gate_149_ = lean_ctor_get(v_lhs_139_, 0);
lean_inc(v_gate_149_);
v_invert_150_ = lean_ctor_get_uint8(v_lhs_139_, sizeof(void*)*1);
v_gate_151_ = lean_ctor_get(v_rhs_140_, 0);
v_invert_152_ = lean_ctor_get_uint8(v_rhs_140_, sizeof(void*)*1);
v___f_153_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_153_, 0, v_inst_136_);
v___x_154_ = lean_unsigned_to_nat(2u);
v___x_155_ = lean_nat_mul(v_gate_149_, v___x_154_);
v___x_156_ = l_Bool_toNat(v_invert_150_);
v___x_157_ = lean_nat_lor(v___x_155_, v___x_156_);
lean_dec(v___x_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_nat_mul(v_gate_151_, v___x_154_);
v___x_159_ = l_Bool_toNat(v_invert_152_);
v___x_160_ = lean_nat_lor(v___x_158_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v___x_158_);
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 2);
lean_ctor_set(v___x_142_, 1, v___x_160_);
lean_ctor_set(v___x_142_, 0, v___x_157_);
v_decl_162_ = v___x_142_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_160_);
v_decl_162_ = v_reuseFailAlloc_289_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___f_164_; lean_object* v___x_165_; 
v___x_163_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_instHashableDecl_hash___boxed), 3, 2);
lean_closure_set(v___x_163_, 0, lean_box(0));
lean_closure_set(v___x_163_, 1, v_inst_135_);
v___f_164_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_164_, 0, v___f_153_);
lean_inc_ref(v_decl_162_);
lean_inc_ref(v___x_163_);
lean_inc_ref(v___f_164_);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_164_, v___x_163_, v_cache_145_, v_decl_162_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_167_; 
lean_inc(v_gate_151_);
lean_inc_ref(v_cache_145_);
lean_inc_ref(v_decls_144_);
if (v_isShared_148_ == 0)
{
v___x_167_ = v___x_147_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_decls_144_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_cache_145_);
v___x_167_ = v_reuseFailAlloc_274_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
uint8_t v___y_169_; uint8_t v___y_174_; lean_object* v_lhsVal_183_; lean_object* v_rhsVal_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_272_; 
v_lhsVal_183_ = l_Std_Sat_AIG_getConstant___redArg(v___x_167_, v_lhs_139_);
lean_dec_ref(v_lhs_139_);
v_rhsVal_184_ = l_Std_Sat_AIG_getConstant___redArg(v___x_167_, v_rhs_140_);
v_isSharedCheck_272_ = !lean_is_exclusive(v_rhs_140_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_rhs_140_, 0);
lean_dec(v_unused_273_);
v___x_186_ = v_rhs_140_;
v_isShared_187_ = v_isSharedCheck_272_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_rhs_140_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_272_;
goto v_resetjp_185_;
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v_ref_171_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v_ref_171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_ref_171_, 0, v___x_170_);
lean_ctor_set_uint8(v_ref_171_, sizeof(void*)*1, v___y_169_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_167_);
lean_ctor_set(v___x_172_, 1, v_ref_171_);
return v___x_172_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_dec(v_gate_149_);
v___y_169_ = v___y_174_;
goto v___jp_168_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_175_, 0, v_gate_149_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v_invert_150_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_167_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
return v___x_176_;
}
}
v___jp_177_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_178_, 0, v_gate_151_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v_invert_152_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_167_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
v___jp_180_:
{
lean_object* v_ref_181_; lean_object* v___x_182_; 
v_ref_181_ = ((lean_object*)(l_Std_Sat_AIG_mkGateCached_go___redArg___closed__0));
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_167_);
lean_ctor_set(v___x_182_, 1, v_ref_181_);
return v___x_182_;
}
v_resetjp_185_:
{
if (lean_obj_tag(v_lhsVal_183_) == 1)
{
lean_object* v_val_188_; uint8_t v___x_189_; 
lean_del_object(v___x_186_);
lean_dec_ref(v___f_164_);
lean_dec_ref(v___x_163_);
lean_dec_ref(v_decl_162_);
lean_dec(v_gate_149_);
lean_dec_ref(v_cache_145_);
lean_dec_ref(v_decls_144_);
v_val_188_ = lean_ctor_get(v_lhsVal_183_, 0);
lean_inc(v_val_188_);
lean_dec_ref_known(v_lhsVal_183_, 1);
v___x_189_ = lean_unbox(v_val_188_);
lean_dec(v_val_188_);
if (v___x_189_ == 0)
{
lean_dec(v_rhsVal_184_);
lean_dec(v_gate_151_);
goto v___jp_180_;
}
else
{
if (lean_obj_tag(v_rhsVal_184_) == 1)
{
lean_object* v_val_190_; uint8_t v___x_191_; 
v_val_190_ = lean_ctor_get(v_rhsVal_184_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v_rhsVal_184_, 1);
v___x_191_ = lean_unbox(v_val_190_);
lean_dec(v_val_190_);
if (v___x_191_ == 0)
{
lean_dec(v_gate_151_);
goto v___jp_180_;
}
else
{
goto v___jp_177_;
}
}
else
{
lean_dec(v_rhsVal_184_);
goto v___jp_177_;
}
}
}
else
{
lean_dec(v_lhsVal_183_);
if (lean_obj_tag(v_rhsVal_184_) == 1)
{
lean_object* v_val_192_; uint8_t v___x_193_; 
lean_dec_ref(v___f_164_);
lean_dec_ref(v___x_163_);
lean_dec_ref(v_decl_162_);
lean_dec(v_gate_151_);
lean_dec_ref(v_cache_145_);
lean_dec_ref(v_decls_144_);
v_val_192_ = lean_ctor_get(v_rhsVal_184_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_rhsVal_184_, 1);
v___x_193_ = lean_unbox(v_val_192_);
lean_dec(v_val_192_);
if (v___x_193_ == 0)
{
lean_del_object(v___x_186_);
lean_dec(v_gate_149_);
goto v___jp_180_;
}
else
{
lean_object* v___x_195_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v_gate_149_);
v___x_195_ = v___x_186_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_gate_149_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v_invert_150_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_167_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
return v___x_196_;
}
}
}
else
{
uint8_t v___x_198_; 
lean_dec(v_rhsVal_184_);
v___x_198_ = lean_nat_dec_eq(v_gate_149_, v_gate_151_);
lean_dec(v_gate_151_);
if (v___x_198_ == 0)
{
lean_object* v_g_199_; lean_object* v___y_201_; lean_object* v___y_209_; lean_object* v_i_210_; lean_object* v___y_216_; lean_object* v_i_217_; lean_object* v___y_223_; lean_object* v___x_242_; 
lean_dec_ref(v___x_167_);
lean_dec(v_gate_149_);
v_g_199_ = lean_array_get_size(v_decls_144_);
lean_inc_ref(v_decl_162_);
lean_inc_ref(v___x_163_);
lean_inc_ref(v___f_164_);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_164_, v___x_163_, v_cache_145_, v_decl_162_);
switch(lean_obj_tag(v___x_242_))
{
case 0:
{
lean_object* v_index_243_; lean_object* v_size_244_; lean_object* v___x_245_; 
lean_dec_ref(v___f_164_);
lean_dec_ref(v___x_163_);
v_index_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_index_243_);
lean_dec_ref_known(v___x_242_, 3);
v_size_244_ = lean_ctor_get(v_cache_145_, 0);
lean_inc(v_size_244_);
lean_inc_ref(v_decl_162_);
v___x_245_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_145_, v_size_244_, v_index_243_, v_decl_162_, v_g_199_);
lean_dec(v_index_243_);
v___y_201_ = v___x_245_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_246_; lean_object* v_size_247_; lean_object* v_keyArray_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_index_246_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_index_246_);
lean_dec_ref_known(v___x_242_, 1);
v_size_247_ = lean_ctor_get(v_cache_145_, 0);
v_keyArray_248_ = lean_ctor_get(v_cache_145_, 1);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_size_247_, v___x_249_);
v___x_251_ = lean_array_get_size(v_keyArray_248_);
v___x_252_ = lean_nat_dec_lt(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v___x_250_);
lean_dec(v_index_246_);
goto v___jp_232_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_253_ = lean_unsigned_to_nat(4u);
v___x_254_ = lean_nat_mul(v___x_250_, v___x_253_);
v___x_255_ = lean_unsigned_to_nat(3u);
v___x_256_ = lean_nat_mul(v___x_251_, v___x_255_);
v___x_257_ = lean_nat_dec_le(v___x_254_, v___x_256_);
lean_dec(v___x_256_);
lean_dec(v___x_254_);
if (v___x_257_ == 0)
{
lean_dec(v___x_250_);
lean_dec(v_index_246_);
goto v___jp_232_;
}
else
{
lean_object* v___x_258_; 
lean_dec_ref(v___f_164_);
lean_dec_ref(v___x_163_);
lean_inc_ref(v_decl_162_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v_cache_145_, v___x_250_, v_index_246_, v_decl_162_, v_g_199_);
lean_dec(v_index_246_);
v___y_201_ = v___x_258_;
goto v___jp_200_;
}
}
}
default: 
{
lean_object* v_size_259_; lean_object* v_keyArray_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_size_259_ = lean_ctor_get(v_cache_145_, 0);
v_keyArray_260_ = lean_ctor_get(v_cache_145_, 1);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_size_259_, v___x_261_);
v___x_263_ = lean_array_get_size(v_keyArray_260_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v___x_262_);
lean_inc_ref(v___x_163_);
lean_inc_ref(v___f_164_);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_164_, v___x_163_, v_cache_145_);
v___y_223_ = v___x_265_;
goto v___jp_222_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_266_ = lean_unsigned_to_nat(4u);
v___x_267_ = lean_nat_mul(v___x_262_, v___x_266_);
lean_dec(v___x_262_);
v___x_268_ = lean_unsigned_to_nat(3u);
v___x_269_ = lean_nat_mul(v___x_263_, v___x_268_);
v___x_270_ = lean_nat_dec_le(v___x_267_, v___x_269_);
lean_dec(v___x_269_);
lean_dec(v___x_267_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_inc_ref(v___x_163_);
lean_inc_ref(v___f_164_);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_164_, v___x_163_, v_cache_145_);
v___y_223_ = v___x_271_;
goto v___jp_222_;
}
else
{
v___y_223_ = v_cache_145_;
goto v___jp_222_;
}
}
}
}
v___jp_200_:
{
lean_object* v_decls_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v_decls_202_ = lean_array_push(v_decls_144_, v_decl_162_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_decls_202_);
lean_ctor_set(v___x_203_, 1, v___y_201_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v_g_199_);
v___x_205_ = v___x_186_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_g_199_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_198_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
v___jp_208_:
{
lean_object* v_size_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_size_211_ = lean_ctor_get(v___y_209_, 0);
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v_size_211_, v___x_212_);
lean_inc_ref(v_decl_162_);
v___x_214_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_209_, v___x_213_, v_i_210_, v_decl_162_, v_g_199_);
lean_dec(v_i_210_);
v___y_201_ = v___x_214_;
goto v___jp_200_;
}
v___jp_215_:
{
lean_object* v_size_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_size_218_ = lean_ctor_get(v___y_216_, 0);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_size_218_, v___x_219_);
lean_inc_ref(v_decl_162_);
v___x_221_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_216_, v___x_220_, v_i_217_, v_decl_162_, v_g_199_);
lean_dec(v_i_217_);
v___y_201_ = v___x_221_;
goto v___jp_200_;
}
v___jp_222_:
{
lean_object* v___x_224_; 
lean_inc_ref(v_decl_162_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_164_, v___x_163_, v___y_223_, v_decl_162_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_object* v_index_225_; lean_object* v_size_226_; lean_object* v___x_227_; 
v_index_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_224_, 3);
v_size_226_ = lean_ctor_get(v___y_223_, 0);
lean_inc(v_size_226_);
lean_inc_ref(v_decl_162_);
v___x_227_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_223_, v_size_226_, v_index_225_, v_decl_162_, v_g_199_);
lean_dec(v_index_225_);
v___y_201_ = v___x_227_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_228_; 
v_index_228_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_228_);
lean_dec_ref_known(v___x_224_, 1);
v___y_216_ = v___y_223_;
v_i_217_ = v_index_228_;
goto v___jp_215_;
}
default: 
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_223_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_index_231_; 
v_index_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_230_, 1);
v___y_216_ = v___y_223_;
v_i_217_ = v_index_231_;
goto v___jp_215_;
}
else
{
v___y_201_ = v___y_223_;
goto v___jp_200_;
}
}
}
}
v___jp_232_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc_ref(v___x_163_);
lean_inc_ref(v___f_164_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_164_, v___x_163_, v_cache_145_);
lean_inc_ref(v_decl_162_);
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_164_, v___x_163_, v___x_233_, v_decl_162_);
switch(lean_obj_tag(v___x_234_))
{
case 0:
{
lean_object* v_index_235_; lean_object* v_size_236_; lean_object* v___x_237_; 
v_index_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_index_235_);
lean_dec_ref_known(v___x_234_, 3);
v_size_236_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_size_236_);
lean_inc_ref(v_decl_162_);
v___x_237_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_233_, v_size_236_, v_index_235_, v_decl_162_, v_g_199_);
lean_dec(v_index_235_);
v___y_201_ = v___x_237_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_238_; 
v_index_238_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_index_238_);
lean_dec_ref_known(v___x_234_, 1);
v___y_209_ = v___x_233_;
v_i_210_ = v_index_238_;
goto v___jp_208_;
}
default: 
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_233_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_index_241_; 
v_index_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_index_241_);
lean_dec_ref_known(v___x_240_, 1);
v___y_209_ = v___x_233_;
v_i_210_ = v_index_241_;
goto v___jp_208_;
}
else
{
v___y_201_ = v___x_233_;
goto v___jp_200_;
}
}
}
}
}
else
{
lean_del_object(v___x_186_);
lean_dec_ref(v___f_164_);
lean_dec_ref(v___x_163_);
lean_dec_ref(v_decl_162_);
lean_dec_ref(v_cache_145_);
lean_dec_ref(v_decls_144_);
if (v_invert_150_ == 0)
{
if (v_invert_152_ == 0)
{
v___y_174_ = v___x_198_;
goto v___jp_173_;
}
else
{
lean_dec(v_gate_149_);
v___y_169_ = v_invert_150_;
goto v___jp_168_;
}
}
else
{
v___y_174_ = v_invert_152_;
goto v___jp_173_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v___f_164_);
lean_dec_ref(v___x_163_);
lean_dec_ref(v_decl_162_);
lean_dec(v_gate_149_);
lean_dec_ref(v_lhs_139_);
v_isSharedCheck_287_ = !lean_is_exclusive(v_rhs_140_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_rhs_140_, 0);
lean_dec(v_unused_288_);
v___x_276_ = v_rhs_140_;
v_isShared_277_ = v_isSharedCheck_287_;
goto v_resetjp_275_;
}
else
{
lean_dec(v_rhs_140_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_287_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_val_278_; lean_object* v___x_280_; 
v_val_278_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_165_, 1);
if (v_isShared_148_ == 0)
{
v___x_280_ = v___x_147_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_decls_144_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_cache_145_);
v___x_280_ = v_reuseFailAlloc_286_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
uint8_t v___x_281_; lean_object* v___x_283_; 
v___x_281_ = 0;
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_val_278_);
v___x_283_ = v___x_276_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_val_278_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_281_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_280_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
return v___x_284_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_aig_295_, lean_object* v_input_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_293_, v_inst_294_, v_aig_295_, v_input_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_aig_300_, lean_object* v_input_301_){
_start:
{
lean_object* v_lhs_302_; lean_object* v_rhs_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_318_; 
v_lhs_302_ = lean_ctor_get(v_input_301_, 0);
v_rhs_303_ = lean_ctor_get(v_input_301_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_input_301_);
if (v_isSharedCheck_318_ == 0)
{
v___x_305_ = v_input_301_;
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_rhs_303_);
lean_inc(v_lhs_302_);
lean_dec(v_input_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_318_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_gate_307_; lean_object* v_gate_308_; uint8_t v___x_309_; 
v_gate_307_ = lean_ctor_get(v_lhs_302_, 0);
v_gate_308_ = lean_ctor_get(v_rhs_303_, 0);
v___x_309_ = lean_nat_dec_lt(v_gate_307_, v_gate_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_311_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_lhs_302_);
lean_ctor_set(v___x_305_, 0, v_rhs_303_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_rhs_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_lhs_302_);
v___x_311_ = v_reuseFailAlloc_313_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_298_, v_inst_299_, v_aig_300_, v___x_311_);
return v___x_312_;
}
}
else
{
lean_object* v___x_315_; 
if (v_isShared_306_ == 0)
{
v___x_315_ = v___x_305_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_lhs_302_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_rhs_303_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_Sat_AIG_mkGateCached_go___redArg(v_inst_298_, v_inst_299_, v_aig_300_, v___x_315_);
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_aig_322_, lean_object* v_input_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_320_, v_inst_321_, v_aig_322_, v_input_323_);
return v___x_324_;
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
