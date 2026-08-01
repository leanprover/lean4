// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpValue
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM
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
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Compiler_hasInductiveOverride(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInductiveOverride_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
if (lean_obj_tag(v_e_1_) == 2)
{
lean_object* v_idx_7_; lean_object* v_struct_8_; lean_object* v___x_9_; 
v_idx_7_ = lean_ctor_get(v_e_1_, 1);
v_struct_8_ = lean_ctor_get(v_e_1_, 2);
v___x_9_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_struct_8_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_36_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_36_ == 0)
{
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_36_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_36_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
if (lean_obj_tag(v_a_10_) == 1)
{
lean_object* v_val_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_31_; 
v_val_14_ = lean_ctor_get(v_a_10_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_31_ == 0)
{
v___x_16_ = v_a_10_;
v_isShared_17_ = v_isSharedCheck_31_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_val_14_);
lean_dec(v_a_10_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_31_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_val_18_; lean_object* v_args_19_; lean_object* v_numParams_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v_val_18_ = lean_ctor_get(v_val_14_, 0);
lean_inc_ref(v_val_18_);
v_args_19_ = lean_ctor_get(v_val_14_, 1);
lean_inc_ref(v_args_19_);
lean_dec(v_val_14_);
v_numParams_20_ = lean_ctor_get(v_val_18_, 3);
lean_inc(v_numParams_20_);
lean_dec_ref(v_val_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_nat_add(v_numParams_20_, v_idx_7_);
lean_dec(v_numParams_20_);
v___x_23_ = lean_array_get(v___x_21_, v_args_19_, v___x_22_);
lean_dec(v___x_22_);
lean_dec_ref(v_args_19_);
v___x_24_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_23_);
lean_dec(v___x_23_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_24_);
v___x_26_ = v___x_16_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_30_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_28_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_26_);
v___x_28_ = v___x_12_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
lean_object* v___x_32_; lean_object* v___x_34_; 
lean_dec(v_a_10_);
v___x_32_ = lean_box(0);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_32_);
v___x_34_ = v___x_12_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_9_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_9_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_box(0);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg___boxed(lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_e_47_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* v_e_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_54_, v_a_57_, v_a_59_, v_a_60_, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object* v_e_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(v_e_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_e_64_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(lean_object* v_e_76_, lean_object* v_a_77_){
_start:
{
if (lean_obj_tag(v_e_76_) == 4)
{
lean_object* v_fvarId_79_; lean_object* v_args_80_; uint8_t v___x_81_; lean_object* v___x_82_; 
v_fvarId_79_ = lean_ctor_get(v_e_76_, 0);
v_args_80_ = lean_ctor_get(v_e_76_, 1);
v___x_81_ = 0;
v___x_82_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_81_, v_fvarId_79_, v_a_77_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_152_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_152_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_152_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_152_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
if (lean_obj_tag(v_a_83_) == 1)
{
lean_object* v_val_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_147_; 
v_val_87_ = lean_ctor_get(v_a_83_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_a_83_);
if (v_isSharedCheck_147_ == 0)
{
v___x_89_ = v_a_83_;
v_isShared_90_ = v_isSharedCheck_147_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_val_87_);
lean_dec(v_a_83_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_147_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_value_91_; 
v_value_91_ = lean_ctor_get(v_val_87_, 3);
lean_inc(v_value_91_);
lean_dec(v_val_87_);
switch(lean_obj_tag(v_value_91_))
{
case 1:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_del_object(v___x_89_);
v___x_92_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0));
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_92_);
v___x_94_ = v___x_85_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
case 3:
{
lean_object* v_declName_96_; lean_object* v_us_97_; lean_object* v_args_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_119_; 
v_declName_96_ = lean_ctor_get(v_value_91_, 0);
v_us_97_ = lean_ctor_get(v_value_91_, 1);
v_args_98_ = lean_ctor_get(v_value_91_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v_value_91_);
if (v_isSharedCheck_119_ == 0)
{
v___x_100_ = v_value_91_;
v_isShared_101_ = v_isSharedCheck_119_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_args_98_);
lean_inc(v_us_97_);
lean_inc(v_declName_96_);
lean_dec(v_value_91_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_119_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = lean_array_get_size(v_args_80_);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_dec_eq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = l_Array_append___redArg(v_args_98_, v_args_80_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 2, v___x_105_);
v___x_107_ = v___x_100_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_declName_96_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_us_97_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v___x_105_);
v___x_107_ = v_reuseFailAlloc_114_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_107_);
v___x_109_ = v___x_89_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_109_);
v___x_111_ = v___x_85_;
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
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_del_object(v___x_100_);
lean_dec_ref(v_args_98_);
lean_dec(v_us_97_);
lean_dec(v_declName_96_);
lean_del_object(v___x_89_);
v___x_115_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_115_);
v___x_117_ = v___x_85_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_120_; lean_object* v_args_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_142_; 
v_fvarId_120_ = lean_ctor_get(v_value_91_, 0);
v_args_121_ = lean_ctor_get(v_value_91_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_value_91_);
if (v_isSharedCheck_142_ == 0)
{
v___x_123_ = v_value_91_;
v_isShared_124_ = v_isSharedCheck_142_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_args_121_);
lean_inc(v_fvarId_120_);
lean_dec(v_value_91_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_142_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = lean_array_get_size(v_args_80_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_nat_dec_eq(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = l_Array_append___redArg(v_args_121_, v_args_80_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_128_);
v___x_130_ = v___x_123_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_fvarId_120_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_137_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_130_);
v___x_132_ = v___x_89_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_136_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_132_);
v___x_134_ = v___x_85_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_del_object(v___x_123_);
lean_dec_ref(v_args_121_);
lean_dec(v_fvarId_120_);
lean_del_object(v___x_89_);
v___x_138_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_138_);
v___x_140_ = v___x_85_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
default: 
{
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v_value_91_);
lean_del_object(v___x_89_);
v___x_143_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_143_);
v___x_145_ = v___x_85_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
else
{
lean_object* v___x_148_; lean_object* v___x_150_; 
lean_dec(v_a_83_);
v___x_148_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_148_);
v___x_150_ = v___x_85_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_153_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_82_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_82_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___boxed(lean_object* v_e_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec(v_e_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_167_, v_a_172_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_e_177_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(lean_object* v_e_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
if (lean_obj_tag(v_e_189_) == 3)
{
lean_object* v_declName_196_; lean_object* v___x_197_; lean_object* v_env_235_; lean_object* v___x_243_; 
v_declName_196_ = lean_ctor_get(v_e_189_, 0);
v___x_197_ = lean_st_ref_get(v_a_194_);
v_env_235_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref_n(v_env_235_, 2);
lean_dec(v___x_197_);
lean_inc(v_declName_196_);
v___x_243_ = l_Lean_Compiler_getInductiveOverride_x3f(v_env_235_, v_declName_196_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_243_, 1);
if (lean_obj_tag(v_val_244_) == 2)
{
lean_dec_ref_known(v_val_244_, 2);
lean_dec_ref(v_env_235_);
goto v___jp_198_;
}
else
{
lean_dec(v_val_244_);
goto v___jp_236_;
}
}
else
{
lean_dec(v___x_243_);
goto v___jp_236_;
}
v___jp_198_:
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = 0;
v___x_200_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_199_, v_e_189_);
v___x_201_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(v___x_200_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_223_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_223_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_223_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_223_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
if (lean_obj_tag(v_a_202_) == 1)
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_218_; 
v_val_206_ = lean_ctor_get(v_a_202_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_202_);
if (v_isSharedCheck_218_ == 0)
{
v___x_208_ = v_a_202_;
v_isShared_209_ = v_isSharedCheck_218_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v_a_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_218_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0));
v___x_211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_211_, 0, v_val_206_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_213_);
v___x_215_ = v___x_204_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec(v_a_202_);
v___x_219_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_219_);
v___x_221_ = v___x_204_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_201_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_201_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
v___jp_232_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_box(0);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
v___jp_236_:
{
uint8_t v___x_237_; lean_object* v___x_238_; 
v___x_237_ = 0;
lean_inc(v_declName_196_);
lean_inc_ref(v_env_235_);
v___x_238_ = l_Lean_Environment_find_x3f(v_env_235_, v_declName_196_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_dec_ref(v_env_235_);
lean_dec_ref_known(v_e_189_, 3);
goto v___jp_232_;
}
else
{
lean_object* v_val_239_; 
v_val_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v___x_238_, 1);
if (lean_obj_tag(v_val_239_) == 6)
{
lean_object* v_val_240_; lean_object* v_induct_241_; uint8_t v___x_242_; 
v_val_240_ = lean_ctor_get(v_val_239_, 0);
lean_inc_ref(v_val_240_);
lean_dec_ref_known(v_val_239_, 1);
v_induct_241_ = lean_ctor_get(v_val_240_, 1);
lean_inc(v_induct_241_);
lean_dec_ref(v_val_240_);
v___x_242_ = l_Lean_Compiler_hasInductiveOverride(v_env_235_, v_induct_241_);
if (v___x_242_ == 0)
{
goto v___jp_198_;
}
else
{
lean_dec_ref_known(v_e_189_, 3);
goto v___jp_232_;
}
}
else
{
lean_dec(v_val_239_);
lean_dec_ref(v_env_235_);
lean_dec_ref_known(v_e_189_, 3);
goto v___jp_232_;
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v_e_189_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___boxed(lean_object* v_e_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object* v_e_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_255_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(v_e_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(lean_object* v_e_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_config_279_; uint8_t v_implementedBy_280_; 
v_config_279_ = lean_ctor_get(v_a_276_, 1);
v_implementedBy_280_ = lean_ctor_get_uint8(v_config_279_, 2);
if (v_implementedBy_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_e_275_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
else
{
if (lean_obj_tag(v_e_275_) == 3)
{
lean_object* v_declName_283_; lean_object* v_us_284_; lean_object* v_args_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_306_; 
v_declName_283_ = lean_ctor_get(v_e_275_, 0);
v_us_284_ = lean_ctor_get(v_e_275_, 1);
v_args_285_ = lean_ctor_get(v_e_275_, 2);
v_isSharedCheck_306_ = !lean_is_exclusive(v_e_275_);
if (v_isSharedCheck_306_ == 0)
{
v___x_287_ = v_e_275_;
v_isShared_288_ = v_isSharedCheck_306_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_args_285_);
lean_inc(v_us_284_);
lean_inc(v_declName_283_);
lean_dec(v_e_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_306_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v_env_290_; lean_object* v___x_291_; 
v___x_289_ = lean_st_ref_get(v_a_277_);
v_env_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_env_290_);
lean_dec(v___x_289_);
v___x_291_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_290_, v_declName_283_);
if (lean_obj_tag(v___x_291_) == 1)
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_303_; 
v_val_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_303_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_303_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_303_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v_val_292_);
v___x_297_ = v___x_287_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_val_292_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_us_284_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_args_285_);
v___x_297_ = v_reuseFailAlloc_302_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_297_);
v___x_299_ = v___x_294_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_301_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_291_);
lean_del_object(v___x_287_);
lean_dec_ref(v_args_285_);
lean_dec(v_us_284_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_e_275_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(lean_object* v_e_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_314_, v_a_315_, v_a_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* v_e_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(v_e_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_334_, v_a_336_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
if (lean_obj_tag(v_a_343_) == 0)
{
lean_object* v___x_344_; 
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_334_, v_a_338_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
if (lean_obj_tag(v_a_345_) == 0)
{
lean_object* v___x_346_; 
lean_dec_ref_known(v___x_344_, 1);
lean_inc(v_e_334_);
v___x_346_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_334_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
if (lean_obj_tag(v_a_347_) == 0)
{
lean_object* v___x_348_; 
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_334_, v_a_335_, v_a_340_);
return v___x_348_;
}
else
{
lean_dec_ref_known(v_a_347_, 1);
lean_dec(v_e_334_);
return v___x_346_;
}
}
else
{
lean_dec(v_e_334_);
return v___x_346_;
}
}
else
{
lean_dec_ref_known(v_a_345_, 1);
lean_dec(v_e_334_);
return v___x_344_;
}
}
else
{
lean_dec(v_e_334_);
return v___x_344_;
}
}
else
{
lean_dec_ref_known(v_a_343_, 1);
lean_dec(v_e_334_);
return v___x_342_;
}
}
else
{
lean_dec(v_e_334_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_358_, v_a_359_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_377_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
}
#ifdef __cplusplus
}
#endif
