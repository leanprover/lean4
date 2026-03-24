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
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
if (lean_obj_tag(v_e_1_) == 2)
{
lean_object* v_idx_6_; lean_object* v_struct_7_; lean_object* v___x_8_; 
v_idx_6_ = lean_ctor_get(v_e_1_, 1);
v_struct_7_ = lean_ctor_get(v_e_1_, 2);
v___x_8_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_struct_7_, v_a_2_, v_a_3_, v_a_4_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_39_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_39_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_39_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_39_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
if (lean_obj_tag(v_a_9_) == 1)
{
lean_object* v_val_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_34_; 
v_val_13_ = lean_ctor_get(v_a_9_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v_a_9_);
if (v_isSharedCheck_34_ == 0)
{
v___x_15_ = v_a_9_;
v_isShared_16_ = v_isSharedCheck_34_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_val_13_);
lean_dec(v_a_9_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_34_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
if (lean_obj_tag(v_val_13_) == 0)
{
lean_object* v_val_17_; lean_object* v_args_18_; lean_object* v_numParams_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
v_val_17_ = lean_ctor_get(v_val_13_, 0);
lean_inc_ref(v_val_17_);
v_args_18_ = lean_ctor_get(v_val_13_, 1);
lean_inc_ref(v_args_18_);
lean_dec_ref(v_val_13_);
v_numParams_19_ = lean_ctor_get(v_val_17_, 3);
lean_inc(v_numParams_19_);
lean_dec_ref(v_val_17_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_nat_add(v_numParams_19_, v_idx_6_);
lean_dec(v_numParams_19_);
v___x_22_ = lean_array_get(v___x_20_, v_args_18_, v___x_21_);
lean_dec(v___x_21_);
lean_dec_ref(v_args_18_);
v___x_23_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_22_);
lean_dec(v___x_22_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_23_);
v___x_25_ = v___x_15_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_29_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_27_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v___x_25_);
v___x_27_ = v___x_11_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v___x_30_; lean_object* v___x_32_; 
lean_dec_ref(v_val_13_);
lean_del_object(v___x_15_);
v___x_30_ = lean_box(0);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v___x_30_);
v___x_32_ = v___x_11_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_dec(v_a_9_);
v___x_35_ = lean_box(0);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v___x_35_);
v___x_37_ = v___x_11_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_8_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_8_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_box(0);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg___boxed(lean_object* v_e_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_50_, v_a_51_, v_a_52_, v_a_53_);
lean_dec(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_e_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* v_e_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_56_, v_a_59_, v_a_61_, v_a_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object* v_e_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(v_e_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_e_66_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(lean_object* v_e_78_, lean_object* v_a_79_){
_start:
{
if (lean_obj_tag(v_e_78_) == 4)
{
lean_object* v_fvarId_81_; lean_object* v_args_82_; uint8_t v___x_83_; lean_object* v___x_84_; 
v_fvarId_81_ = lean_ctor_get(v_e_78_, 0);
v_args_82_ = lean_ctor_get(v_e_78_, 1);
v___x_83_ = 0;
v___x_84_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_83_, v_fvarId_81_, v_a_79_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_154_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_154_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_154_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_154_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
if (lean_obj_tag(v_a_85_) == 1)
{
lean_object* v_val_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_149_; 
v_val_89_ = lean_ctor_get(v_a_85_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_149_ == 0)
{
v___x_91_ = v_a_85_;
v_isShared_92_ = v_isSharedCheck_149_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_val_89_);
lean_dec(v_a_85_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_149_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_value_93_; 
v_value_93_ = lean_ctor_get(v_val_89_, 3);
lean_inc(v_value_93_);
lean_dec(v_val_89_);
switch(lean_obj_tag(v_value_93_))
{
case 1:
{
lean_object* v___x_94_; lean_object* v___x_96_; 
lean_del_object(v___x_91_);
v___x_94_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0));
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_94_);
v___x_96_ = v___x_87_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
case 3:
{
lean_object* v_declName_98_; lean_object* v_us_99_; lean_object* v_args_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_121_; 
v_declName_98_ = lean_ctor_get(v_value_93_, 0);
v_us_99_ = lean_ctor_get(v_value_93_, 1);
v_args_100_ = lean_ctor_get(v_value_93_, 2);
v_isSharedCheck_121_ = !lean_is_exclusive(v_value_93_);
if (v_isSharedCheck_121_ == 0)
{
v___x_102_ = v_value_93_;
v_isShared_103_ = v_isSharedCheck_121_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_args_100_);
lean_inc(v_us_99_);
lean_inc(v_declName_98_);
lean_dec(v_value_93_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_121_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_array_get_size(v_args_82_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_Array_append___redArg(v_args_100_, v_args_82_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_107_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_declName_98_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_us_99_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v___x_107_);
v___x_109_ = v_reuseFailAlloc_116_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_109_);
v___x_111_ = v___x_91_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_115_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_111_);
v___x_113_ = v___x_87_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
else
{
lean_object* v___x_117_; lean_object* v___x_119_; 
lean_del_object(v___x_102_);
lean_dec_ref(v_args_100_);
lean_dec(v_us_99_);
lean_dec(v_declName_98_);
lean_del_object(v___x_91_);
v___x_117_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_117_);
v___x_119_ = v___x_87_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_122_; lean_object* v_args_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_144_; 
v_fvarId_122_ = lean_ctor_get(v_value_93_, 0);
v_args_123_ = lean_ctor_get(v_value_93_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_value_93_);
if (v_isSharedCheck_144_ == 0)
{
v___x_125_ = v_value_93_;
v_isShared_126_ = v_isSharedCheck_144_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_args_123_);
lean_inc(v_fvarId_122_);
lean_dec(v_value_93_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_144_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_array_get_size(v_args_82_);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_dec_eq(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = l_Array_append___redArg(v_args_123_, v_args_82_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_130_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_fvarId_122_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_139_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_132_);
v___x_134_ = v___x_91_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_138_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_134_);
v___x_136_ = v___x_87_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_del_object(v___x_125_);
lean_dec_ref(v_args_123_);
lean_dec(v_fvarId_122_);
lean_del_object(v___x_91_);
v___x_140_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_140_);
v___x_142_ = v___x_87_;
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
}
}
default: 
{
lean_object* v___x_145_; lean_object* v___x_147_; 
lean_dec(v_value_93_);
lean_del_object(v___x_91_);
v___x_145_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_145_);
v___x_147_ = v___x_87_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
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
else
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_dec(v_a_85_);
v___x_150_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_150_);
v___x_152_ = v___x_87_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_84_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_84_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___boxed(lean_object* v_e_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec(v_e_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_169_, v_a_174_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* v_e_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(v_e_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_e_179_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(lean_object* v_e_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
if (lean_obj_tag(v_e_191_) == 3)
{
lean_object* v_declName_201_; lean_object* v___x_202_; lean_object* v_env_203_; uint8_t v___x_204_; lean_object* v___x_205_; 
v_declName_201_ = lean_ctor_get(v_e_191_, 0);
v___x_202_ = lean_st_ref_get(v_a_196_);
v_env_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_env_203_);
lean_dec(v___x_202_);
v___x_204_ = 0;
lean_inc(v_declName_201_);
v___x_205_ = l_Lean_Environment_find_x3f(v_env_203_, v_declName_201_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 1)
{
lean_object* v_val_206_; 
v_val_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v___x_205_);
if (lean_obj_tag(v_val_206_) == 6)
{
uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref(v_val_206_);
v___x_207_ = 0;
v___x_208_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_207_, v_e_191_);
lean_inc_ref(v_a_192_);
v___x_209_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(v___x_208_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_231_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_231_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_231_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_231_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
if (lean_obj_tag(v_a_210_) == 1)
{
lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_226_; 
v_val_214_ = lean_ctor_get(v_a_210_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_216_ = v_a_210_;
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_dec(v_a_210_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0));
v___x_219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_219_, 0, v_val_214_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_221_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_a_210_);
v___x_227_ = lean_box(0);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_227_);
v___x_229_ = v___x_212_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
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
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_209_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_209_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_dec(v_val_206_);
lean_dec_ref(v_e_191_);
goto v___jp_198_;
}
}
else
{
lean_dec(v___x_205_);
lean_dec_ref(v_e_191_);
goto v___jp_198_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_e_191_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
v___jp_198_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___boxed(lean_object* v_e_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object* v_e_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_250_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(v_e_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(lean_object* v_e_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_config_274_; uint8_t v_implementedBy_275_; 
v_config_274_ = lean_ctor_get(v_a_271_, 1);
v_implementedBy_275_ = lean_ctor_get_uint8(v_config_274_, 2);
if (v_implementedBy_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_e_270_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
else
{
if (lean_obj_tag(v_e_270_) == 3)
{
lean_object* v_declName_278_; lean_object* v_us_279_; lean_object* v_args_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_301_; 
v_declName_278_ = lean_ctor_get(v_e_270_, 0);
v_us_279_ = lean_ctor_get(v_e_270_, 1);
v_args_280_ = lean_ctor_get(v_e_270_, 2);
v_isSharedCheck_301_ = !lean_is_exclusive(v_e_270_);
if (v_isSharedCheck_301_ == 0)
{
v___x_282_ = v_e_270_;
v_isShared_283_ = v_isSharedCheck_301_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_args_280_);
lean_inc(v_us_279_);
lean_inc(v_declName_278_);
lean_dec(v_e_270_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_301_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_env_285_; lean_object* v___x_286_; 
v___x_284_ = lean_st_ref_get(v_a_272_);
v_env_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc_ref(v_env_285_);
lean_dec(v___x_284_);
v___x_286_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_285_, v_declName_278_);
if (lean_obj_tag(v___x_286_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_298_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_298_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_val_287_);
v___x_292_ = v___x_282_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_val_287_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_us_279_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_args_280_);
v___x_292_ = v_reuseFailAlloc_297_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_296_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v___x_286_);
lean_del_object(v___x_282_);
lean_dec_ref(v_args_280_);
lean_dec(v_us_279_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_e_270_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(lean_object* v_e_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* v_e_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_309_, v_a_310_, v_a_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* v_e_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(v_e_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_329_, v_a_331_, v_a_333_, v_a_335_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
if (lean_obj_tag(v_a_338_) == 0)
{
lean_object* v___x_339_; 
lean_dec_ref(v___x_337_);
v___x_339_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_329_, v_a_333_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
if (lean_obj_tag(v_a_340_) == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v___x_339_);
lean_inc(v_e_329_);
v___x_341_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_329_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
if (lean_obj_tag(v_a_342_) == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v___x_341_);
v___x_343_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_329_, v_a_330_, v_a_335_);
return v___x_343_;
}
else
{
lean_dec_ref(v_a_342_);
lean_dec(v_e_329_);
return v___x_341_;
}
}
else
{
lean_dec(v_e_329_);
return v___x_341_;
}
}
else
{
lean_dec_ref(v_a_340_);
lean_dec(v_e_329_);
return v___x_339_;
}
}
else
{
lean_dec(v_e_329_);
return v___x_339_;
}
}
else
{
lean_dec_ref(v_a_338_);
lean_dec(v_e_329_);
return v___x_337_;
}
}
else
{
lean_dec(v_e_329_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(lean_object* v_e_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_a_345_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* v_e_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_353_, v_a_354_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* v_e_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(v_e_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_372_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
