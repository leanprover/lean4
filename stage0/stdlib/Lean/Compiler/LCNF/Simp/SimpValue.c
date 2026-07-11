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
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v_val_13_, 2);
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
lean_dec_ref_known(v_val_13_, 1);
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
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_156_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_156_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_156_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_156_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
if (lean_obj_tag(v_a_85_) == 1)
{
lean_object* v_val_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_151_; 
v_val_89_ = lean_ctor_get(v_a_85_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_151_ == 0)
{
v___x_91_ = v_a_85_;
v_isShared_92_ = v_isSharedCheck_151_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_val_89_);
lean_dec(v_a_85_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_151_;
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
lean_object* v_declName_98_; lean_object* v_us_99_; lean_object* v_args_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_122_; 
v_declName_98_ = lean_ctor_get(v_value_93_, 0);
v_us_99_ = lean_ctor_get(v_value_93_, 1);
v_args_100_ = lean_ctor_get(v_value_93_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v_value_93_);
if (v_isSharedCheck_122_ == 0)
{
v___x_102_ = v_value_93_;
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_args_100_);
lean_inc(v_us_99_);
lean_inc(v_declName_98_);
lean_dec(v_value_93_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; uint8_t v___x_107_; 
v___x_104_ = lean_array_get_size(v_args_82_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
v___x_107_ = lean_bool_not(v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_110_; 
lean_del_object(v___x_102_);
lean_dec_ref(v_args_100_);
lean_dec(v_us_99_);
lean_dec(v_declName_98_);
lean_del_object(v___x_91_);
v___x_108_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_108_);
v___x_110_ = v___x_87_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = l_Array_append___redArg(v_args_100_, v_args_82_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_112_);
v___x_114_ = v___x_102_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_declName_98_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_us_99_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v___x_112_);
v___x_114_ = v_reuseFailAlloc_121_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_116_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_114_);
v___x_116_ = v___x_91_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_120_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_118_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_116_);
v___x_118_ = v___x_87_;
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
}
}
}
}
case 4:
{
lean_object* v_fvarId_123_; lean_object* v_args_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_146_; 
v_fvarId_123_ = lean_ctor_get(v_value_93_, 0);
v_args_124_ = lean_ctor_get(v_value_93_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_value_93_);
if (v_isSharedCheck_146_ == 0)
{
v___x_126_ = v_value_93_;
v_isShared_127_ = v_isSharedCheck_146_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_args_124_);
lean_inc(v_fvarId_123_);
lean_dec(v_value_93_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_146_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_array_get_size(v_args_82_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_nat_dec_eq(v___x_128_, v___x_129_);
v___x_131_ = lean_bool_not(v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_del_object(v___x_126_);
lean_dec_ref(v_args_124_);
lean_dec(v_fvarId_123_);
lean_del_object(v___x_91_);
v___x_132_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_132_);
v___x_134_ = v___x_87_;
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
else
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = l_Array_append___redArg(v_args_124_, v_args_82_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_136_);
v___x_138_ = v___x_126_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_fvarId_123_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_145_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_138_);
v___x_140_ = v___x_91_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
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
}
}
default: 
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_value_93_);
lean_del_object(v___x_91_);
v___x_147_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_147_);
v___x_149_ = v___x_87_;
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
}
}
}
else
{
lean_object* v___x_152_; lean_object* v___x_154_; 
lean_dec(v_a_85_);
v___x_152_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_152_);
v___x_154_ = v___x_87_;
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
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_84_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_84_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___boxed(lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec(v_e_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* v_e_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_171_, v_a_176_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(v_e_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_e_181_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(lean_object* v_e_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
if (lean_obj_tag(v_e_193_) == 3)
{
lean_object* v_declName_203_; lean_object* v___x_204_; lean_object* v_env_205_; uint8_t v___x_206_; lean_object* v___x_207_; 
v_declName_203_ = lean_ctor_get(v_e_193_, 0);
v___x_204_ = lean_st_ref_get(v_a_198_);
v_env_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_ref(v_env_205_);
lean_dec(v___x_204_);
v___x_206_ = 0;
lean_inc(v_declName_203_);
v___x_207_ = l_Lean_Environment_find_x3f(v_env_205_, v_declName_203_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 1)
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_207_, 1);
if (lean_obj_tag(v_val_208_) == 6)
{
uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec_ref_known(v_val_208_, 1);
v___x_209_ = 0;
v___x_210_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_209_, v_e_193_);
v___x_211_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(v___x_210_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_233_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_233_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_228_; 
v_val_216_ = lean_ctor_get(v_a_212_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_228_ == 0)
{
v___x_218_ = v_a_212_;
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_val_216_);
lean_dec(v_a_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_220_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0));
v___x_221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_221_, 0, v_val_216_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_227_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_223_);
v___x_225_ = v___x_214_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v_a_212_);
v___x_229_ = lean_box(0);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_229_);
v___x_231_ = v___x_214_;
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
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_211_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_211_);
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
lean_dec(v_val_208_);
lean_dec_ref_known(v_e_193_, 3);
goto v___jp_200_;
}
}
else
{
lean_dec(v___x_207_);
lean_dec_ref_known(v_e_193_, 3);
goto v___jp_200_;
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_e_193_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
v___jp_200_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___boxed(lean_object* v_e_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object* v_e_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_252_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(v_e_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(lean_object* v_e_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_config_276_; uint8_t v_implementedBy_277_; 
v_config_276_ = lean_ctor_get(v_a_273_, 1);
v_implementedBy_277_ = lean_ctor_get_uint8(v_config_276_, 2);
if (v_implementedBy_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_e_272_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
else
{
if (lean_obj_tag(v_e_272_) == 3)
{
lean_object* v_declName_280_; lean_object* v_us_281_; lean_object* v_args_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_303_; 
v_declName_280_ = lean_ctor_get(v_e_272_, 0);
v_us_281_ = lean_ctor_get(v_e_272_, 1);
v_args_282_ = lean_ctor_get(v_e_272_, 2);
v_isSharedCheck_303_ = !lean_is_exclusive(v_e_272_);
if (v_isSharedCheck_303_ == 0)
{
v___x_284_ = v_e_272_;
v_isShared_285_ = v_isSharedCheck_303_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_args_282_);
lean_inc(v_us_281_);
lean_inc(v_declName_280_);
lean_dec(v_e_272_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_303_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v_env_287_; lean_object* v___x_288_; 
v___x_286_ = lean_st_ref_get(v_a_274_);
v_env_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_ref(v_env_287_);
lean_dec(v___x_286_);
v___x_288_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_287_, v_declName_280_);
if (lean_obj_tag(v___x_288_) == 1)
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_300_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_300_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_val_289_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_val_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_us_281_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_args_282_);
v___x_294_ = v_reuseFailAlloc_299_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_296_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v___x_288_);
lean_del_object(v___x_284_);
lean_dec_ref(v_args_282_);
lean_dec(v_us_281_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_e_272_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(lean_object* v_e_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_311_, v_a_312_, v_a_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* v_e_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(v_e_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object* v_e_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_331_, v_a_333_, v_a_335_, v_a_337_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
if (lean_obj_tag(v_a_340_) == 0)
{
lean_object* v___x_341_; 
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_331_, v_a_335_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
if (lean_obj_tag(v_a_342_) == 0)
{
lean_object* v___x_343_; 
lean_dec_ref_known(v___x_341_, 1);
lean_inc(v_e_331_);
v___x_343_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_331_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
if (lean_obj_tag(v_a_344_) == 0)
{
lean_object* v___x_345_; 
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_331_, v_a_332_, v_a_337_);
return v___x_345_;
}
else
{
lean_dec_ref_known(v_a_344_, 1);
lean_dec(v_e_331_);
return v___x_343_;
}
}
else
{
lean_dec(v_e_331_);
return v___x_343_;
}
}
else
{
lean_dec_ref_known(v_a_342_, 1);
lean_dec(v_e_331_);
return v___x_341_;
}
}
else
{
lean_dec(v_e_331_);
return v___x_341_;
}
}
else
{
lean_dec_ref_known(v_a_340_, 1);
lean_dec(v_e_331_);
return v___x_339_;
}
}
else
{
lean_dec(v_e_331_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(lean_object* v_e_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec_ref(v_a_347_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* v_e_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_355_, v_a_356_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_374_;
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
