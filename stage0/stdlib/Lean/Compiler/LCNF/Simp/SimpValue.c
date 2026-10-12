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
lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_1_, v_a_2_, v_a_3_, v_a_4_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg___boxed(lean_object* v_e_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_e_51_);
return v_res_56_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* v_e_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_57_, v_a_60_, v_a_62_, v_a_64_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpProj_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_a_59_ = stack[2].m_obj;
lean_object* v_a_60_ = stack[3].m_obj;
lean_object* v_a_61_ = stack[4].m_obj;
lean_object* v_a_62_ = stack[5].m_obj;
lean_object* v_a_63_ = stack[6].m_obj;
lean_object* v_a_64_ = stack[7].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(v_e_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object* v_e_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(v_e_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_e_68_);
return v_res_77_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(lean_object* v_e_80_, lean_object* v_a_81_){
_start:
{
if (lean_obj_tag(v_e_80_) == 4)
{
lean_object* v_fvarId_83_; lean_object* v_args_84_; uint8_t v___x_85_; lean_object* v___x_86_; 
v_fvarId_83_ = lean_ctor_get(v_e_80_, 0);
v_args_84_ = lean_ctor_get(v_e_80_, 1);
v___x_85_ = 0;
v___x_86_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_85_, v_fvarId_83_, v_a_81_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_156_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_156_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_156_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_156_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
if (lean_obj_tag(v_a_87_) == 1)
{
lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_151_; 
v_val_91_ = lean_ctor_get(v_a_87_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_a_87_);
if (v_isSharedCheck_151_ == 0)
{
v___x_93_ = v_a_87_;
v_isShared_94_ = v_isSharedCheck_151_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_dec(v_a_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_151_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_value_95_; 
v_value_95_ = lean_ctor_get(v_val_91_, 3);
lean_inc(v_value_95_);
lean_dec(v_val_91_);
switch(lean_obj_tag(v_value_95_))
{
case 1:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_del_object(v___x_93_);
v___x_96_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0));
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_96_);
v___x_98_ = v___x_89_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
case 3:
{
lean_object* v_declName_100_; lean_object* v_us_101_; lean_object* v_args_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_123_; 
v_declName_100_ = lean_ctor_get(v_value_95_, 0);
v_us_101_ = lean_ctor_get(v_value_95_, 1);
v_args_102_ = lean_ctor_get(v_value_95_, 2);
v_isSharedCheck_123_ = !lean_is_exclusive(v_value_95_);
if (v_isSharedCheck_123_ == 0)
{
v___x_104_ = v_value_95_;
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_args_102_);
lean_inc(v_us_101_);
lean_inc(v_declName_100_);
lean_dec(v_value_95_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_array_get_size(v_args_84_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_dec_eq(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = l_Array_append___redArg(v_args_102_, v_args_84_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 2, v___x_109_);
v___x_111_ = v___x_104_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_declName_100_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_us_101_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v___x_109_);
v___x_111_ = v_reuseFailAlloc_118_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_111_);
v___x_113_ = v___x_93_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_117_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_113_);
v___x_115_ = v___x_89_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_del_object(v___x_104_);
lean_dec_ref(v_args_102_);
lean_dec(v_us_101_);
lean_dec(v_declName_100_);
lean_del_object(v___x_93_);
v___x_119_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_119_);
v___x_121_ = v___x_89_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
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
case 4:
{
lean_object* v_fvarId_124_; lean_object* v_args_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_146_; 
v_fvarId_124_ = lean_ctor_get(v_value_95_, 0);
v_args_125_ = lean_ctor_get(v_value_95_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_value_95_);
if (v_isSharedCheck_146_ == 0)
{
v___x_127_ = v_value_95_;
v_isShared_128_ = v_isSharedCheck_146_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_args_125_);
lean_inc(v_fvarId_124_);
lean_dec(v_value_95_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_146_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = lean_array_get_size(v_args_84_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_dec_eq(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = l_Array_append___redArg(v_args_125_, v_args_84_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_132_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_fvarId_124_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_141_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_134_);
v___x_136_ = v___x_93_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_136_);
v___x_138_ = v___x_89_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_del_object(v___x_127_);
lean_dec_ref(v_args_125_);
lean_dec(v_fvarId_124_);
lean_del_object(v___x_93_);
v___x_142_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_142_);
v___x_144_ = v___x_89_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
default: 
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_value_95_);
lean_del_object(v___x_93_);
v___x_147_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_147_);
v___x_149_ = v___x_89_;
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
lean_dec(v_a_87_);
v___x_152_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_152_);
v___x_154_ = v___x_89_;
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
v_a_157_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_86_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_86_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_80_ = stack[0].m_obj;
lean_object* v_a_81_ = stack[1].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_80_, v_a_81_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___boxed(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec(v_e_168_);
return v_res_171_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* v_e_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_172_, v_a_177_);
return v___x_181_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_172_ = stack[0].m_obj;
lean_object* v_a_173_ = stack[1].m_obj;
lean_object* v_a_174_ = stack[2].m_obj;
lean_object* v_a_175_ = stack[3].m_obj;
lean_object* v_a_176_ = stack[4].m_obj;
lean_object* v_a_177_ = stack[5].m_obj;
lean_object* v_a_178_ = stack[6].m_obj;
lean_object* v_a_179_ = stack[7].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(v_e_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* v_e_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_e_183_);
return v_res_192_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(lean_object* v_e_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
if (lean_obj_tag(v_e_195_) == 3)
{
lean_object* v_declName_205_; lean_object* v___x_206_; lean_object* v_env_207_; uint8_t v___x_208_; lean_object* v___x_209_; 
v_declName_205_ = lean_ctor_get(v_e_195_, 0);
v___x_206_ = lean_st_ref_get(v_a_200_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_env_207_);
lean_dec(v___x_206_);
v___x_208_ = 0;
lean_inc(v_declName_205_);
v___x_209_ = l_Lean_Environment_find_x3f(v_env_207_, v_declName_205_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 1)
{
lean_object* v_val_210_; 
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_209_, 1);
if (lean_obj_tag(v_val_210_) == 6)
{
uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref_known(v_val_210_, 1);
v___x_211_ = 0;
v___x_212_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_211_, v_e_195_);
v___x_213_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(v___x_212_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_235_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_235_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_235_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_235_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
if (lean_obj_tag(v_a_214_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_230_; 
v_val_218_ = lean_ctor_get(v_a_214_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_230_ == 0)
{
v___x_220_ = v_a_214_;
v_isShared_221_ = v_isSharedCheck_230_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v_a_214_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_230_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0));
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v_val_218_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_225_);
v___x_227_ = v___x_216_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_a_214_);
v___x_231_ = lean_box(0);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_231_);
v___x_233_ = v___x_216_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_a_236_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_213_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_213_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_dec(v_val_210_);
lean_dec_ref_known(v_e_195_, 3);
goto v___jp_202_;
}
}
else
{
lean_dec(v___x_209_);
lean_dec_ref_known(v_e_195_, 3);
goto v___jp_202_;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_e_195_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
v___jp_202_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_195_ = stack[0].m_obj;
lean_object* v_a_196_ = stack[1].m_obj;
lean_object* v_a_197_ = stack[2].m_obj;
lean_object* v_a_198_ = stack[3].m_obj;
lean_object* v_a_199_ = stack[4].m_obj;
lean_object* v_a_200_ = stack[5].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
stack->m_obj
 = v_res_246_;
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
lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object* v_e_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_255_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_264_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_255_ = stack[0].m_obj;
lean_object* v_a_256_ = stack[1].m_obj;
lean_object* v_a_257_ = stack[2].m_obj;
lean_object* v_a_258_ = stack[3].m_obj;
lean_object* v_a_259_ = stack[4].m_obj;
lean_object* v_a_260_ = stack[5].m_obj;
lean_object* v_a_261_ = stack[6].m_obj;
lean_object* v_a_262_ = stack[7].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(v_e_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_275_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_config_280_; uint8_t v_implementedBy_281_; 
v_config_280_ = lean_ctor_get(v_a_277_, 1);
v_implementedBy_281_ = lean_ctor_get_uint8(v_config_280_, 2);
if (v_implementedBy_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_e_276_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
else
{
if (lean_obj_tag(v_e_276_) == 3)
{
lean_object* v_declName_284_; lean_object* v_us_285_; lean_object* v_args_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_307_; 
v_declName_284_ = lean_ctor_get(v_e_276_, 0);
v_us_285_ = lean_ctor_get(v_e_276_, 1);
v_args_286_ = lean_ctor_get(v_e_276_, 2);
v_isSharedCheck_307_ = !lean_is_exclusive(v_e_276_);
if (v_isSharedCheck_307_ == 0)
{
v___x_288_ = v_e_276_;
v_isShared_289_ = v_isSharedCheck_307_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_args_286_);
lean_inc(v_us_285_);
lean_inc(v_declName_284_);
lean_dec(v_e_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_307_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v_env_291_; lean_object* v___x_292_; 
v___x_290_ = lean_st_ref_get(v_a_278_);
v_env_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_env_291_);
lean_dec(v___x_290_);
v___x_292_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_291_, v_declName_284_);
if (lean_obj_tag(v___x_292_) == 1)
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_304_; 
v_val_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_304_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_val_293_);
v___x_298_ = v___x_288_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_val_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_us_285_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_args_286_);
v___x_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_298_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___x_292_);
lean_del_object(v___x_288_);
lean_dec_ref(v_args_286_);
lean_dec(v_us_285_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_e_276_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_276_ = stack[0].m_obj;
lean_object* v_a_277_ = stack[1].m_obj;
lean_object* v_a_278_ = stack[2].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_276_, v_a_277_, v_a_278_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_315_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_316_, v_a_317_, v_a_323_);
return v___x_325_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_316_ = stack[0].m_obj;
lean_object* v_a_317_ = stack[1].m_obj;
lean_object* v_a_318_ = stack[2].m_obj;
lean_object* v_a_319_ = stack[3].m_obj;
lean_object* v_a_320_ = stack[4].m_obj;
lean_object* v_a_321_ = stack[5].m_obj;
lean_object* v_a_322_ = stack[6].m_obj;
lean_object* v_a_323_ = stack[7].m_obj;
lean_object* v_res_326_;
v_res_326_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(v_e_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_336_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object* v_e_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_337_, v_a_339_, v_a_341_, v_a_343_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
if (lean_obj_tag(v_a_346_) == 0)
{
lean_object* v___x_347_; 
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_337_, v_a_341_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
if (lean_obj_tag(v_a_348_) == 0)
{
lean_object* v___x_349_; 
lean_dec_ref_known(v___x_347_, 1);
lean_inc(v_e_337_);
v___x_349_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(v_e_337_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
if (lean_obj_tag(v_a_350_) == 0)
{
lean_object* v___x_351_; 
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_337_, v_a_338_, v_a_343_);
return v___x_351_;
}
else
{
lean_dec(v_e_337_);
return v___x_349_;
}
}
else
{
lean_dec(v_e_337_);
return v___x_349_;
}
}
else
{
lean_dec(v_e_337_);
return v___x_347_;
}
}
else
{
lean_dec(v_e_337_);
return v___x_347_;
}
}
else
{
lean_dec(v_e_337_);
return v___x_345_;
}
}
else
{
lean_dec(v_e_337_);
return v___x_345_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_337_ = stack[0].m_obj;
lean_object* v_a_338_ = stack[1].m_obj;
lean_object* v_a_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_a_341_ = stack[4].m_obj;
lean_object* v_a_342_ = stack[5].m_obj;
lean_object* v_a_343_ = stack[6].m_obj;
lean_object* v_res_352_;
v_res_352_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(lean_object* v_e_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_a_354_);
return v_res_361_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_e_362_, v_a_363_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
return v___x_371_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpValue_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_362_ = stack[0].m_obj;
lean_object* v_a_363_ = stack[1].m_obj;
lean_object* v_a_364_ = stack[2].m_obj;
lean_object* v_a_365_ = stack[3].m_obj;
lean_object* v_a_366_ = stack[4].m_obj;
lean_object* v_a_367_ = stack[5].m_obj;
lean_object* v_a_368_ = stack[6].m_obj;
lean_object* v_a_369_ = stack[7].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_382_;
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
