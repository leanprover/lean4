// Lean compiler output
// Module: Lean.Compiler.IR.Sorry
// Imports: public import Lean.Compiler.IR.CompilerM
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_IR_Alt_body(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_IR_updateSorryDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_IR_updateSorryDep___closed__0 = (const lean_object*)&l_Lean_IR_updateSorryDep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg(lean_object* v_f_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_g_11_; lean_object* v___y_12_; lean_object* v___y_22_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__1));
v___x_27_ = lean_name_eq(v_f_6_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v_localSorryMap_28_; lean_object* v___x_29_; 
v_localSorryMap_28_ = lean_ctor_get(v_a_7_, 0);
v___x_29_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_28_, v_f_6_);
if (lean_obj_tag(v___x_29_) == 1)
{
lean_object* v_val_30_; 
v_val_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_val_30_);
lean_dec_ref_known(v___x_29_, 1);
v_g_11_ = v_val_30_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_object* v___x_31_; 
lean_dec(v___x_29_);
lean_inc(v_f_6_);
v___x_31_ = l_Lean_IR_findDecl___redArg(v_f_6_, v_a_8_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_31_, 1);
if (lean_obj_tag(v_a_32_) == 1)
{
lean_object* v_val_33_; 
v_val_33_ = lean_ctor_get(v_a_32_, 0);
lean_inc(v_val_33_);
lean_dec_ref_known(v_a_32_, 1);
if (lean_obj_tag(v_val_33_) == 0)
{
lean_object* v_info_34_; lean_object* v_sorryDep_x3f_35_; 
v_info_34_ = lean_ctor_get(v_val_33_, 4);
lean_inc_ref(v_info_34_);
lean_dec_ref_known(v_val_33_, 5);
v_sorryDep_x3f_35_ = lean_ctor_get(v_info_34_, 0);
lean_inc(v_sorryDep_x3f_35_);
lean_dec_ref(v_info_34_);
if (lean_obj_tag(v_sorryDep_x3f_35_) == 1)
{
lean_object* v_val_36_; 
v_val_36_ = lean_ctor_get(v_sorryDep_x3f_35_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v_sorryDep_x3f_35_, 1);
v_g_11_ = v_val_36_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_dec(v_sorryDep_x3f_35_);
lean_dec(v_f_6_);
v___y_22_ = v_a_7_;
goto v___jp_21_;
}
}
else
{
lean_dec(v_val_33_);
lean_dec(v_f_6_);
v___y_22_ = v_a_7_;
goto v___jp_21_;
}
}
else
{
lean_dec(v_a_32_);
lean_dec(v_f_6_);
v___y_22_ = v_a_7_;
goto v___jp_21_;
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
lean_dec_ref(v_a_7_);
lean_dec(v_f_6_);
v_a_37_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_31_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_31_);
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
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v_f_6_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v_a_7_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
v___jp_10_:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__1));
v___x_14_ = lean_name_eq(v_g_11_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_f_6_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v_g_11_);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___y_12_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_g_11_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v_f_6_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___y_12_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
v___jp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2));
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___y_22_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___boxed(lean_object* v_f_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg(v_f_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f(lean_object* v_f_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg(v_f_53_, v_a_54_, v_a_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___boxed(lean_object* v_f_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f(v_f_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody(lean_object* v_b_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
switch(lean_obj_tag(v_b_65_))
{
case 6:
{
lean_object* v_b_70_; lean_object* v_c_71_; lean_object* v___x_72_; 
v_b_70_ = lean_ctor_get(v_b_65_, 1);
lean_inc(v_b_70_);
v_c_71_ = lean_ctor_get(v_b_65_, 3);
lean_inc(v_c_71_);
lean_dec_ref_known(v_b_65_, 5);
v___x_72_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg(v_c_71_, v_a_66_, v_a_68_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_fst_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_fst_74_ = lean_ctor_get(v_a_73_, 0);
if (lean_obj_tag(v_fst_74_) == 0)
{
lean_dec(v_b_70_);
return v___x_72_;
}
else
{
lean_object* v_snd_75_; 
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v_snd_75_ = lean_ctor_get(v_a_73_, 1);
lean_inc(v_snd_75_);
lean_dec(v_a_73_);
v_b_65_ = v_b_70_;
v_a_66_ = v_snd_75_;
goto _start;
}
}
else
{
lean_dec(v_b_70_);
return v___x_72_;
}
}
case 7:
{
lean_object* v_b_77_; lean_object* v_c_78_; lean_object* v___x_79_; 
v_b_77_ = lean_ctor_get(v_b_65_, 1);
lean_inc(v_b_77_);
v_c_78_ = lean_ctor_get(v_b_65_, 2);
lean_inc(v_c_78_);
lean_dec_ref_known(v_b_65_, 4);
v___x_79_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg(v_c_78_, v_a_66_, v_a_68_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v_fst_81_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_fst_81_ = lean_ctor_get(v_a_80_, 0);
if (lean_obj_tag(v_fst_81_) == 0)
{
lean_dec(v_b_77_);
return v___x_79_;
}
else
{
lean_object* v_snd_82_; 
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_79_, 1);
v_snd_82_ = lean_ctor_get(v_a_80_, 1);
lean_inc(v_snd_82_);
lean_dec(v_a_80_);
v_b_65_ = v_b_77_;
v_a_66_ = v_snd_82_;
goto _start;
}
}
else
{
lean_dec(v_b_77_);
return v___x_79_;
}
}
case 19:
{
lean_object* v_v_84_; lean_object* v_b_85_; lean_object* v___x_86_; 
v_v_84_ = lean_ctor_get(v_b_65_, 2);
lean_inc(v_v_84_);
v_b_85_ = lean_ctor_get(v_b_65_, 3);
lean_inc(v_b_85_);
lean_dec_ref_known(v_b_65_, 4);
v___x_86_ = l_Lean_IR_Sorry_visitFnBody(v_v_84_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v_fst_88_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_fst_88_ = lean_ctor_get(v_a_87_, 0);
if (lean_obj_tag(v_fst_88_) == 0)
{
lean_dec(v_b_85_);
return v___x_86_;
}
else
{
lean_object* v_snd_89_; 
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
v_snd_89_ = lean_ctor_get(v_a_87_, 1);
lean_inc(v_snd_89_);
lean_dec(v_a_87_);
v_b_65_ = v_b_85_;
v_a_66_ = v_snd_89_;
goto _start;
}
}
else
{
lean_dec(v_b_85_);
return v___x_86_;
}
}
case 27:
{
lean_object* v_cs_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_cs_91_ = lean_ctor_get(v_b_65_, 3);
lean_inc_ref(v_cs_91_);
lean_dec_ref_known(v_b_65_, 4);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_array_get_size(v_cs_91_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_nat_dec_lt(v___x_92_, v___x_93_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec_ref(v_cs_91_);
v___x_96_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2));
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_66_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = lean_nat_dec_le(v___x_93_, v___x_93_);
if (v___x_99_ == 0)
{
if (v___x_95_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec_ref(v_cs_91_);
v___x_100_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2));
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_66_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
else
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((size_t)0ULL);
v___x_104_ = lean_usize_of_nat(v___x_93_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_91_, v___x_103_, v___x_104_, v___x_94_, v_a_66_, v_a_67_, v_a_68_);
lean_dec_ref(v_cs_91_);
return v___x_105_;
}
}
else
{
size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((size_t)0ULL);
v___x_107_ = lean_usize_of_nat(v___x_93_);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_91_, v___x_106_, v___x_107_, v___x_94_, v_a_66_, v_a_67_, v_a_68_);
lean_dec_ref(v_cs_91_);
return v___x_108_;
}
}
}
default: 
{
uint8_t v___x_109_; 
v___x_109_ = l_Lean_IR_FnBody_isTerminal(v_b_65_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_IR_FnBody_body(v_b_65_);
lean_dec(v_b_65_);
v_b_65_ = v___x_110_;
goto _start;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_b_65_);
v___x_112_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2));
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_66_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object* v_as_115_, size_t v_i_116_, size_t v_stop_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = lean_usize_dec_eq(v_i_116_, v_stop_117_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_array_uget_borrowed(v_as_115_, v_i_116_);
v___x_125_ = l_Lean_IR_Alt_body(v___x_124_);
v___x_126_ = l_Lean_IR_Sorry_visitFnBody(v___x_125_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v_fst_128_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_fst_128_ = lean_ctor_get(v_a_127_, 0);
if (lean_obj_tag(v_fst_128_) == 0)
{
return v___x_126_;
}
else
{
lean_object* v_snd_129_; lean_object* v_a_130_; size_t v___x_131_; size_t v___x_132_; 
lean_inc_ref(v_fst_128_);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_126_, 1);
v_snd_129_ = lean_ctor_get(v_a_127_, 1);
lean_inc(v_snd_129_);
lean_dec(v_a_127_);
v_a_130_ = lean_ctor_get(v_fst_128_, 0);
lean_inc(v_a_130_);
lean_dec_ref_known(v_fst_128_, 1);
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_116_, v___x_131_);
v_i_116_ = v___x_132_;
v_b_118_ = v_a_130_;
v___y_119_ = v_snd_129_;
goto _start;
}
}
else
{
return v___x_126_;
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_b_118_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___y_119_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object* v_as_137_, lean_object* v_i_138_, lean_object* v_stop_139_, lean_object* v_b_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
size_t v_i_boxed_145_; size_t v_stop_boxed_146_; lean_object* v_res_147_; 
v_i_boxed_145_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_139_);
lean_dec(v_stop_139_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_137_, v_i_boxed_145_, v_stop_boxed_146_, v_b_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_as_137_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object* v_b_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_IR_Sorry_visitFnBody(v_b_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* v_d_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
if (lean_obj_tag(v_d_154_) == 0)
{
lean_object* v_f_159_; lean_object* v_body_160_; lean_object* v_localSorryMap_161_; lean_object* v___x_162_; 
v_f_159_ = lean_ctor_get(v_d_154_, 0);
lean_inc(v_f_159_);
v_body_160_ = lean_ctor_get(v_d_154_, 3);
lean_inc(v_body_160_);
lean_dec_ref_known(v_d_154_, 5);
v_localSorryMap_161_ = lean_ctor_get(v_a_155_, 0);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_161_, v_f_159_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_IR_Sorry_visitFnBody(v_body_160_, v_a_155_, v_a_156_, v_a_157_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_206_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_206_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_206_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_206_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_fst_168_; 
v_fst_168_ = lean_ctor_get(v_a_164_, 0);
if (lean_obj_tag(v_fst_168_) == 0)
{
lean_object* v_snd_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_191_; 
lean_inc_ref(v_fst_168_);
v_snd_169_ = lean_ctor_get(v_a_164_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_a_164_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_a_164_, 0);
lean_dec(v_unused_192_);
v___x_171_ = v_a_164_;
v_isShared_172_ = v_isSharedCheck_191_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_snd_169_);
lean_dec(v_a_164_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_191_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_a_173_; lean_object* v_localSorryMap_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_190_; 
v_a_173_ = lean_ctor_get(v_fst_168_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v_fst_168_, 1);
v_localSorryMap_174_ = lean_ctor_get(v_snd_169_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_snd_169_);
if (v_isSharedCheck_190_ == 0)
{
v___x_176_ = v_snd_169_;
v_isShared_177_ = v_isSharedCheck_190_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_localSorryMap_174_);
lean_dec(v_snd_169_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_190_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_182_; 
v___x_178_ = lean_box(0);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_159_, v_a_173_, v_localSorryMap_174_);
v___x_180_ = 1;
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_179_);
v___x_182_ = v___x_176_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_179_);
v___x_182_ = v_reuseFailAlloc_189_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_180_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_182_);
lean_ctor_set(v___x_171_, 0, v___x_178_);
v___x_184_ = v___x_171_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_182_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_184_);
v___x_186_ = v___x_166_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
else
{
lean_object* v_snd_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_f_159_);
v_snd_193_ = lean_ctor_get(v_a_164_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_a_164_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_a_164_, 0);
lean_dec(v_unused_205_);
v___x_195_ = v_a_164_;
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_snd_193_);
lean_dec(v_a_164_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_box(0);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_snd_193_);
v___x_199_ = v_reuseFailAlloc_203_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_199_);
v___x_201_ = v___x_166_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_f_159_);
v_a_207_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_163_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_163_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_body_160_);
lean_dec(v_f_159_);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v___x_162_, 0);
lean_dec(v_unused_224_);
v___x_216_ = v___x_162_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_dec(v___x_162_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = lean_box(0);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_155_);
if (v_isShared_217_ == 0)
{
lean_ctor_set_tag(v___x_216_, 0);
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_221_ = v___x_216_;
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
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref(v_d_154_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_a_155_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* v_d_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_IR_Sorry_visitDecl(v_d_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object* v_as_234_, size_t v_i_235_, size_t v_stop_236_, lean_object* v_b_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = lean_usize_dec_eq(v_i_235_, v_stop_236_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_array_uget_borrowed(v_as_234_, v_i_235_);
lean_inc(v___x_243_);
v___x_244_ = l_Lean_IR_Sorry_visitDecl(v___x_243_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_fst_246_; lean_object* v_snd_247_; size_t v___x_248_; size_t v___x_249_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v_fst_246_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_fst_246_);
v_snd_247_ = lean_ctor_get(v_a_245_, 1);
lean_inc(v_snd_247_);
lean_dec(v_a_245_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_add(v_i_235_, v___x_248_);
v_i_235_ = v___x_249_;
v_b_237_ = v_fst_246_;
v___y_238_ = v_snd_247_;
goto _start;
}
else
{
return v___x_244_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_b_237_);
lean_ctor_set(v___x_251_, 1, v___y_238_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object* v_as_253_, lean_object* v_i_254_, lean_object* v_stop_255_, lean_object* v_b_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
size_t v_i_boxed_261_; size_t v_stop_boxed_262_; lean_object* v_res_263_; 
v_i_boxed_261_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_stop_boxed_262_ = lean_unbox_usize(v_stop_255_);
lean_dec(v_stop_255_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_253_, v_i_boxed_261_, v_stop_boxed_262_, v_b_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec_ref(v_as_253_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* v_decls_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_snd_270_; lean_object* v___y_275_; lean_object* v_localSorryMap_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_299_; 
v_localSorryMap_280_ = lean_ctor_get(v_a_265_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_299_ == 0)
{
v___x_282_ = v_a_265_;
v_isShared_283_ = v_isSharedCheck_299_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_localSorryMap_280_);
lean_dec(v_a_265_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_299_;
goto v_resetjp_281_;
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_snd_270_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
v___jp_274_:
{
if (lean_obj_tag(v___y_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_snd_277_; uint8_t v_modified_278_; 
v_a_276_ = lean_ctor_get(v___y_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___y_275_, 1);
v_snd_277_ = lean_ctor_get(v_a_276_, 1);
lean_inc(v_snd_277_);
lean_dec(v_a_276_);
v_modified_278_ = lean_ctor_get_uint8(v_snd_277_, sizeof(void*)*1);
if (v_modified_278_ == 0)
{
v_snd_270_ = v_snd_277_;
goto v___jp_269_;
}
else
{
v_a_265_ = v_snd_277_;
goto _start;
}
}
else
{
return v___y_275_;
}
}
v_resetjp_281_:
{
uint8_t v___x_284_; lean_object* v___x_286_; 
v___x_284_ = 0;
if (v_isShared_283_ == 0)
{
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_localSorryMap_280_);
v___x_286_ = v_reuseFailAlloc_298_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_284_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_array_get_size(v_decls_264_);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
v_snd_270_ = v___x_286_;
goto v___jp_269_;
}
else
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_box(0);
v___x_291_ = lean_nat_dec_le(v___x_288_, v___x_288_);
if (v___x_291_ == 0)
{
if (v___x_289_ == 0)
{
v_snd_270_ = v___x_286_;
goto v___jp_269_;
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_288_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_264_, v___x_292_, v___x_293_, v___x_290_, v___x_286_, v_a_266_, v_a_267_);
v___y_275_ = v___x_294_;
goto v___jp_274_;
}
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_288_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_264_, v___x_295_, v___x_296_, v___x_290_, v___x_286_, v_a_266_, v_a_267_);
v___y_275_ = v___x_297_;
goto v___jp_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* v_decls_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_IR_Sorry_collect(v_decls_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_decls_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object* v_snd_306_, size_t v_sz_307_, size_t v_i_308_, lean_object* v_bs_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_310_ == 0)
{
return v_bs_309_;
}
else
{
lean_object* v_v_311_; lean_object* v___x_312_; lean_object* v_bs_x27_313_; lean_object* v___y_315_; 
v_v_311_ = lean_array_uget(v_bs_309_, v_i_308_);
v___x_312_ = lean_unsigned_to_nat(0u);
v_bs_x27_313_ = lean_array_uset(v_bs_309_, v_i_308_, v___x_312_);
if (lean_obj_tag(v_v_311_) == 0)
{
lean_object* v_f_320_; lean_object* v_xs_321_; lean_object* v_type_322_; lean_object* v_body_323_; lean_object* v_info_324_; lean_object* v_localSorryMap_325_; lean_object* v___x_326_; 
v_f_320_ = lean_ctor_get(v_v_311_, 0);
v_xs_321_ = lean_ctor_get(v_v_311_, 1);
v_type_322_ = lean_ctor_get(v_v_311_, 2);
v_body_323_ = lean_ctor_get(v_v_311_, 3);
v_info_324_ = lean_ctor_get(v_v_311_, 4);
lean_inc_ref(v_info_324_);
v_localSorryMap_325_ = lean_ctor_get(v_snd_306_, 0);
v___x_326_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_325_, v_f_320_);
if (lean_obj_tag(v___x_326_) == 1)
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_343_; 
lean_inc(v_body_323_);
lean_inc(v_type_322_);
lean_inc_ref(v_xs_321_);
lean_inc(v_f_320_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_v_311_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_344_ = lean_ctor_get(v_v_311_, 4);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_v_311_, 3);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_v_311_, 2);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_v_311_, 1);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_v_311_, 0);
lean_dec(v_unused_348_);
v___x_328_ = v_v_311_;
v_isShared_329_ = v_isSharedCheck_343_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_v_311_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_343_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_maxJp_330_; lean_object* v_maxVar_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_341_; 
v_maxJp_330_ = lean_ctor_get(v_info_324_, 1);
v_maxVar_331_ = lean_ctor_get(v_info_324_, 2);
v_isSharedCheck_341_ = !lean_is_exclusive(v_info_324_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v_info_324_, 0);
lean_dec(v_unused_342_);
v___x_333_ = v_info_324_;
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_maxVar_331_);
lean_inc(v_maxJp_330_);
lean_dec(v_info_324_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_326_);
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_maxJp_330_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_maxVar_331_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 4, v___x_336_);
v___x_338_ = v___x_328_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_f_320_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_xs_321_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_type_322_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_body_323_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
v___y_315_ = v___x_338_;
goto v___jp_314_;
}
}
}
}
}
else
{
lean_dec(v___x_326_);
lean_dec_ref(v_info_324_);
v___y_315_ = v_v_311_;
goto v___jp_314_;
}
}
else
{
v___y_315_ = v_v_311_;
goto v___jp_314_;
}
v___jp_314_:
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_308_, v___x_316_);
v___x_318_ = lean_array_uset(v_bs_x27_313_, v_i_308_, v___y_315_);
v_i_308_ = v___x_317_;
v_bs_309_ = v___x_318_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object* v_snd_349_, lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_bs_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_354_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_349_, v_sz_boxed_353_, v_i_boxed_354_, v_bs_352_);
lean_dec_ref(v_snd_349_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* v_decls_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_IR_updateSorryDep___closed__0));
v___x_364_ = l_Lean_IR_Sorry_collect(v_decls_359_, v___x_363_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_376_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_376_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_376_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_376_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_snd_369_; size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v_snd_369_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_snd_369_);
lean_dec(v_a_365_);
v_sz_370_ = lean_array_size(v_decls_359_);
v___x_371_ = ((size_t)0ULL);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_369_, v_sz_370_, v___x_371_, v_decls_359_);
lean_dec(v_snd_369_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_372_);
v___x_374_ = v___x_367_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_decls_359_);
v_a_377_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_364_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_364_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* v_decls_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_IR_updateSorryDep(v_decls_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_389_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Sorry(builtin);
}
#ifdef __cplusplus
}
#endif
