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
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_93_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_91_, v___x_99_, v___x_100_, v___x_94_, v_a_66_, v_a_67_, v_a_68_);
lean_dec_ref(v_cs_91_);
return v___x_101_;
}
}
default: 
{
uint8_t v___x_102_; 
v___x_102_ = l_Lean_IR_FnBody_isTerminal(v_b_65_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_IR_FnBody_body(v_b_65_);
lean_dec(v_b_65_);
v_b_65_ = v___x_103_;
goto _start;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_b_65_);
v___x_105_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitFnBody_getSorryDepFor_x3f___redArg___closed__2));
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_a_66_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object* v_as_108_, size_t v_i_109_, size_t v_stop_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_usize_dec_eq(v_i_109_, v_stop_110_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_array_uget_borrowed(v_as_108_, v_i_109_);
v___x_118_ = l_Lean_IR_Alt_body(v___x_117_);
v___x_119_ = l_Lean_IR_Sorry_visitFnBody(v___x_118_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v_fst_121_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_fst_121_ = lean_ctor_get(v_a_120_, 0);
if (lean_obj_tag(v_fst_121_) == 0)
{
return v___x_119_;
}
else
{
lean_object* v_snd_122_; lean_object* v_a_123_; size_t v___x_124_; size_t v___x_125_; 
lean_inc_ref(v_fst_121_);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
v_snd_122_ = lean_ctor_get(v_a_120_, 1);
lean_inc(v_snd_122_);
lean_dec(v_a_120_);
v_a_123_ = lean_ctor_get(v_fst_121_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v_fst_121_, 1);
v___x_124_ = ((size_t)1ULL);
v___x_125_ = lean_usize_add(v_i_109_, v___x_124_);
v_i_109_ = v___x_125_;
v_b_111_ = v_a_123_;
v___y_112_ = v_snd_122_;
goto _start;
}
}
else
{
return v___x_119_;
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_b_111_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___y_112_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object* v_as_130_, lean_object* v_i_131_, lean_object* v_stop_132_, lean_object* v_b_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
size_t v_i_boxed_138_; size_t v_stop_boxed_139_; lean_object* v_res_140_; 
v_i_boxed_138_ = lean_unbox_usize(v_i_131_);
lean_dec(v_i_131_);
v_stop_boxed_139_ = lean_unbox_usize(v_stop_132_);
lean_dec(v_stop_132_);
v_res_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_130_, v_i_boxed_138_, v_stop_boxed_139_, v_b_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec_ref(v_as_130_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object* v_b_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_IR_Sorry_visitFnBody(v_b_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* v_d_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
if (lean_obj_tag(v_d_147_) == 0)
{
lean_object* v_f_152_; lean_object* v_body_153_; lean_object* v_localSorryMap_154_; lean_object* v___x_155_; 
v_f_152_ = lean_ctor_get(v_d_147_, 0);
lean_inc(v_f_152_);
v_body_153_ = lean_ctor_get(v_d_147_, 3);
lean_inc(v_body_153_);
lean_dec_ref_known(v_d_147_, 5);
v_localSorryMap_154_ = lean_ctor_get(v_a_148_, 0);
v___x_155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_154_, v_f_152_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_IR_Sorry_visitFnBody(v_body_153_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_199_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_199_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_199_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_199_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_fst_161_; 
v_fst_161_ = lean_ctor_get(v_a_157_, 0);
if (lean_obj_tag(v_fst_161_) == 0)
{
lean_object* v_snd_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_184_; 
lean_inc_ref(v_fst_161_);
v_snd_162_ = lean_ctor_get(v_a_157_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v_a_157_, 0);
lean_dec(v_unused_185_);
v___x_164_ = v_a_157_;
v_isShared_165_ = v_isSharedCheck_184_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snd_162_);
lean_dec(v_a_157_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_184_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_a_166_; lean_object* v_localSorryMap_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_183_; 
v_a_166_ = lean_ctor_get(v_fst_161_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v_fst_161_, 1);
v_localSorryMap_167_ = lean_ctor_get(v_snd_162_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_snd_162_);
if (v_isSharedCheck_183_ == 0)
{
v___x_169_ = v_snd_162_;
v_isShared_170_ = v_isSharedCheck_183_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_localSorryMap_167_);
lean_dec(v_snd_162_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_183_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_175_; 
v___x_171_ = lean_box(0);
v___x_172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_152_, v_a_166_, v_localSorryMap_167_);
v___x_173_ = 1;
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_172_);
v___x_175_ = v___x_169_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_172_);
v___x_175_ = v_reuseFailAlloc_182_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_173_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___x_175_);
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_177_ = v___x_164_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_177_);
v___x_179_ = v___x_159_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
else
{
lean_object* v_snd_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_f_152_);
v_snd_186_ = lean_ctor_get(v_a_157_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v_a_157_, 0);
lean_dec(v_unused_198_);
v___x_188_ = v_a_157_;
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_snd_186_);
lean_dec(v_a_157_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_box(0);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_snd_186_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_192_);
v___x_194_ = v___x_159_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_f_152_);
v_a_200_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_156_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_156_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
lean_dec(v_body_153_);
lean_dec(v_f_152_);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v___x_155_, 0);
lean_dec(v_unused_217_);
v___x_209_ = v___x_155_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_dec(v___x_155_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_148_);
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 0);
lean_ctor_set(v___x_209_, 0, v___x_212_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v_d_147_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_148_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* v_d_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_IR_Sorry_visitDecl(v_d_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = lean_usize_dec_eq(v_i_228_, v_stop_229_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_array_uget_borrowed(v_as_227_, v_i_228_);
lean_inc(v___x_236_);
v___x_237_ = l_Lean_IR_Sorry_visitDecl(v___x_236_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; size_t v___x_241_; size_t v___x_242_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v_fst_239_ = lean_ctor_get(v_a_238_, 0);
lean_inc(v_fst_239_);
v_snd_240_ = lean_ctor_get(v_a_238_, 1);
lean_inc(v_snd_240_);
lean_dec(v_a_238_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_228_, v___x_241_);
v_i_228_ = v___x_242_;
v_b_230_ = v_fst_239_;
v___y_231_ = v_snd_240_;
goto _start;
}
else
{
return v___x_237_;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_b_230_);
lean_ctor_set(v___x_244_, 1, v___y_231_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_stop_248_, lean_object* v_b_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
size_t v_i_boxed_254_; size_t v_stop_boxed_255_; lean_object* v_res_256_; 
v_i_boxed_254_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_stop_boxed_255_ = lean_unbox_usize(v_stop_248_);
lean_dec(v_stop_248_);
v_res_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_246_, v_i_boxed_254_, v_stop_boxed_255_, v_b_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec_ref(v_as_246_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* v_decls_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_snd_263_; lean_object* v_localSorryMap_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_286_; 
v_localSorryMap_267_ = lean_ctor_get(v_a_258_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_a_258_);
if (v_isSharedCheck_286_ == 0)
{
v___x_269_ = v_a_258_;
v_isShared_270_ = v_isSharedCheck_286_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_localSorryMap_267_);
lean_dec(v_a_258_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_286_;
goto v_resetjp_268_;
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_snd_263_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
v_resetjp_268_:
{
uint8_t v___x_271_; lean_object* v___x_273_; 
v___x_271_ = 0;
if (v_isShared_270_ == 0)
{
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_localSorryMap_267_);
v___x_273_ = v_reuseFailAlloc_285_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_271_);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_array_get_size(v_decls_257_);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
v_snd_263_ = v___x_273_;
goto v___jp_262_;
}
else
{
lean_object* v___x_277_; size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_box(0);
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_275_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_257_, v___x_278_, v___x_279_, v___x_277_, v___x_273_, v_a_259_, v_a_260_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v_snd_282_; uint8_t v_modified_283_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v_snd_282_ = lean_ctor_get(v_a_281_, 1);
lean_inc(v_snd_282_);
lean_dec(v_a_281_);
v_modified_283_ = lean_ctor_get_uint8(v_snd_282_, sizeof(void*)*1);
if (v_modified_283_ == 0)
{
v_snd_263_ = v_snd_282_;
goto v___jp_262_;
}
else
{
v_a_258_ = v_snd_282_;
goto _start;
}
}
else
{
return v___x_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* v_decls_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_IR_Sorry_collect(v_decls_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec_ref(v_decls_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object* v_snd_293_, size_t v_sz_294_, size_t v_i_295_, lean_object* v_bs_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_lt(v_i_295_, v_sz_294_);
if (v___x_297_ == 0)
{
return v_bs_296_;
}
else
{
lean_object* v_v_298_; lean_object* v___x_299_; lean_object* v_bs_x27_300_; lean_object* v___y_302_; 
v_v_298_ = lean_array_uget(v_bs_296_, v_i_295_);
v___x_299_ = lean_unsigned_to_nat(0u);
v_bs_x27_300_ = lean_array_uset(v_bs_296_, v_i_295_, v___x_299_);
if (lean_obj_tag(v_v_298_) == 0)
{
lean_object* v_f_307_; lean_object* v_xs_308_; lean_object* v_type_309_; lean_object* v_body_310_; lean_object* v_info_311_; lean_object* v_localSorryMap_312_; lean_object* v___x_313_; 
v_f_307_ = lean_ctor_get(v_v_298_, 0);
v_xs_308_ = lean_ctor_get(v_v_298_, 1);
v_type_309_ = lean_ctor_get(v_v_298_, 2);
v_body_310_ = lean_ctor_get(v_v_298_, 3);
v_info_311_ = lean_ctor_get(v_v_298_, 4);
lean_inc_ref(v_info_311_);
v_localSorryMap_312_ = lean_ctor_get(v_snd_293_, 0);
v___x_313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_312_, v_f_307_);
if (lean_obj_tag(v___x_313_) == 1)
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
lean_inc(v_body_310_);
lean_inc(v_type_309_);
lean_inc_ref(v_xs_308_);
lean_inc(v_f_307_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_331_ = lean_ctor_get(v_v_298_, 4);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_v_298_, 3);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_v_298_, 2);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_v_298_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_v_298_, 0);
lean_dec(v_unused_335_);
v___x_315_ = v_v_298_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_v_298_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_maxJp_317_; lean_object* v_maxVar_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_maxJp_317_ = lean_ctor_get(v_info_311_, 1);
v_maxVar_318_ = lean_ctor_get(v_info_311_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_info_311_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_info_311_, 0);
lean_dec(v_unused_329_);
v___x_320_ = v_info_311_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_maxVar_318_);
lean_inc(v_maxJp_317_);
lean_dec(v_info_311_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_313_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_maxJp_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_maxVar_318_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 4, v___x_323_);
v___x_325_ = v___x_315_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_f_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_xs_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_type_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_body_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v___y_302_ = v___x_325_;
goto v___jp_301_;
}
}
}
}
}
else
{
lean_dec(v___x_313_);
lean_dec_ref(v_info_311_);
v___y_302_ = v_v_298_;
goto v___jp_301_;
}
}
else
{
v___y_302_ = v_v_298_;
goto v___jp_301_;
}
v___jp_301_:
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_i_295_, v___x_303_);
v___x_305_ = lean_array_uset(v_bs_x27_300_, v_i_295_, v___y_302_);
v_i_295_ = v___x_304_;
v_bs_296_ = v___x_305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object* v_snd_336_, lean_object* v_sz_337_, lean_object* v_i_338_, lean_object* v_bs_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_337_);
lean_dec(v_sz_337_);
v_i_boxed_341_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_336_, v_sz_boxed_340_, v_i_boxed_341_, v_bs_339_);
lean_dec_ref(v_snd_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* v_decls_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_IR_updateSorryDep___closed__0));
v___x_351_ = l_Lean_IR_Sorry_collect(v_decls_346_, v___x_350_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_363_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_363_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_snd_356_; size_t v_sz_357_; size_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v_snd_356_ = lean_ctor_get(v_a_352_, 1);
lean_inc(v_snd_356_);
lean_dec(v_a_352_);
v_sz_357_ = lean_array_size(v_decls_346_);
v___x_358_ = ((size_t)0ULL);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_356_, v_sz_357_, v___x_358_, v_decls_346_);
lean_dec(v_snd_356_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_359_);
v___x_361_ = v___x_354_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_decls_346_);
v_a_364_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_351_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_351_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* v_decls_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_IR_updateSorryDep(v_decls_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_376_;
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
