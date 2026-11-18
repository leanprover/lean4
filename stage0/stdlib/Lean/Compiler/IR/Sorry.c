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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_IR_Alt_body(lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(lean_object* v_f_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_g_11_; lean_object* v___y_12_; lean_object* v___y_22_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1));
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
v___x_13_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1));
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
v___x_23_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___y_22_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___boxed(lean_object* v_f_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_f_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object* v_f_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_f_53_, v_a_54_, v_a_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object* v_f_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(v_f_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg(lean_object* v_x_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
switch(lean_obj_tag(v_x_65_))
{
case 6:
{
lean_object* v_c_69_; lean_object* v___x_70_; 
v_c_69_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_c_69_);
lean_dec_ref_known(v_x_65_, 2);
v___x_70_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_69_, v_a_66_, v_a_67_);
return v___x_70_;
}
case 7:
{
lean_object* v_c_71_; lean_object* v___x_72_; 
v_c_71_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_c_71_);
lean_dec_ref_known(v_x_65_, 2);
v___x_72_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_71_, v_a_66_, v_a_67_);
return v___x_72_;
}
default: 
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec_ref(v_x_65_);
v___x_73_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_a_66_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg___boxed(lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object* v_x_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_81_, v_a_82_, v_a_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object* v_x_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_IR_Sorry_visitExpr(v_x_87_, v_a_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody(lean_object* v_b_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
switch(lean_obj_tag(v_b_93_))
{
case 0:
{
lean_object* v_e_98_; lean_object* v_b_99_; lean_object* v___x_100_; 
v_e_98_ = lean_ctor_get(v_b_93_, 2);
lean_inc_ref(v_e_98_);
v_b_99_ = lean_ctor_get(v_b_93_, 3);
lean_inc(v_b_99_);
lean_dec_ref_known(v_b_93_, 4);
v___x_100_ = l_Lean_IR_Sorry_visitExpr___redArg(v_e_98_, v_a_94_, v_a_96_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_fst_102_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_fst_102_ = lean_ctor_get(v_a_101_, 0);
if (lean_obj_tag(v_fst_102_) == 0)
{
lean_dec(v_b_99_);
return v___x_100_;
}
else
{
lean_object* v_snd_103_; 
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_100_, 1);
v_snd_103_ = lean_ctor_get(v_a_101_, 1);
lean_inc(v_snd_103_);
lean_dec(v_a_101_);
v_b_93_ = v_b_99_;
v_a_94_ = v_snd_103_;
goto _start;
}
}
else
{
lean_dec(v_b_99_);
return v___x_100_;
}
}
case 1:
{
lean_object* v_v_105_; lean_object* v_b_106_; lean_object* v___x_107_; 
v_v_105_ = lean_ctor_get(v_b_93_, 2);
lean_inc(v_v_105_);
v_b_106_ = lean_ctor_get(v_b_93_, 3);
lean_inc(v_b_106_);
lean_dec_ref_known(v_b_93_, 4);
v___x_107_ = l_Lean_IR_Sorry_visitFnBody(v_v_105_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v_fst_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_fst_109_ = lean_ctor_get(v_a_108_, 0);
if (lean_obj_tag(v_fst_109_) == 0)
{
lean_dec(v_b_106_);
return v___x_107_;
}
else
{
lean_object* v_snd_110_; 
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
v_snd_110_ = lean_ctor_get(v_a_108_, 1);
lean_inc(v_snd_110_);
lean_dec(v_a_108_);
v_b_93_ = v_b_106_;
v_a_94_ = v_snd_110_;
goto _start;
}
}
else
{
lean_dec(v_b_106_);
return v___x_107_;
}
}
case 9:
{
lean_object* v_cs_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_cs_112_ = lean_ctor_get(v_b_93_, 3);
lean_inc_ref(v_cs_112_);
lean_dec_ref_known(v_b_93_, 4);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_array_get_size(v_cs_112_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_nat_dec_lt(v___x_113_, v___x_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec_ref(v_cs_112_);
v___x_117_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_a_94_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
else
{
size_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_114_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_112_, v___x_120_, v___x_121_, v___x_115_, v_a_94_, v_a_95_, v_a_96_);
lean_dec_ref(v_cs_112_);
return v___x_122_;
}
}
default: 
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_IR_FnBody_isTerminal(v_b_93_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_IR_FnBody_body(v_b_93_);
lean_dec(v_b_93_);
v_b_93_ = v___x_124_;
goto _start;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_b_93_);
v___x_126_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_94_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object* v_as_129_, size_t v_i_130_, size_t v_stop_131_, lean_object* v_b_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = lean_usize_dec_eq(v_i_130_, v_stop_131_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_array_uget_borrowed(v_as_129_, v_i_130_);
v___x_139_ = l_Lean_IR_Alt_body(v___x_138_);
v___x_140_ = l_Lean_IR_Sorry_visitFnBody(v___x_139_, v___y_133_, v___y_134_, v___y_135_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v_fst_142_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_fst_142_ = lean_ctor_get(v_a_141_, 0);
if (lean_obj_tag(v_fst_142_) == 0)
{
return v___x_140_;
}
else
{
lean_object* v_snd_143_; lean_object* v_a_144_; size_t v___x_145_; size_t v___x_146_; 
lean_inc_ref(v_fst_142_);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v_snd_143_ = lean_ctor_get(v_a_141_, 1);
lean_inc(v_snd_143_);
lean_dec(v_a_141_);
v_a_144_ = lean_ctor_get(v_fst_142_, 0);
lean_inc(v_a_144_);
lean_dec_ref_known(v_fst_142_, 1);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_i_130_, v___x_145_);
v_i_130_ = v___x_146_;
v_b_132_ = v_a_144_;
v___y_133_ = v_snd_143_;
goto _start;
}
}
else
{
return v___x_140_;
}
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_b_132_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___y_133_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object* v_as_151_, lean_object* v_i_152_, lean_object* v_stop_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
size_t v_i_boxed_159_; size_t v_stop_boxed_160_; lean_object* v_res_161_; 
v_i_boxed_159_ = lean_unbox_usize(v_i_152_);
lean_dec(v_i_152_);
v_stop_boxed_160_ = lean_unbox_usize(v_stop_153_);
lean_dec(v_stop_153_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_151_, v_i_boxed_159_, v_stop_boxed_160_, v_b_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec_ref(v_as_151_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object* v_b_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_IR_Sorry_visitFnBody(v_b_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* v_d_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
if (lean_obj_tag(v_d_168_) == 0)
{
lean_object* v_f_173_; lean_object* v_body_174_; lean_object* v_localSorryMap_175_; lean_object* v___x_176_; 
v_f_173_ = lean_ctor_get(v_d_168_, 0);
lean_inc(v_f_173_);
v_body_174_ = lean_ctor_get(v_d_168_, 3);
lean_inc(v_body_174_);
lean_dec_ref_known(v_d_168_, 5);
v_localSorryMap_175_ = lean_ctor_get(v_a_169_, 0);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_175_, v_f_173_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_IR_Sorry_visitFnBody(v_body_174_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_220_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_220_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_220_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_220_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_fst_182_; 
v_fst_182_ = lean_ctor_get(v_a_178_, 0);
if (lean_obj_tag(v_fst_182_) == 0)
{
lean_object* v_snd_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_205_; 
lean_inc_ref(v_fst_182_);
v_snd_183_ = lean_ctor_get(v_a_178_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_a_178_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_a_178_, 0);
lean_dec(v_unused_206_);
v___x_185_ = v_a_178_;
v_isShared_186_ = v_isSharedCheck_205_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_snd_183_);
lean_dec(v_a_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_205_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_a_187_; lean_object* v_localSorryMap_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_204_; 
v_a_187_ = lean_ctor_get(v_fst_182_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v_fst_182_, 1);
v_localSorryMap_188_ = lean_ctor_get(v_snd_183_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v_snd_183_);
if (v_isSharedCheck_204_ == 0)
{
v___x_190_ = v_snd_183_;
v_isShared_191_ = v_isSharedCheck_204_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_localSorryMap_188_);
lean_dec(v_snd_183_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_204_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_196_; 
v___x_192_ = lean_box(0);
v___x_193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_173_, v_a_187_, v_localSorryMap_188_);
v___x_194_ = 1;
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_196_ = v___x_190_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_193_);
v___x_196_ = v_reuseFailAlloc_203_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*1, v___x_194_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_196_);
lean_ctor_set(v___x_185_, 0, v___x_192_);
v___x_198_ = v___x_185_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_198_);
v___x_200_ = v___x_180_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
}
else
{
lean_object* v_snd_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_f_173_);
v_snd_207_ = lean_ctor_get(v_a_178_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_178_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_a_178_, 0);
lean_dec(v_unused_219_);
v___x_209_ = v_a_178_;
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snd_207_);
lean_dec(v_a_178_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_box(0);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_snd_207_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_213_);
v___x_215_ = v___x_180_;
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
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec(v_f_173_);
v_a_221_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_177_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_177_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
lean_dec(v_body_174_);
lean_dec(v_f_173_);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v___x_176_, 0);
lean_dec(v_unused_238_);
v___x_230_ = v___x_176_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_dec(v___x_176_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_a_169_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 0);
lean_ctor_set(v___x_230_, 0, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_d_168_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_a_169_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* v_d_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_IR_Sorry_visitDecl(v_d_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_, lean_object* v_b_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_array_uget_borrowed(v_as_248_, v_i_249_);
lean_inc(v___x_257_);
v___x_258_ = l_Lean_IR_Sorry_visitDecl(v___x_257_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v_fst_260_; lean_object* v_snd_261_; size_t v___x_262_; size_t v___x_263_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_258_, 1);
v_fst_260_ = lean_ctor_get(v_a_259_, 0);
lean_inc(v_fst_260_);
v_snd_261_ = lean_ctor_get(v_a_259_, 1);
lean_inc(v_snd_261_);
lean_dec(v_a_259_);
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_add(v_i_249_, v___x_262_);
v_i_249_ = v___x_263_;
v_b_251_ = v_fst_260_;
v___y_252_ = v_snd_261_;
goto _start;
}
else
{
return v___x_258_;
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_b_251_);
lean_ctor_set(v___x_265_, 1, v___y_252_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object* v_as_267_, lean_object* v_i_268_, lean_object* v_stop_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
size_t v_i_boxed_275_; size_t v_stop_boxed_276_; lean_object* v_res_277_; 
v_i_boxed_275_ = lean_unbox_usize(v_i_268_);
lean_dec(v_i_268_);
v_stop_boxed_276_ = lean_unbox_usize(v_stop_269_);
lean_dec(v_stop_269_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_267_, v_i_boxed_275_, v_stop_boxed_276_, v_b_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_as_267_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* v_decls_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_snd_284_; lean_object* v_localSorryMap_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_307_; 
v_localSorryMap_288_ = lean_ctor_get(v_a_279_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_279_);
if (v_isSharedCheck_307_ == 0)
{
v___x_290_ = v_a_279_;
v_isShared_291_ = v_isSharedCheck_307_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_localSorryMap_288_);
lean_dec(v_a_279_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_307_;
goto v_resetjp_289_;
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_snd_284_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
v_resetjp_289_:
{
uint8_t v___x_292_; lean_object* v___x_294_; 
v___x_292_ = 0;
if (v_isShared_291_ == 0)
{
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_localSorryMap_288_);
v___x_294_ = v_reuseFailAlloc_306_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*1, v___x_292_);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_array_get_size(v_decls_278_);
v___x_297_ = lean_nat_dec_lt(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
v_snd_284_ = v___x_294_;
goto v___jp_283_;
}
else
{
lean_object* v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_298_ = lean_box(0);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_296_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_278_, v___x_299_, v___x_300_, v___x_298_, v___x_294_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_snd_303_; uint8_t v_modified_304_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v_snd_303_ = lean_ctor_get(v_a_302_, 1);
lean_inc(v_snd_303_);
lean_dec(v_a_302_);
v_modified_304_ = lean_ctor_get_uint8(v_snd_303_, sizeof(void*)*1);
if (v_modified_304_ == 0)
{
v_snd_284_ = v_snd_303_;
goto v___jp_283_;
}
else
{
v_a_279_ = v_snd_303_;
goto _start;
}
}
else
{
return v___x_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* v_decls_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_IR_Sorry_collect(v_decls_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_decls_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object* v_snd_314_, size_t v_sz_315_, size_t v_i_316_, lean_object* v_bs_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_usize_dec_lt(v_i_316_, v_sz_315_);
if (v___x_318_ == 0)
{
return v_bs_317_;
}
else
{
lean_object* v_v_319_; lean_object* v___x_320_; lean_object* v_bs_x27_321_; lean_object* v___y_323_; 
v_v_319_ = lean_array_uget(v_bs_317_, v_i_316_);
v___x_320_ = lean_unsigned_to_nat(0u);
v_bs_x27_321_ = lean_array_uset(v_bs_317_, v_i_316_, v___x_320_);
if (lean_obj_tag(v_v_319_) == 0)
{
lean_object* v_f_328_; lean_object* v_xs_329_; lean_object* v_type_330_; lean_object* v_body_331_; lean_object* v_info_332_; lean_object* v_localSorryMap_333_; lean_object* v___x_334_; 
v_f_328_ = lean_ctor_get(v_v_319_, 0);
v_xs_329_ = lean_ctor_get(v_v_319_, 1);
v_type_330_ = lean_ctor_get(v_v_319_, 2);
v_body_331_ = lean_ctor_get(v_v_319_, 3);
v_info_332_ = lean_ctor_get(v_v_319_, 4);
lean_inc_ref(v_info_332_);
v_localSorryMap_333_ = lean_ctor_get(v_snd_314_, 0);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_333_, v_f_328_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_351_; 
lean_inc(v_body_331_);
lean_inc(v_type_330_);
lean_inc_ref(v_xs_329_);
lean_inc(v_f_328_);
v_isSharedCheck_351_ = !lean_is_exclusive(v_v_319_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_352_ = lean_ctor_get(v_v_319_, 4);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_v_319_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_v_319_, 2);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_v_319_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_v_319_, 0);
lean_dec(v_unused_356_);
v___x_336_ = v_v_319_;
v_isShared_337_ = v_isSharedCheck_351_;
goto v_resetjp_335_;
}
else
{
lean_dec(v_v_319_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_351_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_maxJp_338_; lean_object* v_maxVar_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_349_; 
v_maxJp_338_ = lean_ctor_get(v_info_332_, 1);
v_maxVar_339_ = lean_ctor_get(v_info_332_, 2);
v_isSharedCheck_349_ = !lean_is_exclusive(v_info_332_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_info_332_, 0);
lean_dec(v_unused_350_);
v___x_341_ = v_info_332_;
v_isShared_342_ = v_isSharedCheck_349_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_maxVar_339_);
lean_inc(v_maxJp_338_);
lean_dec(v_info_332_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_349_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_334_);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_maxJp_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_maxVar_339_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v___x_344_);
v___x_346_ = v___x_336_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_f_328_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_xs_329_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_type_330_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_body_331_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v___y_323_ = v___x_346_;
goto v___jp_322_;
}
}
}
}
}
else
{
lean_dec(v___x_334_);
lean_dec_ref(v_info_332_);
v___y_323_ = v_v_319_;
goto v___jp_322_;
}
}
else
{
v___y_323_ = v_v_319_;
goto v___jp_322_;
}
v___jp_322_:
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_316_, v___x_324_);
v___x_326_ = lean_array_uset(v_bs_x27_321_, v_i_316_, v___y_323_);
v_i_316_ = v___x_325_;
v_bs_317_ = v___x_326_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object* v_snd_357_, lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_bs_360_){
_start:
{
size_t v_sz_boxed_361_; size_t v_i_boxed_362_; lean_object* v_res_363_; 
v_sz_boxed_361_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_362_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_357_, v_sz_boxed_361_, v_i_boxed_362_, v_bs_360_);
lean_dec_ref(v_snd_357_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* v_decls_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_IR_updateSorryDep___closed__0));
v___x_372_ = l_Lean_IR_Sorry_collect(v_decls_367_, v___x_371_, v_a_368_, v_a_369_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_384_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_snd_377_; size_t v_sz_378_; size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v_snd_377_ = lean_ctor_get(v_a_373_, 1);
lean_inc(v_snd_377_);
lean_dec(v_a_373_);
v_sz_378_ = lean_array_size(v_decls_367_);
v___x_379_ = ((size_t)0ULL);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_377_, v_sz_378_, v___x_379_, v_decls_367_);
lean_dec(v_snd_377_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_380_);
v___x_382_ = v___x_375_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v_decls_367_);
v_a_385_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_372_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_372_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* v_decls_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_IR_updateSorryDep(v_decls_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_397_;
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
