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
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_le(v___x_114_, v___x_114_);
if (v___x_120_ == 0)
{
if (v___x_116_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec_ref(v_cs_112_);
v___x_121_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v_a_94_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
else
{
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_114_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_112_, v___x_124_, v___x_125_, v___x_115_, v_a_94_, v_a_95_, v_a_96_);
lean_dec_ref(v_cs_112_);
return v___x_126_;
}
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_114_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_112_, v___x_127_, v___x_128_, v___x_115_, v_a_94_, v_a_95_, v_a_96_);
lean_dec_ref(v_cs_112_);
return v___x_129_;
}
}
}
default: 
{
uint8_t v___x_130_; 
v___x_130_ = l_Lean_IR_FnBody_isTerminal(v_b_93_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_IR_FnBody_body(v_b_93_);
lean_dec(v_b_93_);
v_b_93_ = v___x_131_;
goto _start;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_b_93_);
v___x_133_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v_a_94_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object* v_as_136_, size_t v_i_137_, size_t v_stop_138_, lean_object* v_b_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_usize_dec_eq(v_i_137_, v_stop_138_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_array_uget_borrowed(v_as_136_, v_i_137_);
v___x_146_ = l_Lean_IR_Alt_body(v___x_145_);
v___x_147_ = l_Lean_IR_Sorry_visitFnBody(v___x_146_, v___y_140_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v_fst_149_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_fst_149_ = lean_ctor_get(v_a_148_, 0);
if (lean_obj_tag(v_fst_149_) == 0)
{
return v___x_147_;
}
else
{
lean_object* v_snd_150_; lean_object* v_a_151_; size_t v___x_152_; size_t v___x_153_; 
lean_inc_ref(v_fst_149_);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v_snd_150_ = lean_ctor_get(v_a_148_, 1);
lean_inc(v_snd_150_);
lean_dec(v_a_148_);
v_a_151_ = lean_ctor_get(v_fst_149_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v_fst_149_, 1);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_add(v_i_137_, v___x_152_);
v_i_137_ = v___x_153_;
v_b_139_ = v_a_151_;
v___y_140_ = v_snd_150_;
goto _start;
}
}
else
{
return v___x_147_;
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_b_139_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___y_140_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object* v_as_158_, lean_object* v_i_159_, lean_object* v_stop_160_, lean_object* v_b_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
size_t v_i_boxed_166_; size_t v_stop_boxed_167_; lean_object* v_res_168_; 
v_i_boxed_166_ = lean_unbox_usize(v_i_159_);
lean_dec(v_i_159_);
v_stop_boxed_167_ = lean_unbox_usize(v_stop_160_);
lean_dec(v_stop_160_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_158_, v_i_boxed_166_, v_stop_boxed_167_, v_b_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec_ref(v_as_158_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object* v_b_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_IR_Sorry_visitFnBody(v_b_169_, v_a_170_, v_a_171_, v_a_172_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* v_d_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
if (lean_obj_tag(v_d_175_) == 0)
{
lean_object* v_f_180_; lean_object* v_body_181_; lean_object* v_localSorryMap_182_; lean_object* v___x_183_; 
v_f_180_ = lean_ctor_get(v_d_175_, 0);
lean_inc(v_f_180_);
v_body_181_ = lean_ctor_get(v_d_175_, 3);
lean_inc(v_body_181_);
lean_dec_ref_known(v_d_175_, 5);
v_localSorryMap_182_ = lean_ctor_get(v_a_176_, 0);
v___x_183_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_182_, v_f_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_IR_Sorry_visitFnBody(v_body_181_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_227_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_227_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_227_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_227_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_fst_189_; 
v_fst_189_ = lean_ctor_get(v_a_185_, 0);
if (lean_obj_tag(v_fst_189_) == 0)
{
lean_object* v_snd_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_212_; 
lean_inc_ref(v_fst_189_);
v_snd_190_ = lean_ctor_get(v_a_185_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_a_185_, 0);
lean_dec(v_unused_213_);
v___x_192_ = v_a_185_;
v_isShared_193_ = v_isSharedCheck_212_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snd_190_);
lean_dec(v_a_185_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_212_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_a_194_; lean_object* v_localSorryMap_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_211_; 
v_a_194_ = lean_ctor_get(v_fst_189_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v_fst_189_, 1);
v_localSorryMap_195_ = lean_ctor_get(v_snd_190_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_snd_190_);
if (v_isSharedCheck_211_ == 0)
{
v___x_197_ = v_snd_190_;
v_isShared_198_ = v_isSharedCheck_211_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_localSorryMap_195_);
lean_dec(v_snd_190_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_211_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_203_; 
v___x_199_ = lean_box(0);
v___x_200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_180_, v_a_194_, v_localSorryMap_195_);
v___x_201_ = 1;
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_203_ = v___x_197_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_200_);
v___x_203_ = v_reuseFailAlloc_210_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_201_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_203_);
lean_ctor_set(v___x_192_, 0, v___x_199_);
v___x_205_ = v___x_192_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_205_);
v___x_207_ = v___x_187_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
}
else
{
lean_object* v_snd_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_f_180_);
v_snd_214_ = lean_ctor_get(v_a_185_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; 
v_unused_226_ = lean_ctor_get(v_a_185_, 0);
lean_dec(v_unused_226_);
v___x_216_ = v_a_185_;
v_isShared_217_ = v_isSharedCheck_225_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_snd_214_);
lean_dec(v_a_185_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_225_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_box(0);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_snd_214_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_220_);
v___x_222_ = v___x_187_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_f_180_);
v_a_228_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_184_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_184_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
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
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_body_181_);
lean_dec(v_f_180_);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_245_);
v___x_237_ = v___x_183_;
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
else
{
lean_dec(v___x_183_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_a_176_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 0);
lean_ctor_set(v___x_237_, 0, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_d_175_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_176_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* v_d_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_IR_Sorry_visitDecl(v_d_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object* v_as_255_, size_t v_i_256_, size_t v_stop_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_usize_dec_eq(v_i_256_, v_stop_257_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_array_uget_borrowed(v_as_255_, v_i_256_);
lean_inc(v___x_264_);
v___x_265_ = l_Lean_IR_Sorry_visitDecl(v___x_264_, v___y_259_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v_fst_267_; lean_object* v_snd_268_; size_t v___x_269_; size_t v___x_270_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v_fst_267_ = lean_ctor_get(v_a_266_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v_a_266_, 1);
lean_inc(v_snd_268_);
lean_dec(v_a_266_);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_add(v_i_256_, v___x_269_);
v_i_256_ = v___x_270_;
v_b_258_ = v_fst_267_;
v___y_259_ = v_snd_268_;
goto _start;
}
else
{
return v___x_265_;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_b_258_);
lean_ctor_set(v___x_272_, 1, v___y_259_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_stop_276_, lean_object* v_b_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
size_t v_i_boxed_282_; size_t v_stop_boxed_283_; lean_object* v_res_284_; 
v_i_boxed_282_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_stop_boxed_283_ = lean_unbox_usize(v_stop_276_);
lean_dec(v_stop_276_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_274_, v_i_boxed_282_, v_stop_boxed_283_, v_b_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_as_274_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* v_decls_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_snd_291_; lean_object* v___y_296_; lean_object* v_localSorryMap_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_320_; 
v_localSorryMap_301_ = lean_ctor_get(v_a_286_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_320_ == 0)
{
v___x_303_ = v_a_286_;
v_isShared_304_ = v_isSharedCheck_320_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_localSorryMap_301_);
lean_dec(v_a_286_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_320_;
goto v_resetjp_302_;
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_snd_291_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
v___jp_295_:
{
if (lean_obj_tag(v___y_296_) == 0)
{
lean_object* v_a_297_; lean_object* v_snd_298_; uint8_t v_modified_299_; 
v_a_297_ = lean_ctor_get(v___y_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___y_296_, 1);
v_snd_298_ = lean_ctor_get(v_a_297_, 1);
lean_inc(v_snd_298_);
lean_dec(v_a_297_);
v_modified_299_ = lean_ctor_get_uint8(v_snd_298_, sizeof(void*)*1);
if (v_modified_299_ == 0)
{
v_snd_291_ = v_snd_298_;
goto v___jp_290_;
}
else
{
v_a_286_ = v_snd_298_;
goto _start;
}
}
else
{
return v___y_296_;
}
}
v_resetjp_302_:
{
uint8_t v___x_305_; lean_object* v___x_307_; 
v___x_305_ = 0;
if (v_isShared_304_ == 0)
{
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_localSorryMap_301_);
v___x_307_ = v_reuseFailAlloc_319_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*1, v___x_305_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_array_get_size(v_decls_285_);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
v_snd_291_ = v___x_307_;
goto v___jp_290_;
}
else
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_nat_dec_le(v___x_309_, v___x_309_);
if (v___x_312_ == 0)
{
if (v___x_310_ == 0)
{
v_snd_291_ = v___x_307_;
goto v___jp_290_;
}
else
{
size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = ((size_t)0ULL);
v___x_314_ = lean_usize_of_nat(v___x_309_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_285_, v___x_313_, v___x_314_, v___x_311_, v___x_307_, v_a_287_, v_a_288_);
v___y_296_ = v___x_315_;
goto v___jp_295_;
}
}
else
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_309_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_285_, v___x_316_, v___x_317_, v___x_311_, v___x_307_, v_a_287_, v_a_288_);
v___y_296_ = v___x_318_;
goto v___jp_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* v_decls_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_IR_Sorry_collect(v_decls_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec_ref(v_decls_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object* v_snd_327_, size_t v_sz_328_, size_t v_i_329_, lean_object* v_bs_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_331_ == 0)
{
return v_bs_330_;
}
else
{
lean_object* v_v_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; lean_object* v___y_336_; 
v_v_332_ = lean_array_uget(v_bs_330_, v_i_329_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_330_, v_i_329_, v___x_333_);
if (lean_obj_tag(v_v_332_) == 0)
{
lean_object* v_f_341_; lean_object* v_xs_342_; lean_object* v_type_343_; lean_object* v_body_344_; lean_object* v_info_345_; lean_object* v_localSorryMap_346_; lean_object* v___x_347_; 
v_f_341_ = lean_ctor_get(v_v_332_, 0);
v_xs_342_ = lean_ctor_get(v_v_332_, 1);
v_type_343_ = lean_ctor_get(v_v_332_, 2);
v_body_344_ = lean_ctor_get(v_v_332_, 3);
v_info_345_ = lean_ctor_get(v_v_332_, 4);
lean_inc_ref(v_info_345_);
v_localSorryMap_346_ = lean_ctor_get(v_snd_327_, 0);
v___x_347_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_346_, v_f_341_);
if (lean_obj_tag(v___x_347_) == 1)
{
lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_364_; 
lean_inc(v_body_344_);
lean_inc(v_type_343_);
lean_inc_ref(v_xs_342_);
lean_inc(v_f_341_);
v_isSharedCheck_364_ = !lean_is_exclusive(v_v_332_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; lean_object* v_unused_366_; lean_object* v_unused_367_; lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_365_ = lean_ctor_get(v_v_332_, 4);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_v_332_, 3);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_v_332_, 2);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_v_332_, 1);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_v_332_, 0);
lean_dec(v_unused_369_);
v___x_349_ = v_v_332_;
v_isShared_350_ = v_isSharedCheck_364_;
goto v_resetjp_348_;
}
else
{
lean_dec(v_v_332_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_364_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_maxJp_351_; lean_object* v_maxVar_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
v_maxJp_351_ = lean_ctor_get(v_info_345_, 1);
v_maxVar_352_ = lean_ctor_get(v_info_345_, 2);
v_isSharedCheck_362_ = !lean_is_exclusive(v_info_345_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_info_345_, 0);
lean_dec(v_unused_363_);
v___x_354_ = v_info_345_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_maxVar_352_);
lean_inc(v_maxJp_351_);
lean_dec(v_info_345_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_347_);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_maxJp_351_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_maxVar_352_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 4, v___x_357_);
v___x_359_ = v___x_349_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_f_341_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_xs_342_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_type_343_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_body_344_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
v___y_336_ = v___x_359_;
goto v___jp_335_;
}
}
}
}
}
else
{
lean_dec(v___x_347_);
lean_dec_ref(v_info_345_);
v___y_336_ = v_v_332_;
goto v___jp_335_;
}
}
else
{
v___y_336_ = v_v_332_;
goto v___jp_335_;
}
v___jp_335_:
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_329_, v___x_337_);
v___x_339_ = lean_array_uset(v_bs_x27_334_, v_i_329_, v___y_336_);
v_i_329_ = v___x_338_;
v_bs_330_ = v___x_339_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object* v_snd_370_, lean_object* v_sz_371_, lean_object* v_i_372_, lean_object* v_bs_373_){
_start:
{
size_t v_sz_boxed_374_; size_t v_i_boxed_375_; lean_object* v_res_376_; 
v_sz_boxed_374_ = lean_unbox_usize(v_sz_371_);
lean_dec(v_sz_371_);
v_i_boxed_375_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_370_, v_sz_boxed_374_, v_i_boxed_375_, v_bs_373_);
lean_dec_ref(v_snd_370_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* v_decls_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_IR_updateSorryDep___closed__0));
v___x_385_ = l_Lean_IR_Sorry_collect(v_decls_380_, v___x_384_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_397_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_snd_390_; size_t v_sz_391_; size_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v_snd_390_ = lean_ctor_get(v_a_386_, 1);
lean_inc(v_snd_390_);
lean_dec(v_a_386_);
v_sz_391_ = lean_array_size(v_decls_380_);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_390_, v_sz_391_, v___x_392_, v_decls_380_);
lean_dec(v_snd_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_393_);
v___x_395_ = v___x_388_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_decls_380_);
v_a_398_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_385_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_385_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* v_decls_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_IR_updateSorryDep(v_decls_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_410_;
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
