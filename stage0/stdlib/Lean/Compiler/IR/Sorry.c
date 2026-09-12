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
lean_object* v_info_34_; 
v_info_34_ = lean_ctor_get(v_val_33_, 4);
lean_inc(v_info_34_);
lean_dec_ref_known(v_val_33_, 5);
if (lean_obj_tag(v_info_34_) == 1)
{
lean_object* v_val_35_; 
v_val_35_ = lean_ctor_get(v_info_34_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v_info_34_, 1);
v_g_11_ = v_val_35_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_dec(v_info_34_);
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
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec_ref(v_a_7_);
lean_dec(v_f_6_);
v_a_36_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_31_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_31_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_f_6_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v_a_7_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___boxed(lean_object* v_f_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_f_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object* v_f_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_f_52_, v_a_53_, v_a_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object* v_f_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(v_f_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg(lean_object* v_x_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
switch(lean_obj_tag(v_x_64_))
{
case 6:
{
lean_object* v_c_68_; lean_object* v___x_69_; 
v_c_68_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_c_68_);
lean_dec_ref_known(v_x_64_, 2);
v___x_69_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_68_, v_a_65_, v_a_66_);
return v___x_69_;
}
case 7:
{
lean_object* v_c_70_; lean_object* v___x_71_; 
v_c_70_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_c_70_);
lean_dec_ref_known(v_x_64_, 2);
v___x_71_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_70_, v_a_65_, v_a_66_);
return v___x_71_;
}
default: 
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v_x_64_);
v___x_72_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_a_65_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg___boxed(lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object* v_x_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_80_, v_a_81_, v_a_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_IR_Sorry_visitExpr(v_x_86_, v_a_87_, v_a_88_, v_a_89_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody(lean_object* v_b_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
switch(lean_obj_tag(v_b_92_))
{
case 0:
{
lean_object* v_e_97_; lean_object* v_b_98_; lean_object* v___x_99_; 
v_e_97_ = lean_ctor_get(v_b_92_, 2);
lean_inc_ref(v_e_97_);
v_b_98_ = lean_ctor_get(v_b_92_, 3);
lean_inc(v_b_98_);
lean_dec_ref_known(v_b_92_, 4);
v___x_99_ = l_Lean_IR_Sorry_visitExpr___redArg(v_e_97_, v_a_93_, v_a_95_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_fst_101_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_fst_101_ = lean_ctor_get(v_a_100_, 0);
if (lean_obj_tag(v_fst_101_) == 0)
{
lean_dec(v_a_100_);
lean_dec(v_b_98_);
return v___x_99_;
}
else
{
lean_object* v_snd_102_; 
lean_dec_ref_known(v___x_99_, 1);
v_snd_102_ = lean_ctor_get(v_a_100_, 1);
lean_inc(v_snd_102_);
lean_dec(v_a_100_);
v_b_92_ = v_b_98_;
v_a_93_ = v_snd_102_;
goto _start;
}
}
else
{
lean_dec(v_b_98_);
return v___x_99_;
}
}
case 1:
{
lean_object* v_v_104_; lean_object* v_b_105_; lean_object* v___x_106_; 
v_v_104_ = lean_ctor_get(v_b_92_, 2);
lean_inc(v_v_104_);
v_b_105_ = lean_ctor_get(v_b_92_, 3);
lean_inc(v_b_105_);
lean_dec_ref_known(v_b_92_, 4);
v___x_106_ = l_Lean_IR_Sorry_visitFnBody(v_v_104_, v_a_93_, v_a_94_, v_a_95_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_fst_108_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
v_fst_108_ = lean_ctor_get(v_a_107_, 0);
if (lean_obj_tag(v_fst_108_) == 0)
{
lean_dec(v_a_107_);
lean_dec(v_b_105_);
return v___x_106_;
}
else
{
lean_object* v_snd_109_; 
lean_dec_ref_known(v___x_106_, 1);
v_snd_109_ = lean_ctor_get(v_a_107_, 1);
lean_inc(v_snd_109_);
lean_dec(v_a_107_);
v_b_92_ = v_b_105_;
v_a_93_ = v_snd_109_;
goto _start;
}
}
else
{
lean_dec(v_b_105_);
return v___x_106_;
}
}
case 9:
{
lean_object* v_cs_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_cs_111_ = lean_ctor_get(v_b_92_, 3);
lean_inc_ref(v_cs_111_);
lean_dec_ref_known(v_b_92_, 4);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_array_get_size(v_cs_111_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_nat_dec_lt(v___x_112_, v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec_ref(v_cs_111_);
v___x_116_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_93_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_le(v___x_113_, v___x_113_);
if (v___x_119_ == 0)
{
if (v___x_115_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec_ref(v_cs_111_);
v___x_120_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_a_93_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
else
{
size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; 
v___x_123_ = ((size_t)0ULL);
v___x_124_ = lean_usize_of_nat(v___x_113_);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_111_, v___x_123_, v___x_124_, v___x_114_, v_a_93_, v_a_94_, v_a_95_);
lean_dec_ref(v_cs_111_);
return v___x_125_;
}
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_113_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_111_, v___x_126_, v___x_127_, v___x_114_, v_a_93_, v_a_94_, v_a_95_);
lean_dec_ref(v_cs_111_);
return v___x_128_;
}
}
}
default: 
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_IR_FnBody_isTerminal(v_b_92_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_IR_FnBody_body(v_b_92_);
lean_dec(v_b_92_);
v_b_92_ = v___x_130_;
goto _start;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_b_92_);
v___x_132_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_a_93_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object* v_as_135_, size_t v_i_136_, size_t v_stop_137_, lean_object* v_b_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = lean_usize_dec_eq(v_i_136_, v_stop_137_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_array_uget_borrowed(v_as_135_, v_i_136_);
v___x_145_ = l_Lean_IR_Alt_body(v___x_144_);
v___x_146_ = l_Lean_IR_Sorry_visitFnBody(v___x_145_, v___y_139_, v___y_140_, v___y_141_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v_fst_148_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
v_fst_148_ = lean_ctor_get(v_a_147_, 0);
lean_inc(v_fst_148_);
if (lean_obj_tag(v_fst_148_) == 0)
{
lean_dec_ref_known(v_fst_148_, 1);
lean_dec(v_a_147_);
return v___x_146_;
}
else
{
lean_object* v_snd_149_; lean_object* v_a_150_; size_t v___x_151_; size_t v___x_152_; 
lean_dec_ref_known(v___x_146_, 1);
v_snd_149_ = lean_ctor_get(v_a_147_, 1);
lean_inc(v_snd_149_);
lean_dec(v_a_147_);
v_a_150_ = lean_ctor_get(v_fst_148_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v_fst_148_, 1);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_add(v_i_136_, v___x_151_);
v_i_136_ = v___x_152_;
v_b_138_ = v_a_150_;
v___y_139_ = v_snd_149_;
goto _start;
}
}
else
{
return v___x_146_;
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v_b_138_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___y_139_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object* v_as_157_, lean_object* v_i_158_, lean_object* v_stop_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
size_t v_i_boxed_165_; size_t v_stop_boxed_166_; lean_object* v_res_167_; 
v_i_boxed_165_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_stop_boxed_166_ = lean_unbox_usize(v_stop_159_);
lean_dec(v_stop_159_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_157_, v_i_boxed_165_, v_stop_boxed_166_, v_b_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v_as_157_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object* v_b_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_IR_Sorry_visitFnBody(v_b_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* v_d_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
if (lean_obj_tag(v_d_174_) == 0)
{
lean_object* v_f_179_; lean_object* v_body_180_; lean_object* v_localSorryMap_181_; lean_object* v___x_182_; 
v_f_179_ = lean_ctor_get(v_d_174_, 0);
lean_inc(v_f_179_);
v_body_180_ = lean_ctor_get(v_d_174_, 3);
lean_inc(v_body_180_);
lean_dec_ref_known(v_d_174_, 5);
v_localSorryMap_181_ = lean_ctor_get(v_a_175_, 0);
v___x_182_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_181_, v_f_179_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_IR_Sorry_visitFnBody(v_body_180_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_226_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_226_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_226_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_226_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_fst_188_; 
v_fst_188_ = lean_ctor_get(v_a_184_, 0);
if (lean_obj_tag(v_fst_188_) == 0)
{
lean_object* v_snd_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_211_; 
lean_inc_ref(v_fst_188_);
v_snd_189_ = lean_ctor_get(v_a_184_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_a_184_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_a_184_, 0);
lean_dec(v_unused_212_);
v___x_191_ = v_a_184_;
v_isShared_192_ = v_isSharedCheck_211_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_snd_189_);
lean_dec(v_a_184_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_211_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_a_193_; lean_object* v_localSorryMap_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_210_; 
v_a_193_ = lean_ctor_get(v_fst_188_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v_fst_188_, 1);
v_localSorryMap_194_ = lean_ctor_get(v_snd_189_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_snd_189_);
if (v_isSharedCheck_210_ == 0)
{
v___x_196_ = v_snd_189_;
v_isShared_197_ = v_isSharedCheck_210_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_localSorryMap_194_);
lean_dec(v_snd_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_210_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_202_; 
v___x_198_ = lean_box(0);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_179_, v_a_193_, v_localSorryMap_194_);
v___x_200_ = 1;
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_199_);
v___x_202_ = v___x_196_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_199_);
v___x_202_ = v_reuseFailAlloc_209_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*1, v___x_200_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_202_);
lean_ctor_set(v___x_191_, 0, v___x_198_);
v___x_204_ = v___x_191_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_208_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_206_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_204_);
v___x_206_ = v___x_186_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
else
{
lean_object* v_snd_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_f_179_);
v_snd_213_ = lean_ctor_get(v_a_184_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_a_184_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v_a_184_, 0);
lean_dec(v_unused_225_);
v___x_215_ = v_a_184_;
v_isShared_216_ = v_isSharedCheck_224_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snd_213_);
lean_dec(v_a_184_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_224_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_219_ = v___x_215_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_snd_213_);
v___x_219_ = v_reuseFailAlloc_223_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_219_);
v___x_221_ = v___x_186_;
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
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_f_179_);
v_a_227_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_183_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_183_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_body_180_);
lean_dec(v_f_179_);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v___x_182_, 0);
lean_dec(v_unused_244_);
v___x_236_ = v___x_182_;
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_182_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_175_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 0);
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
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
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v_d_174_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_a_175_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* v_d_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_IR_Sorry_visitDecl(v_d_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object* v_as_254_, size_t v_i_255_, size_t v_stop_256_, lean_object* v_b_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = lean_usize_dec_eq(v_i_255_, v_stop_256_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_array_uget_borrowed(v_as_254_, v_i_255_);
lean_inc(v___x_263_);
v___x_264_ = l_Lean_IR_Sorry_visitDecl(v___x_263_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v_fst_266_; lean_object* v_snd_267_; size_t v___x_268_; size_t v___x_269_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v_fst_266_ = lean_ctor_get(v_a_265_, 0);
lean_inc(v_fst_266_);
v_snd_267_ = lean_ctor_get(v_a_265_, 1);
lean_inc(v_snd_267_);
lean_dec(v_a_265_);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_255_, v___x_268_);
v_i_255_ = v___x_269_;
v_b_257_ = v_fst_266_;
v___y_258_ = v_snd_267_;
goto _start;
}
else
{
return v___x_264_;
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_b_257_);
lean_ctor_set(v___x_271_, 1, v___y_258_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object* v_as_273_, lean_object* v_i_274_, lean_object* v_stop_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
size_t v_i_boxed_281_; size_t v_stop_boxed_282_; lean_object* v_res_283_; 
v_i_boxed_281_ = lean_unbox_usize(v_i_274_);
lean_dec(v_i_274_);
v_stop_boxed_282_ = lean_unbox_usize(v_stop_275_);
lean_dec(v_stop_275_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_273_, v_i_boxed_281_, v_stop_boxed_282_, v_b_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec_ref(v_as_273_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* v_decls_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_snd_290_; lean_object* v___y_295_; lean_object* v_localSorryMap_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_319_; 
v_localSorryMap_300_ = lean_ctor_get(v_a_285_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_319_ == 0)
{
v___x_302_ = v_a_285_;
v_isShared_303_ = v_isSharedCheck_319_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_localSorryMap_300_);
lean_dec(v_a_285_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_319_;
goto v_resetjp_301_;
}
v___jp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_snd_290_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
v___jp_294_:
{
if (lean_obj_tag(v___y_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_snd_297_; uint8_t v_modified_298_; 
v_a_296_ = lean_ctor_get(v___y_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___y_295_, 1);
v_snd_297_ = lean_ctor_get(v_a_296_, 1);
lean_inc(v_snd_297_);
lean_dec(v_a_296_);
v_modified_298_ = lean_ctor_get_uint8(v_snd_297_, sizeof(void*)*1);
if (v_modified_298_ == 0)
{
v_snd_290_ = v_snd_297_;
goto v___jp_289_;
}
else
{
v_a_285_ = v_snd_297_;
goto _start;
}
}
else
{
return v___y_295_;
}
}
v_resetjp_301_:
{
uint8_t v___x_304_; lean_object* v___x_306_; 
v___x_304_ = 0;
if (v_isShared_303_ == 0)
{
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_localSorryMap_300_);
v___x_306_ = v_reuseFailAlloc_318_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*1, v___x_304_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_array_get_size(v_decls_284_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
v_snd_290_ = v___x_306_;
goto v___jp_289_;
}
else
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_nat_dec_le(v___x_308_, v___x_308_);
if (v___x_311_ == 0)
{
if (v___x_309_ == 0)
{
v_snd_290_ = v___x_306_;
goto v___jp_289_;
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_308_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_284_, v___x_312_, v___x_313_, v___x_310_, v___x_306_, v_a_286_, v_a_287_);
v___y_295_ = v___x_314_;
goto v___jp_294_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_308_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_284_, v___x_315_, v___x_316_, v___x_310_, v___x_306_, v_a_286_, v_a_287_);
v___y_295_ = v___x_317_;
goto v___jp_294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* v_decls_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_IR_Sorry_collect(v_decls_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_decls_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object* v_snd_326_, size_t v_sz_327_, size_t v_i_328_, lean_object* v_bs_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_328_, v_sz_327_);
if (v___x_330_ == 0)
{
return v_bs_329_;
}
else
{
lean_object* v_v_331_; lean_object* v___x_332_; lean_object* v_bs_x27_333_; lean_object* v___y_335_; 
v_v_331_ = lean_array_uget(v_bs_329_, v_i_328_);
v___x_332_ = lean_unsigned_to_nat(0u);
v_bs_x27_333_ = lean_array_uset(v_bs_329_, v_i_328_, v___x_332_);
if (lean_obj_tag(v_v_331_) == 0)
{
lean_object* v_f_340_; lean_object* v_xs_341_; lean_object* v_type_342_; lean_object* v_body_343_; lean_object* v_localSorryMap_344_; lean_object* v___x_345_; 
v_f_340_ = lean_ctor_get(v_v_331_, 0);
v_xs_341_ = lean_ctor_get(v_v_331_, 1);
v_type_342_ = lean_ctor_get(v_v_331_, 2);
v_body_343_ = lean_ctor_get(v_v_331_, 3);
v_localSorryMap_344_ = lean_ctor_get(v_snd_326_, 0);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_344_, v_f_340_);
if (lean_obj_tag(v___x_345_) == 1)
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_inc(v_body_343_);
lean_inc(v_type_342_);
lean_inc_ref(v_xs_341_);
lean_inc(v_f_340_);
v_isSharedCheck_352_ = !lean_is_exclusive(v_v_331_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_353_ = lean_ctor_get(v_v_331_, 4);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_v_331_, 3);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_v_331_, 2);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_v_331_, 1);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_v_331_, 0);
lean_dec(v_unused_357_);
v___x_347_ = v_v_331_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_v_331_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 4, v___x_345_);
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_f_340_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_xs_341_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_type_342_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_body_343_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v___x_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
v___y_335_ = v___x_350_;
goto v___jp_334_;
}
}
}
else
{
lean_dec(v___x_345_);
v___y_335_ = v_v_331_;
goto v___jp_334_;
}
}
else
{
v___y_335_ = v_v_331_;
goto v___jp_334_;
}
v___jp_334_:
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_328_, v___x_336_);
v___x_338_ = lean_array_uset(v_bs_x27_333_, v_i_328_, v___y_335_);
v_i_328_ = v___x_337_;
v_bs_329_ = v___x_338_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object* v_snd_358_, lean_object* v_sz_359_, lean_object* v_i_360_, lean_object* v_bs_361_){
_start:
{
size_t v_sz_boxed_362_; size_t v_i_boxed_363_; lean_object* v_res_364_; 
v_sz_boxed_362_ = lean_unbox_usize(v_sz_359_);
lean_dec(v_sz_359_);
v_i_boxed_363_ = lean_unbox_usize(v_i_360_);
lean_dec(v_i_360_);
v_res_364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_358_, v_sz_boxed_362_, v_i_boxed_363_, v_bs_361_);
lean_dec_ref(v_snd_358_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* v_decls_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_IR_updateSorryDep___closed__0));
v___x_373_ = l_Lean_IR_Sorry_collect(v_decls_368_, v___x_372_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_385_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_385_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_385_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_385_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_snd_378_; size_t v_sz_379_; size_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v_snd_378_ = lean_ctor_get(v_a_374_, 1);
lean_inc(v_snd_378_);
lean_dec(v_a_374_);
v_sz_379_ = lean_array_size(v_decls_368_);
v___x_380_ = ((size_t)0ULL);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_378_, v_sz_379_, v___x_380_, v_decls_368_);
lean_dec(v_snd_378_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_381_);
v___x_383_ = v___x_376_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v_decls_368_);
v_a_386_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_373_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_373_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* v_decls_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_IR_updateSorryDep(v_decls_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_398_;
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
