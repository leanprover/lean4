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
lean_object* v_g_11_; lean_object* v___y_12_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1));
v___x_22_ = lean_name_eq(v_f_6_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v_localSorryMap_23_; lean_object* v___x_24_; 
v_localSorryMap_23_ = lean_ctor_get(v_a_7_, 0);
v___x_24_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_23_, v_f_6_);
if (lean_obj_tag(v___x_24_) == 1)
{
lean_object* v_val_25_; 
v_val_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_25_);
lean_dec_ref(v___x_24_);
v_g_11_ = v_val_25_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_object* v___x_26_; 
lean_dec(v___x_24_);
lean_inc(v_f_6_);
v___x_26_ = l_Lean_IR_findDecl___redArg(v_f_6_, v_a_8_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_41_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_41_ == 0)
{
v___x_29_ = v___x_26_;
v_isShared_30_ = v_isSharedCheck_41_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_26_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_41_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___y_32_; 
if (lean_obj_tag(v_a_27_) == 1)
{
lean_object* v_val_38_; 
v_val_38_ = lean_ctor_get(v_a_27_, 0);
lean_inc(v_val_38_);
lean_dec_ref(v_a_27_);
if (lean_obj_tag(v_val_38_) == 0)
{
lean_object* v_info_39_; 
v_info_39_ = lean_ctor_get(v_val_38_, 4);
lean_inc(v_info_39_);
lean_dec_ref(v_val_38_);
if (lean_obj_tag(v_info_39_) == 1)
{
lean_object* v_val_40_; 
lean_del_object(v___x_29_);
v_val_40_ = lean_ctor_get(v_info_39_, 0);
lean_inc(v_val_40_);
lean_dec_ref(v_info_39_);
v_g_11_ = v_val_40_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_dec(v_info_39_);
lean_dec(v_f_6_);
v___y_32_ = v_a_7_;
goto v___jp_31_;
}
}
else
{
lean_dec(v_val_38_);
lean_dec(v_f_6_);
v___y_32_ = v_a_7_;
goto v___jp_31_;
}
}
else
{
lean_dec(v_a_27_);
lean_dec(v_f_6_);
v___y_32_ = v_a_7_;
goto v___jp_31_;
}
v___jp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_33_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___y_32_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v___x_34_);
v___x_36_ = v___x_29_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec_ref(v_a_7_);
lean_dec(v_f_6_);
v_a_42_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_26_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_26_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v_f_6_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_a_7_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___boxed(lean_object* v_f_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_f_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(lean_object* v_f_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_f_58_, v_a_59_, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(lean_object* v_f_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(v_f_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
switch(lean_obj_tag(v_x_70_))
{
case 6:
{
lean_object* v_c_74_; lean_object* v___x_75_; 
v_c_74_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_c_74_);
lean_dec_ref(v_x_70_);
v___x_75_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_74_, v_a_71_, v_a_72_);
return v___x_75_;
}
case 7:
{
lean_object* v_c_76_; lean_object* v___x_77_; 
v_c_76_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_c_76_);
lean_dec_ref(v_x_70_);
v___x_77_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_76_, v_a_71_, v_a_72_);
return v___x_77_;
}
default: 
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec_ref(v_x_70_);
v___x_78_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_a_71_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___redArg___boxed(lean_object* v_x_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr(lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_86_, v_a_87_, v_a_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitExpr___boxed(lean_object* v_x_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_IR_Sorry_visitExpr(v_x_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody(lean_object* v_b_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
switch(lean_obj_tag(v_b_98_))
{
case 0:
{
lean_object* v_e_103_; lean_object* v_b_104_; lean_object* v___x_105_; 
v_e_103_ = lean_ctor_get(v_b_98_, 2);
lean_inc_ref(v_e_103_);
v_b_104_ = lean_ctor_get(v_b_98_, 3);
lean_inc(v_b_104_);
lean_dec_ref(v_b_98_);
v___x_105_ = l_Lean_IR_Sorry_visitExpr___redArg(v_e_103_, v_a_99_, v_a_101_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_fst_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
v_fst_107_ = lean_ctor_get(v_a_106_, 0);
if (lean_obj_tag(v_fst_107_) == 0)
{
lean_dec(v_a_106_);
lean_dec(v_b_104_);
return v___x_105_;
}
else
{
lean_object* v_snd_108_; 
lean_dec_ref(v___x_105_);
v_snd_108_ = lean_ctor_get(v_a_106_, 1);
lean_inc(v_snd_108_);
lean_dec(v_a_106_);
v_b_98_ = v_b_104_;
v_a_99_ = v_snd_108_;
goto _start;
}
}
else
{
lean_dec(v_b_104_);
return v___x_105_;
}
}
case 1:
{
lean_object* v_v_110_; lean_object* v_b_111_; lean_object* v___x_112_; 
v_v_110_ = lean_ctor_get(v_b_98_, 2);
lean_inc(v_v_110_);
v_b_111_ = lean_ctor_get(v_b_98_, 3);
lean_inc(v_b_111_);
lean_dec_ref(v_b_98_);
v___x_112_ = l_Lean_IR_Sorry_visitFnBody(v_v_110_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_fst_114_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
v_fst_114_ = lean_ctor_get(v_a_113_, 0);
if (lean_obj_tag(v_fst_114_) == 0)
{
lean_dec(v_a_113_);
lean_dec(v_b_111_);
return v___x_112_;
}
else
{
lean_object* v_snd_115_; 
lean_dec_ref(v___x_112_);
v_snd_115_ = lean_ctor_get(v_a_113_, 1);
lean_inc(v_snd_115_);
lean_dec(v_a_113_);
v_b_98_ = v_b_111_;
v_a_99_ = v_snd_115_;
goto _start;
}
}
else
{
lean_dec(v_b_111_);
return v___x_112_;
}
}
case 9:
{
lean_object* v_cs_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_cs_117_ = lean_ctor_get(v_b_98_, 3);
lean_inc_ref(v_cs_117_);
lean_dec_ref(v_b_98_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_array_get_size(v_cs_117_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_nat_dec_lt(v___x_118_, v___x_119_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v_cs_117_);
v___x_122_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_99_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_le(v___x_119_, v___x_119_);
if (v___x_125_ == 0)
{
if (v___x_121_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref(v_cs_117_);
v___x_126_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_99_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_119_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_117_, v___x_129_, v___x_130_, v___x_120_, v_a_99_, v_a_100_, v_a_101_);
lean_dec_ref(v_cs_117_);
return v___x_131_;
}
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_119_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_117_, v___x_132_, v___x_133_, v___x_120_, v_a_99_, v_a_100_, v_a_101_);
lean_dec_ref(v_cs_117_);
return v___x_134_;
}
}
}
default: 
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_IR_FnBody_isTerminal(v_b_98_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_IR_FnBody_body(v_b_98_);
lean_dec(v_b_98_);
v_b_98_ = v___x_136_;
goto _start;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_b_98_);
v___x_138_ = ((lean_object*)(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2));
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_99_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(lean_object* v_as_141_, size_t v_i_142_, size_t v_stop_143_, lean_object* v_b_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_eq(v_i_142_, v_stop_143_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_array_uget_borrowed(v_as_141_, v_i_142_);
v___x_151_ = l_Lean_IR_Alt_body(v___x_150_);
v___x_152_ = l_Lean_IR_Sorry_visitFnBody(v___x_151_, v___y_145_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v_fst_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
v_fst_154_ = lean_ctor_get(v_a_153_, 0);
lean_inc(v_fst_154_);
if (lean_obj_tag(v_fst_154_) == 0)
{
lean_dec_ref(v_fst_154_);
lean_dec(v_a_153_);
return v___x_152_;
}
else
{
lean_object* v_snd_155_; lean_object* v_a_156_; size_t v___x_157_; size_t v___x_158_; 
lean_dec_ref(v___x_152_);
v_snd_155_ = lean_ctor_get(v_a_153_, 1);
lean_inc(v_snd_155_);
lean_dec(v_a_153_);
v_a_156_ = lean_ctor_get(v_fst_154_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v_fst_154_);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_add(v_i_142_, v___x_157_);
v_i_142_ = v___x_158_;
v_b_144_ = v_a_156_;
v___y_145_ = v_snd_155_;
goto _start;
}
}
else
{
return v___x_152_;
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_b_144_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___y_145_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(lean_object* v_as_163_, lean_object* v_i_164_, lean_object* v_stop_165_, lean_object* v_b_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
size_t v_i_boxed_171_; size_t v_stop_boxed_172_; lean_object* v_res_173_; 
v_i_boxed_171_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_stop_boxed_172_ = lean_unbox_usize(v_stop_165_);
lean_dec(v_stop_165_);
v_res_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_163_, v_i_boxed_171_, v_stop_boxed_172_, v_b_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec_ref(v_as_163_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitFnBody___boxed(lean_object* v_b_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_IR_Sorry_visitFnBody(v_b_174_, v_a_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl(lean_object* v_d_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
if (lean_obj_tag(v_d_180_) == 0)
{
lean_object* v_f_185_; lean_object* v_body_186_; lean_object* v_localSorryMap_187_; lean_object* v___x_188_; 
v_f_185_ = lean_ctor_get(v_d_180_, 0);
lean_inc(v_f_185_);
v_body_186_ = lean_ctor_get(v_d_180_, 3);
lean_inc(v_body_186_);
lean_dec_ref(v_d_180_);
v_localSorryMap_187_ = lean_ctor_get(v_a_181_, 0);
v___x_188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_187_, v_f_185_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_IR_Sorry_visitFnBody(v_body_186_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_232_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_232_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_232_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_232_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_fst_194_; 
v_fst_194_ = lean_ctor_get(v_a_190_, 0);
if (lean_obj_tag(v_fst_194_) == 0)
{
lean_object* v_snd_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_217_; 
lean_inc_ref(v_fst_194_);
v_snd_195_ = lean_ctor_get(v_a_190_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_a_190_, 0);
lean_dec(v_unused_218_);
v___x_197_ = v_a_190_;
v_isShared_198_ = v_isSharedCheck_217_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_snd_195_);
lean_dec(v_a_190_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_217_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_a_199_; lean_object* v_localSorryMap_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_216_; 
v_a_199_ = lean_ctor_get(v_fst_194_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v_fst_194_);
v_localSorryMap_200_ = lean_ctor_get(v_snd_195_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_snd_195_);
if (v_isSharedCheck_216_ == 0)
{
v___x_202_ = v_snd_195_;
v_isShared_203_ = v_isSharedCheck_216_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_localSorryMap_200_);
lean_dec(v_snd_195_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_216_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_208_; 
v___x_204_ = lean_box(0);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_185_, v_a_199_, v_localSorryMap_200_);
v___x_206_ = 1;
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_205_);
v___x_208_ = v___x_202_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_205_);
v___x_208_ = v_reuseFailAlloc_215_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*1, v___x_206_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_208_);
lean_ctor_set(v___x_197_, 0, v___x_204_);
v___x_210_ = v___x_197_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_210_);
v___x_212_ = v___x_192_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
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
}
}
else
{
lean_object* v_snd_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_230_; 
lean_dec(v_f_185_);
v_snd_219_ = lean_ctor_get(v_a_190_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v_a_190_, 0);
lean_dec(v_unused_231_);
v___x_221_ = v_a_190_;
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snd_219_);
lean_dec(v_a_190_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_snd_219_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_225_);
v___x_227_ = v___x_192_;
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
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_f_185_);
v_a_233_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_189_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_189_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_body_186_);
lean_dec(v_f_185_);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v___x_188_, 0);
lean_dec(v_unused_250_);
v___x_242_ = v___x_188_;
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
else
{
lean_dec(v___x_188_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_244_ = lean_box(0);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_181_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v___x_245_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v_d_180_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_a_181_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_visitDecl___boxed(lean_object* v_d_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_IR_Sorry_visitDecl(v_d_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(lean_object* v_as_260_, size_t v_i_261_, size_t v_stop_262_, lean_object* v_b_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_eq(v_i_261_, v_stop_262_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_array_uget_borrowed(v_as_260_, v_i_261_);
lean_inc(v___x_269_);
v___x_270_ = l_Lean_IR_Sorry_visitDecl(v___x_269_, v___y_264_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; size_t v___x_274_; size_t v___x_275_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
v_fst_272_ = lean_ctor_get(v_a_271_, 0);
lean_inc(v_fst_272_);
v_snd_273_ = lean_ctor_get(v_a_271_, 1);
lean_inc(v_snd_273_);
lean_dec(v_a_271_);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_add(v_i_261_, v___x_274_);
v_i_261_ = v___x_275_;
v_b_263_ = v_fst_272_;
v___y_264_ = v_snd_273_;
goto _start;
}
else
{
return v___x_270_;
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_b_263_);
lean_ctor_set(v___x_277_, 1, v___y_264_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(lean_object* v_as_279_, lean_object* v_i_280_, lean_object* v_stop_281_, lean_object* v_b_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
size_t v_i_boxed_287_; size_t v_stop_boxed_288_; lean_object* v_res_289_; 
v_i_boxed_287_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_stop_boxed_288_ = lean_unbox_usize(v_stop_281_);
lean_dec(v_stop_281_);
v_res_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_279_, v_i_boxed_287_, v_stop_boxed_288_, v_b_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec_ref(v_as_279_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect(lean_object* v_decls_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_snd_296_; lean_object* v___y_301_; lean_object* v_localSorryMap_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_325_; 
v_localSorryMap_306_ = lean_ctor_get(v_a_291_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_325_ == 0)
{
v___x_308_ = v_a_291_;
v_isShared_309_ = v_isSharedCheck_325_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_localSorryMap_306_);
lean_dec(v_a_291_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_325_;
goto v_resetjp_307_;
}
v___jp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_snd_296_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
v___jp_300_:
{
if (lean_obj_tag(v___y_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_snd_303_; uint8_t v_modified_304_; 
v_a_302_ = lean_ctor_get(v___y_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref(v___y_301_);
v_snd_303_ = lean_ctor_get(v_a_302_, 1);
lean_inc(v_snd_303_);
lean_dec(v_a_302_);
v_modified_304_ = lean_ctor_get_uint8(v_snd_303_, sizeof(void*)*1);
if (v_modified_304_ == 0)
{
v_snd_296_ = v_snd_303_;
goto v___jp_295_;
}
else
{
v_a_291_ = v_snd_303_;
goto _start;
}
}
else
{
return v___y_301_;
}
}
v_resetjp_307_:
{
uint8_t v___x_310_; lean_object* v___x_312_; 
v___x_310_ = 0;
if (v_isShared_309_ == 0)
{
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_localSorryMap_306_);
v___x_312_ = v_reuseFailAlloc_324_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_310_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_decls_290_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
v_snd_296_ = v___x_312_;
goto v___jp_295_;
}
else
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_box(0);
v___x_317_ = lean_nat_dec_le(v___x_314_, v___x_314_);
if (v___x_317_ == 0)
{
if (v___x_315_ == 0)
{
v_snd_296_ = v___x_312_;
goto v___jp_295_;
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_314_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_290_, v___x_318_, v___x_319_, v___x_316_, v___x_312_, v_a_292_, v_a_293_);
v___y_301_ = v___x_320_;
goto v___jp_300_;
}
}
else
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((size_t)0ULL);
v___x_322_ = lean_usize_of_nat(v___x_314_);
v___x_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_290_, v___x_321_, v___x_322_, v___x_316_, v___x_312_, v_a_292_, v_a_293_);
v___y_301_ = v___x_323_;
goto v___jp_300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Sorry_collect___boxed(lean_object* v_decls_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_IR_Sorry_collect(v_decls_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec_ref(v_decls_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(lean_object* v_snd_332_, size_t v_sz_333_, size_t v_i_334_, lean_object* v_bs_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_usize_dec_lt(v_i_334_, v_sz_333_);
if (v___x_336_ == 0)
{
return v_bs_335_;
}
else
{
lean_object* v_v_337_; lean_object* v___x_338_; lean_object* v_bs_x27_339_; lean_object* v___y_341_; 
v_v_337_ = lean_array_uget(v_bs_335_, v_i_334_);
v___x_338_ = lean_unsigned_to_nat(0u);
v_bs_x27_339_ = lean_array_uset(v_bs_335_, v_i_334_, v___x_338_);
if (lean_obj_tag(v_v_337_) == 0)
{
lean_object* v_f_346_; lean_object* v_xs_347_; lean_object* v_type_348_; lean_object* v_body_349_; lean_object* v_localSorryMap_350_; lean_object* v___x_351_; 
v_f_346_ = lean_ctor_get(v_v_337_, 0);
v_xs_347_ = lean_ctor_get(v_v_337_, 1);
v_type_348_ = lean_ctor_get(v_v_337_, 2);
v_body_349_ = lean_ctor_get(v_v_337_, 3);
v_localSorryMap_350_ = lean_ctor_get(v_snd_332_, 0);
v___x_351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_350_, v_f_346_);
if (lean_obj_tag(v___x_351_) == 1)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_inc(v_body_349_);
lean_inc(v_type_348_);
lean_inc_ref(v_xs_347_);
lean_inc(v_f_346_);
v_isSharedCheck_358_ = !lean_is_exclusive(v_v_337_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_359_ = lean_ctor_get(v_v_337_, 4);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_v_337_, 3);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_v_337_, 2);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_v_337_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_v_337_, 0);
lean_dec(v_unused_363_);
v___x_353_ = v_v_337_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_v_337_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 4, v___x_351_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_f_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_xs_347_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_type_348_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_body_349_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v___x_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v___y_341_ = v___x_356_;
goto v___jp_340_;
}
}
}
else
{
lean_dec(v___x_351_);
v___y_341_ = v_v_337_;
goto v___jp_340_;
}
}
else
{
v___y_341_ = v_v_337_;
goto v___jp_340_;
}
v___jp_340_:
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_334_, v___x_342_);
v___x_344_ = lean_array_uset(v_bs_x27_339_, v_i_334_, v___y_341_);
v_i_334_ = v___x_343_;
v_bs_335_ = v___x_344_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(lean_object* v_snd_364_, lean_object* v_sz_365_, lean_object* v_i_366_, lean_object* v_bs_367_){
_start:
{
size_t v_sz_boxed_368_; size_t v_i_boxed_369_; lean_object* v_res_370_; 
v_sz_boxed_368_ = lean_unbox_usize(v_sz_365_);
lean_dec(v_sz_365_);
v_i_boxed_369_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_364_, v_sz_boxed_368_, v_i_boxed_369_, v_bs_367_);
lean_dec_ref(v_snd_364_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep(lean_object* v_decls_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_IR_updateSorryDep___closed__0));
v___x_379_ = l_Lean_IR_Sorry_collect(v_decls_374_, v___x_378_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_391_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_391_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_snd_384_; size_t v_sz_385_; size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v_snd_384_ = lean_ctor_get(v_a_380_, 1);
lean_inc(v_snd_384_);
lean_dec(v_a_380_);
v_sz_385_ = lean_array_size(v_decls_374_);
v___x_386_ = ((size_t)0ULL);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_384_, v_sz_385_, v___x_386_, v_decls_374_);
lean_dec(v_snd_384_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_387_);
v___x_389_ = v___x_382_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_decls_374_);
v_a_392_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_379_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_379_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_updateSorryDep___boxed(lean_object* v_decls_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_IR_updateSorryDep(v_decls_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_404_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
