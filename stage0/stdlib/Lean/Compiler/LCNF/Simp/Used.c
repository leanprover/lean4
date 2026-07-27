// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Used
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM import Init.Omega
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object* v_fvarId_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_subst_5_; lean_object* v_used_6_; lean_object* v_binderRenaming_7_; lean_object* v_funDeclInfoMap_8_; uint8_t v_simplified_9_; lean_object* v_visited_10_; lean_object* v_inline_11_; lean_object* v_inlineLocal_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_23_; 
v___x_4_ = lean_st_ref_take(v_a_2_);
v_subst_5_ = lean_ctor_get(v___x_4_, 0);
v_used_6_ = lean_ctor_get(v___x_4_, 1);
v_binderRenaming_7_ = lean_ctor_get(v___x_4_, 2);
v_funDeclInfoMap_8_ = lean_ctor_get(v___x_4_, 3);
v_simplified_9_ = lean_ctor_get_uint8(v___x_4_, sizeof(void*)*7);
v_visited_10_ = lean_ctor_get(v___x_4_, 4);
v_inline_11_ = lean_ctor_get(v___x_4_, 5);
v_inlineLocal_12_ = lean_ctor_get(v___x_4_, 6);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_23_ == 0)
{
v___x_14_ = v___x_4_;
v_isShared_15_ = v_isSharedCheck_23_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_inlineLocal_12_);
lean_inc(v_inline_11_);
lean_inc(v_visited_10_);
lean_inc(v_funDeclInfoMap_8_);
lean_inc(v_binderRenaming_7_);
lean_inc(v_used_6_);
lean_inc(v_subst_5_);
lean_dec(v___x_4_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_23_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; lean_object* v___x_18_; 
v___x_16_ = l_Lean_FVarIdSet_insert(v_used_6_, v_fvarId_1_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v___x_16_);
v___x_18_ = v___x_14_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_subst_5_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v___x_16_);
lean_ctor_set(v_reuseFailAlloc_22_, 2, v_binderRenaming_7_);
lean_ctor_set(v_reuseFailAlloc_22_, 3, v_funDeclInfoMap_8_);
lean_ctor_set(v_reuseFailAlloc_22_, 4, v_visited_10_);
lean_ctor_set(v_reuseFailAlloc_22_, 5, v_inline_11_);
lean_ctor_set(v_reuseFailAlloc_22_, 6, v_inlineLocal_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_22_, sizeof(void*)*7, v_simplified_9_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_st_ref_set(v_a_2_, v___x_18_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(lean_object* v_fvarId_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_24_, v_a_25_);
lean_dec(v_a_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object* v_fvarId_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_28_, v_a_30_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object* v_fvarId_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar(v_fvarId_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object* v_arg_48_, lean_object* v_a_49_){
_start:
{
if (lean_obj_tag(v_arg_48_) == 1)
{
lean_object* v_fvarId_51_; lean_object* v___x_52_; 
v_fvarId_51_ = lean_ctor_get(v_arg_48_, 0);
lean_inc(v_fvarId_51_);
lean_dec_ref_known(v_arg_48_, 1);
v___x_52_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_51_, v_a_49_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_arg_48_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(lean_object* v_arg_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_55_, v_a_56_);
lean_dec(v_a_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg(lean_object* v_arg_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_59_, v_a_61_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(lean_object* v_arg_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Compiler_LCNF_Simp_markUsedArg(v_arg_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object* v_as_79_, size_t v_i_80_, size_t v_stop_81_, lean_object* v_b_82_, lean_object* v___y_83_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = lean_usize_dec_eq(v_i_80_, v_stop_81_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_array_uget_borrowed(v_as_79_, v_i_80_);
lean_inc(v___x_86_);
v___x_87_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_86_, v___y_83_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; size_t v___x_89_; size_t v___x_90_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_add(v_i_80_, v___x_89_);
v_i_80_ = v___x_90_;
v_b_82_ = v_a_88_;
goto _start;
}
else
{
return v___x_87_;
}
}
else
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v_b_82_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(lean_object* v_as_93_, lean_object* v_i_94_, lean_object* v_stop_95_, lean_object* v_b_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
size_t v_i_boxed_99_; size_t v_stop_boxed_100_; lean_object* v_res_101_; 
v_i_boxed_99_ = lean_unbox_usize(v_i_94_);
lean_dec(v_i_94_);
v_stop_boxed_100_ = lean_unbox_usize(v_stop_95_);
lean_dec(v_stop_95_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_93_, v_i_boxed_99_, v_stop_boxed_100_, v_b_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v_as_93_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue(lean_object* v_e_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
switch(lean_obj_tag(v_e_102_))
{
case 0:
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
v_isSharedCheck_118_ = !lean_is_exclusive(v_e_102_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v_e_102_, 0);
lean_dec(v_unused_119_);
v___x_112_ = v_e_102_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_e_102_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_box(0);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_114_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
case 1:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_box(0);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
case 2:
{
lean_object* v_struct_122_; lean_object* v___x_123_; 
v_struct_122_ = lean_ctor_get(v_e_102_, 2);
lean_inc(v_struct_122_);
lean_dec_ref_known(v_e_102_, 3);
v___x_123_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_struct_122_, v_a_104_);
return v___x_123_;
}
case 3:
{
lean_object* v_args_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_args_124_ = lean_ctor_get(v_e_102_, 2);
lean_inc_ref(v_args_124_);
lean_dec_ref_known(v_e_102_, 3);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_array_get_size(v_args_124_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec_ref(v_args_124_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_le(v___x_126_, v___x_126_);
if (v___x_130_ == 0)
{
if (v___x_128_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v_args_124_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_127_);
return v___x_131_;
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_126_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_124_, v___x_132_, v___x_133_, v___x_127_, v_a_104_);
lean_dec_ref(v_args_124_);
return v___x_134_;
}
}
else
{
size_t v___x_135_; size_t v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_126_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_124_, v___x_135_, v___x_136_, v___x_127_, v_a_104_);
lean_dec_ref(v_args_124_);
return v___x_137_;
}
}
}
default: 
{
lean_object* v_fvarId_138_; lean_object* v_args_139_; lean_object* v___x_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_161_; 
v_fvarId_138_ = lean_ctor_get(v_e_102_, 0);
lean_inc(v_fvarId_138_);
v_args_139_ = lean_ctor_get(v_e_102_, 1);
lean_inc_ref(v_args_139_);
lean_dec_ref_known(v_e_102_, 2);
v___x_140_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_138_, v_a_104_);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_140_, 0);
lean_dec(v_unused_162_);
v___x_142_ = v___x_140_;
v_isShared_143_ = v_isSharedCheck_161_;
goto v_resetjp_141_;
}
else
{
lean_dec(v___x_140_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_161_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_array_get_size(v_args_139_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_nat_dec_lt(v___x_144_, v___x_145_);
if (v___x_147_ == 0)
{
lean_object* v___x_149_; 
lean_dec_ref(v_args_139_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_146_);
v___x_149_ = v___x_142_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_146_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_le(v___x_145_, v___x_145_);
if (v___x_151_ == 0)
{
if (v___x_147_ == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v_args_139_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_146_);
v___x_153_ = v___x_142_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_146_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
else
{
size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
lean_del_object(v___x_142_);
v___x_155_ = ((size_t)0ULL);
v___x_156_ = lean_usize_of_nat(v___x_145_);
v___x_157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_139_, v___x_155_, v___x_156_, v___x_146_, v_a_104_);
lean_dec_ref(v_args_139_);
return v___x_157_;
}
}
else
{
size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; 
lean_del_object(v___x_142_);
v___x_158_ = ((size_t)0ULL);
v___x_159_ = lean_usize_of_nat(v___x_145_);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_139_, v___x_158_, v___x_159_, v___x_146_, v_a_104_);
lean_dec_ref(v_args_139_);
return v___x_160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object* v_e_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_e_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object* v_as_173_, size_t v_i_174_, size_t v_stop_175_, lean_object* v_b_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_173_, v_i_174_, v_stop_175_, v_b_176_, v___y_178_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object* v_as_186_, lean_object* v_i_187_, lean_object* v_stop_188_, lean_object* v_b_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
size_t v_i_boxed_198_; size_t v_stop_boxed_199_; lean_object* v_res_200_; 
v_i_boxed_198_ = lean_unbox_usize(v_i_187_);
lean_dec(v_i_187_);
v_stop_boxed_199_ = lean_unbox_usize(v_stop_188_);
lean_dec(v_stop_188_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_186_, v_i_boxed_198_, v_stop_boxed_199_, v_b_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec_ref(v_as_186_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object* v_letDecl_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_value_210_; lean_object* v___x_211_; 
v_value_210_ = lean_ctor_get(v_letDecl_201_, 3);
lean_inc(v_value_210_);
lean_dec_ref(v_letDecl_201_);
v___x_211_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_value_210_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object* v_letDecl_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_letDecl_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_, lean_object* v_b_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___y_235_; uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_eq(v_i_223_, v_stop_224_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_array_uget_borrowed(v_as_222_, v_i_223_);
switch(lean_obj_tag(v___x_242_))
{
case 0:
{
lean_object* v_code_243_; 
v_code_243_ = lean_ctor_get(v___x_242_, 2);
lean_inc_ref(v_code_243_);
v___y_235_ = v_code_243_;
goto v___jp_234_;
}
case 1:
{
lean_object* v_code_244_; 
v_code_244_ = lean_ctor_get(v___x_242_, 1);
lean_inc_ref(v_code_244_);
v___y_235_ = v_code_244_;
goto v___jp_234_;
}
default: 
{
lean_object* v_code_245_; 
v_code_245_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_code_245_);
v___y_235_ = v_code_245_;
goto v___jp_234_;
}
}
}
else
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_225_);
return v___x_246_;
}
v___jp_234_:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v___y_235_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; size_t v___x_238_; size_t v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_223_, v___x_238_);
v_i_223_ = v___x_239_;
v_b_225_ = v_a_237_;
goto _start;
}
else
{
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object* v_code_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_decl_257_; lean_object* v_k_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; 
switch(lean_obj_tag(v_code_247_))
{
case 0:
{
lean_object* v_decl_268_; lean_object* v_k_269_; lean_object* v___x_270_; 
v_decl_268_ = lean_ctor_get(v_code_247_, 0);
lean_inc_ref(v_decl_268_);
v_k_269_ = lean_ctor_get(v_code_247_, 1);
lean_inc_ref(v_k_269_);
lean_dec_ref_known(v_code_247_, 2);
v___x_270_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_268_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_dec_ref_known(v___x_270_, 1);
v_code_247_ = v_k_269_;
goto _start;
}
else
{
lean_dec_ref(v_k_269_);
return v___x_270_;
}
}
case 3:
{
lean_object* v_fvarId_272_; lean_object* v_args_273_; lean_object* v___x_274_; 
v_fvarId_272_ = lean_ctor_get(v_code_247_, 0);
lean_inc(v_fvarId_272_);
v_args_273_ = lean_ctor_get(v_code_247_, 1);
lean_inc_ref(v_args_273_);
lean_dec_ref_known(v_code_247_, 2);
v___x_274_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_272_, v_a_249_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_296_);
v___x_276_ = v___x_274_;
v_isShared_277_ = v_isSharedCheck_295_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___x_274_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_295_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_array_get_size(v_args_273_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_281_ == 0)
{
lean_object* v___x_283_; 
lean_dec_ref(v_args_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_280_);
v___x_283_ = v___x_276_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_280_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
uint8_t v___x_285_; 
v___x_285_ = lean_nat_dec_le(v___x_279_, v___x_279_);
if (v___x_285_ == 0)
{
if (v___x_281_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref(v_args_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_280_);
v___x_287_ = v___x_276_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_280_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
lean_del_object(v___x_276_);
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_279_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_273_, v___x_289_, v___x_290_, v___x_280_, v_a_249_);
lean_dec_ref(v_args_273_);
return v___x_291_;
}
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
lean_del_object(v___x_276_);
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_279_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_273_, v___x_292_, v___x_293_, v___x_280_, v_a_249_);
lean_dec_ref(v_args_273_);
return v___x_294_;
}
}
}
}
else
{
lean_dec_ref(v_args_273_);
return v___x_274_;
}
}
case 4:
{
lean_object* v_cases_297_; lean_object* v_discr_298_; lean_object* v_alts_299_; lean_object* v___x_300_; 
v_cases_297_ = lean_ctor_get(v_code_247_, 0);
lean_inc_ref(v_cases_297_);
lean_dec_ref_known(v_code_247_, 1);
v_discr_298_ = lean_ctor_get(v_cases_297_, 2);
lean_inc(v_discr_298_);
v_alts_299_ = lean_ctor_get(v_cases_297_, 3);
lean_inc_ref(v_alts_299_);
lean_dec_ref(v_cases_297_);
v___x_300_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_discr_298_, v_a_249_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_321_; 
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_300_, 0);
lean_dec(v_unused_322_);
v___x_302_ = v___x_300_;
v_isShared_303_ = v_isSharedCheck_321_;
goto v_resetjp_301_;
}
else
{
lean_dec(v___x_300_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_321_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_array_get_size(v_alts_299_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_nat_dec_lt(v___x_304_, v___x_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v_alts_299_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_306_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_306_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_le(v___x_305_, v___x_305_);
if (v___x_311_ == 0)
{
if (v___x_307_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref(v_alts_299_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_306_);
v___x_313_ = v___x_302_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_306_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
lean_del_object(v___x_302_);
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_305_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_299_, v___x_315_, v___x_316_, v___x_306_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec_ref(v_alts_299_);
return v___x_317_;
}
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
lean_del_object(v___x_302_);
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_305_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_299_, v___x_318_, v___x_319_, v___x_306_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec_ref(v_alts_299_);
return v___x_320_;
}
}
}
}
else
{
lean_dec_ref(v_alts_299_);
return v___x_300_;
}
}
case 5:
{
lean_object* v_fvarId_323_; lean_object* v___x_324_; 
v_fvarId_323_ = lean_ctor_get(v_code_247_, 0);
lean_inc(v_fvarId_323_);
lean_dec_ref_known(v_code_247_, 1);
v___x_324_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_323_, v_a_249_);
return v___x_324_;
}
case 6:
{
lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v_code_247_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v_code_247_, 0);
lean_dec(v_unused_333_);
v___x_326_ = v_code_247_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_dec(v_code_247_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_box(0);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 0);
lean_ctor_set(v___x_326_, 0, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
default: 
{
lean_object* v_decl_334_; lean_object* v_k_335_; 
v_decl_334_ = lean_ctor_get(v_code_247_, 0);
lean_inc_ref(v_decl_334_);
v_k_335_ = lean_ctor_get(v_code_247_, 1);
lean_inc_ref(v_k_335_);
lean_dec_ref(v_code_247_);
v_decl_257_ = v_decl_334_;
v_k_258_ = v_k_335_;
v___y_259_ = v_a_248_;
v___y_260_ = v_a_249_;
v___y_261_ = v_a_250_;
v___y_262_ = v_a_251_;
v___y_263_ = v_a_252_;
v___y_264_ = v_a_253_;
v___y_265_ = v_a_254_;
goto v___jp_256_;
}
}
v___jp_256_:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_257_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_dec_ref_known(v___x_266_, 1);
v_code_247_ = v_k_258_;
v_a_248_ = v___y_259_;
v_a_249_ = v___y_260_;
v_a_250_ = v___y_261_;
v_a_251_ = v___y_262_;
v_a_252_ = v___y_263_;
v_a_253_ = v___y_264_;
v_a_254_ = v___y_265_;
goto _start;
}
else
{
lean_dec_ref(v_k_258_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object* v_funDecl_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_value_345_; lean_object* v___x_346_; 
v_value_345_ = lean_ctor_get(v_funDecl_336_, 4);
lean_inc_ref(v_value_345_);
lean_dec_ref(v_funDecl_336_);
v___x_346_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_value_345_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object* v_funDecl_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_funDecl_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object* v_as_357_, lean_object* v_i_358_, lean_object* v_stop_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
size_t v_i_boxed_369_; size_t v_stop_boxed_370_; lean_object* v_res_371_; 
v_i_boxed_369_ = lean_unbox_usize(v_i_358_);
lean_dec(v_i_358_);
v_stop_boxed_370_ = lean_unbox_usize(v_stop_359_);
lean_dec(v_stop_359_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_357_, v_i_boxed_369_, v_stop_boxed_370_, v_b_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v_as_357_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object* v_code_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_code_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_381_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object* v_k_382_, lean_object* v_t_383_){
_start:
{
if (lean_obj_tag(v_t_383_) == 0)
{
lean_object* v_k_384_; lean_object* v_l_385_; lean_object* v_r_386_; uint8_t v___x_387_; 
v_k_384_ = lean_ctor_get(v_t_383_, 1);
v_l_385_ = lean_ctor_get(v_t_383_, 3);
v_r_386_ = lean_ctor_get(v_t_383_, 4);
v___x_387_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_382_, v_k_384_);
switch(v___x_387_)
{
case 0:
{
v_t_383_ = v_l_385_;
goto _start;
}
case 1:
{
uint8_t v___x_389_; 
v___x_389_ = 1;
return v___x_389_;
}
default: 
{
v_t_383_ = v_r_386_;
goto _start;
}
}
}
else
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object* v_k_392_, lean_object* v_t_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_392_, v_t_393_);
lean_dec(v_t_393_);
lean_dec(v_k_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object* v_fvarId_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_used_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_399_ = lean_st_ref_get(v_a_397_);
v_used_400_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_used_400_);
lean_dec(v___x_399_);
v___x_401_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_fvarId_396_, v_used_400_);
lean_dec(v_used_400_);
v___x_402_ = lean_box(v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object* v_fvarId_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec(v_fvarId_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object* v_fvarId_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_408_, v_a_410_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object* v_fvarId_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Compiler_LCNF_Simp_isUsed(v_fvarId_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_fvarId_418_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object* v_00_u03b2_428_, lean_object* v_k_429_, lean_object* v_t_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_429_, v_t_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object* v_00_u03b2_432_, lean_object* v_k_433_, lean_object* v_t_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(v_00_u03b2_432_, v_k_433_, v_t_434_);
lean_dec(v_t_434_);
lean_dec(v_k_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0(void){
_start:
{
uint8_t v___x_437_; lean_object* v___x_438_; 
v___x_437_ = 0;
v___x_438_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object* v_decls_439_, lean_object* v_i_440_, lean_object* v_code_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_lt(v___x_450_, v_i_440_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec(v_i_440_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_code_441_);
return v___x_452_;
}
else
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_decl_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_a_460_; uint8_t v___x_461_; 
v___x_453_ = 0;
v___x_454_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_sub(v_i_440_, v___x_455_);
lean_dec(v_i_440_);
v_decl_457_ = lean_array_get_borrowed(v___x_454_, v_decls_439_, v___x_456_);
v___x_458_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_457_);
v___x_459_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_458_, v_a_443_);
lean_dec(v___x_458_);
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_459_);
v___x_461_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_453_, v_decl_457_, v_a_446_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_dec_ref_known(v___x_462_, 1);
v_i_440_ = v___x_456_;
goto _start;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v___x_456_);
lean_dec_ref(v_code_441_);
v_a_464_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_462_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
switch(lean_obj_tag(v_decl_457_))
{
case 0:
{
lean_object* v_decl_472_; lean_object* v___x_473_; 
v_decl_472_ = lean_ctor_get(v_decl_457_, 0);
lean_inc_ref(v_decl_472_);
v___x_473_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_472_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v___x_474_; 
lean_dec_ref_known(v___x_473_, 1);
lean_inc_ref(v_decl_472_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_decl_472_);
lean_ctor_set(v___x_474_, 1, v_code_441_);
v_i_440_ = v___x_456_;
v_code_441_ = v___x_474_;
goto _start;
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v___x_456_);
lean_dec_ref(v_code_441_);
v_a_476_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_473_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_473_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
case 1:
{
lean_object* v_decl_484_; lean_object* v___x_485_; 
v_decl_484_ = lean_ctor_get(v_decl_457_, 0);
lean_inc_ref(v_decl_484_);
v___x_485_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_484_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v___x_486_; 
lean_dec_ref_known(v___x_485_, 1);
lean_inc_ref(v_decl_484_);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v_decl_484_);
lean_ctor_set(v___x_486_, 1, v_code_441_);
v_i_440_ = v___x_456_;
v_code_441_ = v___x_486_;
goto _start;
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v___x_456_);
lean_dec_ref(v_code_441_);
v_a_488_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_485_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
default: 
{
lean_object* v_decl_496_; lean_object* v___x_497_; 
v_decl_496_ = lean_ctor_get(v_decl_457_, 0);
lean_inc_ref(v_decl_496_);
v___x_497_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_496_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; 
lean_dec_ref_known(v___x_497_, 1);
lean_inc_ref(v_decl_496_);
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v_decl_496_);
lean_ctor_set(v___x_498_, 1, v_code_441_);
v_i_440_ = v___x_456_;
v_code_441_ = v___x_498_;
goto _start;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v___x_456_);
lean_dec_ref(v_code_441_);
v_a_500_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_497_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object* v_decls_508_, lean_object* v_i_509_, lean_object* v_code_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_508_, v_i_509_, v_code_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec_ref(v_decls_508_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object* v_decl_520_, lean_object* v_h__1_521_, lean_object* v_h__2_522_, lean_object* v_h__3_523_){
_start:
{
switch(lean_obj_tag(v_decl_520_))
{
case 0:
{
lean_object* v_decl_524_; lean_object* v___x_525_; 
lean_dec(v_h__3_523_);
lean_dec(v_h__2_522_);
v_decl_524_ = lean_ctor_get(v_decl_520_, 0);
lean_inc_ref(v_decl_524_);
lean_dec_ref_known(v_decl_520_, 1);
v___x_525_ = lean_apply_1(v_h__1_521_, v_decl_524_);
return v___x_525_;
}
case 1:
{
lean_object* v_decl_526_; lean_object* v___x_527_; 
lean_dec(v_h__3_523_);
lean_dec(v_h__1_521_);
v_decl_526_ = lean_ctor_get(v_decl_520_, 0);
lean_inc_ref(v_decl_526_);
lean_dec_ref_known(v_decl_520_, 1);
v___x_527_ = lean_apply_1(v_h__2_522_, v_decl_526_);
return v___x_527_;
}
default: 
{
lean_object* v_decl_528_; lean_object* v___x_529_; 
lean_dec(v_h__2_522_);
lean_dec(v_h__1_521_);
v_decl_528_ = lean_ctor_get(v_decl_520_, 0);
lean_inc_ref(v_decl_528_);
lean_dec_ref_known(v_decl_520_, 1);
v___x_529_ = lean_apply_1(v_h__3_523_, v_decl_528_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object* v_motive_530_, lean_object* v_decl_531_, lean_object* v_h__1_532_, lean_object* v_h__2_533_, lean_object* v_h__3_534_){
_start:
{
switch(lean_obj_tag(v_decl_531_))
{
case 0:
{
lean_object* v_decl_535_; lean_object* v___x_536_; 
lean_dec(v_h__3_534_);
lean_dec(v_h__2_533_);
v_decl_535_ = lean_ctor_get(v_decl_531_, 0);
lean_inc_ref(v_decl_535_);
lean_dec_ref_known(v_decl_531_, 1);
v___x_536_ = lean_apply_1(v_h__1_532_, v_decl_535_);
return v___x_536_;
}
case 1:
{
lean_object* v_decl_537_; lean_object* v___x_538_; 
lean_dec(v_h__3_534_);
lean_dec(v_h__1_532_);
v_decl_537_ = lean_ctor_get(v_decl_531_, 0);
lean_inc_ref(v_decl_537_);
lean_dec_ref_known(v_decl_531_, 1);
v___x_538_ = lean_apply_1(v_h__2_533_, v_decl_537_);
return v___x_538_;
}
default: 
{
lean_object* v_decl_539_; lean_object* v___x_540_; 
lean_dec(v_h__2_533_);
lean_dec(v_h__1_532_);
v_decl_539_ = lean_ctor_get(v_decl_531_, 0);
lean_inc_ref(v_decl_539_);
lean_dec_ref_known(v_decl_531_, 1);
v___x_540_ = lean_apply_1(v_h__3_534_, v_decl_539_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object* v_decls_541_, lean_object* v_code_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_array_get_size(v_decls_541_);
v___x_552_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_541_, v___x_551_, v_code_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object* v_decls_553_, lean_object* v_code_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_decls_553_, v_code_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_decls_553_);
return v_res_563_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
}
#ifdef __cplusplus
}
#endif
