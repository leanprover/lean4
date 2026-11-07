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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
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
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_16_ = lean_box(0);
v___x_17_ = l_Lean_FVarIdSet_insert(v_used_6_, v_fvarId_1_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v___x_17_);
v___x_19_ = v___x_14_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_subst_5_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_22_, 2, v_binderRenaming_7_);
lean_ctor_set(v_reuseFailAlloc_22_, 3, v_funDeclInfoMap_8_);
lean_ctor_set(v_reuseFailAlloc_22_, 4, v_visited_10_);
lean_ctor_set(v_reuseFailAlloc_22_, 5, v_inline_11_);
lean_ctor_set(v_reuseFailAlloc_22_, 6, v_inlineLocal_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_22_, sizeof(void*)*7, v_simplified_9_);
v___x_19_ = v_reuseFailAlloc_22_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_st_ref_put(v_a_2_, v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_16_);
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
case 2:
{
lean_object* v_struct_111_; lean_object* v___x_112_; 
v_struct_111_ = lean_ctor_get(v_e_102_, 2);
lean_inc(v_struct_111_);
lean_dec_ref_known(v_e_102_, 3);
v___x_112_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_struct_111_, v_a_104_);
return v___x_112_;
}
case 3:
{
lean_object* v_args_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_args_113_ = lean_ctor_get(v_e_102_, 2);
lean_inc_ref(v_args_113_);
lean_dec_ref_known(v_e_102_, 3);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_array_get_size(v_args_113_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_nat_dec_lt(v___x_114_, v___x_115_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v_args_113_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
return v___x_118_;
}
else
{
size_t v___x_119_; size_t v___x_120_; lean_object* v___x_121_; 
v___x_119_ = ((size_t)0ULL);
v___x_120_ = lean_usize_of_nat(v___x_115_);
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_113_, v___x_119_, v___x_120_, v___x_116_, v_a_104_);
lean_dec_ref(v_args_113_);
return v___x_121_;
}
}
case 4:
{
lean_object* v_fvarId_122_; lean_object* v_args_123_; lean_object* v___x_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_138_; 
v_fvarId_122_ = lean_ctor_get(v_e_102_, 0);
lean_inc(v_fvarId_122_);
v_args_123_ = lean_ctor_get(v_e_102_, 1);
lean_inc_ref(v_args_123_);
lean_dec_ref_known(v_e_102_, 2);
v___x_124_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_122_, v_a_104_);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_139_);
v___x_126_ = v___x_124_;
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
else
{
lean_dec(v___x_124_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_array_get_size(v_args_123_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_nat_dec_lt(v___x_128_, v___x_129_);
if (v___x_131_ == 0)
{
lean_object* v___x_133_; 
lean_dec_ref(v_args_123_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_130_);
v___x_133_ = v___x_126_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
size_t v___x_135_; size_t v___x_136_; lean_object* v___x_137_; 
lean_del_object(v___x_126_);
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_129_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_123_, v___x_135_, v___x_136_, v___x_130_, v_a_104_);
lean_dec_ref(v_args_123_);
return v___x_137_;
}
}
}
default: 
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_e_102_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object* v_e_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_e_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object* v_as_152_, size_t v_i_153_, size_t v_stop_154_, lean_object* v_b_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_152_, v_i_153_, v_stop_154_, v_b_155_, v___y_157_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object* v_as_165_, lean_object* v_i_166_, lean_object* v_stop_167_, lean_object* v_b_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
size_t v_i_boxed_177_; size_t v_stop_boxed_178_; lean_object* v_res_179_; 
v_i_boxed_177_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_167_);
lean_dec(v_stop_167_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_165_, v_i_boxed_177_, v_stop_boxed_178_, v_b_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec_ref(v_as_165_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object* v_letDecl_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_value_189_; lean_object* v___x_190_; 
v_value_189_ = lean_ctor_get(v_letDecl_180_, 3);
lean_inc(v_value_189_);
lean_dec_ref(v_letDecl_180_);
v___x_190_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_value_189_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object* v_letDecl_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_letDecl_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object* v_as_201_, size_t v_i_202_, size_t v_stop_203_, lean_object* v_b_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___y_214_; uint8_t v___x_220_; 
v___x_220_ = lean_usize_dec_eq(v_i_202_, v_stop_203_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_array_uget_borrowed(v_as_201_, v_i_202_);
switch(lean_obj_tag(v___x_221_))
{
case 0:
{
lean_object* v_code_222_; 
v_code_222_ = lean_ctor_get(v___x_221_, 2);
lean_inc_ref(v_code_222_);
v___y_214_ = v_code_222_;
goto v___jp_213_;
}
case 1:
{
lean_object* v_code_223_; 
v_code_223_ = lean_ctor_get(v___x_221_, 1);
lean_inc_ref(v_code_223_);
v___y_214_ = v_code_223_;
goto v___jp_213_;
}
default: 
{
lean_object* v_code_224_; 
v_code_224_ = lean_ctor_get(v___x_221_, 0);
lean_inc_ref(v_code_224_);
v___y_214_ = v_code_224_;
goto v___jp_213_;
}
}
}
else
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_b_204_);
return v___x_225_;
}
v___jp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v___y_214_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; size_t v___x_217_; size_t v___x_218_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_202_, v___x_217_);
v_i_202_ = v___x_218_;
v_b_204_ = v_a_216_;
goto _start;
}
else
{
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object* v_code_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_decl_236_; lean_object* v_k_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; 
switch(lean_obj_tag(v_code_226_))
{
case 0:
{
lean_object* v_decl_247_; lean_object* v_k_248_; lean_object* v___x_249_; 
v_decl_247_ = lean_ctor_get(v_code_226_, 0);
lean_inc_ref(v_decl_247_);
v_k_248_ = lean_ctor_get(v_code_226_, 1);
lean_inc_ref(v_k_248_);
lean_dec_ref_known(v_code_226_, 2);
v___x_249_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_247_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_dec_ref_known(v___x_249_, 1);
v_code_226_ = v_k_248_;
goto _start;
}
else
{
lean_dec_ref(v_k_248_);
return v___x_249_;
}
}
case 3:
{
lean_object* v_fvarId_251_; lean_object* v_args_252_; lean_object* v___x_253_; 
v_fvarId_251_ = lean_ctor_get(v_code_226_, 0);
lean_inc(v_fvarId_251_);
v_args_252_ = lean_ctor_get(v_code_226_, 1);
lean_inc_ref(v_args_252_);
lean_dec_ref_known(v_code_226_, 2);
v___x_253_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_251_, v_a_228_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_253_, 0);
lean_dec(v_unused_268_);
v___x_255_ = v___x_253_;
v_isShared_256_ = v_isSharedCheck_267_;
goto v_resetjp_254_;
}
else
{
lean_dec(v___x_253_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_267_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_array_get_size(v_args_252_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_nat_dec_lt(v___x_257_, v___x_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v_args_252_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
lean_del_object(v___x_255_);
v___x_264_ = ((size_t)0ULL);
v___x_265_ = lean_usize_of_nat(v___x_258_);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_252_, v___x_264_, v___x_265_, v___x_259_, v_a_228_);
lean_dec_ref(v_args_252_);
return v___x_266_;
}
}
}
else
{
lean_dec_ref(v_args_252_);
return v___x_253_;
}
}
case 4:
{
lean_object* v_cases_269_; lean_object* v_discr_270_; lean_object* v_alts_271_; lean_object* v___x_272_; 
v_cases_269_ = lean_ctor_get(v_code_226_, 0);
lean_inc_ref(v_cases_269_);
lean_dec_ref_known(v_code_226_, 1);
v_discr_270_ = lean_ctor_get(v_cases_269_, 2);
lean_inc(v_discr_270_);
v_alts_271_ = lean_ctor_get(v_cases_269_, 3);
lean_inc_ref(v_alts_271_);
lean_dec_ref(v_cases_269_);
v___x_272_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_discr_270_, v_a_228_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_286_; 
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_272_, 0);
lean_dec(v_unused_287_);
v___x_274_ = v___x_272_;
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
else
{
lean_dec(v___x_272_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_array_get_size(v_alts_271_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_279_ == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v_alts_271_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_278_);
v___x_281_ = v___x_274_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_278_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_274_);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = lean_usize_of_nat(v___x_277_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_271_, v___x_283_, v___x_284_, v___x_278_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec_ref(v_alts_271_);
return v___x_285_;
}
}
}
else
{
lean_dec_ref(v_alts_271_);
return v___x_272_;
}
}
case 5:
{
lean_object* v_fvarId_288_; lean_object* v___x_289_; 
v_fvarId_288_ = lean_ctor_get(v_code_226_, 0);
lean_inc(v_fvarId_288_);
lean_dec_ref_known(v_code_226_, 1);
v___x_289_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_288_, v_a_228_);
return v___x_289_;
}
case 6:
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_isSharedCheck_297_ = !lean_is_exclusive(v_code_226_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_code_226_, 0);
lean_dec(v_unused_298_);
v___x_291_ = v_code_226_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_dec(v_code_226_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 0);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
default: 
{
lean_object* v_decl_299_; lean_object* v_k_300_; 
v_decl_299_ = lean_ctor_get(v_code_226_, 0);
lean_inc_ref(v_decl_299_);
v_k_300_ = lean_ctor_get(v_code_226_, 1);
lean_inc_ref(v_k_300_);
lean_dec_ref(v_code_226_);
v_decl_236_ = v_decl_299_;
v_k_237_ = v_k_300_;
v___y_238_ = v_a_227_;
v___y_239_ = v_a_228_;
v___y_240_ = v_a_229_;
v___y_241_ = v_a_230_;
v___y_242_ = v_a_231_;
v___y_243_ = v_a_232_;
v___y_244_ = v_a_233_;
goto v___jp_235_;
}
}
v___jp_235_:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_236_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_dec_ref_known(v___x_245_, 1);
v_code_226_ = v_k_237_;
v_a_227_ = v___y_238_;
v_a_228_ = v___y_239_;
v_a_229_ = v___y_240_;
v_a_230_ = v___y_241_;
v_a_231_ = v___y_242_;
v_a_232_ = v___y_243_;
v_a_233_ = v___y_244_;
goto _start;
}
else
{
lean_dec_ref(v_k_237_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object* v_funDecl_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_value_310_; lean_object* v___x_311_; 
v_value_310_ = lean_ctor_get(v_funDecl_301_, 4);
lean_inc_ref(v_value_310_);
lean_dec_ref(v_funDecl_301_);
v___x_311_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_value_310_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object* v_funDecl_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_funDecl_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object* v_as_322_, lean_object* v_i_323_, lean_object* v_stop_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; lean_object* v_res_336_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_323_);
lean_dec(v_i_323_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_324_);
lean_dec(v_stop_324_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_322_, v_i_boxed_334_, v_stop_boxed_335_, v_b_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec_ref(v_as_322_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object* v_code_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_code_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object* v_k_347_, lean_object* v_t_348_){
_start:
{
if (lean_obj_tag(v_t_348_) == 0)
{
lean_object* v_k_349_; lean_object* v_l_350_; lean_object* v_r_351_; uint8_t v___x_352_; 
v_k_349_ = lean_ctor_get(v_t_348_, 1);
v_l_350_ = lean_ctor_get(v_t_348_, 3);
v_r_351_ = lean_ctor_get(v_t_348_, 4);
v___x_352_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_347_, v_k_349_);
switch(v___x_352_)
{
case 0:
{
v_t_348_ = v_l_350_;
goto _start;
}
case 1:
{
uint8_t v___x_354_; 
v___x_354_ = 1;
return v___x_354_;
}
default: 
{
v_t_348_ = v_r_351_;
goto _start;
}
}
}
else
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object* v_k_357_, lean_object* v_t_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_357_, v_t_358_);
lean_dec(v_t_358_);
lean_dec(v_k_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object* v_fvarId_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_used_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_364_ = lean_st_ref_get(v_a_362_);
v_used_365_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_used_365_);
lean_dec(v___x_364_);
v___x_366_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_fvarId_361_, v_used_365_);
lean_dec(v_used_365_);
v___x_367_ = lean_box(v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object* v_fvarId_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec(v_fvarId_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object* v_fvarId_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_373_, v_a_375_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object* v_fvarId_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Compiler_LCNF_Simp_isUsed(v_fvarId_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_fvarId_383_);
return v_res_392_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object* v_00_u03b2_393_, lean_object* v_k_394_, lean_object* v_t_395_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_394_, v_t_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object* v_00_u03b2_397_, lean_object* v_k_398_, lean_object* v_t_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(v_00_u03b2_397_, v_k_398_, v_t_399_);
lean_dec(v_t_399_);
lean_dec(v_k_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object* v_decls_403_, lean_object* v_i_404_, lean_object* v_code_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_nat_dec_lt(v___x_414_, v_i_404_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_dec(v_i_404_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v_code_405_);
return v___x_416_;
}
else
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_decl_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_a_424_; uint8_t v___x_425_; 
v___x_417_ = 0;
v___x_418_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_sub(v_i_404_, v___x_419_);
lean_dec(v_i_404_);
v_decl_421_ = lean_array_get_borrowed(v___x_418_, v_decls_403_, v___x_420_);
v___x_422_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_421_);
v___x_423_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_422_, v_a_407_);
lean_dec(v___x_422_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
v___x_425_ = lean_unbox(v_a_424_);
lean_dec(v_a_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_417_, v_decl_421_, v_a_410_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_dec_ref_known(v___x_426_, 1);
v_i_404_ = v___x_420_;
goto _start;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v___x_420_);
lean_dec_ref(v_code_405_);
v_a_428_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_426_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_426_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
switch(lean_obj_tag(v_decl_421_))
{
case 0:
{
lean_object* v_decl_436_; lean_object* v___x_437_; 
v_decl_436_ = lean_ctor_get(v_decl_421_, 0);
lean_inc_ref(v_decl_436_);
v___x_437_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_436_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; 
lean_dec_ref_known(v___x_437_, 1);
lean_inc_ref(v_decl_436_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_decl_436_);
lean_ctor_set(v___x_438_, 1, v_code_405_);
v_i_404_ = v___x_420_;
v_code_405_ = v___x_438_;
goto _start;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v___x_420_);
lean_dec_ref(v_code_405_);
v_a_440_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_437_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
case 1:
{
lean_object* v_decl_448_; lean_object* v___x_449_; 
v_decl_448_ = lean_ctor_get(v_decl_421_, 0);
lean_inc_ref(v_decl_448_);
v___x_449_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_448_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; 
lean_dec_ref_known(v___x_449_, 1);
lean_inc_ref(v_decl_448_);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v_decl_448_);
lean_ctor_set(v___x_450_, 1, v_code_405_);
v_i_404_ = v___x_420_;
v_code_405_ = v___x_450_;
goto _start;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v___x_420_);
lean_dec_ref(v_code_405_);
v_a_452_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_449_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
default: 
{
lean_object* v_decl_460_; lean_object* v___x_461_; 
v_decl_460_ = lean_ctor_get(v_decl_421_, 0);
lean_inc_ref(v_decl_460_);
v___x_461_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_460_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; 
lean_dec_ref_known(v___x_461_, 1);
lean_inc_ref(v_decl_460_);
v___x_462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_462_, 0, v_decl_460_);
lean_ctor_set(v___x_462_, 1, v_code_405_);
v_i_404_ = v___x_420_;
v_code_405_ = v___x_462_;
goto _start;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v___x_420_);
lean_dec_ref(v_code_405_);
v_a_464_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_461_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_461_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object* v_decls_472_, lean_object* v_i_473_, lean_object* v_code_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_472_, v_i_473_, v_code_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec_ref(v_decls_472_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object* v_decl_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_, lean_object* v_h__3_487_){
_start:
{
switch(lean_obj_tag(v_decl_484_))
{
case 0:
{
lean_object* v_decl_488_; lean_object* v___x_489_; 
lean_dec(v_h__3_487_);
lean_dec(v_h__2_486_);
v_decl_488_ = lean_ctor_get(v_decl_484_, 0);
lean_inc_ref(v_decl_488_);
lean_dec_ref_known(v_decl_484_, 1);
v___x_489_ = lean_apply_1(v_h__1_485_, v_decl_488_);
return v___x_489_;
}
case 1:
{
lean_object* v_decl_490_; lean_object* v___x_491_; 
lean_dec(v_h__3_487_);
lean_dec(v_h__1_485_);
v_decl_490_ = lean_ctor_get(v_decl_484_, 0);
lean_inc_ref(v_decl_490_);
lean_dec_ref_known(v_decl_484_, 1);
v___x_491_ = lean_apply_1(v_h__2_486_, v_decl_490_);
return v___x_491_;
}
default: 
{
lean_object* v_decl_492_; lean_object* v___x_493_; 
lean_dec(v_h__2_486_);
lean_dec(v_h__1_485_);
v_decl_492_ = lean_ctor_get(v_decl_484_, 0);
lean_inc_ref(v_decl_492_);
lean_dec_ref_known(v_decl_484_, 1);
v___x_493_ = lean_apply_1(v_h__3_487_, v_decl_492_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object* v_motive_494_, lean_object* v_decl_495_, lean_object* v_h__1_496_, lean_object* v_h__2_497_, lean_object* v_h__3_498_){
_start:
{
switch(lean_obj_tag(v_decl_495_))
{
case 0:
{
lean_object* v_decl_499_; lean_object* v___x_500_; 
lean_dec(v_h__3_498_);
lean_dec(v_h__2_497_);
v_decl_499_ = lean_ctor_get(v_decl_495_, 0);
lean_inc_ref(v_decl_499_);
lean_dec_ref_known(v_decl_495_, 1);
v___x_500_ = lean_apply_1(v_h__1_496_, v_decl_499_);
return v___x_500_;
}
case 1:
{
lean_object* v_decl_501_; lean_object* v___x_502_; 
lean_dec(v_h__3_498_);
lean_dec(v_h__1_496_);
v_decl_501_ = lean_ctor_get(v_decl_495_, 0);
lean_inc_ref(v_decl_501_);
lean_dec_ref_known(v_decl_495_, 1);
v___x_502_ = lean_apply_1(v_h__2_497_, v_decl_501_);
return v___x_502_;
}
default: 
{
lean_object* v_decl_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_497_);
lean_dec(v_h__1_496_);
v_decl_503_ = lean_ctor_get(v_decl_495_, 0);
lean_inc_ref(v_decl_503_);
lean_dec_ref_known(v_decl_495_, 1);
v___x_504_ = lean_apply_1(v_h__3_498_, v_decl_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object* v_decls_505_, lean_object* v_code_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_array_get_size(v_decls_505_);
v___x_516_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_505_, v___x_515_, v_code_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object* v_decls_517_, lean_object* v_code_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_decls_517_, v_code_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec_ref(v_decls_517_);
return v_res_527_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
