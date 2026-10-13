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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_le(v___x_115_, v___x_115_);
if (v___x_119_ == 0)
{
if (v___x_117_ == 0)
{
lean_object* v___x_120_; 
lean_dec_ref(v_args_113_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_116_);
return v___x_120_;
}
else
{
size_t v___x_121_; size_t v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((size_t)0ULL);
v___x_122_ = lean_usize_of_nat(v___x_115_);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_113_, v___x_121_, v___x_122_, v___x_116_, v_a_104_);
lean_dec_ref(v_args_113_);
return v___x_123_;
}
}
else
{
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_115_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_113_, v___x_124_, v___x_125_, v___x_116_, v_a_104_);
lean_dec_ref(v_args_113_);
return v___x_126_;
}
}
}
case 4:
{
lean_object* v_fvarId_127_; lean_object* v_args_128_; lean_object* v___x_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_150_; 
v_fvarId_127_ = lean_ctor_get(v_e_102_, 0);
lean_inc(v_fvarId_127_);
v_args_128_ = lean_ctor_get(v_e_102_, 1);
lean_inc_ref(v_args_128_);
lean_dec_ref_known(v_e_102_, 2);
v___x_129_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_127_, v_a_104_);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v___x_129_, 0);
lean_dec(v_unused_151_);
v___x_131_ = v___x_129_;
v_isShared_132_ = v_isSharedCheck_150_;
goto v_resetjp_130_;
}
else
{
lean_dec(v___x_129_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_150_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v_args_128_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_136_ == 0)
{
lean_object* v___x_138_; 
lean_dec_ref(v_args_128_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_135_);
v___x_138_ = v___x_131_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_135_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
else
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_le(v___x_134_, v___x_134_);
if (v___x_140_ == 0)
{
if (v___x_136_ == 0)
{
lean_object* v___x_142_; 
lean_dec_ref(v_args_128_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_135_);
v___x_142_ = v___x_131_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_135_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
else
{
size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; 
lean_del_object(v___x_131_);
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_134_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_128_, v___x_144_, v___x_145_, v___x_135_, v_a_104_);
lean_dec_ref(v_args_128_);
return v___x_146_;
}
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
lean_del_object(v___x_131_);
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_134_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_128_, v___x_147_, v___x_148_, v___x_135_, v_a_104_);
lean_dec_ref(v_args_128_);
return v___x_149_;
}
}
}
}
default: 
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_e_102_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object* v_e_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_e_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object* v_as_164_, size_t v_i_165_, size_t v_stop_166_, lean_object* v_b_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_164_, v_i_165_, v_stop_166_, v_b_167_, v___y_169_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object* v_as_177_, lean_object* v_i_178_, lean_object* v_stop_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
size_t v_i_boxed_189_; size_t v_stop_boxed_190_; lean_object* v_res_191_; 
v_i_boxed_189_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_stop_boxed_190_ = lean_unbox_usize(v_stop_179_);
lean_dec(v_stop_179_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_177_, v_i_boxed_189_, v_stop_boxed_190_, v_b_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec_ref(v_as_177_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object* v_letDecl_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_value_201_; lean_object* v___x_202_; 
v_value_201_ = lean_ctor_get(v_letDecl_192_, 3);
lean_inc(v_value_201_);
lean_dec_ref(v_letDecl_192_);
v___x_202_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_value_201_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object* v_letDecl_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_letDecl_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object* v_as_213_, size_t v_i_214_, size_t v_stop_215_, lean_object* v_b_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___y_226_; uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_eq(v_i_214_, v_stop_215_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_array_uget_borrowed(v_as_213_, v_i_214_);
switch(lean_obj_tag(v___x_233_))
{
case 0:
{
lean_object* v_code_234_; 
v_code_234_ = lean_ctor_get(v___x_233_, 2);
lean_inc_ref(v_code_234_);
v___y_226_ = v_code_234_;
goto v___jp_225_;
}
case 1:
{
lean_object* v_code_235_; 
v_code_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc_ref(v_code_235_);
v___y_226_ = v_code_235_;
goto v___jp_225_;
}
default: 
{
lean_object* v_code_236_; 
v_code_236_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_code_236_);
v___y_226_ = v_code_236_;
goto v___jp_225_;
}
}
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_b_216_);
return v___x_237_;
}
v___jp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v___y_226_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; size_t v___x_229_; size_t v___x_230_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_214_, v___x_229_);
v_i_214_ = v___x_230_;
v_b_216_ = v_a_228_;
goto _start;
}
else
{
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object* v_code_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_decl_248_; lean_object* v_k_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; 
switch(lean_obj_tag(v_code_238_))
{
case 0:
{
lean_object* v_decl_259_; lean_object* v_k_260_; lean_object* v___x_261_; 
v_decl_259_ = lean_ctor_get(v_code_238_, 0);
lean_inc_ref(v_decl_259_);
v_k_260_ = lean_ctor_get(v_code_238_, 1);
lean_inc_ref(v_k_260_);
lean_dec_ref_known(v_code_238_, 2);
v___x_261_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_259_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_dec_ref_known(v___x_261_, 1);
v_code_238_ = v_k_260_;
goto _start;
}
else
{
lean_dec_ref(v_k_260_);
return v___x_261_;
}
}
case 3:
{
lean_object* v_fvarId_263_; lean_object* v_args_264_; lean_object* v___x_265_; 
v_fvarId_263_ = lean_ctor_get(v_code_238_, 0);
lean_inc(v_fvarId_263_);
v_args_264_ = lean_ctor_get(v_code_238_, 1);
lean_inc_ref(v_args_264_);
lean_dec_ref_known(v_code_238_, 2);
v___x_265_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_263_, v_a_240_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_286_; 
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_265_, 0);
lean_dec(v_unused_287_);
v___x_267_ = v___x_265_;
v_isShared_268_ = v_isSharedCheck_286_;
goto v_resetjp_266_;
}
else
{
lean_dec(v___x_265_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_286_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_array_get_size(v_args_264_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; 
lean_dec_ref(v_args_264_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_271_);
v___x_274_ = v___x_267_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_271_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
uint8_t v___x_276_; 
v___x_276_ = lean_nat_dec_le(v___x_270_, v___x_270_);
if (v___x_276_ == 0)
{
if (v___x_272_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref(v_args_264_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_271_);
v___x_278_ = v___x_267_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_271_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
lean_del_object(v___x_267_);
v___x_280_ = ((size_t)0ULL);
v___x_281_ = lean_usize_of_nat(v___x_270_);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_264_, v___x_280_, v___x_281_, v___x_271_, v_a_240_);
lean_dec_ref(v_args_264_);
return v___x_282_;
}
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_267_);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = lean_usize_of_nat(v___x_270_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_264_, v___x_283_, v___x_284_, v___x_271_, v_a_240_);
lean_dec_ref(v_args_264_);
return v___x_285_;
}
}
}
}
else
{
lean_dec_ref(v_args_264_);
return v___x_265_;
}
}
case 4:
{
lean_object* v_cases_288_; lean_object* v_discr_289_; lean_object* v_alts_290_; lean_object* v___x_291_; 
v_cases_288_ = lean_ctor_get(v_code_238_, 0);
lean_inc_ref(v_cases_288_);
lean_dec_ref_known(v_code_238_, 1);
v_discr_289_ = lean_ctor_get(v_cases_288_, 2);
lean_inc(v_discr_289_);
v_alts_290_ = lean_ctor_get(v_cases_288_, 3);
lean_inc_ref(v_alts_290_);
lean_dec_ref(v_cases_288_);
v___x_291_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_discr_289_, v_a_240_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_312_; 
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v___x_291_, 0);
lean_dec(v_unused_313_);
v___x_293_ = v___x_291_;
v_isShared_294_ = v_isSharedCheck_312_;
goto v_resetjp_292_;
}
else
{
lean_dec(v___x_291_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_312_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_array_get_size(v_alts_290_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_nat_dec_lt(v___x_295_, v___x_296_);
if (v___x_298_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_alts_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_300_ = v___x_293_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_297_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
uint8_t v___x_302_; 
v___x_302_ = lean_nat_dec_le(v___x_296_, v___x_296_);
if (v___x_302_ == 0)
{
if (v___x_298_ == 0)
{
lean_object* v___x_304_; 
lean_dec_ref(v_alts_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_304_ = v___x_293_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_297_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
lean_del_object(v___x_293_);
v___x_306_ = ((size_t)0ULL);
v___x_307_ = lean_usize_of_nat(v___x_296_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_290_, v___x_306_, v___x_307_, v___x_297_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec_ref(v_alts_290_);
return v___x_308_;
}
}
else
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; 
lean_del_object(v___x_293_);
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_296_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_290_, v___x_309_, v___x_310_, v___x_297_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec_ref(v_alts_290_);
return v___x_311_;
}
}
}
}
else
{
lean_dec_ref(v_alts_290_);
return v___x_291_;
}
}
case 5:
{
lean_object* v_fvarId_314_; lean_object* v___x_315_; 
v_fvarId_314_ = lean_ctor_get(v_code_238_, 0);
lean_inc(v_fvarId_314_);
lean_dec_ref_known(v_code_238_, 1);
v___x_315_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_314_, v_a_240_);
return v___x_315_;
}
case 6:
{
lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
v_isSharedCheck_323_ = !lean_is_exclusive(v_code_238_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_code_238_, 0);
lean_dec(v_unused_324_);
v___x_317_ = v_code_238_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_dec(v_code_238_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 0);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
default: 
{
lean_object* v_decl_325_; lean_object* v_k_326_; 
v_decl_325_ = lean_ctor_get(v_code_238_, 0);
lean_inc_ref(v_decl_325_);
v_k_326_ = lean_ctor_get(v_code_238_, 1);
lean_inc_ref(v_k_326_);
lean_dec_ref(v_code_238_);
v_decl_248_ = v_decl_325_;
v_k_249_ = v_k_326_;
v___y_250_ = v_a_239_;
v___y_251_ = v_a_240_;
v___y_252_ = v_a_241_;
v___y_253_ = v_a_242_;
v___y_254_ = v_a_243_;
v___y_255_ = v_a_244_;
v___y_256_ = v_a_245_;
goto v___jp_247_;
}
}
v___jp_247_:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_248_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_dec_ref_known(v___x_257_, 1);
v_code_238_ = v_k_249_;
v_a_239_ = v___y_250_;
v_a_240_ = v___y_251_;
v_a_241_ = v___y_252_;
v_a_242_ = v___y_253_;
v_a_243_ = v___y_254_;
v_a_244_ = v___y_255_;
v_a_245_ = v___y_256_;
goto _start;
}
else
{
lean_dec_ref(v_k_249_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object* v_funDecl_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_value_336_; lean_object* v___x_337_; 
v_value_336_ = lean_ctor_get(v_funDecl_327_, 4);
lean_inc_ref(v_value_336_);
lean_dec_ref(v_funDecl_327_);
v___x_337_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_value_336_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object* v_funDecl_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_funDecl_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_stop_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
size_t v_i_boxed_360_; size_t v_stop_boxed_361_; lean_object* v_res_362_; 
v_i_boxed_360_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_361_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_348_, v_i_boxed_360_, v_stop_boxed_361_, v_b_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_as_348_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object* v_code_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_code_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_372_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object* v_k_373_, lean_object* v_t_374_){
_start:
{
if (lean_obj_tag(v_t_374_) == 0)
{
lean_object* v_k_375_; lean_object* v_l_376_; lean_object* v_r_377_; uint8_t v___x_378_; 
v_k_375_ = lean_ctor_get(v_t_374_, 1);
v_l_376_ = lean_ctor_get(v_t_374_, 3);
v_r_377_ = lean_ctor_get(v_t_374_, 4);
v___x_378_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_373_, v_k_375_);
switch(v___x_378_)
{
case 0:
{
v_t_374_ = v_l_376_;
goto _start;
}
case 1:
{
uint8_t v___x_380_; 
v___x_380_ = 1;
return v___x_380_;
}
default: 
{
v_t_374_ = v_r_377_;
goto _start;
}
}
}
else
{
uint8_t v___x_382_; 
v___x_382_ = 0;
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object* v_k_383_, lean_object* v_t_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_383_, v_t_384_);
lean_dec(v_t_384_);
lean_dec(v_k_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object* v_fvarId_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_used_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_390_ = lean_st_ref_get(v_a_388_);
v_used_391_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_used_391_);
lean_dec(v___x_390_);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_fvarId_387_, v_used_391_);
lean_dec(v_used_391_);
v___x_393_ = lean_box(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object* v_fvarId_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec(v_fvarId_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object* v_fvarId_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_399_, v_a_401_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object* v_fvarId_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Compiler_LCNF_Simp_isUsed(v_fvarId_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_fvarId_409_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object* v_00_u03b2_419_, lean_object* v_k_420_, lean_object* v_t_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_420_, v_t_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object* v_00_u03b2_423_, lean_object* v_k_424_, lean_object* v_t_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(v_00_u03b2_423_, v_k_424_, v_t_425_);
lean_dec(v_t_425_);
lean_dec(v_k_424_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0(void){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object* v_decls_429_, lean_object* v_i_430_, lean_object* v_code_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_nat_dec_lt(v___x_440_, v_i_430_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v_i_430_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_code_431_);
return v___x_442_;
}
else
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_decl_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_a_450_; uint8_t v___x_451_; 
v___x_443_ = 0;
v___x_444_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_sub(v_i_430_, v___x_445_);
lean_dec(v_i_430_);
v_decl_447_ = lean_array_get_borrowed(v___x_444_, v_decls_429_, v___x_446_);
v___x_448_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_447_);
v___x_449_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_448_, v_a_433_);
lean_dec(v___x_448_);
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_unbox(v_a_450_);
lean_dec(v_a_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_443_, v_decl_447_, v_a_436_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_dec_ref_known(v___x_452_, 1);
v_i_430_ = v___x_446_;
goto _start;
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v___x_446_);
lean_dec_ref(v_code_431_);
v_a_454_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_452_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
switch(lean_obj_tag(v_decl_447_))
{
case 0:
{
lean_object* v_decl_462_; lean_object* v___x_463_; 
v_decl_462_ = lean_ctor_get(v_decl_447_, 0);
lean_inc_ref(v_decl_462_);
v___x_463_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_462_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; 
lean_dec_ref_known(v___x_463_, 1);
lean_inc_ref(v_decl_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_decl_462_);
lean_ctor_set(v___x_464_, 1, v_code_431_);
v_i_430_ = v___x_446_;
v_code_431_ = v___x_464_;
goto _start;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v___x_446_);
lean_dec_ref(v_code_431_);
v_a_466_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_463_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
case 1:
{
lean_object* v_decl_474_; lean_object* v___x_475_; 
v_decl_474_ = lean_ctor_get(v_decl_447_, 0);
lean_inc_ref(v_decl_474_);
v___x_475_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_474_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; 
lean_dec_ref_known(v___x_475_, 1);
lean_inc_ref(v_decl_474_);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v_decl_474_);
lean_ctor_set(v___x_476_, 1, v_code_431_);
v_i_430_ = v___x_446_;
v_code_431_ = v___x_476_;
goto _start;
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v___x_446_);
lean_dec_ref(v_code_431_);
v_a_478_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_475_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_475_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
default: 
{
lean_object* v_decl_486_; lean_object* v___x_487_; 
v_decl_486_ = lean_ctor_get(v_decl_447_, 0);
lean_inc_ref(v_decl_486_);
v___x_487_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_486_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_488_; 
lean_dec_ref_known(v___x_487_, 1);
lean_inc_ref(v_decl_486_);
v___x_488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_488_, 0, v_decl_486_);
lean_ctor_set(v___x_488_, 1, v_code_431_);
v_i_430_ = v___x_446_;
v_code_431_ = v___x_488_;
goto _start;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___x_446_);
lean_dec_ref(v_code_431_);
v_a_490_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_487_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_487_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object* v_decls_498_, lean_object* v_i_499_, lean_object* v_code_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_498_, v_i_499_, v_code_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec_ref(v_decls_498_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object* v_decl_510_, lean_object* v_h__1_511_, lean_object* v_h__2_512_, lean_object* v_h__3_513_){
_start:
{
switch(lean_obj_tag(v_decl_510_))
{
case 0:
{
lean_object* v_decl_514_; lean_object* v___x_515_; 
lean_dec(v_h__3_513_);
lean_dec(v_h__2_512_);
v_decl_514_ = lean_ctor_get(v_decl_510_, 0);
lean_inc_ref(v_decl_514_);
lean_dec_ref_known(v_decl_510_, 1);
v___x_515_ = lean_apply_1(v_h__1_511_, v_decl_514_);
return v___x_515_;
}
case 1:
{
lean_object* v_decl_516_; lean_object* v___x_517_; 
lean_dec(v_h__3_513_);
lean_dec(v_h__1_511_);
v_decl_516_ = lean_ctor_get(v_decl_510_, 0);
lean_inc_ref(v_decl_516_);
lean_dec_ref_known(v_decl_510_, 1);
v___x_517_ = lean_apply_1(v_h__2_512_, v_decl_516_);
return v___x_517_;
}
default: 
{
lean_object* v_decl_518_; lean_object* v___x_519_; 
lean_dec(v_h__2_512_);
lean_dec(v_h__1_511_);
v_decl_518_ = lean_ctor_get(v_decl_510_, 0);
lean_inc_ref(v_decl_518_);
lean_dec_ref_known(v_decl_510_, 1);
v___x_519_ = lean_apply_1(v_h__3_513_, v_decl_518_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object* v_motive_520_, lean_object* v_decl_521_, lean_object* v_h__1_522_, lean_object* v_h__2_523_, lean_object* v_h__3_524_){
_start:
{
switch(lean_obj_tag(v_decl_521_))
{
case 0:
{
lean_object* v_decl_525_; lean_object* v___x_526_; 
lean_dec(v_h__3_524_);
lean_dec(v_h__2_523_);
v_decl_525_ = lean_ctor_get(v_decl_521_, 0);
lean_inc_ref(v_decl_525_);
lean_dec_ref_known(v_decl_521_, 1);
v___x_526_ = lean_apply_1(v_h__1_522_, v_decl_525_);
return v___x_526_;
}
case 1:
{
lean_object* v_decl_527_; lean_object* v___x_528_; 
lean_dec(v_h__3_524_);
lean_dec(v_h__1_522_);
v_decl_527_ = lean_ctor_get(v_decl_521_, 0);
lean_inc_ref(v_decl_527_);
lean_dec_ref_known(v_decl_521_, 1);
v___x_528_ = lean_apply_1(v_h__2_523_, v_decl_527_);
return v___x_528_;
}
default: 
{
lean_object* v_decl_529_; lean_object* v___x_530_; 
lean_dec(v_h__2_523_);
lean_dec(v_h__1_522_);
v_decl_529_ = lean_ctor_get(v_decl_521_, 0);
lean_inc_ref(v_decl_529_);
lean_dec_ref_known(v_decl_521_, 1);
v___x_530_ = lean_apply_1(v_h__3_524_, v_decl_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object* v_decls_531_, lean_object* v_code_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_array_get_size(v_decls_531_);
v___x_542_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_531_, v___x_541_, v_code_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object* v_decls_543_, lean_object* v_code_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_decls_543_, v_code_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_decls_543_);
return v_res_553_;
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
