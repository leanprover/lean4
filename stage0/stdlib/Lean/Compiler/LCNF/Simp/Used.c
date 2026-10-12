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
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object* v_fvarId_1_, lean_object* v_a_2_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1_, v_a_2_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(lean_object* v_fvarId_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_25_, v_a_26_);
lean_dec(v_a_26_);
return v_res_28_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object* v_fvarId_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_29_, v_a_31_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_29_ = stack[0].m_obj;
lean_object* v_a_30_ = stack[1].m_obj;
lean_object* v_a_31_ = stack[2].m_obj;
lean_object* v_a_32_ = stack[3].m_obj;
lean_object* v_a_33_ = stack[4].m_obj;
lean_object* v_a_34_ = stack[5].m_obj;
lean_object* v_a_35_ = stack[6].m_obj;
lean_object* v_a_36_ = stack[7].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar(v_fvarId_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object* v_fvarId_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar(v_fvarId_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_49_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object* v_arg_50_, lean_object* v_a_51_){
_start:
{
if (lean_obj_tag(v_arg_50_) == 1)
{
lean_object* v_fvarId_53_; lean_object* v___x_54_; 
v_fvarId_53_ = lean_ctor_get(v_arg_50_, 0);
lean_inc(v_fvarId_53_);
lean_dec_ref_known(v_arg_50_, 1);
v___x_54_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_53_, v_a_51_);
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_arg_50_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_50_ = stack[0].m_obj;
lean_object* v_a_51_ = stack[1].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_50_, v_a_51_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(lean_object* v_arg_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_58_, v_a_59_);
lean_dec(v_a_59_);
return v_res_61_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg(lean_object* v_arg_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_62_, v_a_64_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_62_ = stack[0].m_obj;
lean_object* v_a_63_ = stack[1].m_obj;
lean_object* v_a_64_ = stack[2].m_obj;
lean_object* v_a_65_ = stack[3].m_obj;
lean_object* v_a_66_ = stack[4].m_obj;
lean_object* v_a_67_ = stack[5].m_obj;
lean_object* v_a_68_ = stack[6].m_obj;
lean_object* v_a_69_ = stack[7].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Compiler_LCNF_Simp_markUsedArg(v_arg_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(lean_object* v_arg_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Compiler_LCNF_Simp_markUsedArg(v_arg_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v_res_82_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object* v_as_83_, size_t v_i_84_, size_t v_stop_85_, lean_object* v_b_86_, lean_object* v___y_87_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_usize_dec_eq(v_i_84_, v_stop_85_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_array_uget_borrowed(v_as_83_, v_i_84_);
lean_inc(v___x_90_);
v___x_91_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_90_, v___y_87_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; size_t v___x_93_; size_t v___x_94_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_add(v_i_84_, v___x_93_);
v_i_84_ = v___x_94_;
v_b_86_ = v_a_92_;
goto _start;
}
else
{
return v___x_91_;
}
}
else
{
lean_object* v___x_96_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_b_86_);
return v___x_96_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_83_ = stack[0].m_obj;
size_t v_i_84_ = stack[1].m_num;
size_t v_stop_85_ = stack[2].m_num;
lean_object* v_b_86_ = stack[3].m_obj;
lean_object* v___y_87_ = stack[4].m_obj;
lean_object* v_res_97_;
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_83_, v_i_84_, v_stop_85_, v_b_86_, v___y_87_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(lean_object* v_as_98_, lean_object* v_i_99_, lean_object* v_stop_100_, lean_object* v_b_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
size_t v_i_boxed_104_; size_t v_stop_boxed_105_; lean_object* v_res_106_; 
v_i_boxed_104_ = lean_unbox_usize(v_i_99_);
lean_dec(v_i_99_);
v_stop_boxed_105_ = lean_unbox_usize(v_stop_100_);
lean_dec(v_stop_100_);
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_98_, v_i_boxed_104_, v_stop_boxed_105_, v_b_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v_as_98_);
return v_res_106_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue(lean_object* v_e_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
switch(lean_obj_tag(v_e_107_))
{
case 2:
{
lean_object* v_struct_116_; lean_object* v___x_117_; 
v_struct_116_ = lean_ctor_get(v_e_107_, 2);
lean_inc(v_struct_116_);
lean_dec_ref_known(v_e_107_, 3);
v___x_117_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_struct_116_, v_a_109_);
return v___x_117_;
}
case 3:
{
lean_object* v_args_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_args_118_ = lean_ctor_get(v_e_107_, 2);
lean_inc_ref(v_args_118_);
lean_dec_ref_known(v_e_107_, 3);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_array_get_size(v_args_118_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_nat_dec_lt(v___x_119_, v___x_120_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec_ref(v_args_118_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_le(v___x_120_, v___x_120_);
if (v___x_124_ == 0)
{
if (v___x_122_ == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v_args_118_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_121_);
return v___x_125_;
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_120_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_118_, v___x_126_, v___x_127_, v___x_121_, v_a_109_);
lean_dec_ref(v_args_118_);
return v___x_128_;
}
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_120_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_118_, v___x_129_, v___x_130_, v___x_121_, v_a_109_);
lean_dec_ref(v_args_118_);
return v___x_131_;
}
}
}
case 4:
{
lean_object* v_fvarId_132_; lean_object* v_args_133_; lean_object* v___x_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_155_; 
v_fvarId_132_ = lean_ctor_get(v_e_107_, 0);
lean_inc(v_fvarId_132_);
v_args_133_ = lean_ctor_get(v_e_107_, 1);
lean_inc_ref(v_args_133_);
lean_dec_ref_known(v_e_107_, 2);
v___x_134_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_132_, v_a_109_);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_156_);
v___x_136_ = v___x_134_;
v_isShared_137_ = v_isSharedCheck_155_;
goto v_resetjp_135_;
}
else
{
lean_dec(v___x_134_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_155_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_array_get_size(v_args_133_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
if (v___x_141_ == 0)
{
lean_object* v___x_143_; 
lean_dec_ref(v_args_133_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_140_);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_140_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___x_139_, v___x_139_);
if (v___x_145_ == 0)
{
if (v___x_141_ == 0)
{
lean_object* v___x_147_; 
lean_dec_ref(v_args_133_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_140_);
v___x_147_ = v___x_136_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_140_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
lean_del_object(v___x_136_);
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_139_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_133_, v___x_149_, v___x_150_, v___x_140_, v_a_109_);
lean_dec_ref(v_args_133_);
return v___x_151_;
}
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
lean_del_object(v___x_136_);
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_139_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_133_, v___x_152_, v___x_153_, v___x_140_, v_a_109_);
lean_dec_ref(v_args_133_);
return v___x_154_;
}
}
}
}
default: 
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_e_107_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedLetValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_107_ = stack[0].m_obj;
lean_object* v_a_108_ = stack[1].m_obj;
lean_object* v_a_109_ = stack[2].m_obj;
lean_object* v_a_110_ = stack[3].m_obj;
lean_object* v_a_111_ = stack[4].m_obj;
lean_object* v_a_112_ = stack[5].m_obj;
lean_object* v_a_113_ = stack[6].m_obj;
lean_object* v_a_114_ = stack[7].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_e_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(lean_object* v_e_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_e_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_169_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(lean_object* v_as_170_, size_t v_i_171_, size_t v_stop_172_, lean_object* v_b_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_170_, v_i_171_, v_stop_172_, v_b_173_, v___y_175_);
return v___x_182_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_170_ = stack[0].m_obj;
size_t v_i_171_ = stack[1].m_num;
size_t v_stop_172_ = stack[2].m_num;
lean_object* v_b_173_ = stack[3].m_obj;
lean_object* v___y_174_ = stack[4].m_obj;
lean_object* v___y_175_ = stack[5].m_obj;
lean_object* v___y_176_ = stack[6].m_obj;
lean_object* v___y_177_ = stack[7].m_obj;
lean_object* v___y_178_ = stack[8].m_obj;
lean_object* v___y_179_ = stack[9].m_obj;
lean_object* v___y_180_ = stack[10].m_obj;
lean_object* v_res_183_;
v_res_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_170_, v_i_171_, v_stop_172_, v_b_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(lean_object* v_as_184_, lean_object* v_i_185_, lean_object* v_stop_186_, lean_object* v_b_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
size_t v_i_boxed_196_; size_t v_stop_boxed_197_; lean_object* v_res_198_; 
v_i_boxed_196_ = lean_unbox_usize(v_i_185_);
lean_dec(v_i_185_);
v_stop_boxed_197_ = lean_unbox_usize(v_stop_186_);
lean_dec(v_stop_186_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_184_, v_i_boxed_196_, v_stop_boxed_197_, v_b_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec_ref(v_as_184_);
return v_res_198_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object* v_letDecl_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_value_208_; lean_object* v___x_209_; 
v_value_208_ = lean_ctor_get(v_letDecl_199_, 3);
lean_inc(v_value_208_);
lean_dec_ref(v_letDecl_199_);
v___x_209_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(v_value_208_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedLetDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_letDecl_199_ = stack[0].m_obj;
lean_object* v_a_200_ = stack[1].m_obj;
lean_object* v_a_201_ = stack[2].m_obj;
lean_object* v_a_202_ = stack[3].m_obj;
lean_object* v_a_203_ = stack[4].m_obj;
lean_object* v_a_204_ = stack[5].m_obj;
lean_object* v_a_205_ = stack[6].m_obj;
lean_object* v_a_206_ = stack[7].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_letDecl_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object* v_letDecl_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_letDecl_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_220_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(lean_object* v_as_221_, size_t v_i_222_, size_t v_stop_223_, lean_object* v_b_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___y_234_; uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_eq(v_i_222_, v_stop_223_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_array_uget_borrowed(v_as_221_, v_i_222_);
switch(lean_obj_tag(v___x_241_))
{
case 0:
{
lean_object* v_code_242_; 
v_code_242_ = lean_ctor_get(v___x_241_, 2);
lean_inc_ref(v_code_242_);
v___y_234_ = v_code_242_;
goto v___jp_233_;
}
case 1:
{
lean_object* v_code_243_; 
v_code_243_ = lean_ctor_get(v___x_241_, 1);
lean_inc_ref(v_code_243_);
v___y_234_ = v_code_243_;
goto v___jp_233_;
}
default: 
{
lean_object* v_code_244_; 
v_code_244_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_code_244_);
v___y_234_ = v_code_244_;
goto v___jp_233_;
}
}
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v_b_224_);
return v___x_245_;
}
v___jp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v___y_234_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; size_t v___x_237_; size_t v___x_238_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_222_, v___x_237_);
v_i_222_ = v___x_238_;
v_b_224_ = v_a_236_;
goto _start;
}
else
{
return v___x_235_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_221_ = stack[0].m_obj;
size_t v_i_222_ = stack[1].m_num;
size_t v_stop_223_ = stack[2].m_num;
lean_object* v_b_224_ = stack[3].m_obj;
lean_object* v___y_225_ = stack[4].m_obj;
lean_object* v___y_226_ = stack[5].m_obj;
lean_object* v___y_227_ = stack[6].m_obj;
lean_object* v___y_228_ = stack[7].m_obj;
lean_object* v___y_229_ = stack[8].m_obj;
lean_object* v___y_230_ = stack[9].m_obj;
lean_object* v___y_231_ = stack[10].m_obj;
lean_object* v_res_246_;
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_221_, v_i_222_, v_stop_223_, v_b_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
stack->m_obj
 = v_res_246_;
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object* v_code_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_247_ = stack[0].m_obj;
lean_object* v_a_248_ = stack[1].m_obj;
lean_object* v_a_249_ = stack[2].m_obj;
lean_object* v_a_250_ = stack[3].m_obj;
lean_object* v_a_251_ = stack[4].m_obj;
lean_object* v_a_252_ = stack[5].m_obj;
lean_object* v_a_253_ = stack[6].m_obj;
lean_object* v_a_254_ = stack[7].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_code_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
stack->m_obj
 = v_res_336_;
}
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object* v_funDecl_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_value_346_; lean_object* v___x_347_; 
v_value_346_ = lean_ctor_get(v_funDecl_337_, 4);
lean_inc_ref(v_value_346_);
lean_dec_ref(v_funDecl_337_);
v___x_347_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_value_346_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
return v___x_347_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markUsedFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_funDecl_337_ = stack[0].m_obj;
lean_object* v_a_338_ = stack[1].m_obj;
lean_object* v_a_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_a_341_ = stack[4].m_obj;
lean_object* v_a_342_ = stack[5].m_obj;
lean_object* v_a_343_ = stack[6].m_obj;
lean_object* v_a_344_ = stack[7].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_funDecl_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(lean_object* v_funDecl_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_funDecl_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(lean_object* v_as_359_, lean_object* v_i_360_, lean_object* v_stop_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_i_boxed_371_; size_t v_stop_boxed_372_; lean_object* v_res_373_; 
v_i_boxed_371_ = lean_unbox_usize(v_i_360_);
lean_dec(v_i_360_);
v_stop_boxed_372_ = lean_unbox_usize(v_stop_361_);
lean_dec(v_stop_361_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_359_, v_i_boxed_371_, v_stop_boxed_372_, v_b_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_as_359_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(lean_object* v_code_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(v_code_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_383_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(lean_object* v_k_384_, lean_object* v_t_385_){
_start:
{
if (lean_obj_tag(v_t_385_) == 0)
{
lean_object* v_k_386_; lean_object* v_l_387_; lean_object* v_r_388_; uint8_t v___x_389_; 
v_k_386_ = lean_ctor_get(v_t_385_, 1);
v_l_387_ = lean_ctor_get(v_t_385_, 3);
v_r_388_ = lean_ctor_get(v_t_385_, 4);
v___x_389_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_384_, v_k_386_);
switch(v___x_389_)
{
case 0:
{
v_t_385_ = v_l_387_;
goto _start;
}
case 1:
{
uint8_t v___x_391_; 
v___x_391_ = 1;
return v___x_391_;
}
default: 
{
v_t_385_ = v_r_388_;
goto _start;
}
}
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_384_ = stack[0].m_obj;
lean_object* v_t_385_ = stack[1].m_obj;
uint8_t v_res_394_;
v_res_394_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_384_, v_t_385_);
stack->m_num = v_res_394_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(lean_object* v_k_395_, lean_object* v_t_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_395_, v_t_396_);
lean_dec(v_t_396_);
lean_dec(v_k_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object* v_fvarId_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_used_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_402_ = lean_st_ref_get(v_a_400_);
v_used_403_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_used_403_);
lean_dec(v___x_402_);
v___x_404_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_fvarId_399_, v_used_403_);
lean_dec(v_used_403_);
v___x_405_ = lean_box(v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isUsed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_399_ = stack[0].m_obj;
lean_object* v_a_400_ = stack[1].m_obj;
lean_object* v_res_407_;
v_res_407_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_399_, v_a_400_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(lean_object* v_fvarId_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec(v_fvarId_408_);
return v_res_411_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object* v_fvarId_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_412_, v_a_414_);
return v___x_421_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isUsed_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_412_ = stack[0].m_obj;
lean_object* v_a_413_ = stack[1].m_obj;
lean_object* v_a_414_ = stack[2].m_obj;
lean_object* v_a_415_ = stack[3].m_obj;
lean_object* v_a_416_ = stack[4].m_obj;
lean_object* v_a_417_ = stack[5].m_obj;
lean_object* v_a_418_ = stack[6].m_obj;
lean_object* v_a_419_ = stack[7].m_obj;
lean_object* v_res_422_;
v_res_422_ = l_Lean_Compiler_LCNF_Simp_isUsed(v_fvarId_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object* v_fvarId_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Compiler_LCNF_Simp_isUsed(v_fvarId_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_fvarId_423_);
return v_res_432_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_object* v_00_u03b2_433_, lean_object* v_k_434_, lean_object* v_t_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_k_434_, v_t_435_);
return v___x_436_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_434_ = stack[1].m_obj;
lean_object* v_t_435_ = stack[2].m_obj;
uint8_t v_res_437_;
v_res_437_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(lean_box(0), v_k_434_, v_t_435_);
stack->m_num = v_res_437_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(lean_object* v_00_u03b2_438_, lean_object* v_k_439_, lean_object* v_t_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(v_00_u03b2_438_, v_k_439_, v_t_440_);
lean_dec(v_t_440_);
lean_dec(v_k_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_443_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object* v_decls_444_, lean_object* v_i_445_, lean_object* v_code_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_nat_dec_lt(v___x_455_, v_i_445_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v_i_445_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_code_446_);
return v___x_457_;
}
else
{
uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_decl_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_a_465_; uint8_t v___x_466_; 
v___x_458_ = 0;
v___x_459_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_sub(v_i_445_, v___x_460_);
lean_dec(v_i_445_);
v_decl_462_ = lean_array_get_borrowed(v___x_459_, v_decls_444_, v___x_461_);
v___x_463_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_462_);
v___x_464_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_463_, v_a_448_);
lean_dec(v___x_463_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref(v___x_464_);
v___x_466_ = lean_unbox(v_a_465_);
lean_dec(v_a_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_458_, v_decl_462_, v_a_451_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec_ref_known(v___x_467_, 1);
v_i_445_ = v___x_461_;
goto _start;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v___x_461_);
lean_dec_ref(v_code_446_);
v_a_469_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_467_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_467_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
switch(lean_obj_tag(v_decl_462_))
{
case 0:
{
lean_object* v_decl_477_; lean_object* v___x_478_; 
v_decl_477_ = lean_ctor_get(v_decl_462_, 0);
lean_inc_ref(v_decl_477_);
v___x_478_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v_decl_477_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; 
lean_dec_ref_known(v___x_478_, 1);
lean_inc_ref(v_decl_477_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_decl_477_);
lean_ctor_set(v___x_479_, 1, v_code_446_);
v_i_445_ = v___x_461_;
v_code_446_ = v___x_479_;
goto _start;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v___x_461_);
lean_dec_ref(v_code_446_);
v_a_481_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_478_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
case 1:
{
lean_object* v_decl_489_; lean_object* v___x_490_; 
v_decl_489_ = lean_ctor_get(v_decl_462_, 0);
lean_inc_ref(v_decl_489_);
v___x_490_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_489_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; 
lean_dec_ref_known(v___x_490_, 1);
lean_inc_ref(v_decl_489_);
v___x_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_491_, 0, v_decl_489_);
lean_ctor_set(v___x_491_, 1, v_code_446_);
v_i_445_ = v___x_461_;
v_code_446_ = v___x_491_;
goto _start;
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v___x_461_);
lean_dec_ref(v_code_446_);
v_a_493_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_490_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
default: 
{
lean_object* v_decl_501_; lean_object* v___x_502_; 
v_decl_501_ = lean_ctor_get(v_decl_462_, 0);
lean_inc_ref(v_decl_501_);
v___x_502_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_501_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; 
lean_dec_ref_known(v___x_502_, 1);
lean_inc_ref(v_decl_501_);
v___x_503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_503_, 0, v_decl_501_);
lean_ctor_set(v___x_503_, 1, v_code_446_);
v_i_445_ = v___x_461_;
v_code_446_ = v___x_503_;
goto _start;
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v___x_461_);
lean_dec_ref(v_code_446_);
v_a_505_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_502_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_444_ = stack[0].m_obj;
lean_object* v_i_445_ = stack[1].m_obj;
lean_object* v_code_446_ = stack[2].m_obj;
lean_object* v_a_447_ = stack[3].m_obj;
lean_object* v_a_448_ = stack[4].m_obj;
lean_object* v_a_449_ = stack[5].m_obj;
lean_object* v_a_450_ = stack[6].m_obj;
lean_object* v_a_451_ = stack[7].m_obj;
lean_object* v_a_452_ = stack[8].m_obj;
lean_object* v_a_453_ = stack[9].m_obj;
lean_object* v_res_513_;
v_res_513_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_444_, v_i_445_, v_code_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object* v_decls_514_, lean_object* v_i_515_, lean_object* v_code_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_514_, v_i_515_, v_code_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec_ref(v_decls_514_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(lean_object* v_decl_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_, lean_object* v_h__3_529_){
_start:
{
switch(lean_obj_tag(v_decl_526_))
{
case 0:
{
lean_object* v_decl_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_529_);
lean_dec(v_h__2_528_);
v_decl_530_ = lean_ctor_get(v_decl_526_, 0);
lean_inc_ref(v_decl_530_);
lean_dec_ref_known(v_decl_526_, 1);
v___x_531_ = lean_apply_1(v_h__1_527_, v_decl_530_);
return v___x_531_;
}
case 1:
{
lean_object* v_decl_532_; lean_object* v___x_533_; 
lean_dec(v_h__3_529_);
lean_dec(v_h__1_527_);
v_decl_532_ = lean_ctor_get(v_decl_526_, 0);
lean_inc_ref(v_decl_532_);
lean_dec_ref_known(v_decl_526_, 1);
v___x_533_ = lean_apply_1(v_h__2_528_, v_decl_532_);
return v___x_533_;
}
default: 
{
lean_object* v_decl_534_; lean_object* v___x_535_; 
lean_dec(v_h__2_528_);
lean_dec(v_h__1_527_);
v_decl_534_ = lean_ctor_get(v_decl_526_, 0);
lean_inc_ref(v_decl_534_);
lean_dec_ref_known(v_decl_526_, 1);
v___x_535_ = lean_apply_1(v_h__3_529_, v_decl_534_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(lean_object* v_motive_536_, lean_object* v_decl_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_, lean_object* v_h__3_540_){
_start:
{
switch(lean_obj_tag(v_decl_537_))
{
case 0:
{
lean_object* v_decl_541_; lean_object* v___x_542_; 
lean_dec(v_h__3_540_);
lean_dec(v_h__2_539_);
v_decl_541_ = lean_ctor_get(v_decl_537_, 0);
lean_inc_ref(v_decl_541_);
lean_dec_ref_known(v_decl_537_, 1);
v___x_542_ = lean_apply_1(v_h__1_538_, v_decl_541_);
return v___x_542_;
}
case 1:
{
lean_object* v_decl_543_; lean_object* v___x_544_; 
lean_dec(v_h__3_540_);
lean_dec(v_h__1_538_);
v_decl_543_ = lean_ctor_get(v_decl_537_, 0);
lean_inc_ref(v_decl_543_);
lean_dec_ref_known(v_decl_537_, 1);
v___x_544_ = lean_apply_1(v_h__2_539_, v_decl_543_);
return v___x_544_;
}
default: 
{
lean_object* v_decl_545_; lean_object* v___x_546_; 
lean_dec(v_h__2_539_);
lean_dec(v_h__1_538_);
v_decl_545_ = lean_ctor_get(v_decl_537_, 0);
lean_inc_ref(v_decl_545_);
lean_dec_ref_known(v_decl_537_, 1);
v___x_546_ = lean_apply_1(v_h__3_540_, v_decl_545_);
return v___x_546_;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object* v_decls_547_, lean_object* v_code_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_array_get_size(v_decls_547_);
v___x_558_ = l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(v_decls_547_, v___x_557_, v_code_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
return v___x_558_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_attachCodeDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_547_ = stack[0].m_obj;
lean_object* v_code_548_ = stack[1].m_obj;
lean_object* v_a_549_ = stack[2].m_obj;
lean_object* v_a_550_ = stack[3].m_obj;
lean_object* v_a_551_ = stack[4].m_obj;
lean_object* v_a_552_ = stack[5].m_obj;
lean_object* v_a_553_ = stack[6].m_obj;
lean_object* v_a_554_ = stack[7].m_obj;
lean_object* v_a_555_ = stack[8].m_obj;
lean_object* v_res_559_;
v_res_559_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_decls_547_, v_code_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object* v_decls_560_, lean_object* v_code_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_decls_560_, v_code_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec_ref(v_decls_560_);
return v_res_570_;
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
