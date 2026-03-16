// Lean compiler output
// Module: Lean.Compiler.LCNF.MonadScope
// Imports: public import Lean.Compiler.LCNF.Basic
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_inScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_inScope___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_inScope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_withParams___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_withParams___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_withParams___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0(lean_object* v_00_u03b1_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v___y_2_, v___y_4_);
v___x_6_ = lean_apply_1(v___y_3_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(lean_object* v_inst_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0));
v___x_10_ = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, lean_box(0));
lean_closure_set(v___x_10_, 2, v_inst_8_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___f_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad(lean_object* v_m_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(v_inst_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object* v_withScope_15_, lean_object* v_f_16_, lean_object* v_00_u03b2_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_apply_3(v_withScope_15_, lean_box(0), v_f_16_, v___y_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1(lean_object* v_withScope_20_, lean_object* v_inst_21_, lean_object* v_00_u03b1_22_, lean_object* v_f_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_25_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_25_, 0, v_withScope_20_);
lean_closure_set(v___f_25_, 1, v_f_23_);
v___x_26_ = lean_apply_3(v_inst_21_, lean_box(0), v___f_25_, v___y_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v_getScope_30_; lean_object* v_withScope_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_40_; 
v_getScope_30_ = lean_ctor_get(v_inst_29_, 0);
v_withScope_31_ = lean_ctor_get(v_inst_29_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_inst_29_);
if (v_isSharedCheck_40_ == 0)
{
v___x_33_ = v_inst_29_;
v_isShared_34_ = v_isSharedCheck_40_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_withScope_31_);
lean_inc(v_getScope_30_);
lean_dec(v_inst_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_40_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___f_35_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_35_, 0, v_withScope_31_);
lean_closure_set(v___f_35_, 1, v_inst_28_);
v___x_36_ = lean_apply_2(v_inst_27_, lean_box(0), v_getScope_30_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___f_35_);
lean_ctor_set(v___x_33_, 0, v___x_36_);
v___x_38_ = v___x_33_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v___f_35_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor(lean_object* v_m_41_, lean_object* v_n_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(v_inst_43_, v_inst_44_, v_inst_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope___redArg___lam__0(lean_object* v___f_47_, lean_object* v_fvarId_48_, lean_object* v_toPure_49_, lean_object* v_____do__lift_50_){
_start:
{
uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_47_, v_fvarId_48_, v_____do__lift_50_);
v___x_52_ = lean_box(v___x_51_);
v___x_53_ = lean_apply_2(v_toPure_49_, lean_box(0), v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope___redArg(lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_fvarId_57_){
_start:
{
lean_object* v_toApplicative_58_; lean_object* v_toBind_59_; lean_object* v_getScope_60_; lean_object* v_toPure_61_; lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
v_toApplicative_58_ = lean_ctor_get(v_inst_56_, 0);
lean_inc_ref(v_toApplicative_58_);
v_toBind_59_ = lean_ctor_get(v_inst_56_, 1);
lean_inc(v_toBind_59_);
lean_dec_ref(v_inst_56_);
v_getScope_60_ = lean_ctor_get(v_inst_55_, 0);
lean_inc(v_getScope_60_);
lean_dec_ref(v_inst_55_);
v_toPure_61_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_61_);
lean_dec_ref(v_toApplicative_58_);
v___f_62_ = ((lean_object*)(l_Lean_Compiler_LCNF_inScope___redArg___closed__0));
v___f_63_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inScope___redArg___lam__0), 4, 3);
lean_closure_set(v___f_63_, 0, v___f_62_);
lean_closure_set(v___f_63_, 1, v_fvarId_57_);
lean_closure_set(v___f_63_, 2, v_toPure_61_);
v___x_64_ = lean_apply_4(v_toBind_59_, lean_box(0), lean_box(0), v_getScope_60_, v___f_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope(lean_object* v_m_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_fvarId_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Compiler_LCNF_inScope___redArg(v_inst_66_, v_inst_67_, v_fvarId_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_70_, lean_object* v_x2_71_){
_start:
{
lean_object* v_fvarId_72_; lean_object* v___x_73_; 
v_fvarId_72_ = lean_ctor_get(v_x2_71_, 0);
lean_inc(v_fvarId_72_);
lean_dec_ref(v_x2_71_);
v___x_73_ = l_Lean_FVarIdSet_insert(v_x1_70_, v_fvarId_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1(lean_object* v_ps_93_, lean_object* v___f_94_, lean_object* v_s_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_array_get_size(v_ps_93_);
v___x_98_ = ((lean_object*)(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9));
v___x_99_ = lean_nat_dec_lt(v___x_96_, v___x_97_);
if (v___x_99_ == 0)
{
lean_dec_ref(v___f_94_);
lean_dec_ref(v_ps_93_);
return v_s_95_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_le(v___x_97_, v___x_97_);
if (v___x_100_ == 0)
{
if (v___x_99_ == 0)
{
lean_dec_ref(v___f_94_);
lean_dec_ref(v_ps_93_);
return v_s_95_;
}
else
{
size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((size_t)0ULL);
v___x_102_ = lean_usize_of_nat(v___x_97_);
v___x_103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_98_, v___f_94_, v_ps_93_, v___x_101_, v___x_102_, v_s_95_);
return v___x_103_;
}
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_97_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_98_, v___f_94_, v_ps_93_, v___x_104_, v___x_105_, v_s_95_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg(lean_object* v_inst_108_, lean_object* v_ps_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_withScope_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; 
v_withScope_111_ = lean_ctor_get(v_inst_108_, 1);
lean_inc(v_withScope_111_);
lean_dec_ref(v_inst_108_);
v___f_112_ = ((lean_object*)(l_Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___f_113_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withParams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_113_, 0, v_ps_109_);
lean_closure_set(v___f_113_, 1, v___f_112_);
v___x_114_ = lean_apply_3(v_withScope_111_, lean_box(0), v___f_113_, v_x_110_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams(lean_object* v_m_115_, uint8_t v_pu_116_, lean_object* v_00_u03b1_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_ps_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_withScope_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; 
v_withScope_122_ = lean_ctor_get(v_inst_118_, 1);
lean_inc(v_withScope_122_);
lean_dec_ref(v_inst_118_);
v___f_123_ = ((lean_object*)(l_Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___f_124_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withParams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_124_, 0, v_ps_120_);
lean_closure_set(v___f_124_, 1, v___f_123_);
v___x_125_ = lean_apply_3(v_withScope_122_, lean_box(0), v___f_124_, v_x_121_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___boxed(lean_object* v_m_126_, lean_object* v_pu_127_, lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_ps_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_pu_boxed_133_; lean_object* v_res_134_; 
v_pu_boxed_133_ = lean_unbox(v_pu_127_);
v_res_134_ = l_Lean_Compiler_LCNF_withParams(v_m_126_, v_pu_boxed_133_, v_00_u03b1_128_, v_inst_129_, v_inst_130_, v_ps_131_, v_x_132_);
lean_dec_ref(v_inst_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___redArg___lam__0(lean_object* v_fvarId_135_, lean_object* v_s_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_FVarIdSet_insert(v_s_136_, v_fvarId_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___redArg(lean_object* v_inst_138_, lean_object* v_fvarId_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_withScope_141_; lean_object* v___f_142_; lean_object* v___x_143_; 
v_withScope_141_ = lean_ctor_get(v_inst_138_, 1);
lean_inc(v_withScope_141_);
lean_dec_ref(v_inst_138_);
v___f_142_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withFVar___redArg___lam__0), 2, 1);
lean_closure_set(v___f_142_, 0, v_fvarId_139_);
v___x_143_ = lean_apply_3(v_withScope_141_, lean_box(0), v___f_142_, v_x_140_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar(lean_object* v_m_144_, lean_object* v_00_u03b1_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_fvarId_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_withScope_150_; lean_object* v___f_151_; lean_object* v___x_152_; 
v_withScope_150_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_withScope_150_);
lean_dec_ref(v_inst_146_);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withFVar___redArg___lam__0), 2, 1);
lean_closure_set(v___f_151_, 0, v_fvarId_148_);
v___x_152_ = lean_apply_3(v_withScope_150_, lean_box(0), v___f_151_, v_x_149_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___boxed(lean_object* v_m_153_, lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_fvarId_157_, lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Compiler_LCNF_withFVar(v_m_153_, v_00_u03b1_154_, v_inst_155_, v_inst_156_, v_fvarId_157_, v_x_158_);
lean_dec_ref(v_inst_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(lean_object* v___x_160_, lean_object* v_x_161_){
_start:
{
lean_inc(v___x_160_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0___boxed(lean_object* v___x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(v___x_162_, v_x_163_);
lean_dec(v_x_163_);
lean_dec(v___x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg(lean_object* v_inst_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_withScope_169_; lean_object* v___f_170_; lean_object* v___x_171_; 
v_withScope_169_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_withScope_169_);
lean_dec_ref(v_inst_167_);
v___f_170_ = ((lean_object*)(l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0));
v___x_171_ = lean_apply_3(v_withScope_169_, lean_box(0), v___f_170_, v_x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope(lean_object* v_m_172_, lean_object* v_00_u03b1_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_withScope_177_; lean_object* v___f_178_; lean_object* v___x_179_; 
v_withScope_177_ = lean_ctor_get(v_inst_174_, 1);
lean_inc(v_withScope_177_);
lean_dec_ref(v_inst_174_);
v___f_178_ = ((lean_object*)(l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0));
v___x_179_ = lean_apply_3(v_withScope_177_, lean_box(0), v___f_178_, v_x_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___boxed(lean_object* v_m_180_, lean_object* v_00_u03b1_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Compiler_LCNF_withNewScope(v_m_180_, v_00_u03b1_181_, v_inst_182_, v_inst_183_, v_x_184_);
lean_dec_ref(v_inst_183_);
return v_res_185_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_MonadScope(builtin);
}
#ifdef __cplusplus
}
#endif
