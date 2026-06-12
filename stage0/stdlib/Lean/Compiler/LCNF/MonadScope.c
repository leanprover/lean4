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
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
lean_inc(v___y_4_);
v___x_5_ = lean_apply_1(v___y_2_, v___y_4_);
v___x_6_ = lean_apply_1(v___y_3_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b1_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0(v_00_u03b1_7_, v___y_8_, v___y_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(lean_object* v_inst_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___f_14_ = ((lean_object*)(l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0));
v___x_15_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_15_, 0, lean_box(0));
lean_closure_set(v___x_15_, 1, lean_box(0));
lean_closure_set(v___x_15_, 2, v_inst_13_);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___f_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad(lean_object* v_m_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(v_inst_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object* v_withScope_20_, lean_object* v_f_21_, lean_object* v_00_u03b2_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_apply_3(v_withScope_20_, lean_box(0), v_f_21_, v___y_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1(lean_object* v_withScope_25_, lean_object* v_inst_26_, lean_object* v_00_u03b1_27_, lean_object* v_f_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; 
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_30_, 0, v_withScope_25_);
lean_closure_set(v___f_30_, 1, v_f_28_);
v___x_31_ = lean_apply_3(v_inst_26_, lean_box(0), v___f_30_, v___y_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v_getScope_35_; lean_object* v_withScope_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_45_; 
v_getScope_35_ = lean_ctor_get(v_inst_34_, 0);
v_withScope_36_ = lean_ctor_get(v_inst_34_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_inst_34_);
if (v_isSharedCheck_45_ == 0)
{
v___x_38_ = v_inst_34_;
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_withScope_36_);
lean_inc(v_getScope_35_);
lean_dec(v_inst_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___f_40_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_40_, 0, v_withScope_36_);
lean_closure_set(v___f_40_, 1, v_inst_33_);
v___x_41_ = lean_apply_2(v_inst_32_, lean_box(0), v_getScope_35_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v___f_40_);
lean_ctor_set(v___x_38_, 0, v___x_41_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___f_40_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor(lean_object* v_m_46_, lean_object* v_n_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(v_inst_48_, v_inst_49_, v_inst_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope___redArg___lam__0(lean_object* v___f_52_, lean_object* v_fvarId_53_, lean_object* v_toPure_54_, lean_object* v_____do__lift_55_){
_start:
{
uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_52_, v_fvarId_53_, v_____do__lift_55_);
v___x_57_ = lean_box(v___x_56_);
v___x_58_ = lean_apply_2(v_toPure_54_, lean_box(0), v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_fvarId_62_){
_start:
{
lean_object* v_toApplicative_63_; lean_object* v_toBind_64_; lean_object* v_getScope_65_; lean_object* v_toPure_66_; lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
v_toApplicative_63_ = lean_ctor_get(v_inst_61_, 0);
lean_inc_ref(v_toApplicative_63_);
v_toBind_64_ = lean_ctor_get(v_inst_61_, 1);
lean_inc(v_toBind_64_);
lean_dec_ref(v_inst_61_);
v_getScope_65_ = lean_ctor_get(v_inst_60_, 0);
lean_inc(v_getScope_65_);
lean_dec_ref(v_inst_60_);
v_toPure_66_ = lean_ctor_get(v_toApplicative_63_, 1);
lean_inc(v_toPure_66_);
lean_dec_ref(v_toApplicative_63_);
v___f_67_ = ((lean_object*)(l_Lean_Compiler_LCNF_inScope___redArg___closed__0));
v___f_68_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inScope___redArg___lam__0), 4, 3);
lean_closure_set(v___f_68_, 0, v___f_67_);
lean_closure_set(v___f_68_, 1, v_fvarId_62_);
lean_closure_set(v___f_68_, 2, v_toPure_66_);
v___x_69_ = lean_apply_4(v_toBind_64_, lean_box(0), lean_box(0), v_getScope_65_, v___f_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inScope(lean_object* v_m_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_fvarId_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Compiler_LCNF_inScope___redArg(v_inst_71_, v_inst_72_, v_fvarId_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_75_, lean_object* v_x2_76_){
_start:
{
lean_object* v_fvarId_77_; lean_object* v___x_78_; 
v_fvarId_77_ = lean_ctor_get(v_x2_76_, 0);
lean_inc(v_fvarId_77_);
lean_dec_ref(v_x2_76_);
v___x_78_ = l_Lean_FVarIdSet_insert(v_x1_75_, v_fvarId_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg___lam__1(lean_object* v_ps_98_, lean_object* v___f_99_, lean_object* v_s_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_ps_98_);
v___x_103_ = ((lean_object*)(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9));
v___x_104_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_104_ == 0)
{
lean_dec_ref(v___f_99_);
lean_dec_ref(v_ps_98_);
return v_s_100_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_105_ == 0)
{
if (v___x_104_ == 0)
{
lean_dec_ref(v___f_99_);
lean_dec_ref(v_ps_98_);
return v_s_100_;
}
else
{
size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((size_t)0ULL);
v___x_107_ = lean_usize_of_nat(v___x_102_);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_103_, v___f_99_, v_ps_98_, v___x_106_, v___x_107_, v_s_100_);
return v___x_108_;
}
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_102_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_103_, v___f_99_, v_ps_98_, v___x_109_, v___x_110_, v_s_100_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___redArg(lean_object* v_inst_113_, lean_object* v_ps_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_withScope_116_; lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_withScope_116_ = lean_ctor_get(v_inst_113_, 1);
lean_inc(v_withScope_116_);
lean_dec_ref(v_inst_113_);
v___f_117_ = ((lean_object*)(l_Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___f_118_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withParams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_118_, 0, v_ps_114_);
lean_closure_set(v___f_118_, 1, v___f_117_);
v___x_119_ = lean_apply_3(v_withScope_116_, lean_box(0), v___f_118_, v_x_115_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams(lean_object* v_m_120_, uint8_t v_pu_121_, lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_ps_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_withScope_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___x_130_; 
v_withScope_127_ = lean_ctor_get(v_inst_123_, 1);
lean_inc(v_withScope_127_);
lean_dec_ref(v_inst_123_);
v___f_128_ = ((lean_object*)(l_Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withParams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_129_, 0, v_ps_125_);
lean_closure_set(v___f_129_, 1, v___f_128_);
v___x_130_ = lean_apply_3(v_withScope_127_, lean_box(0), v___f_129_, v_x_126_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withParams___boxed(lean_object* v_m_131_, lean_object* v_pu_132_, lean_object* v_00_u03b1_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_ps_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_pu_boxed_138_; lean_object* v_res_139_; 
v_pu_boxed_138_ = lean_unbox(v_pu_132_);
v_res_139_ = l_Lean_Compiler_LCNF_withParams(v_m_131_, v_pu_boxed_138_, v_00_u03b1_133_, v_inst_134_, v_inst_135_, v_ps_136_, v_x_137_);
lean_dec_ref(v_inst_135_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___redArg___lam__0(lean_object* v_fvarId_140_, lean_object* v_s_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_FVarIdSet_insert(v_s_141_, v_fvarId_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___redArg(lean_object* v_inst_143_, lean_object* v_fvarId_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_withScope_146_; lean_object* v___f_147_; lean_object* v___x_148_; 
v_withScope_146_ = lean_ctor_get(v_inst_143_, 1);
lean_inc(v_withScope_146_);
lean_dec_ref(v_inst_143_);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withFVar___redArg___lam__0), 2, 1);
lean_closure_set(v___f_147_, 0, v_fvarId_144_);
v___x_148_ = lean_apply_3(v_withScope_146_, lean_box(0), v___f_147_, v_x_145_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar(lean_object* v_m_149_, lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_fvarId_153_, lean_object* v_x_154_){
_start:
{
lean_object* v_withScope_155_; lean_object* v___f_156_; lean_object* v___x_157_; 
v_withScope_155_ = lean_ctor_get(v_inst_151_, 1);
lean_inc(v_withScope_155_);
lean_dec_ref(v_inst_151_);
v___f_156_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_withFVar___redArg___lam__0), 2, 1);
lean_closure_set(v___f_156_, 0, v_fvarId_153_);
v___x_157_ = lean_apply_3(v_withScope_155_, lean_box(0), v___f_156_, v_x_154_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withFVar___boxed(lean_object* v_m_158_, lean_object* v_00_u03b1_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_fvarId_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Compiler_LCNF_withFVar(v_m_158_, v_00_u03b1_159_, v_inst_160_, v_inst_161_, v_fvarId_162_, v_x_163_);
lean_dec_ref(v_inst_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(lean_object* v___x_165_, lean_object* v_x_166_){
_start:
{
lean_inc(v___x_165_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0___boxed(lean_object* v___x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(v___x_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v___x_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___redArg(lean_object* v_inst_172_, lean_object* v_x_173_){
_start:
{
lean_object* v_withScope_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v_withScope_174_ = lean_ctor_get(v_inst_172_, 1);
lean_inc(v_withScope_174_);
lean_dec_ref(v_inst_172_);
v___f_175_ = ((lean_object*)(l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0));
v___x_176_ = lean_apply_3(v_withScope_174_, lean_box(0), v___f_175_, v_x_173_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope(lean_object* v_m_177_, lean_object* v_00_u03b1_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_withScope_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v_withScope_182_ = lean_ctor_get(v_inst_179_, 1);
lean_inc(v_withScope_182_);
lean_dec_ref(v_inst_179_);
v___f_183_ = ((lean_object*)(l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0));
v___x_184_ = lean_apply_3(v_withScope_182_, lean_box(0), v___f_183_, v_x_181_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_withNewScope___boxed(lean_object* v_m_185_, lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Compiler_LCNF_withNewScope(v_m_185_, v_00_u03b1_186_, v_inst_187_, v_inst_188_, v_x_189_);
lean_dec_ref(v_inst_188_);
return v_res_190_;
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
