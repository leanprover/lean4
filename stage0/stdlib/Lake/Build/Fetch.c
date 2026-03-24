// Lean compiler output
// Module: Lake.Build.Fetch
// Imports: public import Lake.Build.Info public import Lake.Build.Store public import Lake.Build.Context public import Lake.Config.Module public import Lake.Util.EquipT public import Lake.Util.Cycle import Lake.Build.Infos
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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0 = (const lean_object*)&l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(lean_object*);
static const lean_string_object l_Lake_buildCycleError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "build cycle detected:\n"};
static const lean_object* l_Lake_buildCycleError___closed__0 = (const lean_object*)&l_Lake_buildCycleError___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildCycleError(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0 = (const lean_object*)&l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0_value;
static const lean_closure_object l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1 = (const lean_object*)&l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_RecBuildT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RecBuildT_run_x27___redArg___closed__0 = (const lean_object*)&l_Lake_RecBuildT_run_x27___redArg___closed__0_value;
static const lean_closure_object l_Lake_RecBuildT_run_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ST_Prim_mkRef___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lake_RecBuildT_run_x27___redArg___closed__1 = (const lean_object*)&l_Lake_RecBuildT_run_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f___redArg___lam__0(lean_object* v_pkg_x3f_1_, lean_object* v_x_2_){
_start:
{
lean_inc(v_pkg_x3f_1_);
return v_pkg_x3f_1_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed(lean_object* v_pkg_x3f_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lake_withCurrPackage_x3f___redArg___lam__0(v_pkg_x3f_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v_pkg_x3f_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f___redArg(lean_object* v_inst_6_, lean_object* v_pkg_x3f_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; 
v___f_9_ = lean_alloc_closure((void*)(l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_9_, 0, v_pkg_x3f_7_);
v___x_10_ = lean_apply_3(v_inst_6_, lean_box(0), v___f_9_, v_x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage_x3f(lean_object* v_m_11_, lean_object* v_00_u03b1_12_, lean_object* v_inst_13_, lean_object* v_pkg_x3f_14_, lean_object* v_x_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; 
v___f_16_ = lean_alloc_closure((void*)(l_Lake_withCurrPackage_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v_pkg_x3f_14_);
v___x_17_ = lean_apply_3(v_inst_13_, lean_box(0), v___f_16_, v_x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage___redArg___lam__0(lean_object* v___x_18_, lean_object* v_x_19_){
_start:
{
lean_inc(v___x_18_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage___redArg___lam__0___boxed(lean_object* v___x_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lake_withCurrPackage___redArg___lam__0(v___x_20_, v_x_21_);
lean_dec(v_x_21_);
lean_dec(v___x_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage___redArg(lean_object* v_inst_23_, lean_object* v_pkg_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v_pkg_24_);
v___f_27_ = lean_alloc_closure((void*)(l_Lake_withCurrPackage___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_27_, 0, v___x_26_);
v___x_28_ = lean_apply_3(v_inst_23_, lean_box(0), v___f_27_, v_x_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_withCurrPackage(lean_object* v_m_29_, lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_pkg_32_, lean_object* v_x_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___f_35_; lean_object* v___x_36_; 
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v_pkg_32_);
v___f_35_ = lean_alloc_closure((void*)(l_Lake_withCurrPackage___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_35_, 0, v___x_34_);
v___x_36_ = lean_apply_3(v_inst_31_, lean_box(0), v___f_35_, v_x_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f___redArg(lean_object* v_inst_37_){
_start:
{
lean_inc(v_inst_37_);
return v_inst_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f___redArg___boxed(lean_object* v_inst_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lake_getCurrPackage_x3f___redArg(v_inst_38_);
lean_dec(v_inst_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f(lean_object* v_m_40_, lean_object* v_inst_41_){
_start:
{
lean_inc(v_inst_41_);
return v_inst_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_getCurrPackage_x3f___boxed(lean_object* v_m_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lake_getCurrPackage_x3f(v_m_42_, v_inst_43_);
lean_dec(v_inst_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
if (lean_obj_tag(v_a_46_) == 0)
{
lean_object* v___x_48_; 
v___x_48_ = l_List_reverse___redArg(v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_61_; 
v_head_49_ = lean_ctor_get(v_a_46_, 0);
v_tail_50_ = lean_ctor_get(v_a_46_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_a_46_);
if (v_isSharedCheck_61_ == 0)
{
v___x_52_ = v_a_46_;
v_isShared_53_ = v_isSharedCheck_61_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_tail_50_);
lean_inc(v_head_49_);
lean_dec(v_a_46_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_61_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_54_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0___closed__0));
v___x_55_ = l_Lake_BuildKey_toString(v_head_49_);
v___x_56_ = lean_string_append(v___x_54_, v___x_55_);
lean_dec_ref(v___x_55_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v_a_47_);
lean_ctor_set(v___x_52_, 0, v___x_56_);
v___x_58_ = v___x_52_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_a_47_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
v_a_46_ = v_tail_50_;
v_a_47_ = v___x_58_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(lean_object* v_cycle_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = ((lean_object*)(l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0___closed__0));
v___x_65_ = lean_box(0);
v___x_66_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_buildCycleError_spec__0_spec__0(v_cycle_63_, v___x_65_);
v___x_67_ = l_String_intercalate(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError(lean_object* v_cycle_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l_Lake_buildCycleError___closed__0));
v___x_71_ = l_Lake_formatCycle___at___00Lake_buildCycleError_spec__0(v_cycle_69_);
v___x_72_ = lean_string_append(v___x_70_, v___x_71_);
lean_dec_ref(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(lean_object* v_inst_73_, lean_object* v_00_u03b1_74_, lean_object* v_cycle_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = l_Lake_buildCycleError(v_cycle_75_);
v___x_81_ = lean_apply_2(v_inst_73_, lean_box(0), v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed(lean_object* v_inst_82_, lean_object* v_00_u03b1_83_, lean_object* v_cycle_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(v_inst_82_, v_00_u03b1_83_, v_cycle_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_86_);
lean_dec(v___y_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(lean_object* v_inst_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___f_94_ = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_94_, 0, v_inst_93_);
v___f_95_ = ((lean_object*)(l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0));
v___f_96_ = ((lean_object*)(l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1));
v___x_97_ = l_ReaderT_instMonad___redArg(v_inst_92_);
v___x_98_ = l_StateRefT_x27_instMonad___redArg(v___x_97_);
v___x_99_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v___x_98_);
v___x_100_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(v___f_95_, v___f_96_, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___f_94_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(lean_object* v_m_102_, lean_object* v_inst_103_, lean_object* v_inst_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(v_inst_103_, v_inst_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__0(lean_object* v_toApplicative_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_toPure_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_toPure_109_ = lean_ctor_get(v_toApplicative_106_, 1);
lean_inc(v_toPure_109_);
lean_dec_ref(v_toApplicative_106_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_a_107_);
lean_ctor_set(v___x_110_, 1, v_a_108_);
v___x_111_ = lean_apply_2(v_toPure_109_, lean_box(0), v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__1(lean_object* v_toApplicative_112_, lean_object* v_a_113_, lean_object* v_inst_114_, lean_object* v_toBind_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_117_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_117_, 0, v_toApplicative_112_);
lean_closure_set(v___f_117_, 1, v_a_116_);
v___x_118_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_118_, 0, lean_box(0));
lean_closure_set(v___x_118_, 1, lean_box(0));
lean_closure_set(v___x_118_, 2, v_a_113_);
v___x_119_ = lean_apply_2(v_inst_114_, lean_box(0), v___x_118_);
v___x_120_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v___x_119_, v___f_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__2(lean_object* v_toApplicative_121_, lean_object* v_inst_122_, lean_object* v_toBind_123_, lean_object* v_build_124_, lean_object* v___x_125_, lean_object* v_stack_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_inc(v_toBind_123_);
lean_inc(v_a_128_);
v___f_129_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_129_, 0, v_toApplicative_121_);
lean_closure_set(v___f_129_, 1, v_a_128_);
lean_closure_set(v___f_129_, 2, v_inst_122_);
lean_closure_set(v___f_129_, 3, v_toBind_123_);
lean_inc_ref(v_a_127_);
v___x_130_ = lean_apply_4(v_build_124_, v___x_125_, v_stack_126_, v_a_128_, v_a_127_);
v___x_131_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_130_, v___f_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__2___boxed(lean_object* v_toApplicative_132_, lean_object* v_inst_133_, lean_object* v_toBind_134_, lean_object* v_build_135_, lean_object* v___x_136_, lean_object* v_stack_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_RecBuildT_run___redArg___lam__2(v_toApplicative_132_, v_inst_133_, v_toBind_134_, v_build_135_, v___x_136_, v_stack_137_, v_a_138_, v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_stack_143_, lean_object* v_store_144_, lean_object* v_build_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_toApplicative_147_; lean_object* v_toBind_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_toApplicative_147_ = lean_ctor_get(v_inst_141_, 0);
lean_inc_ref(v_toApplicative_147_);
v_toBind_148_ = lean_ctor_get(v_inst_141_, 1);
lean_inc(v_toBind_148_);
lean_dec_ref(v_inst_141_);
v___x_149_ = lean_box(0);
lean_inc_ref(v_a_146_);
lean_inc(v_toBind_148_);
lean_inc(v_inst_142_);
v___f_150_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_150_, 0, v_toApplicative_147_);
lean_closure_set(v___f_150_, 1, v_inst_142_);
lean_closure_set(v___f_150_, 2, v_toBind_148_);
lean_closure_set(v___f_150_, 3, v_build_145_);
lean_closure_set(v___f_150_, 4, v___x_149_);
lean_closure_set(v___f_150_, 5, v_stack_143_);
lean_closure_set(v___f_150_, 6, v_a_146_);
v___x_151_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_151_, 0, lean_box(0));
lean_closure_set(v___x_151_, 1, lean_box(0));
lean_closure_set(v___x_151_, 2, v_store_144_);
v___x_152_ = lean_apply_2(v_inst_142_, lean_box(0), v___x_151_);
v___x_153_ = lean_apply_4(v_toBind_148_, lean_box(0), lean_box(0), v___x_152_, v___f_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___boxed(lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_stack_156_, lean_object* v_store_157_, lean_object* v_build_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lake_RecBuildT_run___redArg(v_inst_154_, v_inst_155_, v_stack_156_, v_store_157_, v_build_158_, v_a_159_);
lean_dec_ref(v_a_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run(lean_object* v_m_161_, lean_object* v_00_u03b1_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_stack_165_, lean_object* v_store_166_, lean_object* v_build_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toBind_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_163_, 0);
lean_inc_ref(v_toApplicative_169_);
v_toBind_170_ = lean_ctor_get(v_inst_163_, 1);
lean_inc(v_toBind_170_);
lean_dec_ref(v_inst_163_);
v___x_171_ = lean_box(0);
lean_inc_ref(v_a_168_);
lean_inc(v_toBind_170_);
lean_inc(v_inst_164_);
v___f_172_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_172_, 0, v_toApplicative_169_);
lean_closure_set(v___f_172_, 1, v_inst_164_);
lean_closure_set(v___f_172_, 2, v_toBind_170_);
lean_closure_set(v___f_172_, 3, v_build_167_);
lean_closure_set(v___f_172_, 4, v___x_171_);
lean_closure_set(v___f_172_, 5, v_stack_165_);
lean_closure_set(v___f_172_, 6, v_a_168_);
v___x_173_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, lean_box(0));
lean_closure_set(v___x_173_, 2, v_store_166_);
v___x_174_ = lean_apply_2(v_inst_164_, lean_box(0), v___x_173_);
v___x_175_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_174_, v___f_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___boxed(lean_object* v_m_176_, lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_stack_180_, lean_object* v_store_181_, lean_object* v_build_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lake_RecBuildT_run(v_m_176_, v_00_u03b1_177_, v_inst_178_, v_inst_179_, v_stack_180_, v_store_181_, v_build_182_, v_a_183_);
lean_dec_ref(v_a_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0(lean_object* v_x_185_){
_start:
{
lean_object* v_fst_186_; 
v_fst_186_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_fst_186_);
return v_fst_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lake_RecBuildT_run_x27___redArg___lam__0(v_x_187_);
lean_dec_ref(v_x_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__1(lean_object* v_a_189_, lean_object* v_toPure_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_a_189_);
lean_ctor_set(v___x_192_, 1, v_a_191_);
v___x_193_ = lean_apply_2(v_toPure_190_, lean_box(0), v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__2(lean_object* v_toPure_194_, lean_object* v_a_195_, lean_object* v_inst_196_, lean_object* v_toBind_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___f_199_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_199_, 0, v_a_198_);
lean_closure_set(v___f_199_, 1, v_toPure_194_);
v___x_200_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, lean_box(0));
lean_closure_set(v___x_200_, 2, v_a_195_);
v___x_201_ = lean_apply_2(v_inst_196_, lean_box(0), v___x_200_);
v___x_202_ = lean_apply_4(v_toBind_197_, lean_box(0), lean_box(0), v___x_201_, v___f_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3(lean_object* v_toPure_203_, lean_object* v_inst_204_, lean_object* v_toBind_205_, lean_object* v_build_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_inc(v_toBind_205_);
lean_inc(v_a_210_);
v___f_211_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_211_, 0, v_toPure_203_);
lean_closure_set(v___f_211_, 1, v_a_210_);
lean_closure_set(v___f_211_, 2, v_inst_204_);
lean_closure_set(v___f_211_, 3, v_toBind_205_);
lean_inc_ref(v_a_209_);
v___x_212_ = lean_apply_4(v_build_206_, v___x_207_, v___x_208_, v_a_210_, v_a_209_);
v___x_213_ = lean_apply_4(v_toBind_205_, lean_box(0), lean_box(0), v___x_212_, v___f_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed(lean_object* v_toPure_214_, lean_object* v_inst_215_, lean_object* v_toBind_216_, lean_object* v_build_217_, lean_object* v___x_218_, lean_object* v___x_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lake_RecBuildT_run_x27___redArg___lam__3(v_toPure_214_, v_inst_215_, v_toBind_216_, v_build_217_, v___x_218_, v___x_219_, v_a_220_, v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg(lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_build_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_toApplicative_230_; lean_object* v_toFunctor_231_; lean_object* v_toBind_232_; lean_object* v_toPure_233_; lean_object* v_map_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_toApplicative_230_ = lean_ctor_get(v_inst_226_, 0);
lean_inc_ref(v_toApplicative_230_);
v_toFunctor_231_ = lean_ctor_get(v_toApplicative_230_, 0);
lean_inc_ref(v_toFunctor_231_);
v_toBind_232_ = lean_ctor_get(v_inst_226_, 1);
lean_inc(v_toBind_232_);
lean_dec_ref(v_inst_226_);
v_toPure_233_ = lean_ctor_get(v_toApplicative_230_, 1);
lean_inc(v_toPure_233_);
lean_dec_ref(v_toApplicative_230_);
v_map_234_ = lean_ctor_get(v_toFunctor_231_, 0);
lean_inc(v_map_234_);
lean_dec_ref(v_toFunctor_231_);
v___f_235_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__0));
v___x_236_ = lean_box(0);
v___x_237_ = lean_box(0);
lean_inc_ref(v_a_229_);
lean_inc(v_toBind_232_);
lean_inc(v_inst_227_);
v___f_238_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_238_, 0, v_toPure_233_);
lean_closure_set(v___f_238_, 1, v_inst_227_);
lean_closure_set(v___f_238_, 2, v_toBind_232_);
lean_closure_set(v___f_238_, 3, v_build_228_);
lean_closure_set(v___f_238_, 4, v___x_237_);
lean_closure_set(v___f_238_, 5, v___x_236_);
lean_closure_set(v___f_238_, 6, v_a_229_);
v___x_239_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__1));
v___x_240_ = lean_apply_2(v_inst_227_, lean_box(0), v___x_239_);
v___x_241_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_240_, v___f_238_);
v___x_242_ = lean_apply_4(v_map_234_, lean_box(0), lean_box(0), v___f_235_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___boxed(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_build_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_RecBuildT_run_x27___redArg(v_inst_243_, v_inst_244_, v_build_245_, v_a_246_);
lean_dec_ref(v_a_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27(lean_object* v_m_248_, lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_build_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toFunctor_255_; lean_object* v_toBind_256_; lean_object* v_toPure_257_; lean_object* v_map_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_250_, 0);
lean_inc_ref(v_toApplicative_254_);
v_toFunctor_255_ = lean_ctor_get(v_toApplicative_254_, 0);
lean_inc_ref(v_toFunctor_255_);
v_toBind_256_ = lean_ctor_get(v_inst_250_, 1);
lean_inc(v_toBind_256_);
lean_dec_ref(v_inst_250_);
v_toPure_257_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_inc(v_toPure_257_);
lean_dec_ref(v_toApplicative_254_);
v_map_258_ = lean_ctor_get(v_toFunctor_255_, 0);
lean_inc(v_map_258_);
lean_dec_ref(v_toFunctor_255_);
v___f_259_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__0));
v___x_260_ = lean_box(0);
v___x_261_ = lean_box(0);
lean_inc_ref(v_a_253_);
lean_inc(v_toBind_256_);
lean_inc(v_inst_251_);
v___f_262_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_262_, 0, v_toPure_257_);
lean_closure_set(v___f_262_, 1, v_inst_251_);
lean_closure_set(v___f_262_, 2, v_toBind_256_);
lean_closure_set(v___f_262_, 3, v_build_252_);
lean_closure_set(v___f_262_, 4, v___x_261_);
lean_closure_set(v___f_262_, 5, v___x_260_);
lean_closure_set(v___f_262_, 6, v_a_253_);
v___x_263_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__1));
v___x_264_ = lean_apply_2(v_inst_251_, lean_box(0), v___x_263_);
v___x_265_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v___x_264_, v___f_262_);
v___x_266_ = lean_apply_4(v_map_258_, lean_box(0), lean_box(0), v___f_259_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___boxed(lean_object* v_m_267_, lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_build_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lake_RecBuildT_run_x27(v_m_267_, v_00_u03b1_268_, v_inst_269_, v_inst_270_, v_build_271_, v_a_272_);
lean_dec_ref(v_a_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___redArg(lean_object* v_f_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; 
lean_inc_ref(v_a_279_);
lean_inc(v_a_278_);
lean_inc(v_a_277_);
lean_inc(v_a_276_);
v___x_282_ = lean_apply_7(v_f_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, lean_box(0));
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___redArg___boxed(lean_object* v_f_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lake_FetchM_ofFn___redArg(v_f_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec(v_a_286_);
lean_dec(v_a_285_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn(lean_object* v_00_u03b1_292_, lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
lean_inc_ref(v_a_298_);
lean_inc(v_a_297_);
lean_inc(v_a_296_);
lean_inc(v_a_295_);
v___x_301_ = lean_apply_7(v_f_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, lean_box(0));
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___boxed(lean_object* v_00_u03b1_302_, lean_object* v_f_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lake_FetchM_ofFn(v_00_u03b1_302_, v_f_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___redArg(lean_object* v_self_312_, lean_object* v_fetch_313_, lean_object* v_pkg_x3f_314_, lean_object* v_stack_315_, lean_object* v_store_316_, lean_object* v_ctx_317_, lean_object* v_log_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_apply_7(v_self_312_, v_fetch_313_, v_pkg_x3f_314_, v_stack_315_, v_store_316_, v_ctx_317_, v_log_318_, lean_box(0));
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___redArg___boxed(lean_object* v_self_321_, lean_object* v_fetch_322_, lean_object* v_pkg_x3f_323_, lean_object* v_stack_324_, lean_object* v_store_325_, lean_object* v_ctx_326_, lean_object* v_log_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lake_FetchM_toFn___redArg(v_self_321_, v_fetch_322_, v_pkg_x3f_323_, v_stack_324_, v_store_325_, v_ctx_326_, v_log_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn(lean_object* v_00_u03b1_330_, lean_object* v_self_331_, lean_object* v_fetch_332_, lean_object* v_pkg_x3f_333_, lean_object* v_stack_334_, lean_object* v_store_335_, lean_object* v_ctx_336_, lean_object* v_log_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_apply_7(v_self_331_, v_fetch_332_, v_pkg_x3f_333_, v_stack_334_, v_store_335_, v_ctx_336_, v_log_337_, lean_box(0));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___boxed(lean_object* v_00_u03b1_340_, lean_object* v_self_341_, lean_object* v_fetch_342_, lean_object* v_pkg_x3f_343_, lean_object* v_stack_344_, lean_object* v_store_345_, lean_object* v_ctx_346_, lean_object* v_log_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lake_FetchM_toFn(v_00_u03b1_340_, v_self_341_, v_fetch_342_, v_pkg_x3f_343_, v_stack_344_, v_store_345_, v_ctx_346_, v_log_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg(lean_object* v_self_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; 
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_inc(v_a_352_);
v___x_358_ = lean_apply_7(v_a_351_, v_self_350_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, lean_box(0));
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg___boxed(lean_object* v_self_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lake_BuildInfo_fetch___redArg(v_self_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec(v_a_362_);
lean_dec(v_a_361_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object* v_00_u03b1_368_, lean_object* v_self_369_, lean_object* v_inst_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
lean_inc_ref(v_a_375_);
lean_inc(v_a_374_);
lean_inc(v_a_373_);
lean_inc(v_a_372_);
v___x_378_ = lean_apply_7(v_a_371_, v_self_369_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, lean_box(0));
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___boxed(lean_object* v_00_u03b1_379_, lean_object* v_self_380_, lean_object* v_inst_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_BuildInfo_fetch(v_00_u03b1_379_, v_self_380_, v_inst_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec(v_a_384_);
lean_dec(v_a_383_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object* v_self_390_, lean_object* v_mod_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_lib_399_; lean_object* v_pkg_400_; lean_object* v_name_401_; lean_object* v_keyName_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_lib_399_ = lean_ctor_get(v_mod_391_, 0);
v_pkg_400_ = lean_ctor_get(v_lib_399_, 0);
v_name_401_ = lean_ctor_get(v_mod_391_, 1);
v_keyName_402_ = lean_ctor_get(v_pkg_400_, 2);
lean_inc(v_name_401_);
lean_inc(v_keyName_402_);
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v_keyName_402_);
lean_ctor_set(v___x_403_, 1, v_name_401_);
v___x_404_ = l_Lake_Module_keyword;
v___x_405_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v_mod_391_);
lean_ctor_set(v___x_405_, 3, v_self_390_);
lean_inc_ref(v_a_396_);
lean_inc(v_a_395_);
lean_inc(v_a_394_);
lean_inc(v_a_393_);
v___x_406_ = lean_apply_7(v_a_392_, v___x_405_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, lean_box(0));
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg___boxed(lean_object* v_self_407_, lean_object* v_mod_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_ModuleFacet_fetch___redArg(v_self_407_, v_mod_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec(v_a_411_);
lean_dec(v_a_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch(lean_object* v_00_u03b1_417_, lean_object* v_self_418_, lean_object* v_mod_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lake_ModuleFacet_fetch___redArg(v_self_418_, v_mod_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___boxed(lean_object* v_00_u03b1_428_, lean_object* v_self_429_, lean_object* v_mod_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lake_ModuleFacet_fetch(v_00_u03b1_428_, v_self_429_, v_mod_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec(v_a_433_);
lean_dec(v_a_432_);
return v_res_438_;
}
}
lean_object* runtime_initialize_Lake_Build_Info(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Store(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Context(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Module(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_EquipT(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Cycle(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Info(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_EquipT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Cycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Info(uint8_t builtin);
lean_object* initialize_Lake_Build_Store(uint8_t builtin);
lean_object* initialize_Lake_Build_Context(uint8_t builtin);
lean_object* initialize_Lake_Config_Module(uint8_t builtin);
lean_object* initialize_Lake_Util_EquipT(uint8_t builtin);
lean_object* initialize_Lake_Util_Cycle(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Info(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EquipT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Cycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Fetch(builtin);
}
#ifdef __cplusplus
}
#endif
