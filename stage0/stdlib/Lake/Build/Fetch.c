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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_RecBuildT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RecBuildT_run_x27___redArg___closed__0 = (const lean_object*)&l_Lake_RecBuildT_run_x27___redArg___closed__0_value;
static const lean_closure_object l_Lake_RecBuildT_run_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ST_Prim_mkRef___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lake_RecBuildT_run_x27___redArg___closed__1 = (const lean_object*)&l_Lake_RecBuildT_run_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_98_ = l_ReaderT_instMonad___redArg(v___x_97_);
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
v___x_130_ = lean_apply_4(v_build_124_, v___x_125_, v_stack_126_, v_a_128_, v_a_127_);
v___x_131_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_130_, v___f_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_stack_134_, lean_object* v_store_135_, lean_object* v_build_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_toApplicative_138_; lean_object* v_toBind_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_toApplicative_138_ = lean_ctor_get(v_inst_132_, 0);
lean_inc_ref(v_toApplicative_138_);
v_toBind_139_ = lean_ctor_get(v_inst_132_, 1);
lean_inc(v_toBind_139_);
lean_dec_ref(v_inst_132_);
v___x_140_ = lean_box(0);
lean_inc(v_toBind_139_);
lean_inc(v_inst_133_);
v___f_141_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__2), 8, 7);
lean_closure_set(v___f_141_, 0, v_toApplicative_138_);
lean_closure_set(v___f_141_, 1, v_inst_133_);
lean_closure_set(v___f_141_, 2, v_toBind_139_);
lean_closure_set(v___f_141_, 3, v_build_136_);
lean_closure_set(v___f_141_, 4, v___x_140_);
lean_closure_set(v___f_141_, 5, v_stack_134_);
lean_closure_set(v___f_141_, 6, v_a_137_);
v___x_142_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_142_, 0, lean_box(0));
lean_closure_set(v___x_142_, 1, lean_box(0));
lean_closure_set(v___x_142_, 2, v_store_135_);
v___x_143_ = lean_apply_2(v_inst_133_, lean_box(0), v___x_142_);
v___x_144_ = lean_apply_4(v_toBind_139_, lean_box(0), lean_box(0), v___x_143_, v___f_141_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run(lean_object* v_m_145_, lean_object* v_00_u03b1_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_stack_149_, lean_object* v_store_150_, lean_object* v_build_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_toApplicative_153_; lean_object* v_toBind_154_; lean_object* v___x_155_; lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_toApplicative_153_ = lean_ctor_get(v_inst_147_, 0);
lean_inc_ref(v_toApplicative_153_);
v_toBind_154_ = lean_ctor_get(v_inst_147_, 1);
lean_inc(v_toBind_154_);
lean_dec_ref(v_inst_147_);
v___x_155_ = lean_box(0);
lean_inc(v_toBind_154_);
lean_inc(v_inst_148_);
v___f_156_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__2), 8, 7);
lean_closure_set(v___f_156_, 0, v_toApplicative_153_);
lean_closure_set(v___f_156_, 1, v_inst_148_);
lean_closure_set(v___f_156_, 2, v_toBind_154_);
lean_closure_set(v___f_156_, 3, v_build_151_);
lean_closure_set(v___f_156_, 4, v___x_155_);
lean_closure_set(v___f_156_, 5, v_stack_149_);
lean_closure_set(v___f_156_, 6, v_a_152_);
v___x_157_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_157_, 0, lean_box(0));
lean_closure_set(v___x_157_, 1, lean_box(0));
lean_closure_set(v___x_157_, 2, v_store_150_);
v___x_158_ = lean_apply_2(v_inst_148_, lean_box(0), v___x_157_);
v___x_159_ = lean_apply_4(v_toBind_154_, lean_box(0), lean_box(0), v___x_158_, v___f_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0(lean_object* v_x_160_){
_start:
{
lean_object* v_fst_161_; 
v_fst_161_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_fst_161_);
return v_fst_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(lean_object* v_x_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lake_RecBuildT_run_x27___redArg___lam__0(v_x_162_);
lean_dec_ref(v_x_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__1(lean_object* v_a_164_, lean_object* v_toPure_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_a_164_);
lean_ctor_set(v___x_167_, 1, v_a_166_);
v___x_168_ = lean_apply_2(v_toPure_165_, lean_box(0), v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__2(lean_object* v_toPure_169_, lean_object* v_a_170_, lean_object* v_inst_171_, lean_object* v_toBind_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___f_174_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_174_, 0, v_a_173_);
lean_closure_set(v___f_174_, 1, v_toPure_169_);
v___x_175_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_175_, 0, lean_box(0));
lean_closure_set(v___x_175_, 1, lean_box(0));
lean_closure_set(v___x_175_, 2, v_a_170_);
v___x_176_ = lean_apply_2(v_inst_171_, lean_box(0), v___x_175_);
v___x_177_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_176_, v___f_174_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3(lean_object* v_toPure_178_, lean_object* v_inst_179_, lean_object* v_toBind_180_, lean_object* v_build_181_, lean_object* v___x_182_, lean_object* v___x_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc(v_toBind_180_);
lean_inc(v_a_185_);
v___f_186_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_186_, 0, v_toPure_178_);
lean_closure_set(v___f_186_, 1, v_a_185_);
lean_closure_set(v___f_186_, 2, v_inst_179_);
lean_closure_set(v___f_186_, 3, v_toBind_180_);
v___x_187_ = lean_apply_4(v_build_181_, v___x_182_, v___x_183_, v_a_185_, v_a_184_);
v___x_188_ = lean_apply_4(v_toBind_180_, lean_box(0), lean_box(0), v___x_187_, v___f_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_build_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_toApplicative_196_; lean_object* v_toFunctor_197_; lean_object* v_toBind_198_; lean_object* v_toPure_199_; lean_object* v_map_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_toApplicative_196_ = lean_ctor_get(v_inst_192_, 0);
lean_inc_ref(v_toApplicative_196_);
v_toFunctor_197_ = lean_ctor_get(v_toApplicative_196_, 0);
lean_inc_ref(v_toFunctor_197_);
v_toBind_198_ = lean_ctor_get(v_inst_192_, 1);
lean_inc(v_toBind_198_);
lean_dec_ref(v_inst_192_);
v_toPure_199_ = lean_ctor_get(v_toApplicative_196_, 1);
lean_inc(v_toPure_199_);
lean_dec_ref(v_toApplicative_196_);
v_map_200_ = lean_ctor_get(v_toFunctor_197_, 0);
lean_inc(v_map_200_);
lean_dec_ref(v_toFunctor_197_);
v___f_201_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__0));
v___x_202_ = lean_box(0);
v___x_203_ = lean_box(0);
lean_inc(v_toBind_198_);
lean_inc(v_inst_193_);
v___f_204_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_204_, 0, v_toPure_199_);
lean_closure_set(v___f_204_, 1, v_inst_193_);
lean_closure_set(v___f_204_, 2, v_toBind_198_);
lean_closure_set(v___f_204_, 3, v_build_194_);
lean_closure_set(v___f_204_, 4, v___x_203_);
lean_closure_set(v___f_204_, 5, v___x_202_);
lean_closure_set(v___f_204_, 6, v_a_195_);
v___x_205_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__1));
v___x_206_ = lean_apply_2(v_inst_193_, lean_box(0), v___x_205_);
v___x_207_ = lean_apply_4(v_toBind_198_, lean_box(0), lean_box(0), v___x_206_, v___f_204_);
v___x_208_ = lean_apply_4(v_map_200_, lean_box(0), lean_box(0), v___f_201_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27(lean_object* v_m_209_, lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_build_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_toApplicative_215_; lean_object* v_toFunctor_216_; lean_object* v_toBind_217_; lean_object* v_toPure_218_; lean_object* v_map_219_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_toApplicative_215_ = lean_ctor_get(v_inst_211_, 0);
lean_inc_ref(v_toApplicative_215_);
v_toFunctor_216_ = lean_ctor_get(v_toApplicative_215_, 0);
lean_inc_ref(v_toFunctor_216_);
v_toBind_217_ = lean_ctor_get(v_inst_211_, 1);
lean_inc(v_toBind_217_);
lean_dec_ref(v_inst_211_);
v_toPure_218_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_218_);
lean_dec_ref(v_toApplicative_215_);
v_map_219_ = lean_ctor_get(v_toFunctor_216_, 0);
lean_inc(v_map_219_);
lean_dec_ref(v_toFunctor_216_);
v___f_220_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__0));
v___x_221_ = lean_box(0);
v___x_222_ = lean_box(0);
lean_inc(v_toBind_217_);
lean_inc(v_inst_212_);
v___f_223_ = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_223_, 0, v_toPure_218_);
lean_closure_set(v___f_223_, 1, v_inst_212_);
lean_closure_set(v___f_223_, 2, v_toBind_217_);
lean_closure_set(v___f_223_, 3, v_build_213_);
lean_closure_set(v___f_223_, 4, v___x_222_);
lean_closure_set(v___f_223_, 5, v___x_221_);
lean_closure_set(v___f_223_, 6, v_a_214_);
v___x_224_ = ((lean_object*)(l_Lake_RecBuildT_run_x27___redArg___closed__1));
v___x_225_ = lean_apply_2(v_inst_212_, lean_box(0), v___x_224_);
v___x_226_ = lean_apply_4(v_toBind_217_, lean_box(0), lean_box(0), v___x_225_, v___f_223_);
v___x_227_ = lean_apply_4(v_map_219_, lean_box(0), lean_box(0), v___f_220_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___redArg(lean_object* v_f_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_apply_7(v_f_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, lean_box(0));
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___redArg___boxed(lean_object* v_f_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_FetchM_ofFn___redArg(v_f_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn(lean_object* v_00_u03b1_246_, lean_object* v_f_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_apply_7(v_f_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, lean_box(0));
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_ofFn___boxed(lean_object* v_00_u03b1_256_, lean_object* v_f_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lake_FetchM_ofFn(v_00_u03b1_256_, v_f_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___redArg(lean_object* v_self_266_, lean_object* v_fetch_267_, lean_object* v_pkg_x3f_268_, lean_object* v_stack_269_, lean_object* v_store_270_, lean_object* v_ctx_271_, lean_object* v_log_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_apply_7(v_self_266_, v_fetch_267_, v_pkg_x3f_268_, v_stack_269_, v_store_270_, v_ctx_271_, v_log_272_, lean_box(0));
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___redArg___boxed(lean_object* v_self_275_, lean_object* v_fetch_276_, lean_object* v_pkg_x3f_277_, lean_object* v_stack_278_, lean_object* v_store_279_, lean_object* v_ctx_280_, lean_object* v_log_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lake_FetchM_toFn___redArg(v_self_275_, v_fetch_276_, v_pkg_x3f_277_, v_stack_278_, v_store_279_, v_ctx_280_, v_log_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn(lean_object* v_00_u03b1_284_, lean_object* v_self_285_, lean_object* v_fetch_286_, lean_object* v_pkg_x3f_287_, lean_object* v_stack_288_, lean_object* v_store_289_, lean_object* v_ctx_290_, lean_object* v_log_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_apply_7(v_self_285_, v_fetch_286_, v_pkg_x3f_287_, v_stack_288_, v_store_289_, v_ctx_290_, v_log_291_, lean_box(0));
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_toFn___boxed(lean_object* v_00_u03b1_294_, lean_object* v_self_295_, lean_object* v_fetch_296_, lean_object* v_pkg_x3f_297_, lean_object* v_stack_298_, lean_object* v_store_299_, lean_object* v_ctx_300_, lean_object* v_log_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lake_FetchM_toFn(v_00_u03b1_294_, v_self_295_, v_fetch_296_, v_pkg_x3f_297_, v_stack_298_, v_store_299_, v_ctx_300_, v_log_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg(lean_object* v_self_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_apply_7(v_a_305_, v_self_304_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, lean_box(0));
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg___boxed(lean_object* v_self_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lake_BuildInfo_fetch___redArg(v_self_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object* v_00_u03b1_322_, lean_object* v_self_323_, lean_object* v_inst_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_apply_7(v_a_325_, v_self_323_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, lean_box(0));
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___boxed(lean_object* v_00_u03b1_333_, lean_object* v_self_334_, lean_object* v_inst_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lake_BuildInfo_fetch(v_00_u03b1_333_, v_self_334_, v_inst_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object* v_self_344_, lean_object* v_mod_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_lib_353_; lean_object* v_pkg_354_; lean_object* v_name_355_; lean_object* v_keyName_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_lib_353_ = lean_ctor_get(v_mod_345_, 0);
v_pkg_354_ = lean_ctor_get(v_lib_353_, 0);
v_name_355_ = lean_ctor_get(v_mod_345_, 1);
v_keyName_356_ = lean_ctor_get(v_pkg_354_, 2);
lean_inc(v_name_355_);
lean_inc(v_keyName_356_);
v___x_357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_357_, 0, v_keyName_356_);
lean_ctor_set(v___x_357_, 1, v_name_355_);
v___x_358_ = l_Lake_Module_keyword;
v___x_359_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
lean_ctor_set(v___x_359_, 2, v_mod_345_);
lean_ctor_set(v___x_359_, 3, v_self_344_);
v___x_360_ = lean_apply_7(v_a_346_, v___x_359_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, lean_box(0));
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg___boxed(lean_object* v_self_361_, lean_object* v_mod_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lake_ModuleFacet_fetch___redArg(v_self_361_, v_mod_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch(lean_object* v_00_u03b1_371_, lean_object* v_self_372_, lean_object* v_mod_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lake_ModuleFacet_fetch___redArg(v_self_372_, v_mod_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___boxed(lean_object* v_00_u03b1_382_, lean_object* v_self_383_, lean_object* v_mod_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lake_ModuleFacet_fetch(v_00_u03b1_382_, v_self_383_, v_mod_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
return v_res_392_;
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
