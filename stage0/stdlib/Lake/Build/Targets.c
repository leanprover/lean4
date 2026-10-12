// Lean compiler output
// Module: Lake.Build.Targets
// Imports: public import Lake.Config.Monad public import Lake.Config.InputFile import Lake.Build.Infos
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
extern lean_object* l_Lake_LeanLib_defaultFacet;
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
extern lean_object* l_Lake_LeanExe_exeFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lake_InputDir_defaultFacet;
extern lean_object* l_Lake_InputDir_keyword;
extern lean_object* l_Lake_InputFile_defaultFacet;
extern lean_object* l_Lake_InputFile_keyword;
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__0___boxed(lean_object*);
static const lean_string_object l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "package of target '"};
static const lean_object* l_Lake_KConfigDecl_get___redArg___lam__1___closed__0 = (const lean_object*)&l_Lake_KConfigDecl_get___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_KConfigDecl_get___redArg___lam__1___closed__1 = (const lean_object*)&l_Lake_KConfigDecl_get___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "' not found in workspace"};
static const lean_object* l_Lake_KConfigDecl_get___redArg___lam__1___closed__2 = (const lean_object*)&l_Lake_KConfigDecl_get___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_KConfigDecl_get___redArg___lam__2___closed__0 = (const lean_object*)&l_Lake_KConfigDecl_get___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_KConfigDecl_get___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_KConfigDecl_get___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_KConfigDecl_get___redArg___closed__0 = (const lean_object*)&l_Lake_KConfigDecl_get___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchTargetJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_TargetDecl_fetch___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "package '"};
static const lean_object* l_Lake_TargetDecl_fetch___redArg___closed__0 = (const lean_object*)&l_Lake_TargetDecl_fetch___redArg___closed__0_value;
static const lean_string_object l_Lake_TargetDecl_fetch___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "' of target '"};
static const lean_object* l_Lake_TargetDecl_fetch___redArg___closed__1 = (const lean_object*)&l_Lake_TargetDecl_fetch___redArg___closed__1_value;
static const lean_string_object l_Lake_TargetDecl_fetch___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "' does not exist in workspace"};
static const lean_object* l_Lake_TargetDecl_fetch___redArg___closed__2 = (const lean_object*)&l_Lake_TargetDecl_fetch___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetchJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetchJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchFacetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchFacetJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_fetchFacetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_fetchFacetJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_LeanLib_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_LeanLib_fetch___closed__0 = (const lean_object*)&l_Lake_LeanLib_fetch___closed__0_value;
static const lean_ctor_object l_Lake_LeanLib_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LeanLib_fetch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_LeanLib_fetch___closed__1 = (const lean_object*)&l_Lake_LeanLib_fetch___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetchFacetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetchFacetJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_inc(v_x_1_);
return v_x_1_;
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__0___boxed(lean_object* v_x_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Lake_KConfigDecl_get___redArg___lam__0(v_x_2_);
lean_dec(v_x_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__1(lean_object* v_name_7_, lean_object* v_config_8_, lean_object* v_toPure_9_, lean_object* v_pkg_10_, lean_object* v_inst_11_, lean_object* v_____x_12_){
_start:
{
if (lean_obj_tag(v_____x_12_) == 1)
{
lean_object* v_val_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_inst_11_);
lean_dec(v_pkg_10_);
v_val_13_ = lean_ctor_get(v_____x_12_, 0);
lean_inc(v_val_13_);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v_val_13_);
lean_ctor_set(v___x_14_, 1, v_name_7_);
lean_ctor_set(v___x_14_, 2, v_config_8_);
v___x_15_ = lean_apply_2(v_toPure_9_, lean_box(0), v___x_14_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_toPure_9_);
lean_dec(v_config_8_);
v___x_16_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_17_ = 1;
v___x_18_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_10_, v___x_17_);
v___x_19_ = lean_string_append(v___x_16_, v___x_18_);
lean_dec_ref(v___x_18_);
v___x_20_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_21_ = lean_string_append(v___x_19_, v___x_20_);
v___x_22_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_7_, v___x_17_);
v___x_23_ = lean_string_append(v___x_21_, v___x_22_);
lean_dec_ref(v___x_22_);
v___x_24_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_25_ = lean_string_append(v___x_23_, v___x_24_);
v___x_26_ = lean_apply_2(v_inst_11_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__1___boxed(lean_object* v_name_27_, lean_object* v_config_28_, lean_object* v_toPure_29_, lean_object* v_pkg_30_, lean_object* v_inst_31_, lean_object* v_____x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lake_KConfigDecl_get___redArg___lam__1(v_name_27_, v_config_28_, v_toPure_29_, v_pkg_30_, v_inst_31_, v_____x_32_);
lean_dec(v_____x_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg___lam__2(lean_object* v_pkg_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_packageMap_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_packageMap_37_ = lean_ctor_get(v_x_36_, 5);
lean_inc(v_packageMap_37_);
lean_dec_ref(v_x_36_);
v___x_38_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
v___x_39_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_38_, v_packageMap_37_, v_pkg_35_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___redArg(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_self_44_){
_start:
{
lean_object* v_toApplicative_45_; lean_object* v_toFunctor_46_; lean_object* v_toBind_47_; lean_object* v_toPure_48_; lean_object* v_pkg_49_; lean_object* v_name_50_; lean_object* v_config_51_; lean_object* v_map_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_toApplicative_45_ = lean_ctor_get(v_inst_41_, 0);
lean_inc_ref(v_toApplicative_45_);
v_toFunctor_46_ = lean_ctor_get(v_toApplicative_45_, 0);
lean_inc_ref(v_toFunctor_46_);
v_toBind_47_ = lean_ctor_get(v_inst_41_, 1);
lean_inc(v_toBind_47_);
lean_dec_ref(v_inst_41_);
v_toPure_48_ = lean_ctor_get(v_toApplicative_45_, 1);
lean_inc(v_toPure_48_);
lean_dec_ref(v_toApplicative_45_);
v_pkg_49_ = lean_ctor_get(v_self_44_, 0);
lean_inc_n(v_pkg_49_, 2);
v_name_50_ = lean_ctor_get(v_self_44_, 1);
lean_inc(v_name_50_);
v_config_51_ = lean_ctor_get(v_self_44_, 3);
lean_inc(v_config_51_);
lean_dec_ref(v_self_44_);
v_map_52_ = lean_ctor_get(v_toFunctor_46_, 0);
lean_inc_n(v_map_52_, 2);
lean_dec_ref(v_toFunctor_46_);
v___f_53_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_54_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_54_, 0, v_name_50_);
lean_closure_set(v___f_54_, 1, v_config_51_);
lean_closure_set(v___f_54_, 2, v_toPure_48_);
lean_closure_set(v___f_54_, 3, v_pkg_49_);
lean_closure_set(v___f_54_, 4, v_inst_42_);
v___f_55_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_55_, 0, v_pkg_49_);
v___x_56_ = lean_apply_4(v_map_52_, lean_box(0), lean_box(0), v___f_53_, v_inst_43_);
v___x_57_ = lean_apply_4(v_map_52_, lean_box(0), lean_box(0), v___f_55_, v___x_56_);
v___x_58_ = lean_apply_4(v_toBind_47_, lean_box(0), lean_box(0), v___x_57_, v___f_54_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get(lean_object* v_m_59_, lean_object* v_kind_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_self_64_){
_start:
{
lean_object* v_toApplicative_65_; lean_object* v_toFunctor_66_; lean_object* v_toBind_67_; lean_object* v_toPure_68_; lean_object* v_pkg_69_; lean_object* v_name_70_; lean_object* v_config_71_; lean_object* v_map_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_toApplicative_65_ = lean_ctor_get(v_inst_61_, 0);
lean_inc_ref(v_toApplicative_65_);
v_toFunctor_66_ = lean_ctor_get(v_toApplicative_65_, 0);
lean_inc_ref(v_toFunctor_66_);
v_toBind_67_ = lean_ctor_get(v_inst_61_, 1);
lean_inc(v_toBind_67_);
lean_dec_ref(v_inst_61_);
v_toPure_68_ = lean_ctor_get(v_toApplicative_65_, 1);
lean_inc(v_toPure_68_);
lean_dec_ref(v_toApplicative_65_);
v_pkg_69_ = lean_ctor_get(v_self_64_, 0);
lean_inc_n(v_pkg_69_, 2);
v_name_70_ = lean_ctor_get(v_self_64_, 1);
lean_inc(v_name_70_);
v_config_71_ = lean_ctor_get(v_self_64_, 3);
lean_inc(v_config_71_);
lean_dec_ref(v_self_64_);
v_map_72_ = lean_ctor_get(v_toFunctor_66_, 0);
lean_inc_n(v_map_72_, 2);
lean_dec_ref(v_toFunctor_66_);
v___f_73_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_74_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_74_, 0, v_name_70_);
lean_closure_set(v___f_74_, 1, v_config_71_);
lean_closure_set(v___f_74_, 2, v_toPure_68_);
lean_closure_set(v___f_74_, 3, v_pkg_69_);
lean_closure_set(v___f_74_, 4, v_inst_62_);
v___f_75_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_75_, 0, v_pkg_69_);
v___x_76_ = lean_apply_4(v_map_72_, lean_box(0), lean_box(0), v___f_73_, v_inst_63_);
v___x_77_ = lean_apply_4(v_map_72_, lean_box(0), lean_box(0), v___f_75_, v___x_76_);
v___x_78_ = lean_apply_4(v_toBind_67_, lean_box(0), lean_box(0), v___x_77_, v___f_74_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_get___boxed(lean_object* v_m_79_, lean_object* v_kind_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_self_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lake_KConfigDecl_get(v_m_79_, v_kind_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_self_84_);
lean_dec(v_kind_80_);
return v_res_85_;
}
}
lean_object* l_Lake_Package_fetchTargetJob(lean_object* v_self_86_, lean_object* v_target_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_self_86_);
lean_ctor_set(v___x_95_, 1, v_target_87_);
lean_inc_ref(v_a_92_);
lean_inc(v_a_91_);
lean_inc(v_a_90_);
lean_inc(v_a_89_);
v___x_96_ = lean_apply_7(v_a_88_, v___x_95_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, lean_box(0));
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = l_Lake_Job_toOpaque___redArg(v_a_97_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_a_98_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
return v___x_96_;
}
}
}
LEAN_EXPORT void l_Lake_Package_fetchTargetJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_86_ = stack[0].m_obj;
lean_object* v_target_87_ = stack[1].m_obj;
lean_object* v_a_88_ = stack[2].m_obj;
lean_object* v_a_89_ = stack[3].m_obj;
lean_object* v_a_90_ = stack[4].m_obj;
lean_object* v_a_91_ = stack[5].m_obj;
lean_object* v_a_92_ = stack[6].m_obj;
lean_object* v_a_93_ = stack[7].m_obj;
lean_object* v_res_107_;
v_res_107_ = l_Lake_Package_fetchTargetJob(v_self_86_, v_target_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchTargetJob___boxed(lean_object* v_self_108_, lean_object* v_target_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lake_Package_fetchTargetJob(v_self_108_, v_target_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec(v_a_112_);
lean_dec(v_a_111_);
return v_res_117_;
}
}
lean_object* l_Lake_TargetDecl_fetch___redArg(lean_object* v_self_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_toContext_129_; lean_object* v_pkg_130_; lean_object* v_name_131_; lean_object* v_packageMap_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_toContext_129_ = lean_ctor_get(v_a_126_, 1);
v_pkg_130_ = lean_ctor_get(v_self_121_, 0);
lean_inc_n(v_pkg_130_, 2);
v_name_131_ = lean_ctor_get(v_self_121_, 1);
lean_inc(v_name_131_);
lean_dec_ref(v_self_121_);
v_packageMap_132_ = lean_ctor_get(v_toContext_129_, 5);
v___x_133_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_packageMap_132_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_133_, v_packageMap_132_, v_pkg_130_);
if (lean_obj_tag(v___x_134_) == 1)
{
lean_object* v_val_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_pkg_130_);
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_val_135_);
lean_ctor_set(v___x_136_, 1, v_name_131_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc(v_a_124_);
lean_inc(v_a_123_);
v___x_137_ = lean_apply_7(v_a_122_, v___x_136_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
return v___x_137_;
}
else
{
lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v___x_134_);
lean_dec_ref(v_a_122_);
v___x_138_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__0));
v___x_139_ = 1;
v___x_140_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_130_, v___x_139_);
v___x_141_ = lean_string_append(v___x_138_, v___x_140_);
lean_dec_ref(v___x_140_);
v___x_142_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__1));
v___x_143_ = lean_string_append(v___x_141_, v___x_142_);
v___x_144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_131_, v___x_139_);
v___x_145_ = lean_string_append(v___x_143_, v___x_144_);
lean_dec_ref(v___x_144_);
v___x_146_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__2));
v___x_147_ = lean_string_append(v___x_145_, v___x_146_);
v___x_148_ = 3;
v___x_149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = lean_array_get_size(v_a_127_);
v___x_151_ = lean_array_push(v_a_127_, v___x_149_);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT void l_Lake_TargetDecl_fetch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_121_ = stack[0].m_obj;
lean_object* v_a_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_a_124_ = stack[3].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v_a_126_ = stack[5].m_obj;
lean_object* v_a_127_ = stack[6].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lake_TargetDecl_fetch___redArg(v_self_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___redArg___boxed(lean_object* v_self_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_TargetDecl_fetch___redArg(v_self_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec(v_a_157_);
lean_dec(v_a_156_);
return v_res_162_;
}
}
lean_object* l_Lake_TargetDecl_fetch(lean_object* v_00_u03b1_163_, lean_object* v_self_164_, lean_object* v_inst_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lake_TargetDecl_fetch___redArg(v_self_164_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_173_;
}
}
LEAN_EXPORT void l_Lake_TargetDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_164_ = stack[1].m_obj;
lean_object* v_a_166_ = stack[3].m_obj;
lean_object* v_a_167_ = stack[4].m_obj;
lean_object* v_a_168_ = stack[5].m_obj;
lean_object* v_a_169_ = stack[6].m_obj;
lean_object* v_a_170_ = stack[7].m_obj;
lean_object* v_a_171_ = stack[8].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Lake_TargetDecl_fetch(lean_box(0), v_self_164_, lean_box(0), v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___boxed(lean_object* v_00_u03b1_175_, lean_object* v_self_176_, lean_object* v_inst_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lake_TargetDecl_fetch(v_00_u03b1_175_, v_self_176_, v_inst_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec(v_a_180_);
lean_dec(v_a_179_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(lean_object* v_t_186_, lean_object* v_k_187_){
_start:
{
if (lean_obj_tag(v_t_186_) == 0)
{
lean_object* v_k_188_; lean_object* v_v_189_; lean_object* v_l_190_; lean_object* v_r_191_; uint8_t v___x_192_; 
v_k_188_ = lean_ctor_get(v_t_186_, 1);
v_v_189_ = lean_ctor_get(v_t_186_, 2);
v_l_190_ = lean_ctor_get(v_t_186_, 3);
v_r_191_ = lean_ctor_get(v_t_186_, 4);
v___x_192_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_187_, v_k_188_);
switch(v___x_192_)
{
case 0:
{
v_t_186_ = v_l_190_;
goto _start;
}
case 1:
{
lean_object* v___x_194_; 
lean_inc(v_v_189_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_v_189_);
return v___x_194_;
}
default: 
{
v_t_186_ = v_r_191_;
goto _start;
}
}
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg___boxed(lean_object* v_t_197_, lean_object* v_k_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_t_197_, v_k_198_);
lean_dec(v_k_198_);
lean_dec(v_t_197_);
return v_res_199_;
}
}
lean_object* l_Lake_TargetDecl_fetchJob(lean_object* v_self_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_toContext_208_; lean_object* v_pkg_209_; lean_object* v_name_210_; lean_object* v_packageMap_211_; lean_object* v___x_212_; 
v_toContext_208_ = lean_ctor_get(v_a_205_, 1);
v_pkg_209_ = lean_ctor_get(v_self_200_, 0);
lean_inc(v_pkg_209_);
v_name_210_ = lean_ctor_get(v_self_200_, 1);
lean_inc(v_name_210_);
lean_dec_ref(v_self_200_);
v_packageMap_211_ = lean_ctor_get(v_toContext_208_, 5);
v___x_212_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_packageMap_211_, v_pkg_209_);
if (lean_obj_tag(v___x_212_) == 1)
{
lean_object* v_val_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_pkg_209_);
v_val_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_val_213_);
lean_ctor_set(v___x_214_, 1, v_name_210_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc(v_a_203_);
lean_inc(v_a_202_);
v___x_215_ = lean_apply_7(v_a_201_, v___x_214_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, lean_box(0));
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_a_217_ = lean_ctor_get(v___x_215_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v___x_215_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = l_Lake_Job_toOpaque___redArg(v_a_216_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_a_217_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
return v___x_215_;
}
}
else
{
lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v___x_212_);
lean_dec_ref(v_a_201_);
v___x_226_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__0));
v___x_227_ = 1;
v___x_228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_209_, v___x_227_);
v___x_229_ = lean_string_append(v___x_226_, v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__1));
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
v___x_232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_210_, v___x_227_);
v___x_233_ = lean_string_append(v___x_231_, v___x_232_);
lean_dec_ref(v___x_232_);
v___x_234_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__2));
v___x_235_ = lean_string_append(v___x_233_, v___x_234_);
v___x_236_ = 3;
v___x_237_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_236_);
v___x_238_ = lean_array_get_size(v_a_206_);
v___x_239_ = lean_array_push(v_a_206_, v___x_237_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT void l_Lake_TargetDecl_fetchJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_200_ = stack[0].m_obj;
lean_object* v_a_201_ = stack[1].m_obj;
lean_object* v_a_202_ = stack[2].m_obj;
lean_object* v_a_203_ = stack[3].m_obj;
lean_object* v_a_204_ = stack[4].m_obj;
lean_object* v_a_205_ = stack[5].m_obj;
lean_object* v_a_206_ = stack[6].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lake_TargetDecl_fetchJob(v_self_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetchJob___boxed(lean_object* v_self_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_TargetDecl_fetchJob(v_self_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec(v_a_245_);
lean_dec(v_a_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(lean_object* v_00_u03b2_251_, lean_object* v_inst_252_, lean_object* v_t_253_, lean_object* v_k_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_t_253_, v_k_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___boxed(lean_object* v_00_u03b2_256_, lean_object* v_inst_257_, lean_object* v_t_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(v_00_u03b2_256_, v_inst_257_, v_t_258_, v_k_259_);
lean_dec(v_k_259_);
lean_dec(v_t_258_);
return v_res_260_;
}
}
lean_object* l_Lake_PackageFacetDecl_fetch___redArg(lean_object* v_pkg_261_, lean_object* v_self_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_name_270_; lean_object* v_keyName_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_name_270_ = lean_ctor_get(v_self_262_, 0);
v_keyName_271_ = lean_ctor_get(v_pkg_261_, 2);
lean_inc(v_keyName_271_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_keyName_271_);
v___x_273_ = l_Lake_Package_keyword;
lean_inc(v_name_270_);
v___x_274_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v_pkg_261_);
lean_ctor_set(v___x_274_, 3, v_name_270_);
lean_inc_ref(v_a_267_);
lean_inc(v_a_266_);
lean_inc(v_a_265_);
lean_inc(v_a_264_);
v___x_275_ = lean_apply_7(v_a_263_, v___x_274_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, lean_box(0));
return v___x_275_;
}
}
LEAN_EXPORT void l_Lake_PackageFacetDecl_fetch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_261_ = stack[0].m_obj;
lean_object* v_self_262_ = stack[1].m_obj;
lean_object* v_a_263_ = stack[2].m_obj;
lean_object* v_a_264_ = stack[3].m_obj;
lean_object* v_a_265_ = stack[4].m_obj;
lean_object* v_a_266_ = stack[5].m_obj;
lean_object* v_a_267_ = stack[6].m_obj;
lean_object* v_a_268_ = stack[7].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Lake_PackageFacetDecl_fetch___redArg(v_pkg_261_, v_self_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___redArg___boxed(lean_object* v_pkg_277_, lean_object* v_self_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lake_PackageFacetDecl_fetch___redArg(v_pkg_277_, v_self_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_self_278_);
return v_res_286_;
}
}
lean_object* l_Lake_PackageFacetDecl_fetch(lean_object* v_00_u03b1_287_, lean_object* v_pkg_288_, lean_object* v_self_289_, lean_object* v_inst_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_name_298_; lean_object* v_keyName_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_name_298_ = lean_ctor_get(v_self_289_, 0);
v_keyName_299_ = lean_ctor_get(v_pkg_288_, 2);
lean_inc(v_keyName_299_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_keyName_299_);
v___x_301_ = l_Lake_Package_keyword;
lean_inc(v_name_298_);
v___x_302_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
lean_ctor_set(v___x_302_, 2, v_pkg_288_);
lean_ctor_set(v___x_302_, 3, v_name_298_);
lean_inc_ref(v_a_295_);
lean_inc(v_a_294_);
lean_inc(v_a_293_);
lean_inc(v_a_292_);
v___x_303_ = lean_apply_7(v_a_291_, v___x_302_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, lean_box(0));
return v___x_303_;
}
}
LEAN_EXPORT void l_Lake_PackageFacetDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_288_ = stack[1].m_obj;
lean_object* v_self_289_ = stack[2].m_obj;
lean_object* v_a_291_ = stack[4].m_obj;
lean_object* v_a_292_ = stack[5].m_obj;
lean_object* v_a_293_ = stack[6].m_obj;
lean_object* v_a_294_ = stack[7].m_obj;
lean_object* v_a_295_ = stack[8].m_obj;
lean_object* v_a_296_ = stack[9].m_obj;
lean_object* v_res_304_;
v_res_304_ = l_Lake_PackageFacetDecl_fetch(lean_box(0), v_pkg_288_, v_self_289_, lean_box(0), v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
stack->m_obj
 = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___boxed(lean_object* v_00_u03b1_305_, lean_object* v_pkg_306_, lean_object* v_self_307_, lean_object* v_inst_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lake_PackageFacetDecl_fetch(v_00_u03b1_305_, v_pkg_306_, v_self_307_, v_inst_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_self_307_);
return v_res_316_;
}
}
lean_object* l_Lake_Package_fetchFacetJob(lean_object* v_name_317_, lean_object* v_self_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_keyName_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_keyName_326_ = lean_ctor_get(v_self_318_, 2);
v___x_327_ = l_Lake_Package_keyword;
v___x_328_ = l_Lean_Name_append(v___x_327_, v_name_317_);
lean_inc(v_keyName_326_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_keyName_326_);
v___x_330_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_327_);
lean_ctor_set(v___x_330_, 2, v_self_318_);
lean_ctor_set(v___x_330_, 3, v___x_328_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
v___x_331_ = lean_apply_7(v_a_319_, v___x_330_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_a_333_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = l_Lake_Job_toOpaque___redArg(v_a_332_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_a_333_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
return v___x_331_;
}
}
}
LEAN_EXPORT void l_Lake_Package_fetchFacetJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_317_ = stack[0].m_obj;
lean_object* v_self_318_ = stack[1].m_obj;
lean_object* v_a_319_ = stack[2].m_obj;
lean_object* v_a_320_ = stack[3].m_obj;
lean_object* v_a_321_ = stack[4].m_obj;
lean_object* v_a_322_ = stack[5].m_obj;
lean_object* v_a_323_ = stack[6].m_obj;
lean_object* v_a_324_ = stack[7].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lake_Package_fetchFacetJob(v_name_317_, v_self_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchFacetJob___boxed(lean_object* v_name_343_, lean_object* v_self_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lake_Package_fetchFacetJob(v_name_343_, v_self_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
lean_dec(v_a_346_);
return v_res_352_;
}
}
lean_object* l_Lake_ModuleFacetDecl_fetch___redArg(lean_object* v_mod_353_, lean_object* v_self_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_lib_362_; lean_object* v_pkg_363_; lean_object* v_name_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_376_; 
v_lib_362_ = lean_ctor_get(v_mod_353_, 0);
v_pkg_363_ = lean_ctor_get(v_lib_362_, 0);
v_name_364_ = lean_ctor_get(v_self_354_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_self_354_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v_self_354_, 1);
lean_dec(v_unused_377_);
v___x_366_ = v_self_354_;
v_isShared_367_ = v_isSharedCheck_376_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_name_364_);
lean_dec(v_self_354_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_376_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_name_368_; lean_object* v_keyName_369_; lean_object* v___x_371_; 
v_name_368_ = lean_ctor_get(v_mod_353_, 1);
v_keyName_369_ = lean_ctor_get(v_pkg_363_, 2);
lean_inc(v_name_368_);
lean_inc(v_keyName_369_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 2);
lean_ctor_set(v___x_366_, 1, v_name_368_);
lean_ctor_set(v___x_366_, 0, v_keyName_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_keyName_369_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_name_368_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = l_Lake_Module_keyword;
v___x_373_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
lean_ctor_set(v___x_373_, 2, v_mod_353_);
lean_ctor_set(v___x_373_, 3, v_name_364_);
lean_inc_ref(v_a_359_);
lean_inc(v_a_358_);
lean_inc(v_a_357_);
lean_inc(v_a_356_);
v___x_374_ = lean_apply_7(v_a_355_, v___x_373_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, lean_box(0));
return v___x_374_;
}
}
}
}
LEAN_EXPORT void l_Lake_ModuleFacetDecl_fetch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_353_ = stack[0].m_obj;
lean_object* v_self_354_ = stack[1].m_obj;
lean_object* v_a_355_ = stack[2].m_obj;
lean_object* v_a_356_ = stack[3].m_obj;
lean_object* v_a_357_ = stack[4].m_obj;
lean_object* v_a_358_ = stack[5].m_obj;
lean_object* v_a_359_ = stack[6].m_obj;
lean_object* v_a_360_ = stack[7].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lake_ModuleFacetDecl_fetch___redArg(v_mod_353_, v_self_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___redArg___boxed(lean_object* v_mod_379_, lean_object* v_self_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lake_ModuleFacetDecl_fetch___redArg(v_mod_379_, v_self_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
return v_res_388_;
}
}
lean_object* l_Lake_ModuleFacetDecl_fetch(lean_object* v_00_u03b1_389_, lean_object* v_mod_390_, lean_object* v_self_391_, lean_object* v_inst_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_lib_400_; lean_object* v_pkg_401_; lean_object* v_name_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_414_; 
v_lib_400_ = lean_ctor_get(v_mod_390_, 0);
v_pkg_401_ = lean_ctor_get(v_lib_400_, 0);
v_name_402_ = lean_ctor_get(v_self_391_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_self_391_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v_self_391_, 1);
lean_dec(v_unused_415_);
v___x_404_ = v_self_391_;
v_isShared_405_ = v_isSharedCheck_414_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_name_402_);
lean_dec(v_self_391_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_414_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_name_406_; lean_object* v_keyName_407_; lean_object* v___x_409_; 
v_name_406_ = lean_ctor_get(v_mod_390_, 1);
v_keyName_407_ = lean_ctor_get(v_pkg_401_, 2);
lean_inc(v_name_406_);
lean_inc(v_keyName_407_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 2);
lean_ctor_set(v___x_404_, 1, v_name_406_);
lean_ctor_set(v___x_404_, 0, v_keyName_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_keyName_407_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_name_406_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = l_Lake_Module_keyword;
v___x_411_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_ctor_set(v___x_411_, 2, v_mod_390_);
lean_ctor_set(v___x_411_, 3, v_name_402_);
lean_inc_ref(v_a_397_);
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_inc(v_a_394_);
v___x_412_ = lean_apply_7(v_a_393_, v___x_411_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, lean_box(0));
return v___x_412_;
}
}
}
}
LEAN_EXPORT void l_Lake_ModuleFacetDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_390_ = stack[1].m_obj;
lean_object* v_self_391_ = stack[2].m_obj;
lean_object* v_a_393_ = stack[4].m_obj;
lean_object* v_a_394_ = stack[5].m_obj;
lean_object* v_a_395_ = stack[6].m_obj;
lean_object* v_a_396_ = stack[7].m_obj;
lean_object* v_a_397_ = stack[8].m_obj;
lean_object* v_a_398_ = stack[9].m_obj;
lean_object* v_res_416_;
v_res_416_ = l_Lake_ModuleFacetDecl_fetch(lean_box(0), v_mod_390_, v_self_391_, lean_box(0), v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___boxed(lean_object* v_00_u03b1_417_, lean_object* v_mod_418_, lean_object* v_self_419_, lean_object* v_inst_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lake_ModuleFacetDecl_fetch(v_00_u03b1_417_, v_mod_418_, v_self_419_, v_inst_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec(v_a_423_);
lean_dec(v_a_422_);
return v_res_428_;
}
}
lean_object* l_Lake_Module_fetchFacetJob(lean_object* v_name_429_, lean_object* v_self_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_lib_438_; lean_object* v_pkg_439_; lean_object* v_name_440_; lean_object* v_keyName_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_lib_438_ = lean_ctor_get(v_self_430_, 0);
v_pkg_439_ = lean_ctor_get(v_lib_438_, 0);
v_name_440_ = lean_ctor_get(v_self_430_, 1);
v_keyName_441_ = lean_ctor_get(v_pkg_439_, 2);
v___x_442_ = l_Lake_Module_keyword;
v___x_443_ = l_Lean_Name_append(v___x_442_, v_name_429_);
lean_inc(v_name_440_);
lean_inc(v_keyName_441_);
v___x_444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_444_, 0, v_keyName_441_);
lean_ctor_set(v___x_444_, 1, v_name_440_);
v___x_445_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_442_);
lean_ctor_set(v___x_445_, 2, v_self_430_);
lean_ctor_set(v___x_445_, 3, v___x_443_);
lean_inc_ref(v_a_435_);
lean_inc(v_a_434_);
lean_inc(v_a_433_);
lean_inc(v_a_432_);
v___x_446_ = lean_apply_7(v_a_431_, v___x_445_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, lean_box(0));
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_456_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_a_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_456_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = l_Lake_Job_toOpaque___redArg(v_a_447_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_448_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
return v___x_446_;
}
}
}
LEAN_EXPORT void l_Lake_Module_fetchFacetJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_429_ = stack[0].m_obj;
lean_object* v_self_430_ = stack[1].m_obj;
lean_object* v_a_431_ = stack[2].m_obj;
lean_object* v_a_432_ = stack[3].m_obj;
lean_object* v_a_433_ = stack[4].m_obj;
lean_object* v_a_434_ = stack[5].m_obj;
lean_object* v_a_435_ = stack[6].m_obj;
lean_object* v_a_436_ = stack[7].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lake_Module_fetchFacetJob(v_name_429_, v_self_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lake_Module_fetchFacetJob___boxed(lean_object* v_name_458_, lean_object* v_self_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lake_Module_fetchFacetJob(v_name_458_, v_self_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec(v_a_462_);
lean_dec(v_a_461_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_get___redArg(lean_object* v_self_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_){
_start:
{
lean_object* v_toApplicative_472_; lean_object* v_toFunctor_473_; lean_object* v_toBind_474_; lean_object* v_toPure_475_; lean_object* v_pkg_476_; lean_object* v_name_477_; lean_object* v_config_478_; lean_object* v_map_479_; lean_object* v___f_480_; lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_toApplicative_472_ = lean_ctor_get(v_inst_469_, 0);
lean_inc_ref(v_toApplicative_472_);
v_toFunctor_473_ = lean_ctor_get(v_toApplicative_472_, 0);
lean_inc_ref(v_toFunctor_473_);
v_toBind_474_ = lean_ctor_get(v_inst_469_, 1);
lean_inc(v_toBind_474_);
lean_dec_ref(v_inst_469_);
v_toPure_475_ = lean_ctor_get(v_toApplicative_472_, 1);
lean_inc(v_toPure_475_);
lean_dec_ref(v_toApplicative_472_);
v_pkg_476_ = lean_ctor_get(v_self_468_, 0);
lean_inc_n(v_pkg_476_, 2);
v_name_477_ = lean_ctor_get(v_self_468_, 1);
lean_inc(v_name_477_);
v_config_478_ = lean_ctor_get(v_self_468_, 3);
lean_inc(v_config_478_);
lean_dec_ref(v_self_468_);
v_map_479_ = lean_ctor_get(v_toFunctor_473_, 0);
lean_inc_n(v_map_479_, 2);
lean_dec_ref(v_toFunctor_473_);
v___f_480_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_481_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_481_, 0, v_name_477_);
lean_closure_set(v___f_481_, 1, v_config_478_);
lean_closure_set(v___f_481_, 2, v_toPure_475_);
lean_closure_set(v___f_481_, 3, v_pkg_476_);
lean_closure_set(v___f_481_, 4, v_inst_470_);
v___f_482_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_482_, 0, v_pkg_476_);
v___x_483_ = lean_apply_4(v_map_479_, lean_box(0), lean_box(0), v___f_480_, v_inst_471_);
v___x_484_ = lean_apply_4(v_map_479_, lean_box(0), lean_box(0), v___f_482_, v___x_483_);
v___x_485_ = lean_apply_4(v_toBind_474_, lean_box(0), lean_box(0), v___x_484_, v___f_481_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_get(lean_object* v_m_486_, lean_object* v_self_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v_toApplicative_491_; lean_object* v_toFunctor_492_; lean_object* v_toBind_493_; lean_object* v_toPure_494_; lean_object* v_pkg_495_; lean_object* v_name_496_; lean_object* v_config_497_; lean_object* v_map_498_; lean_object* v___f_499_; lean_object* v___f_500_; lean_object* v___f_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_toApplicative_491_ = lean_ctor_get(v_inst_488_, 0);
lean_inc_ref(v_toApplicative_491_);
v_toFunctor_492_ = lean_ctor_get(v_toApplicative_491_, 0);
lean_inc_ref(v_toFunctor_492_);
v_toBind_493_ = lean_ctor_get(v_inst_488_, 1);
lean_inc(v_toBind_493_);
lean_dec_ref(v_inst_488_);
v_toPure_494_ = lean_ctor_get(v_toApplicative_491_, 1);
lean_inc(v_toPure_494_);
lean_dec_ref(v_toApplicative_491_);
v_pkg_495_ = lean_ctor_get(v_self_487_, 0);
lean_inc_n(v_pkg_495_, 2);
v_name_496_ = lean_ctor_get(v_self_487_, 1);
lean_inc(v_name_496_);
v_config_497_ = lean_ctor_get(v_self_487_, 3);
lean_inc(v_config_497_);
lean_dec_ref(v_self_487_);
v_map_498_ = lean_ctor_get(v_toFunctor_492_, 0);
lean_inc_n(v_map_498_, 2);
lean_dec_ref(v_toFunctor_492_);
v___f_499_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_500_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_500_, 0, v_name_496_);
lean_closure_set(v___f_500_, 1, v_config_497_);
lean_closure_set(v___f_500_, 2, v_toPure_494_);
lean_closure_set(v___f_500_, 3, v_pkg_495_);
lean_closure_set(v___f_500_, 4, v_inst_489_);
v___f_501_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_501_, 0, v_pkg_495_);
v___x_502_ = lean_apply_4(v_map_498_, lean_box(0), lean_box(0), v___f_499_, v_inst_490_);
v___x_503_ = lean_apply_4(v_map_498_, lean_box(0), lean_box(0), v___f_501_, v___x_502_);
v___x_504_ = lean_apply_4(v_toBind_493_, lean_box(0), lean_box(0), v___x_503_, v___f_500_);
return v___x_504_;
}
}
lean_object* l_Lake_LeanLib_fetch(lean_object* v_self_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_pkg_516_; lean_object* v_name_517_; lean_object* v_keyName_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_pkg_516_ = lean_ctor_get(v_self_508_, 0);
v_name_517_ = lean_ctor_get(v_self_508_, 1);
v_keyName_518_ = lean_ctor_get(v_pkg_516_, 2);
v___x_519_ = l_Lake_LeanLib_defaultFacet;
lean_inc(v_name_517_);
lean_inc(v_keyName_518_);
v___x_520_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_520_, 0, v_keyName_518_);
lean_ctor_set(v___x_520_, 1, v_name_517_);
v___x_521_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_522_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_ctor_set(v___x_522_, 2, v_self_508_);
lean_ctor_set(v___x_522_, 3, v___x_519_);
lean_inc_ref(v_a_513_);
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_inc(v_a_510_);
v___x_523_ = lean_apply_7(v_a_509_, v___x_522_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, lean_box(0));
return v___x_523_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_508_ = stack[0].m_obj;
lean_object* v_a_509_ = stack[1].m_obj;
lean_object* v_a_510_ = stack[2].m_obj;
lean_object* v_a_511_ = stack[3].m_obj;
lean_object* v_a_512_ = stack[4].m_obj;
lean_object* v_a_513_ = stack[5].m_obj;
lean_object* v_a_514_ = stack[6].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_Lake_LeanLib_fetch(v_self_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetch___boxed(lean_object* v_self_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lake_LeanLib_fetch(v_self_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec(v_a_528_);
lean_dec(v_a_527_);
return v_res_533_;
}
}
lean_object* l_Lake_LeanLibDecl_fetch(lean_object* v_self_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_toContext_542_; lean_object* v_pkg_543_; lean_object* v_name_544_; lean_object* v_config_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_577_; 
v_toContext_542_ = lean_ctor_get(v_a_539_, 1);
v_pkg_543_ = lean_ctor_get(v_self_534_, 0);
v_name_544_ = lean_ctor_get(v_self_534_, 1);
v_config_545_ = lean_ctor_get(v_self_534_, 3);
v_isSharedCheck_577_ = !lean_is_exclusive(v_self_534_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v_self_534_, 2);
lean_dec(v_unused_578_);
v___x_547_ = v_self_534_;
v_isShared_548_ = v_isSharedCheck_577_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_config_545_);
lean_inc(v_name_544_);
lean_inc(v_pkg_543_);
lean_dec(v_self_534_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_577_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_packageMap_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_packageMap_549_ = lean_ctor_get(v_toContext_542_, 5);
v___x_550_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_543_);
lean_inc(v_packageMap_549_);
v___x_551_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_550_, v_packageMap_549_, v_pkg_543_);
if (lean_obj_tag(v___x_551_) == 1)
{
lean_object* v_val_552_; lean_object* v_keyName_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_pkg_543_);
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
v_keyName_553_ = lean_ctor_get(v_val_552_, 2);
lean_inc(v_keyName_553_);
v___x_554_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
lean_inc(v_name_544_);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v_val_552_);
lean_ctor_set(v___x_555_, 1, v_name_544_);
lean_ctor_set(v___x_555_, 2, v_config_545_);
v___x_556_ = l_Lake_LeanLib_defaultFacet;
v___x_557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_557_, 0, v_keyName_553_);
lean_ctor_set(v___x_557_, 1, v_name_544_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
lean_ctor_set(v___x_547_, 3, v___x_556_);
lean_ctor_set(v___x_547_, 2, v___x_555_);
lean_ctor_set(v___x_547_, 1, v___x_554_);
lean_ctor_set(v___x_547_, 0, v___x_557_);
v___x_559_ = v___x_547_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v___x_556_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
lean_inc_ref(v_a_539_);
lean_inc(v_a_538_);
lean_inc(v_a_537_);
lean_inc(v_a_536_);
v___x_560_ = lean_apply_7(v_a_535_, v___x_559_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, lean_box(0));
return v___x_560_;
}
}
else
{
lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v___x_551_);
lean_del_object(v___x_547_);
lean_dec(v_config_545_);
lean_dec_ref(v_a_535_);
v___x_562_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_563_ = 1;
v___x_564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_543_, v___x_563_);
v___x_565_ = lean_string_append(v___x_562_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_567_ = lean_string_append(v___x_565_, v___x_566_);
v___x_568_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_544_, v___x_563_);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
v___x_572_ = 3;
v___x_573_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*1, v___x_572_);
v___x_574_ = lean_array_get_size(v_a_540_);
v___x_575_ = lean_array_push(v_a_540_, v___x_573_);
v___x_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLibDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_534_ = stack[0].m_obj;
lean_object* v_a_535_ = stack[1].m_obj;
lean_object* v_a_536_ = stack[2].m_obj;
lean_object* v_a_537_ = stack[3].m_obj;
lean_object* v_a_538_ = stack[4].m_obj;
lean_object* v_a_539_ = stack[5].m_obj;
lean_object* v_a_540_ = stack[6].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_Lake_LeanLibDecl_fetch(v_self_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_fetch___boxed(lean_object* v_self_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lake_LeanLibDecl_fetch(v_self_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec(v_a_583_);
lean_dec(v_a_582_);
return v_res_588_;
}
}
lean_object* l_Lake_LibraryFacetDecl_fetch___redArg(lean_object* v_lib_589_, lean_object* v_self_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_pkg_598_; lean_object* v_name_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_611_; 
v_pkg_598_ = lean_ctor_get(v_lib_589_, 0);
v_name_599_ = lean_ctor_get(v_self_590_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_self_590_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_self_590_, 1);
lean_dec(v_unused_612_);
v___x_601_ = v_self_590_;
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_name_599_);
lean_dec(v_self_590_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_name_603_; lean_object* v_keyName_604_; lean_object* v___x_606_; 
v_name_603_ = lean_ctor_get(v_lib_589_, 1);
v_keyName_604_ = lean_ctor_get(v_pkg_598_, 2);
lean_inc(v_name_603_);
lean_inc(v_keyName_604_);
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 3);
lean_ctor_set(v___x_601_, 1, v_name_603_);
lean_ctor_set(v___x_601_, 0, v_keyName_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_keyName_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_name_603_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_608_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_ctor_set(v___x_608_, 2, v_lib_589_);
lean_ctor_set(v___x_608_, 3, v_name_599_);
lean_inc_ref(v_a_595_);
lean_inc(v_a_594_);
lean_inc(v_a_593_);
lean_inc(v_a_592_);
v___x_609_ = lean_apply_7(v_a_591_, v___x_608_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, lean_box(0));
return v___x_609_;
}
}
}
}
LEAN_EXPORT void l_Lake_LibraryFacetDecl_fetch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_589_ = stack[0].m_obj;
lean_object* v_self_590_ = stack[1].m_obj;
lean_object* v_a_591_ = stack[2].m_obj;
lean_object* v_a_592_ = stack[3].m_obj;
lean_object* v_a_593_ = stack[4].m_obj;
lean_object* v_a_594_ = stack[5].m_obj;
lean_object* v_a_595_ = stack[6].m_obj;
lean_object* v_a_596_ = stack[7].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lake_LibraryFacetDecl_fetch___redArg(v_lib_589_, v_self_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___redArg___boxed(lean_object* v_lib_614_, lean_object* v_self_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lake_LibraryFacetDecl_fetch___redArg(v_lib_614_, v_self_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec(v_a_618_);
lean_dec(v_a_617_);
return v_res_623_;
}
}
lean_object* l_Lake_LibraryFacetDecl_fetch(lean_object* v_00_u03b1_624_, lean_object* v_lib_625_, lean_object* v_self_626_, lean_object* v_inst_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_pkg_635_; lean_object* v_name_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_648_; 
v_pkg_635_ = lean_ctor_get(v_lib_625_, 0);
v_name_636_ = lean_ctor_get(v_self_626_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_self_626_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_self_626_, 1);
lean_dec(v_unused_649_);
v___x_638_ = v_self_626_;
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_name_636_);
lean_dec(v_self_626_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_name_640_; lean_object* v_keyName_641_; lean_object* v___x_643_; 
v_name_640_ = lean_ctor_get(v_lib_625_, 1);
v_keyName_641_ = lean_ctor_get(v_pkg_635_, 2);
lean_inc(v_name_640_);
lean_inc(v_keyName_641_);
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 3);
lean_ctor_set(v___x_638_, 1, v_name_640_);
lean_ctor_set(v___x_638_, 0, v_keyName_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_keyName_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_name_640_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_645_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_ctor_set(v___x_645_, 2, v_lib_625_);
lean_ctor_set(v___x_645_, 3, v_name_636_);
lean_inc_ref(v_a_632_);
lean_inc(v_a_631_);
lean_inc(v_a_630_);
lean_inc(v_a_629_);
v___x_646_ = lean_apply_7(v_a_628_, v___x_645_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, lean_box(0));
return v___x_646_;
}
}
}
}
LEAN_EXPORT void l_Lake_LibraryFacetDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_625_ = stack[1].m_obj;
lean_object* v_self_626_ = stack[2].m_obj;
lean_object* v_a_628_ = stack[4].m_obj;
lean_object* v_a_629_ = stack[5].m_obj;
lean_object* v_a_630_ = stack[6].m_obj;
lean_object* v_a_631_ = stack[7].m_obj;
lean_object* v_a_632_ = stack[8].m_obj;
lean_object* v_a_633_ = stack[9].m_obj;
lean_object* v_res_650_;
v_res_650_ = l_Lake_LibraryFacetDecl_fetch(lean_box(0), v_lib_625_, v_self_626_, lean_box(0), v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___boxed(lean_object* v_00_u03b1_651_, lean_object* v_lib_652_, lean_object* v_self_653_, lean_object* v_inst_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lake_LibraryFacetDecl_fetch(v_00_u03b1_651_, v_lib_652_, v_self_653_, v_inst_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec(v_a_657_);
lean_dec(v_a_656_);
return v_res_662_;
}
}
lean_object* l_Lake_LeanLib_fetchFacetJob(lean_object* v_name_663_, lean_object* v_self_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_pkg_672_; lean_object* v_name_673_; lean_object* v_keyName_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_pkg_672_ = lean_ctor_get(v_self_664_, 0);
v_name_673_ = lean_ctor_get(v_self_664_, 1);
v_keyName_674_ = lean_ctor_get(v_pkg_672_, 2);
v___x_675_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_676_ = l_Lean_Name_append(v___x_675_, v_name_663_);
lean_inc(v_name_673_);
lean_inc(v_keyName_674_);
v___x_677_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_677_, 0, v_keyName_674_);
lean_ctor_set(v___x_677_, 1, v_name_673_);
v___x_678_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_675_);
lean_ctor_set(v___x_678_, 2, v_self_664_);
lean_ctor_set(v___x_678_, 3, v___x_676_);
lean_inc_ref(v_a_669_);
lean_inc(v_a_668_);
lean_inc(v_a_667_);
lean_inc(v_a_666_);
v___x_679_ = lean_apply_7(v_a_665_, v___x_678_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, lean_box(0));
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_689_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_a_681_ = lean_ctor_get(v___x_679_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_689_ == 0)
{
v___x_683_ = v___x_679_;
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = l_Lake_Job_toOpaque___redArg(v_a_680_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_a_681_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
return v___x_679_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_fetchFacetJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_663_ = stack[0].m_obj;
lean_object* v_self_664_ = stack[1].m_obj;
lean_object* v_a_665_ = stack[2].m_obj;
lean_object* v_a_666_ = stack[3].m_obj;
lean_object* v_a_667_ = stack[4].m_obj;
lean_object* v_a_668_ = stack[5].m_obj;
lean_object* v_a_669_ = stack[6].m_obj;
lean_object* v_a_670_ = stack[7].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lake_LeanLib_fetchFacetJob(v_name_663_, v_self_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetchFacetJob___boxed(lean_object* v_name_691_, lean_object* v_self_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_LeanLib_fetchFacetJob(v_name_691_, v_self_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec(v_a_695_);
lean_dec(v_a_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_get___redArg(lean_object* v_self_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v_toApplicative_705_; lean_object* v_toFunctor_706_; lean_object* v_toBind_707_; lean_object* v_toPure_708_; lean_object* v_pkg_709_; lean_object* v_name_710_; lean_object* v_config_711_; lean_object* v_map_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_toApplicative_705_ = lean_ctor_get(v_inst_702_, 0);
lean_inc_ref(v_toApplicative_705_);
v_toFunctor_706_ = lean_ctor_get(v_toApplicative_705_, 0);
lean_inc_ref(v_toFunctor_706_);
v_toBind_707_ = lean_ctor_get(v_inst_702_, 1);
lean_inc(v_toBind_707_);
lean_dec_ref(v_inst_702_);
v_toPure_708_ = lean_ctor_get(v_toApplicative_705_, 1);
lean_inc(v_toPure_708_);
lean_dec_ref(v_toApplicative_705_);
v_pkg_709_ = lean_ctor_get(v_self_701_, 0);
lean_inc_n(v_pkg_709_, 2);
v_name_710_ = lean_ctor_get(v_self_701_, 1);
lean_inc(v_name_710_);
v_config_711_ = lean_ctor_get(v_self_701_, 3);
lean_inc(v_config_711_);
lean_dec_ref(v_self_701_);
v_map_712_ = lean_ctor_get(v_toFunctor_706_, 0);
lean_inc_n(v_map_712_, 2);
lean_dec_ref(v_toFunctor_706_);
v___f_713_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_714_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_714_, 0, v_name_710_);
lean_closure_set(v___f_714_, 1, v_config_711_);
lean_closure_set(v___f_714_, 2, v_toPure_708_);
lean_closure_set(v___f_714_, 3, v_pkg_709_);
lean_closure_set(v___f_714_, 4, v_inst_703_);
v___f_715_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_715_, 0, v_pkg_709_);
v___x_716_ = lean_apply_4(v_map_712_, lean_box(0), lean_box(0), v___f_713_, v_inst_704_);
v___x_717_ = lean_apply_4(v_map_712_, lean_box(0), lean_box(0), v___f_715_, v___x_716_);
v___x_718_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_717_, v___f_714_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_get(lean_object* v_m_719_, lean_object* v_self_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_){
_start:
{
lean_object* v_toApplicative_724_; lean_object* v_toFunctor_725_; lean_object* v_toBind_726_; lean_object* v_toPure_727_; lean_object* v_pkg_728_; lean_object* v_name_729_; lean_object* v_config_730_; lean_object* v_map_731_; lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_toApplicative_724_ = lean_ctor_get(v_inst_721_, 0);
lean_inc_ref(v_toApplicative_724_);
v_toFunctor_725_ = lean_ctor_get(v_toApplicative_724_, 0);
lean_inc_ref(v_toFunctor_725_);
v_toBind_726_ = lean_ctor_get(v_inst_721_, 1);
lean_inc(v_toBind_726_);
lean_dec_ref(v_inst_721_);
v_toPure_727_ = lean_ctor_get(v_toApplicative_724_, 1);
lean_inc(v_toPure_727_);
lean_dec_ref(v_toApplicative_724_);
v_pkg_728_ = lean_ctor_get(v_self_720_, 0);
lean_inc_n(v_pkg_728_, 2);
v_name_729_ = lean_ctor_get(v_self_720_, 1);
lean_inc(v_name_729_);
v_config_730_ = lean_ctor_get(v_self_720_, 3);
lean_inc(v_config_730_);
lean_dec_ref(v_self_720_);
v_map_731_ = lean_ctor_get(v_toFunctor_725_, 0);
lean_inc_n(v_map_731_, 2);
lean_dec_ref(v_toFunctor_725_);
v___f_732_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_733_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_733_, 0, v_name_729_);
lean_closure_set(v___f_733_, 1, v_config_730_);
lean_closure_set(v___f_733_, 2, v_toPure_727_);
lean_closure_set(v___f_733_, 3, v_pkg_728_);
lean_closure_set(v___f_733_, 4, v_inst_722_);
v___f_734_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_734_, 0, v_pkg_728_);
v___x_735_ = lean_apply_4(v_map_731_, lean_box(0), lean_box(0), v___f_732_, v_inst_723_);
v___x_736_ = lean_apply_4(v_map_731_, lean_box(0), lean_box(0), v___f_734_, v___x_735_);
v___x_737_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_736_, v___f_733_);
return v___x_737_;
}
}
lean_object* l_Lake_LeanExe_fetch(lean_object* v_self_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_pkg_746_; lean_object* v_name_747_; lean_object* v_keyName_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_pkg_746_ = lean_ctor_get(v_self_738_, 0);
v_name_747_ = lean_ctor_get(v_self_738_, 1);
v_keyName_748_ = lean_ctor_get(v_pkg_746_, 2);
v___x_749_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_747_);
lean_inc(v_keyName_748_);
v___x_750_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_750_, 0, v_keyName_748_);
lean_ctor_set(v___x_750_, 1, v_name_747_);
v___x_751_ = l_Lake_LeanExe_keyword;
v___x_752_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
lean_ctor_set(v___x_752_, 2, v_self_738_);
lean_ctor_set(v___x_752_, 3, v___x_749_);
lean_inc_ref(v_a_743_);
lean_inc(v_a_742_);
lean_inc(v_a_741_);
lean_inc(v_a_740_);
v___x_753_ = lean_apply_7(v_a_739_, v___x_752_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, lean_box(0));
return v___x_753_;
}
}
LEAN_EXPORT void l_Lake_LeanExe_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_738_ = stack[0].m_obj;
lean_object* v_a_739_ = stack[1].m_obj;
lean_object* v_a_740_ = stack[2].m_obj;
lean_object* v_a_741_ = stack[3].m_obj;
lean_object* v_a_742_ = stack[4].m_obj;
lean_object* v_a_743_ = stack[5].m_obj;
lean_object* v_a_744_ = stack[6].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Lake_LeanExe_fetch(v_self_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_fetch___boxed(lean_object* v_self_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_LeanExe_fetch(v_self_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec(v_a_758_);
lean_dec(v_a_757_);
return v_res_763_;
}
}
lean_object* l_Lake_LeanExeDecl_fetch(lean_object* v_self_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_toContext_772_; lean_object* v_pkg_773_; lean_object* v_name_774_; lean_object* v_config_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_807_; 
v_toContext_772_ = lean_ctor_get(v_a_769_, 1);
v_pkg_773_ = lean_ctor_get(v_self_764_, 0);
v_name_774_ = lean_ctor_get(v_self_764_, 1);
v_config_775_ = lean_ctor_get(v_self_764_, 3);
v_isSharedCheck_807_ = !lean_is_exclusive(v_self_764_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_self_764_, 2);
lean_dec(v_unused_808_);
v___x_777_ = v_self_764_;
v_isShared_778_ = v_isSharedCheck_807_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_config_775_);
lean_inc(v_name_774_);
lean_inc(v_pkg_773_);
lean_dec(v_self_764_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_807_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_packageMap_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_packageMap_779_ = lean_ctor_get(v_toContext_772_, 5);
v___x_780_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_773_);
lean_inc(v_packageMap_779_);
v___x_781_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_780_, v_packageMap_779_, v_pkg_773_);
if (lean_obj_tag(v___x_781_) == 1)
{
lean_object* v_val_782_; lean_object* v_keyName_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_pkg_773_);
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_781_, 1);
v_keyName_783_ = lean_ctor_get(v_val_782_, 2);
lean_inc(v_keyName_783_);
v___x_784_ = l_Lake_LeanExe_keyword;
lean_inc(v_name_774_);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v_val_782_);
lean_ctor_set(v___x_785_, 1, v_name_774_);
lean_ctor_set(v___x_785_, 2, v_config_775_);
v___x_786_ = l_Lake_LeanExe_exeFacet;
v___x_787_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_787_, 0, v_keyName_783_);
lean_ctor_set(v___x_787_, 1, v_name_774_);
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 1);
lean_ctor_set(v___x_777_, 3, v___x_786_);
lean_ctor_set(v___x_777_, 2, v___x_785_);
lean_ctor_set(v___x_777_, 1, v___x_784_);
lean_ctor_set(v___x_777_, 0, v___x_787_);
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v___x_786_);
v___x_789_ = v_reuseFailAlloc_791_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; 
lean_inc_ref(v_a_769_);
lean_inc(v_a_768_);
lean_inc(v_a_767_);
lean_inc(v_a_766_);
v___x_790_ = lean_apply_7(v_a_765_, v___x_789_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, lean_box(0));
return v___x_790_;
}
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v___x_781_);
lean_del_object(v___x_777_);
lean_dec(v_config_775_);
lean_dec_ref(v_a_765_);
v___x_792_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_793_ = 1;
v___x_794_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_773_, v___x_793_);
v___x_795_ = lean_string_append(v___x_792_, v___x_794_);
lean_dec_ref(v___x_794_);
v___x_796_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
v___x_798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_774_, v___x_793_);
v___x_799_ = lean_string_append(v___x_797_, v___x_798_);
lean_dec_ref(v___x_798_);
v___x_800_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_801_ = lean_string_append(v___x_799_, v___x_800_);
v___x_802_ = 3;
v___x_803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_802_);
v___x_804_ = lean_array_get_size(v_a_770_);
v___x_805_ = lean_array_push(v_a_770_, v___x_803_);
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanExeDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_764_ = stack[0].m_obj;
lean_object* v_a_765_ = stack[1].m_obj;
lean_object* v_a_766_ = stack[2].m_obj;
lean_object* v_a_767_ = stack[3].m_obj;
lean_object* v_a_768_ = stack[4].m_obj;
lean_object* v_a_769_ = stack[5].m_obj;
lean_object* v_a_770_ = stack[6].m_obj;
lean_object* v_res_809_;
v_res_809_ = l_Lake_LeanExeDecl_fetch(v_self_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_fetch___boxed(lean_object* v_self_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lake_LeanExeDecl_fetch(v_self_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec(v_a_813_);
lean_dec(v_a_812_);
return v_res_818_;
}
}
lean_object* l_Lake_InputFile_fetch(lean_object* v_self_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_pkg_827_; lean_object* v_name_828_; lean_object* v_keyName_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_pkg_827_ = lean_ctor_get(v_self_819_, 0);
v_name_828_ = lean_ctor_get(v_self_819_, 1);
v_keyName_829_ = lean_ctor_get(v_pkg_827_, 2);
v___x_830_ = l_Lake_InputFile_defaultFacet;
lean_inc(v_name_828_);
lean_inc(v_keyName_829_);
v___x_831_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_831_, 0, v_keyName_829_);
lean_ctor_set(v___x_831_, 1, v_name_828_);
v___x_832_ = l_Lake_InputFile_keyword;
v___x_833_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_ctor_set(v___x_833_, 2, v_self_819_);
lean_ctor_set(v___x_833_, 3, v___x_830_);
lean_inc_ref(v_a_824_);
lean_inc(v_a_823_);
lean_inc(v_a_822_);
lean_inc(v_a_821_);
v___x_834_ = lean_apply_7(v_a_820_, v___x_833_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, lean_box(0));
return v___x_834_;
}
}
LEAN_EXPORT void l_Lake_InputFile_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_819_ = stack[0].m_obj;
lean_object* v_a_820_ = stack[1].m_obj;
lean_object* v_a_821_ = stack[2].m_obj;
lean_object* v_a_822_ = stack[3].m_obj;
lean_object* v_a_823_ = stack[4].m_obj;
lean_object* v_a_824_ = stack[5].m_obj;
lean_object* v_a_825_ = stack[6].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Lake_InputFile_fetch(v_self_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lake_InputFile_fetch___boxed(lean_object* v_self_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lake_InputFile_fetch(v_self_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec(v_a_839_);
lean_dec(v_a_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_get___redArg(lean_object* v_self_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_){
_start:
{
lean_object* v_toApplicative_849_; lean_object* v_toFunctor_850_; lean_object* v_toBind_851_; lean_object* v_toPure_852_; lean_object* v_pkg_853_; lean_object* v_name_854_; lean_object* v_config_855_; lean_object* v_map_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_toApplicative_849_ = lean_ctor_get(v_inst_846_, 0);
lean_inc_ref(v_toApplicative_849_);
v_toFunctor_850_ = lean_ctor_get(v_toApplicative_849_, 0);
lean_inc_ref(v_toFunctor_850_);
v_toBind_851_ = lean_ctor_get(v_inst_846_, 1);
lean_inc(v_toBind_851_);
lean_dec_ref(v_inst_846_);
v_toPure_852_ = lean_ctor_get(v_toApplicative_849_, 1);
lean_inc(v_toPure_852_);
lean_dec_ref(v_toApplicative_849_);
v_pkg_853_ = lean_ctor_get(v_self_845_, 0);
lean_inc_n(v_pkg_853_, 2);
v_name_854_ = lean_ctor_get(v_self_845_, 1);
lean_inc(v_name_854_);
v_config_855_ = lean_ctor_get(v_self_845_, 3);
lean_inc(v_config_855_);
lean_dec_ref(v_self_845_);
v_map_856_ = lean_ctor_get(v_toFunctor_850_, 0);
lean_inc_n(v_map_856_, 2);
lean_dec_ref(v_toFunctor_850_);
v___f_857_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_858_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_858_, 0, v_name_854_);
lean_closure_set(v___f_858_, 1, v_config_855_);
lean_closure_set(v___f_858_, 2, v_toPure_852_);
lean_closure_set(v___f_858_, 3, v_pkg_853_);
lean_closure_set(v___f_858_, 4, v_inst_847_);
v___f_859_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_859_, 0, v_pkg_853_);
v___x_860_ = lean_apply_4(v_map_856_, lean_box(0), lean_box(0), v___f_857_, v_inst_848_);
v___x_861_ = lean_apply_4(v_map_856_, lean_box(0), lean_box(0), v___f_859_, v___x_860_);
v___x_862_ = lean_apply_4(v_toBind_851_, lean_box(0), lean_box(0), v___x_861_, v___f_858_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_get(lean_object* v_m_863_, lean_object* v_self_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_inst_867_){
_start:
{
lean_object* v_toApplicative_868_; lean_object* v_toFunctor_869_; lean_object* v_toBind_870_; lean_object* v_toPure_871_; lean_object* v_pkg_872_; lean_object* v_name_873_; lean_object* v_config_874_; lean_object* v_map_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_toApplicative_868_ = lean_ctor_get(v_inst_865_, 0);
lean_inc_ref(v_toApplicative_868_);
v_toFunctor_869_ = lean_ctor_get(v_toApplicative_868_, 0);
lean_inc_ref(v_toFunctor_869_);
v_toBind_870_ = lean_ctor_get(v_inst_865_, 1);
lean_inc(v_toBind_870_);
lean_dec_ref(v_inst_865_);
v_toPure_871_ = lean_ctor_get(v_toApplicative_868_, 1);
lean_inc(v_toPure_871_);
lean_dec_ref(v_toApplicative_868_);
v_pkg_872_ = lean_ctor_get(v_self_864_, 0);
lean_inc_n(v_pkg_872_, 2);
v_name_873_ = lean_ctor_get(v_self_864_, 1);
lean_inc(v_name_873_);
v_config_874_ = lean_ctor_get(v_self_864_, 3);
lean_inc(v_config_874_);
lean_dec_ref(v_self_864_);
v_map_875_ = lean_ctor_get(v_toFunctor_869_, 0);
lean_inc_n(v_map_875_, 2);
lean_dec_ref(v_toFunctor_869_);
v___f_876_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_877_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_877_, 0, v_name_873_);
lean_closure_set(v___f_877_, 1, v_config_874_);
lean_closure_set(v___f_877_, 2, v_toPure_871_);
lean_closure_set(v___f_877_, 3, v_pkg_872_);
lean_closure_set(v___f_877_, 4, v_inst_866_);
v___f_878_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_878_, 0, v_pkg_872_);
v___x_879_ = lean_apply_4(v_map_875_, lean_box(0), lean_box(0), v___f_876_, v_inst_867_);
v___x_880_ = lean_apply_4(v_map_875_, lean_box(0), lean_box(0), v___f_878_, v___x_879_);
v___x_881_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v___x_880_, v___f_877_);
return v___x_881_;
}
}
lean_object* l_Lake_InputFileDecl_fetch(lean_object* v_self_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_toContext_890_; lean_object* v_pkg_891_; lean_object* v_name_892_; lean_object* v_config_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_925_; 
v_toContext_890_ = lean_ctor_get(v_a_887_, 1);
v_pkg_891_ = lean_ctor_get(v_self_882_, 0);
v_name_892_ = lean_ctor_get(v_self_882_, 1);
v_config_893_ = lean_ctor_get(v_self_882_, 3);
v_isSharedCheck_925_ = !lean_is_exclusive(v_self_882_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_self_882_, 2);
lean_dec(v_unused_926_);
v___x_895_ = v_self_882_;
v_isShared_896_ = v_isSharedCheck_925_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_config_893_);
lean_inc(v_name_892_);
lean_inc(v_pkg_891_);
lean_dec(v_self_882_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_925_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_packageMap_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_packageMap_897_ = lean_ctor_get(v_toContext_890_, 5);
v___x_898_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_891_);
lean_inc(v_packageMap_897_);
v___x_899_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_898_, v_packageMap_897_, v_pkg_891_);
if (lean_obj_tag(v___x_899_) == 1)
{
lean_object* v_val_900_; lean_object* v_keyName_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
lean_dec(v_pkg_891_);
v_val_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v___x_899_, 1);
v_keyName_901_ = lean_ctor_get(v_val_900_, 2);
lean_inc(v_keyName_901_);
v___x_902_ = l_Lake_InputFile_keyword;
lean_inc(v_name_892_);
v___x_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_903_, 0, v_val_900_);
lean_ctor_set(v___x_903_, 1, v_name_892_);
lean_ctor_set(v___x_903_, 2, v_config_893_);
v___x_904_ = l_Lake_InputFile_defaultFacet;
v___x_905_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_905_, 0, v_keyName_901_);
lean_ctor_set(v___x_905_, 1, v_name_892_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 1);
lean_ctor_set(v___x_895_, 3, v___x_904_);
lean_ctor_set(v___x_895_, 2, v___x_903_);
lean_ctor_set(v___x_895_, 1, v___x_902_);
lean_ctor_set(v___x_895_, 0, v___x_905_);
v___x_907_ = v___x_895_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v___x_904_);
v___x_907_ = v_reuseFailAlloc_909_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
lean_inc_ref(v_a_887_);
lean_inc(v_a_886_);
lean_inc(v_a_885_);
lean_inc(v_a_884_);
v___x_908_ = lean_apply_7(v_a_883_, v___x_907_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, lean_box(0));
return v___x_908_;
}
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v___x_899_);
lean_del_object(v___x_895_);
lean_dec(v_config_893_);
lean_dec_ref(v_a_883_);
v___x_910_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_911_ = 1;
v___x_912_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_891_, v___x_911_);
v___x_913_ = lean_string_append(v___x_910_, v___x_912_);
lean_dec_ref(v___x_912_);
v___x_914_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_915_ = lean_string_append(v___x_913_, v___x_914_);
v___x_916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_892_, v___x_911_);
v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
lean_dec_ref(v___x_916_);
v___x_918_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
v___x_920_ = 3;
v___x_921_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_920_);
v___x_922_ = lean_array_get_size(v_a_888_);
v___x_923_ = lean_array_push(v_a_888_, v___x_921_);
v___x_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT void l_Lake_InputFileDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_882_ = stack[0].m_obj;
lean_object* v_a_883_ = stack[1].m_obj;
lean_object* v_a_884_ = stack[2].m_obj;
lean_object* v_a_885_ = stack[3].m_obj;
lean_object* v_a_886_ = stack[4].m_obj;
lean_object* v_a_887_ = stack[5].m_obj;
lean_object* v_a_888_ = stack[6].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lake_InputFileDecl_fetch(v_self_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_fetch___boxed(lean_object* v_self_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lake_InputFileDecl_fetch(v_self_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec(v_a_931_);
lean_dec(v_a_930_);
return v_res_936_;
}
}
lean_object* l_Lake_InputDir_fetch(lean_object* v_self_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_pkg_945_; lean_object* v_name_946_; lean_object* v_keyName_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_pkg_945_ = lean_ctor_get(v_self_937_, 0);
v_name_946_ = lean_ctor_get(v_self_937_, 1);
v_keyName_947_ = lean_ctor_get(v_pkg_945_, 2);
v___x_948_ = l_Lake_InputDir_defaultFacet;
lean_inc(v_name_946_);
lean_inc(v_keyName_947_);
v___x_949_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_949_, 0, v_keyName_947_);
lean_ctor_set(v___x_949_, 1, v_name_946_);
v___x_950_ = l_Lake_InputDir_keyword;
v___x_951_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
lean_ctor_set(v___x_951_, 2, v_self_937_);
lean_ctor_set(v___x_951_, 3, v___x_948_);
lean_inc_ref(v_a_942_);
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_inc(v_a_939_);
v___x_952_ = lean_apply_7(v_a_938_, v___x_951_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, lean_box(0));
return v___x_952_;
}
}
LEAN_EXPORT void l_Lake_InputDir_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_937_ = stack[0].m_obj;
lean_object* v_a_938_ = stack[1].m_obj;
lean_object* v_a_939_ = stack[2].m_obj;
lean_object* v_a_940_ = stack[3].m_obj;
lean_object* v_a_941_ = stack[4].m_obj;
lean_object* v_a_942_ = stack[5].m_obj;
lean_object* v_a_943_ = stack[6].m_obj;
lean_object* v_res_953_;
v_res_953_ = l_Lake_InputDir_fetch(v_self_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l_Lake_InputDir_fetch___boxed(lean_object* v_self_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lake_InputDir_fetch(v_self_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec(v_a_957_);
lean_dec(v_a_956_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_get___redArg(lean_object* v_self_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_inst_966_){
_start:
{
lean_object* v_toApplicative_967_; lean_object* v_toFunctor_968_; lean_object* v_toBind_969_; lean_object* v_toPure_970_; lean_object* v_pkg_971_; lean_object* v_name_972_; lean_object* v_config_973_; lean_object* v_map_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_toApplicative_967_ = lean_ctor_get(v_inst_964_, 0);
lean_inc_ref(v_toApplicative_967_);
v_toFunctor_968_ = lean_ctor_get(v_toApplicative_967_, 0);
lean_inc_ref(v_toFunctor_968_);
v_toBind_969_ = lean_ctor_get(v_inst_964_, 1);
lean_inc(v_toBind_969_);
lean_dec_ref(v_inst_964_);
v_toPure_970_ = lean_ctor_get(v_toApplicative_967_, 1);
lean_inc(v_toPure_970_);
lean_dec_ref(v_toApplicative_967_);
v_pkg_971_ = lean_ctor_get(v_self_963_, 0);
lean_inc_n(v_pkg_971_, 2);
v_name_972_ = lean_ctor_get(v_self_963_, 1);
lean_inc(v_name_972_);
v_config_973_ = lean_ctor_get(v_self_963_, 3);
lean_inc(v_config_973_);
lean_dec_ref(v_self_963_);
v_map_974_ = lean_ctor_get(v_toFunctor_968_, 0);
lean_inc_n(v_map_974_, 2);
lean_dec_ref(v_toFunctor_968_);
v___f_975_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_976_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_976_, 0, v_name_972_);
lean_closure_set(v___f_976_, 1, v_config_973_);
lean_closure_set(v___f_976_, 2, v_toPure_970_);
lean_closure_set(v___f_976_, 3, v_pkg_971_);
lean_closure_set(v___f_976_, 4, v_inst_965_);
v___f_977_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_977_, 0, v_pkg_971_);
v___x_978_ = lean_apply_4(v_map_974_, lean_box(0), lean_box(0), v___f_975_, v_inst_966_);
v___x_979_ = lean_apply_4(v_map_974_, lean_box(0), lean_box(0), v___f_977_, v___x_978_);
v___x_980_ = lean_apply_4(v_toBind_969_, lean_box(0), lean_box(0), v___x_979_, v___f_976_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_get(lean_object* v_m_981_, lean_object* v_self_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v_toApplicative_986_; lean_object* v_toFunctor_987_; lean_object* v_toBind_988_; lean_object* v_toPure_989_; lean_object* v_pkg_990_; lean_object* v_name_991_; lean_object* v_config_992_; lean_object* v_map_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_toApplicative_986_ = lean_ctor_get(v_inst_983_, 0);
lean_inc_ref(v_toApplicative_986_);
v_toFunctor_987_ = lean_ctor_get(v_toApplicative_986_, 0);
lean_inc_ref(v_toFunctor_987_);
v_toBind_988_ = lean_ctor_get(v_inst_983_, 1);
lean_inc(v_toBind_988_);
lean_dec_ref(v_inst_983_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_inc(v_toPure_989_);
lean_dec_ref(v_toApplicative_986_);
v_pkg_990_ = lean_ctor_get(v_self_982_, 0);
lean_inc_n(v_pkg_990_, 2);
v_name_991_ = lean_ctor_get(v_self_982_, 1);
lean_inc(v_name_991_);
v_config_992_ = lean_ctor_get(v_self_982_, 3);
lean_inc(v_config_992_);
lean_dec_ref(v_self_982_);
v_map_993_ = lean_ctor_get(v_toFunctor_987_, 0);
lean_inc_n(v_map_993_, 2);
lean_dec_ref(v_toFunctor_987_);
v___f_994_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
v___f_995_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_995_, 0, v_name_991_);
lean_closure_set(v___f_995_, 1, v_config_992_);
lean_closure_set(v___f_995_, 2, v_toPure_989_);
lean_closure_set(v___f_995_, 3, v_pkg_990_);
lean_closure_set(v___f_995_, 4, v_inst_984_);
v___f_996_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_996_, 0, v_pkg_990_);
v___x_997_ = lean_apply_4(v_map_993_, lean_box(0), lean_box(0), v___f_994_, v_inst_985_);
v___x_998_ = lean_apply_4(v_map_993_, lean_box(0), lean_box(0), v___f_996_, v___x_997_);
v___x_999_ = lean_apply_4(v_toBind_988_, lean_box(0), lean_box(0), v___x_998_, v___f_995_);
return v___x_999_;
}
}
lean_object* l_Lake_InputDirDecl_fetch(lean_object* v_self_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_toContext_1008_; lean_object* v_pkg_1009_; lean_object* v_name_1010_; lean_object* v_config_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1043_; 
v_toContext_1008_ = lean_ctor_get(v_a_1005_, 1);
v_pkg_1009_ = lean_ctor_get(v_self_1000_, 0);
v_name_1010_ = lean_ctor_get(v_self_1000_, 1);
v_config_1011_ = lean_ctor_get(v_self_1000_, 3);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_self_1000_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_self_1000_, 2);
lean_dec(v_unused_1044_);
v___x_1013_ = v_self_1000_;
v_isShared_1014_ = v_isSharedCheck_1043_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_config_1011_);
lean_inc(v_name_1010_);
lean_inc(v_pkg_1009_);
lean_dec(v_self_1000_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1043_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_packageMap_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_packageMap_1015_ = lean_ctor_get(v_toContext_1008_, 5);
v___x_1016_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_1009_);
lean_inc(v_packageMap_1015_);
v___x_1017_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_1016_, v_packageMap_1015_, v_pkg_1009_);
if (lean_obj_tag(v___x_1017_) == 1)
{
lean_object* v_val_1018_; lean_object* v_keyName_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec(v_pkg_1009_);
v_val_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v_keyName_1019_ = lean_ctor_get(v_val_1018_, 2);
lean_inc(v_keyName_1019_);
v___x_1020_ = l_Lake_InputDir_keyword;
lean_inc(v_name_1010_);
v___x_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1021_, 0, v_val_1018_);
lean_ctor_set(v___x_1021_, 1, v_name_1010_);
lean_ctor_set(v___x_1021_, 2, v_config_1011_);
v___x_1022_ = l_Lake_InputDir_defaultFacet;
v___x_1023_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_keyName_1019_);
lean_ctor_set(v___x_1023_, 1, v_name_1010_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 1);
lean_ctor_set(v___x_1013_, 3, v___x_1022_);
lean_ctor_set(v___x_1013_, 2, v___x_1021_);
lean_ctor_set(v___x_1013_, 1, v___x_1020_);
lean_ctor_set(v___x_1013_, 0, v___x_1023_);
v___x_1025_ = v___x_1013_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v___x_1022_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
lean_inc_ref(v_a_1005_);
lean_inc(v_a_1004_);
lean_inc(v_a_1003_);
lean_inc(v_a_1002_);
v___x_1026_ = lean_apply_7(v_a_1001_, v___x_1025_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, lean_box(0));
return v___x_1026_;
}
}
else
{
lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v___x_1017_);
lean_del_object(v___x_1013_);
lean_dec(v_config_1011_);
lean_dec_ref(v_a_1001_);
v___x_1028_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_1029_ = 1;
v___x_1030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_1009_, v___x_1029_);
v___x_1031_ = lean_string_append(v___x_1028_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1010_, v___x_1029_);
v___x_1035_ = lean_string_append(v___x_1033_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = 3;
v___x_1039_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*1, v___x_1038_);
v___x_1040_ = lean_array_get_size(v_a_1006_);
v___x_1041_ = lean_array_push(v_a_1006_, v___x_1039_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT void l_Lake_InputDirDecl_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1000_ = stack[0].m_obj;
lean_object* v_a_1001_ = stack[1].m_obj;
lean_object* v_a_1002_ = stack[2].m_obj;
lean_object* v_a_1003_ = stack[3].m_obj;
lean_object* v_a_1004_ = stack[4].m_obj;
lean_object* v_a_1005_ = stack[5].m_obj;
lean_object* v_a_1006_ = stack[6].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Lake_InputDirDecl_fetch(v_self_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_fetch___boxed(lean_object* v_self_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lake_InputDirDecl_fetch(v_self_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
return v_res_1054_;
}
}
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFile(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Targets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Config_InputFile(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Targets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Targets(builtin);
}
#ifdef __cplusplus
}
#endif
