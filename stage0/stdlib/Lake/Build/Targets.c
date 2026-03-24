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
v_packageMap_37_ = lean_ctor_get(v_x_36_, 6);
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
lean_inc(v_pkg_49_);
v_name_50_ = lean_ctor_get(v_self_44_, 1);
lean_inc(v_name_50_);
v_config_51_ = lean_ctor_get(v_self_44_, 3);
lean_inc(v_config_51_);
lean_dec_ref(v_self_44_);
v_map_52_ = lean_ctor_get(v_toFunctor_46_, 0);
lean_inc(v_map_52_);
lean_dec_ref(v_toFunctor_46_);
v___f_53_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_49_);
v___f_54_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_54_, 0, v_name_50_);
lean_closure_set(v___f_54_, 1, v_config_51_);
lean_closure_set(v___f_54_, 2, v_toPure_48_);
lean_closure_set(v___f_54_, 3, v_pkg_49_);
lean_closure_set(v___f_54_, 4, v_inst_42_);
v___f_55_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_55_, 0, v_pkg_49_);
lean_inc(v_map_52_);
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
lean_inc(v_pkg_69_);
v_name_70_ = lean_ctor_get(v_self_64_, 1);
lean_inc(v_name_70_);
v_config_71_ = lean_ctor_get(v_self_64_, 3);
lean_inc(v_config_71_);
lean_dec_ref(v_self_64_);
v_map_72_ = lean_ctor_get(v_toFunctor_66_, 0);
lean_inc(v_map_72_);
lean_dec_ref(v_toFunctor_66_);
v___f_73_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_69_);
v___f_74_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_74_, 0, v_name_70_);
lean_closure_set(v___f_74_, 1, v_config_71_);
lean_closure_set(v___f_74_, 2, v_toPure_68_);
lean_closure_set(v___f_74_, 3, v_pkg_69_);
lean_closure_set(v___f_74_, 4, v_inst_62_);
v___f_75_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_75_, 0, v_pkg_69_);
lean_inc(v_map_72_);
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
LEAN_EXPORT lean_object* l_Lake_Package_fetchTargetJob(lean_object* v_self_86_, lean_object* v_target_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
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
LEAN_EXPORT lean_object* l_Lake_Package_fetchTargetJob___boxed(lean_object* v_self_107_, lean_object* v_target_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lake_Package_fetchTargetJob(v_self_107_, v_target_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec(v_a_111_);
lean_dec(v_a_110_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___redArg(lean_object* v_self_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_toContext_128_; lean_object* v_pkg_129_; lean_object* v_name_130_; lean_object* v_packageMap_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_toContext_128_ = lean_ctor_get(v_a_125_, 1);
v_pkg_129_ = lean_ctor_get(v_self_120_, 0);
lean_inc(v_pkg_129_);
v_name_130_ = lean_ctor_get(v_self_120_, 1);
lean_inc(v_name_130_);
lean_dec_ref(v_self_120_);
v_packageMap_131_ = lean_ctor_get(v_toContext_128_, 6);
v___x_132_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_129_);
lean_inc(v_packageMap_131_);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_132_, v_packageMap_131_, v_pkg_129_);
if (lean_obj_tag(v___x_133_) == 1)
{
lean_object* v_val_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_pkg_129_);
v_val_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_val_134_);
lean_ctor_set(v___x_135_, 1, v_name_130_);
lean_inc(v_a_124_);
lean_inc(v_a_123_);
lean_inc(v_a_122_);
v___x_136_ = lean_apply_7(v_a_121_, v___x_135_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, lean_box(0));
return v___x_136_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_133_);
lean_dec_ref(v_a_125_);
lean_dec_ref(v_a_121_);
v___x_137_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__0));
v___x_138_ = 1;
v___x_139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_129_, v___x_138_);
v___x_140_ = lean_string_append(v___x_137_, v___x_139_);
lean_dec_ref(v___x_139_);
v___x_141_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__1));
v___x_142_ = lean_string_append(v___x_140_, v___x_141_);
v___x_143_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_130_, v___x_138_);
v___x_144_ = lean_string_append(v___x_142_, v___x_143_);
lean_dec_ref(v___x_143_);
v___x_145_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__2));
v___x_146_ = lean_string_append(v___x_144_, v___x_145_);
v___x_147_ = 3;
v___x_148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_147_);
v___x_149_ = lean_array_get_size(v_a_126_);
v___x_150_ = lean_array_push(v_a_126_, v___x_148_);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___redArg___boxed(lean_object* v_self_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lake_TargetDecl_fetch___redArg(v_self_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_156_);
lean_dec(v_a_155_);
lean_dec(v_a_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch(lean_object* v_00_u03b1_161_, lean_object* v_self_162_, lean_object* v_inst_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
lean_inc_ref(v_a_168_);
v___x_171_ = l_Lake_TargetDecl_fetch___redArg(v_self_162_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetch___boxed(lean_object* v_00_u03b1_172_, lean_object* v_self_173_, lean_object* v_inst_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lake_TargetDecl_fetch(v_00_u03b1_172_, v_self_173_, v_inst_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec(v_a_177_);
lean_dec(v_a_176_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(lean_object* v_t_183_, lean_object* v_k_184_){
_start:
{
if (lean_obj_tag(v_t_183_) == 0)
{
lean_object* v_k_185_; lean_object* v_v_186_; lean_object* v_l_187_; lean_object* v_r_188_; uint8_t v___x_189_; 
v_k_185_ = lean_ctor_get(v_t_183_, 1);
v_v_186_ = lean_ctor_get(v_t_183_, 2);
v_l_187_ = lean_ctor_get(v_t_183_, 3);
v_r_188_ = lean_ctor_get(v_t_183_, 4);
v___x_189_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_184_, v_k_185_);
switch(v___x_189_)
{
case 0:
{
v_t_183_ = v_l_187_;
goto _start;
}
case 1:
{
lean_object* v___x_191_; 
lean_inc(v_v_186_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_v_186_);
return v___x_191_;
}
default: 
{
v_t_183_ = v_r_188_;
goto _start;
}
}
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg___boxed(lean_object* v_t_194_, lean_object* v_k_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_t_194_, v_k_195_);
lean_dec(v_k_195_);
lean_dec(v_t_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetchJob(lean_object* v_self_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_toContext_205_; lean_object* v_pkg_206_; lean_object* v_name_207_; lean_object* v_packageMap_208_; lean_object* v___x_209_; 
v_toContext_205_ = lean_ctor_get(v_a_202_, 1);
v_pkg_206_ = lean_ctor_get(v_self_197_, 0);
lean_inc(v_pkg_206_);
v_name_207_ = lean_ctor_get(v_self_197_, 1);
lean_inc(v_name_207_);
lean_dec_ref(v_self_197_);
v_packageMap_208_ = lean_ctor_get(v_toContext_205_, 6);
v___x_209_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_packageMap_208_, v_pkg_206_);
if (lean_obj_tag(v___x_209_) == 1)
{
lean_object* v_val_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_pkg_206_);
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_val_210_);
lean_ctor_set(v___x_211_, 1, v_name_207_);
lean_inc_ref(v_a_202_);
lean_inc(v_a_201_);
lean_inc(v_a_200_);
lean_inc(v_a_199_);
v___x_212_ = lean_apply_7(v_a_198_, v___x_211_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_a_214_ = lean_ctor_get(v___x_212_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v___x_212_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = l_Lake_Job_toOpaque___redArg(v_a_213_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_a_214_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
return v___x_212_;
}
}
else
{
lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___x_209_);
lean_dec_ref(v_a_198_);
v___x_223_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__0));
v___x_224_ = 1;
v___x_225_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_206_, v___x_224_);
v___x_226_ = lean_string_append(v___x_223_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__1));
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
v___x_229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_207_, v___x_224_);
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = ((lean_object*)(l_Lake_TargetDecl_fetch___redArg___closed__2));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v___x_233_ = 3;
v___x_234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = lean_array_get_size(v_a_203_);
v___x_236_ = lean_array_push(v_a_203_, v___x_234_);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetDecl_fetchJob___boxed(lean_object* v_self_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_TargetDecl_fetchJob(v_self_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_t_249_, lean_object* v_k_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___redArg(v_t_249_, v_k_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0___boxed(lean_object* v_00_u03b2_252_, lean_object* v_inst_253_, lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_TargetDecl_fetchJob_spec__0(v_00_u03b2_252_, v_inst_253_, v_t_254_, v_k_255_);
lean_dec(v_k_255_);
lean_dec(v_t_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___redArg(lean_object* v_pkg_257_, lean_object* v_self_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_name_266_; lean_object* v_keyName_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_name_266_ = lean_ctor_get(v_self_258_, 0);
v_keyName_267_ = lean_ctor_get(v_pkg_257_, 2);
lean_inc(v_keyName_267_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_keyName_267_);
v___x_269_ = l_Lake_Package_keyword;
lean_inc(v_name_266_);
v___x_270_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v_pkg_257_);
lean_ctor_set(v___x_270_, 3, v_name_266_);
lean_inc_ref(v_a_263_);
lean_inc(v_a_262_);
lean_inc(v_a_261_);
lean_inc(v_a_260_);
v___x_271_ = lean_apply_7(v_a_259_, v___x_270_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, lean_box(0));
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___redArg___boxed(lean_object* v_pkg_272_, lean_object* v_self_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lake_PackageFacetDecl_fetch___redArg(v_pkg_272_, v_self_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_self_273_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch(lean_object* v_00_u03b1_282_, lean_object* v_pkg_283_, lean_object* v_self_284_, lean_object* v_inst_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_name_293_; lean_object* v_keyName_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_name_293_ = lean_ctor_get(v_self_284_, 0);
v_keyName_294_ = lean_ctor_get(v_pkg_283_, 2);
lean_inc(v_keyName_294_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_keyName_294_);
v___x_296_ = l_Lake_Package_keyword;
lean_inc(v_name_293_);
v___x_297_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
lean_ctor_set(v___x_297_, 2, v_pkg_283_);
lean_ctor_set(v___x_297_, 3, v_name_293_);
lean_inc_ref(v_a_290_);
lean_inc(v_a_289_);
lean_inc(v_a_288_);
lean_inc(v_a_287_);
v___x_298_ = lean_apply_7(v_a_286_, v___x_297_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, lean_box(0));
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageFacetDecl_fetch___boxed(lean_object* v_00_u03b1_299_, lean_object* v_pkg_300_, lean_object* v_self_301_, lean_object* v_inst_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lake_PackageFacetDecl_fetch(v_00_u03b1_299_, v_pkg_300_, v_self_301_, v_inst_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_self_301_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchFacetJob(lean_object* v_name_311_, lean_object* v_self_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_keyName_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_keyName_320_ = lean_ctor_get(v_self_312_, 2);
v___x_321_ = l_Lake_Package_keyword;
v___x_322_ = l_Lean_Name_append(v___x_321_, v_name_311_);
lean_inc(v_keyName_320_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_keyName_320_);
v___x_324_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_321_);
lean_ctor_set(v___x_324_, 2, v_self_312_);
lean_ctor_set(v___x_324_, 3, v___x_322_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc(v_a_315_);
lean_inc(v_a_314_);
v___x_325_ = lean_apply_7(v_a_313_, v___x_324_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, lean_box(0));
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_a_327_ = lean_ctor_get(v___x_325_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_325_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = l_Lake_Job_toOpaque___redArg(v_a_326_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_327_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchFacetJob___boxed(lean_object* v_name_336_, lean_object* v_self_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lake_Package_fetchFacetJob(v_name_336_, v_self_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___redArg(lean_object* v_mod_346_, lean_object* v_self_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_lib_355_; lean_object* v_pkg_356_; lean_object* v_name_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_369_; 
v_lib_355_ = lean_ctor_get(v_mod_346_, 0);
v_pkg_356_ = lean_ctor_get(v_lib_355_, 0);
v_name_357_ = lean_ctor_get(v_self_347_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_self_347_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v_self_347_, 1);
lean_dec(v_unused_370_);
v___x_359_ = v_self_347_;
v_isShared_360_ = v_isSharedCheck_369_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_name_357_);
lean_dec(v_self_347_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_369_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_name_361_; lean_object* v_keyName_362_; lean_object* v___x_364_; 
v_name_361_ = lean_ctor_get(v_mod_346_, 1);
v_keyName_362_ = lean_ctor_get(v_pkg_356_, 2);
lean_inc(v_name_361_);
lean_inc(v_keyName_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 2);
lean_ctor_set(v___x_359_, 1, v_name_361_);
lean_ctor_set(v___x_359_, 0, v_keyName_362_);
v___x_364_ = v___x_359_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_keyName_362_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_name_361_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = l_Lake_Module_keyword;
v___x_366_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
lean_ctor_set(v___x_366_, 2, v_mod_346_);
lean_ctor_set(v___x_366_, 3, v_name_357_);
lean_inc_ref(v_a_352_);
lean_inc(v_a_351_);
lean_inc(v_a_350_);
lean_inc(v_a_349_);
v___x_367_ = lean_apply_7(v_a_348_, v___x_366_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, lean_box(0));
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___redArg___boxed(lean_object* v_mod_371_, lean_object* v_self_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lake_ModuleFacetDecl_fetch___redArg(v_mod_371_, v_self_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec(v_a_375_);
lean_dec(v_a_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch(lean_object* v_00_u03b1_381_, lean_object* v_mod_382_, lean_object* v_self_383_, lean_object* v_inst_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_lib_392_; lean_object* v_pkg_393_; lean_object* v_name_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_406_; 
v_lib_392_ = lean_ctor_get(v_mod_382_, 0);
v_pkg_393_ = lean_ctor_get(v_lib_392_, 0);
v_name_394_ = lean_ctor_get(v_self_383_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_self_383_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_self_383_, 1);
lean_dec(v_unused_407_);
v___x_396_ = v_self_383_;
v_isShared_397_ = v_isSharedCheck_406_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_name_394_);
lean_dec(v_self_383_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_406_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_name_398_; lean_object* v_keyName_399_; lean_object* v___x_401_; 
v_name_398_ = lean_ctor_get(v_mod_382_, 1);
v_keyName_399_ = lean_ctor_get(v_pkg_393_, 2);
lean_inc(v_name_398_);
lean_inc(v_keyName_399_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 2);
lean_ctor_set(v___x_396_, 1, v_name_398_);
lean_ctor_set(v___x_396_, 0, v_keyName_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_keyName_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_name_398_);
v___x_401_ = v_reuseFailAlloc_405_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = l_Lake_Module_keyword;
v___x_403_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v_mod_382_);
lean_ctor_set(v___x_403_, 3, v_name_394_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
lean_inc(v_a_387_);
lean_inc(v_a_386_);
v___x_404_ = lean_apply_7(v_a_385_, v___x_403_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, lean_box(0));
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacetDecl_fetch___boxed(lean_object* v_00_u03b1_408_, lean_object* v_mod_409_, lean_object* v_self_410_, lean_object* v_inst_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lake_ModuleFacetDecl_fetch(v_00_u03b1_408_, v_mod_409_, v_self_410_, v_inst_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec(v_a_414_);
lean_dec(v_a_413_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fetchFacetJob(lean_object* v_name_420_, lean_object* v_self_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_lib_429_; lean_object* v_pkg_430_; lean_object* v_name_431_; lean_object* v_keyName_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_lib_429_ = lean_ctor_get(v_self_421_, 0);
v_pkg_430_ = lean_ctor_get(v_lib_429_, 0);
v_name_431_ = lean_ctor_get(v_self_421_, 1);
v_keyName_432_ = lean_ctor_get(v_pkg_430_, 2);
v___x_433_ = l_Lake_Module_keyword;
v___x_434_ = l_Lean_Name_append(v___x_433_, v_name_420_);
lean_inc(v_name_431_);
lean_inc(v_keyName_432_);
v___x_435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_435_, 0, v_keyName_432_);
lean_ctor_set(v___x_435_, 1, v_name_431_);
v___x_436_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_433_);
lean_ctor_set(v___x_436_, 2, v_self_421_);
lean_ctor_set(v___x_436_, 3, v___x_434_);
lean_inc_ref(v_a_426_);
lean_inc(v_a_425_);
lean_inc(v_a_424_);
lean_inc(v_a_423_);
v___x_437_ = lean_apply_7(v_a_422_, v___x_436_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, lean_box(0));
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_a_439_ = lean_ctor_get(v___x_437_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = l_Lake_Job_toOpaque___redArg(v_a_438_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_a_439_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fetchFacetJob___boxed(lean_object* v_name_448_, lean_object* v_self_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_Module_fetchFacetJob(v_name_448_, v_self_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_get___redArg(lean_object* v_self_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v_toApplicative_462_; lean_object* v_toFunctor_463_; lean_object* v_toBind_464_; lean_object* v_toPure_465_; lean_object* v_pkg_466_; lean_object* v_name_467_; lean_object* v_config_468_; lean_object* v_map_469_; lean_object* v___f_470_; lean_object* v___f_471_; lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_459_, 0);
lean_inc_ref(v_toApplicative_462_);
v_toFunctor_463_ = lean_ctor_get(v_toApplicative_462_, 0);
lean_inc_ref(v_toFunctor_463_);
v_toBind_464_ = lean_ctor_get(v_inst_459_, 1);
lean_inc(v_toBind_464_);
lean_dec_ref(v_inst_459_);
v_toPure_465_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc(v_toPure_465_);
lean_dec_ref(v_toApplicative_462_);
v_pkg_466_ = lean_ctor_get(v_self_458_, 0);
lean_inc(v_pkg_466_);
v_name_467_ = lean_ctor_get(v_self_458_, 1);
lean_inc(v_name_467_);
v_config_468_ = lean_ctor_get(v_self_458_, 3);
lean_inc(v_config_468_);
lean_dec_ref(v_self_458_);
v_map_469_ = lean_ctor_get(v_toFunctor_463_, 0);
lean_inc(v_map_469_);
lean_dec_ref(v_toFunctor_463_);
v___f_470_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_466_);
v___f_471_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_471_, 0, v_name_467_);
lean_closure_set(v___f_471_, 1, v_config_468_);
lean_closure_set(v___f_471_, 2, v_toPure_465_);
lean_closure_set(v___f_471_, 3, v_pkg_466_);
lean_closure_set(v___f_471_, 4, v_inst_460_);
v___f_472_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_472_, 0, v_pkg_466_);
lean_inc(v_map_469_);
v___x_473_ = lean_apply_4(v_map_469_, lean_box(0), lean_box(0), v___f_470_, v_inst_461_);
v___x_474_ = lean_apply_4(v_map_469_, lean_box(0), lean_box(0), v___f_472_, v___x_473_);
v___x_475_ = lean_apply_4(v_toBind_464_, lean_box(0), lean_box(0), v___x_474_, v___f_471_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_get(lean_object* v_m_476_, lean_object* v_self_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_inst_480_){
_start:
{
lean_object* v_toApplicative_481_; lean_object* v_toFunctor_482_; lean_object* v_toBind_483_; lean_object* v_toPure_484_; lean_object* v_pkg_485_; lean_object* v_name_486_; lean_object* v_config_487_; lean_object* v_map_488_; lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_478_, 0);
lean_inc_ref(v_toApplicative_481_);
v_toFunctor_482_ = lean_ctor_get(v_toApplicative_481_, 0);
lean_inc_ref(v_toFunctor_482_);
v_toBind_483_ = lean_ctor_get(v_inst_478_, 1);
lean_inc(v_toBind_483_);
lean_dec_ref(v_inst_478_);
v_toPure_484_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_484_);
lean_dec_ref(v_toApplicative_481_);
v_pkg_485_ = lean_ctor_get(v_self_477_, 0);
lean_inc(v_pkg_485_);
v_name_486_ = lean_ctor_get(v_self_477_, 1);
lean_inc(v_name_486_);
v_config_487_ = lean_ctor_get(v_self_477_, 3);
lean_inc(v_config_487_);
lean_dec_ref(v_self_477_);
v_map_488_ = lean_ctor_get(v_toFunctor_482_, 0);
lean_inc(v_map_488_);
lean_dec_ref(v_toFunctor_482_);
v___f_489_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_485_);
v___f_490_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_490_, 0, v_name_486_);
lean_closure_set(v___f_490_, 1, v_config_487_);
lean_closure_set(v___f_490_, 2, v_toPure_484_);
lean_closure_set(v___f_490_, 3, v_pkg_485_);
lean_closure_set(v___f_490_, 4, v_inst_479_);
v___f_491_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_491_, 0, v_pkg_485_);
lean_inc(v_map_488_);
v___x_492_ = lean_apply_4(v_map_488_, lean_box(0), lean_box(0), v___f_489_, v_inst_480_);
v___x_493_ = lean_apply_4(v_map_488_, lean_box(0), lean_box(0), v___f_491_, v___x_492_);
v___x_494_ = lean_apply_4(v_toBind_483_, lean_box(0), lean_box(0), v___x_493_, v___f_490_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetch(lean_object* v_self_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_pkg_506_; lean_object* v_name_507_; lean_object* v_keyName_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_pkg_506_ = lean_ctor_get(v_self_498_, 0);
v_name_507_ = lean_ctor_get(v_self_498_, 1);
v_keyName_508_ = lean_ctor_get(v_pkg_506_, 2);
v___x_509_ = l_Lake_LeanLib_defaultFacet;
lean_inc(v_name_507_);
lean_inc(v_keyName_508_);
v___x_510_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_510_, 0, v_keyName_508_);
lean_ctor_set(v___x_510_, 1, v_name_507_);
v___x_511_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_512_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
lean_ctor_set(v___x_512_, 2, v_self_498_);
lean_ctor_set(v___x_512_, 3, v___x_509_);
lean_inc_ref(v_a_503_);
lean_inc(v_a_502_);
lean_inc(v_a_501_);
lean_inc(v_a_500_);
v___x_513_ = lean_apply_7(v_a_499_, v___x_512_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, lean_box(0));
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetch___boxed(lean_object* v_self_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lake_LeanLib_fetch(v_self_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_fetch(lean_object* v_self_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_toContext_531_; lean_object* v_pkg_532_; lean_object* v_name_533_; lean_object* v_config_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_566_; 
v_toContext_531_ = lean_ctor_get(v_a_528_, 1);
v_pkg_532_ = lean_ctor_get(v_self_523_, 0);
v_name_533_ = lean_ctor_get(v_self_523_, 1);
v_config_534_ = lean_ctor_get(v_self_523_, 3);
v_isSharedCheck_566_ = !lean_is_exclusive(v_self_523_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_self_523_, 2);
lean_dec(v_unused_567_);
v___x_536_ = v_self_523_;
v_isShared_537_ = v_isSharedCheck_566_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_config_534_);
lean_inc(v_name_533_);
lean_inc(v_pkg_532_);
lean_dec(v_self_523_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_566_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_packageMap_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_packageMap_538_ = lean_ctor_get(v_toContext_531_, 6);
v___x_539_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_532_);
lean_inc(v_packageMap_538_);
v___x_540_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_539_, v_packageMap_538_, v_pkg_532_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v_keyName_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec(v_pkg_532_);
v_val_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref(v___x_540_);
v_keyName_542_ = lean_ctor_get(v_val_541_, 2);
lean_inc(v_keyName_542_);
v___x_543_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
lean_inc(v_name_533_);
v___x_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_544_, 0, v_val_541_);
lean_ctor_set(v___x_544_, 1, v_name_533_);
lean_ctor_set(v___x_544_, 2, v_config_534_);
v___x_545_ = l_Lake_LeanLib_defaultFacet;
v___x_546_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_546_, 0, v_keyName_542_);
lean_ctor_set(v___x_546_, 1, v_name_533_);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 1);
lean_ctor_set(v___x_536_, 3, v___x_545_);
lean_ctor_set(v___x_536_, 2, v___x_544_);
lean_ctor_set(v___x_536_, 1, v___x_543_);
lean_ctor_set(v___x_536_, 0, v___x_546_);
v___x_548_ = v___x_536_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v___x_545_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; 
lean_inc(v_a_527_);
lean_inc(v_a_526_);
lean_inc(v_a_525_);
v___x_549_ = lean_apply_7(v_a_524_, v___x_548_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, lean_box(0));
return v___x_549_;
}
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v___x_540_);
lean_del_object(v___x_536_);
lean_dec(v_config_534_);
lean_dec_ref(v_a_528_);
lean_dec_ref(v_a_524_);
v___x_551_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_552_ = 1;
v___x_553_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_532_, v___x_552_);
v___x_554_ = lean_string_append(v___x_551_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v___x_557_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_533_, v___x_552_);
v___x_558_ = lean_string_append(v___x_556_, v___x_557_);
lean_dec_ref(v___x_557_);
v___x_559_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_560_ = lean_string_append(v___x_558_, v___x_559_);
v___x_561_ = 3;
v___x_562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*1, v___x_561_);
v___x_563_ = lean_array_get_size(v_a_529_);
v___x_564_ = lean_array_push(v_a_529_, v___x_562_);
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibDecl_fetch___boxed(lean_object* v_self_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lake_LeanLibDecl_fetch(v_self_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_572_);
lean_dec(v_a_571_);
lean_dec(v_a_570_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___redArg(lean_object* v_lib_577_, lean_object* v_self_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_pkg_586_; lean_object* v_name_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_599_; 
v_pkg_586_ = lean_ctor_get(v_lib_577_, 0);
v_name_587_ = lean_ctor_get(v_self_578_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_self_578_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_self_578_, 1);
lean_dec(v_unused_600_);
v___x_589_ = v_self_578_;
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_name_587_);
lean_dec(v_self_578_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_name_591_; lean_object* v_keyName_592_; lean_object* v___x_594_; 
v_name_591_ = lean_ctor_get(v_lib_577_, 1);
v_keyName_592_ = lean_ctor_get(v_pkg_586_, 2);
lean_inc(v_name_591_);
lean_inc(v_keyName_592_);
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 3);
lean_ctor_set(v___x_589_, 1, v_name_591_);
lean_ctor_set(v___x_589_, 0, v_keyName_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_keyName_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_name_591_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_596_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_ctor_set(v___x_596_, 2, v_lib_577_);
lean_ctor_set(v___x_596_, 3, v_name_587_);
lean_inc_ref(v_a_583_);
lean_inc(v_a_582_);
lean_inc(v_a_581_);
lean_inc(v_a_580_);
v___x_597_ = lean_apply_7(v_a_579_, v___x_596_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, lean_box(0));
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___redArg___boxed(lean_object* v_lib_601_, lean_object* v_self_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_LibraryFacetDecl_fetch___redArg(v_lib_601_, v_self_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec(v_a_605_);
lean_dec(v_a_604_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch(lean_object* v_00_u03b1_611_, lean_object* v_lib_612_, lean_object* v_self_613_, lean_object* v_inst_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_pkg_622_; lean_object* v_name_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_635_; 
v_pkg_622_ = lean_ctor_get(v_lib_612_, 0);
v_name_623_ = lean_ctor_get(v_self_613_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_self_613_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_self_613_, 1);
lean_dec(v_unused_636_);
v___x_625_ = v_self_613_;
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_name_623_);
lean_dec(v_self_613_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_name_627_; lean_object* v_keyName_628_; lean_object* v___x_630_; 
v_name_627_ = lean_ctor_get(v_lib_612_, 1);
v_keyName_628_ = lean_ctor_get(v_pkg_622_, 2);
lean_inc(v_name_627_);
lean_inc(v_keyName_628_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 3);
lean_ctor_set(v___x_625_, 1, v_name_627_);
lean_ctor_set(v___x_625_, 0, v_keyName_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_keyName_628_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_name_627_);
v___x_630_ = v_reuseFailAlloc_634_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_632_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_ctor_set(v___x_632_, 2, v_lib_612_);
lean_ctor_set(v___x_632_, 3, v_name_623_);
lean_inc_ref(v_a_619_);
lean_inc(v_a_618_);
lean_inc(v_a_617_);
lean_inc(v_a_616_);
v___x_633_ = lean_apply_7(v_a_615_, v___x_632_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, lean_box(0));
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LibraryFacetDecl_fetch___boxed(lean_object* v_00_u03b1_637_, lean_object* v_lib_638_, lean_object* v_self_639_, lean_object* v_inst_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lake_LibraryFacetDecl_fetch(v_00_u03b1_637_, v_lib_638_, v_self_639_, v_inst_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec(v_a_643_);
lean_dec(v_a_642_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetchFacetJob(lean_object* v_name_649_, lean_object* v_self_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_pkg_658_; lean_object* v_name_659_; lean_object* v_keyName_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_pkg_658_ = lean_ctor_get(v_self_650_, 0);
v_name_659_ = lean_ctor_get(v_self_650_, 1);
v_keyName_660_ = lean_ctor_get(v_pkg_658_, 2);
v___x_661_ = ((lean_object*)(l_Lake_LeanLib_fetch___closed__1));
v___x_662_ = l_Lean_Name_append(v___x_661_, v_name_649_);
lean_inc(v_name_659_);
lean_inc(v_keyName_660_);
v___x_663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_663_, 0, v_keyName_660_);
lean_ctor_set(v___x_663_, 1, v_name_659_);
v___x_664_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_661_);
lean_ctor_set(v___x_664_, 2, v_self_650_);
lean_ctor_set(v___x_664_, 3, v___x_662_);
lean_inc_ref(v_a_655_);
lean_inc(v_a_654_);
lean_inc(v_a_653_);
lean_inc(v_a_652_);
v___x_665_ = lean_apply_7(v_a_651_, v___x_664_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, lean_box(0));
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_a_667_ = lean_ctor_get(v___x_665_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = l_Lake_Job_toOpaque___redArg(v_a_666_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_a_667_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_fetchFacetJob___boxed(lean_object* v_name_676_, lean_object* v_self_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lake_LeanLib_fetchFacetJob(v_name_676_, v_self_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec(v_a_680_);
lean_dec(v_a_679_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_get___redArg(lean_object* v_self_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_){
_start:
{
lean_object* v_toApplicative_690_; lean_object* v_toFunctor_691_; lean_object* v_toBind_692_; lean_object* v_toPure_693_; lean_object* v_pkg_694_; lean_object* v_name_695_; lean_object* v_config_696_; lean_object* v_map_697_; lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_toApplicative_690_ = lean_ctor_get(v_inst_687_, 0);
lean_inc_ref(v_toApplicative_690_);
v_toFunctor_691_ = lean_ctor_get(v_toApplicative_690_, 0);
lean_inc_ref(v_toFunctor_691_);
v_toBind_692_ = lean_ctor_get(v_inst_687_, 1);
lean_inc(v_toBind_692_);
lean_dec_ref(v_inst_687_);
v_toPure_693_ = lean_ctor_get(v_toApplicative_690_, 1);
lean_inc(v_toPure_693_);
lean_dec_ref(v_toApplicative_690_);
v_pkg_694_ = lean_ctor_get(v_self_686_, 0);
lean_inc(v_pkg_694_);
v_name_695_ = lean_ctor_get(v_self_686_, 1);
lean_inc(v_name_695_);
v_config_696_ = lean_ctor_get(v_self_686_, 3);
lean_inc(v_config_696_);
lean_dec_ref(v_self_686_);
v_map_697_ = lean_ctor_get(v_toFunctor_691_, 0);
lean_inc(v_map_697_);
lean_dec_ref(v_toFunctor_691_);
v___f_698_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_694_);
v___f_699_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_699_, 0, v_name_695_);
lean_closure_set(v___f_699_, 1, v_config_696_);
lean_closure_set(v___f_699_, 2, v_toPure_693_);
lean_closure_set(v___f_699_, 3, v_pkg_694_);
lean_closure_set(v___f_699_, 4, v_inst_688_);
v___f_700_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_700_, 0, v_pkg_694_);
lean_inc(v_map_697_);
v___x_701_ = lean_apply_4(v_map_697_, lean_box(0), lean_box(0), v___f_698_, v_inst_689_);
v___x_702_ = lean_apply_4(v_map_697_, lean_box(0), lean_box(0), v___f_700_, v___x_701_);
v___x_703_ = lean_apply_4(v_toBind_692_, lean_box(0), lean_box(0), v___x_702_, v___f_699_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_get(lean_object* v_m_704_, lean_object* v_self_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_){
_start:
{
lean_object* v_toApplicative_709_; lean_object* v_toFunctor_710_; lean_object* v_toBind_711_; lean_object* v_toPure_712_; lean_object* v_pkg_713_; lean_object* v_name_714_; lean_object* v_config_715_; lean_object* v_map_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_toApplicative_709_ = lean_ctor_get(v_inst_706_, 0);
lean_inc_ref(v_toApplicative_709_);
v_toFunctor_710_ = lean_ctor_get(v_toApplicative_709_, 0);
lean_inc_ref(v_toFunctor_710_);
v_toBind_711_ = lean_ctor_get(v_inst_706_, 1);
lean_inc(v_toBind_711_);
lean_dec_ref(v_inst_706_);
v_toPure_712_ = lean_ctor_get(v_toApplicative_709_, 1);
lean_inc(v_toPure_712_);
lean_dec_ref(v_toApplicative_709_);
v_pkg_713_ = lean_ctor_get(v_self_705_, 0);
lean_inc(v_pkg_713_);
v_name_714_ = lean_ctor_get(v_self_705_, 1);
lean_inc(v_name_714_);
v_config_715_ = lean_ctor_get(v_self_705_, 3);
lean_inc(v_config_715_);
lean_dec_ref(v_self_705_);
v_map_716_ = lean_ctor_get(v_toFunctor_710_, 0);
lean_inc(v_map_716_);
lean_dec_ref(v_toFunctor_710_);
v___f_717_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_713_);
v___f_718_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_718_, 0, v_name_714_);
lean_closure_set(v___f_718_, 1, v_config_715_);
lean_closure_set(v___f_718_, 2, v_toPure_712_);
lean_closure_set(v___f_718_, 3, v_pkg_713_);
lean_closure_set(v___f_718_, 4, v_inst_707_);
v___f_719_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_719_, 0, v_pkg_713_);
lean_inc(v_map_716_);
v___x_720_ = lean_apply_4(v_map_716_, lean_box(0), lean_box(0), v___f_717_, v_inst_708_);
v___x_721_ = lean_apply_4(v_map_716_, lean_box(0), lean_box(0), v___f_719_, v___x_720_);
v___x_722_ = lean_apply_4(v_toBind_711_, lean_box(0), lean_box(0), v___x_721_, v___f_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_fetch(lean_object* v_self_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_pkg_731_; lean_object* v_name_732_; lean_object* v_keyName_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_pkg_731_ = lean_ctor_get(v_self_723_, 0);
v_name_732_ = lean_ctor_get(v_self_723_, 1);
v_keyName_733_ = lean_ctor_get(v_pkg_731_, 2);
v___x_734_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_732_);
lean_inc(v_keyName_733_);
v___x_735_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_735_, 0, v_keyName_733_);
lean_ctor_set(v___x_735_, 1, v_name_732_);
v___x_736_ = l_Lake_LeanExe_keyword;
v___x_737_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
lean_ctor_set(v___x_737_, 2, v_self_723_);
lean_ctor_set(v___x_737_, 3, v___x_734_);
lean_inc_ref(v_a_728_);
lean_inc(v_a_727_);
lean_inc(v_a_726_);
lean_inc(v_a_725_);
v___x_738_ = lean_apply_7(v_a_724_, v___x_737_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExe_fetch___boxed(lean_object* v_self_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lake_LeanExe_fetch(v_self_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec(v_a_742_);
lean_dec(v_a_741_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_fetch(lean_object* v_self_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_toContext_756_; lean_object* v_pkg_757_; lean_object* v_name_758_; lean_object* v_config_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_791_; 
v_toContext_756_ = lean_ctor_get(v_a_753_, 1);
v_pkg_757_ = lean_ctor_get(v_self_748_, 0);
v_name_758_ = lean_ctor_get(v_self_748_, 1);
v_config_759_ = lean_ctor_get(v_self_748_, 3);
v_isSharedCheck_791_ = !lean_is_exclusive(v_self_748_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_self_748_, 2);
lean_dec(v_unused_792_);
v___x_761_ = v_self_748_;
v_isShared_762_ = v_isSharedCheck_791_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_config_759_);
lean_inc(v_name_758_);
lean_inc(v_pkg_757_);
lean_dec(v_self_748_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_791_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_packageMap_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_packageMap_763_ = lean_ctor_get(v_toContext_756_, 6);
v___x_764_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_757_);
lean_inc(v_packageMap_763_);
v___x_765_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_764_, v_packageMap_763_, v_pkg_757_);
if (lean_obj_tag(v___x_765_) == 1)
{
lean_object* v_val_766_; lean_object* v_keyName_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v_pkg_757_);
v_val_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref(v___x_765_);
v_keyName_767_ = lean_ctor_get(v_val_766_, 2);
lean_inc(v_keyName_767_);
v___x_768_ = l_Lake_LeanExe_keyword;
lean_inc(v_name_758_);
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v_val_766_);
lean_ctor_set(v___x_769_, 1, v_name_758_);
lean_ctor_set(v___x_769_, 2, v_config_759_);
v___x_770_ = l_Lake_LeanExe_exeFacet;
v___x_771_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_771_, 0, v_keyName_767_);
lean_ctor_set(v___x_771_, 1, v_name_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 1);
lean_ctor_set(v___x_761_, 3, v___x_770_);
lean_ctor_set(v___x_761_, 2, v___x_769_);
lean_ctor_set(v___x_761_, 1, v___x_768_);
lean_ctor_set(v___x_761_, 0, v___x_771_);
v___x_773_ = v___x_761_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v___x_770_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
lean_inc(v_a_752_);
lean_inc(v_a_751_);
lean_inc(v_a_750_);
v___x_774_ = lean_apply_7(v_a_749_, v___x_773_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, lean_box(0));
return v___x_774_;
}
}
else
{
lean_object* v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v___x_765_);
lean_del_object(v___x_761_);
lean_dec(v_config_759_);
lean_dec_ref(v_a_753_);
lean_dec_ref(v_a_749_);
v___x_776_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_777_ = 1;
v___x_778_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_757_, v___x_777_);
v___x_779_ = lean_string_append(v___x_776_, v___x_778_);
lean_dec_ref(v___x_778_);
v___x_780_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
v___x_782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_758_, v___x_777_);
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___x_786_ = 3;
v___x_787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*1, v___x_786_);
v___x_788_ = lean_array_get_size(v_a_754_);
v___x_789_ = lean_array_push(v_a_754_, v___x_787_);
v___x_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeDecl_fetch___boxed(lean_object* v_self_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lake_LeanExeDecl_fetch(v_self_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_797_);
lean_dec(v_a_796_);
lean_dec(v_a_795_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_fetch(lean_object* v_self_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_pkg_810_; lean_object* v_name_811_; lean_object* v_keyName_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_pkg_810_ = lean_ctor_get(v_self_802_, 0);
v_name_811_ = lean_ctor_get(v_self_802_, 1);
v_keyName_812_ = lean_ctor_get(v_pkg_810_, 2);
v___x_813_ = l_Lake_InputFile_defaultFacet;
lean_inc(v_name_811_);
lean_inc(v_keyName_812_);
v___x_814_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_814_, 0, v_keyName_812_);
lean_ctor_set(v___x_814_, 1, v_name_811_);
v___x_815_ = l_Lake_InputFile_keyword;
v___x_816_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
lean_ctor_set(v___x_816_, 2, v_self_802_);
lean_ctor_set(v___x_816_, 3, v___x_813_);
lean_inc_ref(v_a_807_);
lean_inc(v_a_806_);
lean_inc(v_a_805_);
lean_inc(v_a_804_);
v___x_817_ = lean_apply_7(v_a_803_, v___x_816_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, lean_box(0));
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFile_fetch___boxed(lean_object* v_self_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lake_InputFile_fetch(v_self_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_get___redArg(lean_object* v_self_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_){
_start:
{
lean_object* v_toApplicative_831_; lean_object* v_toFunctor_832_; lean_object* v_toBind_833_; lean_object* v_toPure_834_; lean_object* v_pkg_835_; lean_object* v_name_836_; lean_object* v_config_837_; lean_object* v_map_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_toApplicative_831_ = lean_ctor_get(v_inst_828_, 0);
lean_inc_ref(v_toApplicative_831_);
v_toFunctor_832_ = lean_ctor_get(v_toApplicative_831_, 0);
lean_inc_ref(v_toFunctor_832_);
v_toBind_833_ = lean_ctor_get(v_inst_828_, 1);
lean_inc(v_toBind_833_);
lean_dec_ref(v_inst_828_);
v_toPure_834_ = lean_ctor_get(v_toApplicative_831_, 1);
lean_inc(v_toPure_834_);
lean_dec_ref(v_toApplicative_831_);
v_pkg_835_ = lean_ctor_get(v_self_827_, 0);
lean_inc(v_pkg_835_);
v_name_836_ = lean_ctor_get(v_self_827_, 1);
lean_inc(v_name_836_);
v_config_837_ = lean_ctor_get(v_self_827_, 3);
lean_inc(v_config_837_);
lean_dec_ref(v_self_827_);
v_map_838_ = lean_ctor_get(v_toFunctor_832_, 0);
lean_inc(v_map_838_);
lean_dec_ref(v_toFunctor_832_);
v___f_839_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_835_);
v___f_840_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_840_, 0, v_name_836_);
lean_closure_set(v___f_840_, 1, v_config_837_);
lean_closure_set(v___f_840_, 2, v_toPure_834_);
lean_closure_set(v___f_840_, 3, v_pkg_835_);
lean_closure_set(v___f_840_, 4, v_inst_829_);
v___f_841_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_841_, 0, v_pkg_835_);
lean_inc(v_map_838_);
v___x_842_ = lean_apply_4(v_map_838_, lean_box(0), lean_box(0), v___f_839_, v_inst_830_);
v___x_843_ = lean_apply_4(v_map_838_, lean_box(0), lean_box(0), v___f_841_, v___x_842_);
v___x_844_ = lean_apply_4(v_toBind_833_, lean_box(0), lean_box(0), v___x_843_, v___f_840_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_get(lean_object* v_m_845_, lean_object* v_self_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_inst_849_){
_start:
{
lean_object* v_toApplicative_850_; lean_object* v_toFunctor_851_; lean_object* v_toBind_852_; lean_object* v_toPure_853_; lean_object* v_pkg_854_; lean_object* v_name_855_; lean_object* v_config_856_; lean_object* v_map_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_toApplicative_850_ = lean_ctor_get(v_inst_847_, 0);
lean_inc_ref(v_toApplicative_850_);
v_toFunctor_851_ = lean_ctor_get(v_toApplicative_850_, 0);
lean_inc_ref(v_toFunctor_851_);
v_toBind_852_ = lean_ctor_get(v_inst_847_, 1);
lean_inc(v_toBind_852_);
lean_dec_ref(v_inst_847_);
v_toPure_853_ = lean_ctor_get(v_toApplicative_850_, 1);
lean_inc(v_toPure_853_);
lean_dec_ref(v_toApplicative_850_);
v_pkg_854_ = lean_ctor_get(v_self_846_, 0);
lean_inc(v_pkg_854_);
v_name_855_ = lean_ctor_get(v_self_846_, 1);
lean_inc(v_name_855_);
v_config_856_ = lean_ctor_get(v_self_846_, 3);
lean_inc(v_config_856_);
lean_dec_ref(v_self_846_);
v_map_857_ = lean_ctor_get(v_toFunctor_851_, 0);
lean_inc(v_map_857_);
lean_dec_ref(v_toFunctor_851_);
v___f_858_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_854_);
v___f_859_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_859_, 0, v_name_855_);
lean_closure_set(v___f_859_, 1, v_config_856_);
lean_closure_set(v___f_859_, 2, v_toPure_853_);
lean_closure_set(v___f_859_, 3, v_pkg_854_);
lean_closure_set(v___f_859_, 4, v_inst_848_);
v___f_860_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_860_, 0, v_pkg_854_);
lean_inc(v_map_857_);
v___x_861_ = lean_apply_4(v_map_857_, lean_box(0), lean_box(0), v___f_858_, v_inst_849_);
v___x_862_ = lean_apply_4(v_map_857_, lean_box(0), lean_box(0), v___f_860_, v___x_861_);
v___x_863_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v___x_862_, v___f_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_fetch(lean_object* v_self_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_toContext_872_; lean_object* v_pkg_873_; lean_object* v_name_874_; lean_object* v_config_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_907_; 
v_toContext_872_ = lean_ctor_get(v_a_869_, 1);
v_pkg_873_ = lean_ctor_get(v_self_864_, 0);
v_name_874_ = lean_ctor_get(v_self_864_, 1);
v_config_875_ = lean_ctor_get(v_self_864_, 3);
v_isSharedCheck_907_ = !lean_is_exclusive(v_self_864_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_self_864_, 2);
lean_dec(v_unused_908_);
v___x_877_ = v_self_864_;
v_isShared_878_ = v_isSharedCheck_907_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_config_875_);
lean_inc(v_name_874_);
lean_inc(v_pkg_873_);
lean_dec(v_self_864_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_907_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_packageMap_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_packageMap_879_ = lean_ctor_get(v_toContext_872_, 6);
v___x_880_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_873_);
lean_inc(v_packageMap_879_);
v___x_881_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_880_, v_packageMap_879_, v_pkg_873_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; lean_object* v_keyName_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
lean_dec(v_pkg_873_);
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref(v___x_881_);
v_keyName_883_ = lean_ctor_get(v_val_882_, 2);
lean_inc(v_keyName_883_);
v___x_884_ = l_Lake_InputFile_keyword;
lean_inc(v_name_874_);
v___x_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_885_, 0, v_val_882_);
lean_ctor_set(v___x_885_, 1, v_name_874_);
lean_ctor_set(v___x_885_, 2, v_config_875_);
v___x_886_ = l_Lake_InputFile_defaultFacet;
v___x_887_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_887_, 0, v_keyName_883_);
lean_ctor_set(v___x_887_, 1, v_name_874_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 1);
lean_ctor_set(v___x_877_, 3, v___x_886_);
lean_ctor_set(v___x_877_, 2, v___x_885_);
lean_ctor_set(v___x_877_, 1, v___x_884_);
lean_ctor_set(v___x_877_, 0, v___x_887_);
v___x_889_ = v___x_877_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v___x_886_);
v___x_889_ = v_reuseFailAlloc_891_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; 
lean_inc(v_a_868_);
lean_inc(v_a_867_);
lean_inc(v_a_866_);
v___x_890_ = lean_apply_7(v_a_865_, v___x_889_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, lean_box(0));
return v___x_890_;
}
}
else
{
lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v___x_881_);
lean_del_object(v___x_877_);
lean_dec(v_config_875_);
lean_dec_ref(v_a_869_);
lean_dec_ref(v_a_865_);
v___x_892_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_893_ = 1;
v___x_894_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_873_, v___x_893_);
v___x_895_ = lean_string_append(v___x_892_, v___x_894_);
lean_dec_ref(v___x_894_);
v___x_896_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_897_ = lean_string_append(v___x_895_, v___x_896_);
v___x_898_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_874_, v___x_893_);
v___x_899_ = lean_string_append(v___x_897_, v___x_898_);
lean_dec_ref(v___x_898_);
v___x_900_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_901_ = lean_string_append(v___x_899_, v___x_900_);
v___x_902_ = 3;
v___x_903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_902_);
v___x_904_ = lean_array_get_size(v_a_870_);
v___x_905_ = lean_array_push(v_a_870_, v___x_903_);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputFileDecl_fetch___boxed(lean_object* v_self_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lake_InputFileDecl_fetch(v_self_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_913_);
lean_dec(v_a_912_);
lean_dec(v_a_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_fetch(lean_object* v_self_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_pkg_926_; lean_object* v_name_927_; lean_object* v_keyName_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_pkg_926_ = lean_ctor_get(v_self_918_, 0);
v_name_927_ = lean_ctor_get(v_self_918_, 1);
v_keyName_928_ = lean_ctor_get(v_pkg_926_, 2);
v___x_929_ = l_Lake_InputDir_defaultFacet;
lean_inc(v_name_927_);
lean_inc(v_keyName_928_);
v___x_930_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_930_, 0, v_keyName_928_);
lean_ctor_set(v___x_930_, 1, v_name_927_);
v___x_931_ = l_Lake_InputDir_keyword;
v___x_932_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
lean_ctor_set(v___x_932_, 2, v_self_918_);
lean_ctor_set(v___x_932_, 3, v___x_929_);
lean_inc_ref(v_a_923_);
lean_inc(v_a_922_);
lean_inc(v_a_921_);
lean_inc(v_a_920_);
v___x_933_ = lean_apply_7(v_a_919_, v___x_932_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, lean_box(0));
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_fetch___boxed(lean_object* v_self_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lake_InputDir_fetch(v_self_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_a_937_);
lean_dec(v_a_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_get___redArg(lean_object* v_self_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_){
_start:
{
lean_object* v_toApplicative_947_; lean_object* v_toFunctor_948_; lean_object* v_toBind_949_; lean_object* v_toPure_950_; lean_object* v_pkg_951_; lean_object* v_name_952_; lean_object* v_config_953_; lean_object* v_map_954_; lean_object* v___f_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_toApplicative_947_ = lean_ctor_get(v_inst_944_, 0);
lean_inc_ref(v_toApplicative_947_);
v_toFunctor_948_ = lean_ctor_get(v_toApplicative_947_, 0);
lean_inc_ref(v_toFunctor_948_);
v_toBind_949_ = lean_ctor_get(v_inst_944_, 1);
lean_inc(v_toBind_949_);
lean_dec_ref(v_inst_944_);
v_toPure_950_ = lean_ctor_get(v_toApplicative_947_, 1);
lean_inc(v_toPure_950_);
lean_dec_ref(v_toApplicative_947_);
v_pkg_951_ = lean_ctor_get(v_self_943_, 0);
lean_inc(v_pkg_951_);
v_name_952_ = lean_ctor_get(v_self_943_, 1);
lean_inc(v_name_952_);
v_config_953_ = lean_ctor_get(v_self_943_, 3);
lean_inc(v_config_953_);
lean_dec_ref(v_self_943_);
v_map_954_ = lean_ctor_get(v_toFunctor_948_, 0);
lean_inc(v_map_954_);
lean_dec_ref(v_toFunctor_948_);
v___f_955_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_951_);
v___f_956_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_956_, 0, v_name_952_);
lean_closure_set(v___f_956_, 1, v_config_953_);
lean_closure_set(v___f_956_, 2, v_toPure_950_);
lean_closure_set(v___f_956_, 3, v_pkg_951_);
lean_closure_set(v___f_956_, 4, v_inst_945_);
v___f_957_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_957_, 0, v_pkg_951_);
lean_inc(v_map_954_);
v___x_958_ = lean_apply_4(v_map_954_, lean_box(0), lean_box(0), v___f_955_, v_inst_946_);
v___x_959_ = lean_apply_4(v_map_954_, lean_box(0), lean_box(0), v___f_957_, v___x_958_);
v___x_960_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___x_959_, v___f_956_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_get(lean_object* v_m_961_, lean_object* v_self_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_inst_965_){
_start:
{
lean_object* v_toApplicative_966_; lean_object* v_toFunctor_967_; lean_object* v_toBind_968_; lean_object* v_toPure_969_; lean_object* v_pkg_970_; lean_object* v_name_971_; lean_object* v_config_972_; lean_object* v_map_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_toApplicative_966_ = lean_ctor_get(v_inst_963_, 0);
lean_inc_ref(v_toApplicative_966_);
v_toFunctor_967_ = lean_ctor_get(v_toApplicative_966_, 0);
lean_inc_ref(v_toFunctor_967_);
v_toBind_968_ = lean_ctor_get(v_inst_963_, 1);
lean_inc(v_toBind_968_);
lean_dec_ref(v_inst_963_);
v_toPure_969_ = lean_ctor_get(v_toApplicative_966_, 1);
lean_inc(v_toPure_969_);
lean_dec_ref(v_toApplicative_966_);
v_pkg_970_ = lean_ctor_get(v_self_962_, 0);
lean_inc(v_pkg_970_);
v_name_971_ = lean_ctor_get(v_self_962_, 1);
lean_inc(v_name_971_);
v_config_972_ = lean_ctor_get(v_self_962_, 3);
lean_inc(v_config_972_);
lean_dec_ref(v_self_962_);
v_map_973_ = lean_ctor_get(v_toFunctor_967_, 0);
lean_inc(v_map_973_);
lean_dec_ref(v_toFunctor_967_);
v___f_974_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___closed__0));
lean_inc(v_pkg_970_);
v___f_975_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_975_, 0, v_name_971_);
lean_closure_set(v___f_975_, 1, v_config_972_);
lean_closure_set(v___f_975_, 2, v_toPure_969_);
lean_closure_set(v___f_975_, 3, v_pkg_970_);
lean_closure_set(v___f_975_, 4, v_inst_964_);
v___f_976_ = lean_alloc_closure((void*)(l_Lake_KConfigDecl_get___redArg___lam__2), 2, 1);
lean_closure_set(v___f_976_, 0, v_pkg_970_);
lean_inc(v_map_973_);
v___x_977_ = lean_apply_4(v_map_973_, lean_box(0), lean_box(0), v___f_974_, v_inst_965_);
v___x_978_ = lean_apply_4(v_map_973_, lean_box(0), lean_box(0), v___f_976_, v___x_977_);
v___x_979_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_978_, v___f_975_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_fetch(lean_object* v_self_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_toContext_988_; lean_object* v_pkg_989_; lean_object* v_name_990_; lean_object* v_config_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1023_; 
v_toContext_988_ = lean_ctor_get(v_a_985_, 1);
v_pkg_989_ = lean_ctor_get(v_self_980_, 0);
v_name_990_ = lean_ctor_get(v_self_980_, 1);
v_config_991_ = lean_ctor_get(v_self_980_, 3);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_self_980_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v_self_980_, 2);
lean_dec(v_unused_1024_);
v___x_993_ = v_self_980_;
v_isShared_994_ = v_isSharedCheck_1023_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_config_991_);
lean_inc(v_name_990_);
lean_inc(v_pkg_989_);
lean_dec(v_self_980_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1023_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_packageMap_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_packageMap_995_ = lean_ctor_get(v_toContext_988_, 6);
v___x_996_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__2___closed__0));
lean_inc(v_pkg_989_);
lean_inc(v_packageMap_995_);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_996_, v_packageMap_995_, v_pkg_989_);
if (lean_obj_tag(v___x_997_) == 1)
{
lean_object* v_val_998_; lean_object* v_keyName_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_pkg_989_);
v_val_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref(v___x_997_);
v_keyName_999_ = lean_ctor_get(v_val_998_, 2);
lean_inc(v_keyName_999_);
v___x_1000_ = l_Lake_InputDir_keyword;
lean_inc(v_name_990_);
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v_val_998_);
lean_ctor_set(v___x_1001_, 1, v_name_990_);
lean_ctor_set(v___x_1001_, 2, v_config_991_);
v___x_1002_ = l_Lake_InputDir_defaultFacet;
v___x_1003_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_keyName_999_);
lean_ctor_set(v___x_1003_, 1, v_name_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 1);
lean_ctor_set(v___x_993_, 3, v___x_1002_);
lean_ctor_set(v___x_993_, 2, v___x_1001_);
lean_ctor_set(v___x_993_, 1, v___x_1000_);
lean_ctor_set(v___x_993_, 0, v___x_1003_);
v___x_1005_ = v___x_993_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v___x_1002_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
lean_inc(v_a_984_);
lean_inc(v_a_983_);
lean_inc(v_a_982_);
v___x_1006_ = lean_apply_7(v_a_981_, v___x_1005_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, lean_box(0));
return v___x_1006_;
}
}
else
{
lean_object* v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v___x_997_);
lean_del_object(v___x_993_);
lean_dec(v_config_991_);
lean_dec_ref(v_a_985_);
lean_dec_ref(v_a_981_);
v___x_1008_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__0));
v___x_1009_ = 1;
v___x_1010_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_989_, v___x_1009_);
v___x_1011_ = lean_string_append(v___x_1008_, v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__1));
v___x_1013_ = lean_string_append(v___x_1011_, v___x_1012_);
v___x_1014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_990_, v___x_1009_);
v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lake_KConfigDecl_get___redArg___lam__1___closed__2));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = 3;
v___x_1019_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*1, v___x_1018_);
v___x_1020_ = lean_array_get_size(v_a_986_);
v___x_1021_ = lean_array_push(v_a_986_, v___x_1019_);
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputDirDecl_fetch___boxed(lean_object* v_self_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lake_InputDirDecl_fetch(v_self_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec(v_a_1027_);
return v_res_1033_;
}
}
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFile(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
