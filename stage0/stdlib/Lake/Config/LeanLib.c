// Lean compiler output
// Module: Lake.Config.LeanLib
// Imports: public import Lake.Config.ConfigTarget public import Lake.Util.NativeLib import Init.Omega
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
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Package_id_x3f(lean_object*);
lean_object* l_Lean_mkModuleInitializationStem(lean_object*, lean_object*);
lean_object* l_Lake_nameToStaticLib(lean_object*, uint8_t);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_BuildType_leanArgs(uint8_t);
uint8_t l_Lake_instOrdBuildType_ord(uint8_t, uint8_t);
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_LeanOptions_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Package_leanLibs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_leanLibs___closed__0 = (const lean_object*)&l_Lake_Package_leanLibs___closed__0_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__1 = (const lean_object*)&l_Lake_Package_leanLibs___closed__1_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__2 = (const lean_object*)&l_Lake_Package_leanLibs___closed__2_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__3 = (const lean_object*)&l_Lake_Package_leanLibs___closed__3_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__4 = (const lean_object*)&l_Lake_Package_leanLibs___closed__4_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__5 = (const lean_object*)&l_Lake_Package_leanLibs___closed__5_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__6 = (const lean_object*)&l_Lake_Package_leanLibs___closed__6_value;
static const lean_closure_object l_Lake_Package_leanLibs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_leanLibs___closed__7 = (const lean_object*)&l_Lake_Package_leanLibs___closed__7_value;
static const lean_ctor_object l_Lake_Package_leanLibs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_leanLibs___closed__1_value),((lean_object*)&l_Lake_Package_leanLibs___closed__2_value)}};
static const lean_object* l_Lake_Package_leanLibs___closed__8 = (const lean_object*)&l_Lake_Package_leanLibs___closed__8_value;
static const lean_ctor_object l_Lake_Package_leanLibs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_leanLibs___closed__8_value),((lean_object*)&l_Lake_Package_leanLibs___closed__3_value),((lean_object*)&l_Lake_Package_leanLibs___closed__4_value),((lean_object*)&l_Lake_Package_leanLibs___closed__5_value),((lean_object*)&l_Lake_Package_leanLibs___closed__6_value)}};
static const lean_object* l_Lake_Package_leanLibs___closed__9 = (const lean_object*)&l_Lake_Package_leanLibs___closed__9_value;
static const lean_ctor_object l_Lake_Package_leanLibs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_leanLibs___closed__9_value),((lean_object*)&l_Lake_Package_leanLibs___closed__7_value)}};
static const lean_object* l_Lake_Package_leanLibs___closed__10 = (const lean_object*)&l_Lake_Package_leanLibs___closed__10_value;
static const lean_string_object l_Lake_Package_leanLibs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_Package_leanLibs___closed__11 = (const lean_object*)&l_Lake_Package_leanLibs___closed__11_value;
static const lean_ctor_object l_Lake_Package_leanLibs___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_leanLibs___closed__11_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_Package_leanLibs___closed__12 = (const lean_object*)&l_Lake_Package_leanLibs___closed__12_value;
LEAN_EXPORT lean_object* l_Lake_Package_leanLibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findLeanLib_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findLeanLib_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_config(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_config___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_srcDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_roots(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_roots___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_isLocalModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_isBuildableModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_isBuildableModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_libPrefixOnWindows(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_libPrefixOnWindows___boxed(lean_object*);
static const lean_string_object l_Lake_LeanLib_libName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_LeanLib_libName___closed__0 = (const lean_object*)&l_Lake_LeanLib_libName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLib_libName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFileName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFile(lean_object*);
static const lean_string_object l_Lake_LeanLib_staticExportLibFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lake_LeanLib_staticExportLibFile___closed__0 = (const lean_object*)&l_Lake_LeanLib_staticExportLibFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportLibFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFileName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFile(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_isPlugin(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_isPlugin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepTargets(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepTargets___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_precompileModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileModules___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_precompileImports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileImports___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_shouldPrecompile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_shouldPrecompile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_buildType(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_buildType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_backend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowImportAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowImportAll___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_requiresModuleSystem(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_requiresModuleSystem___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowNonModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowNonModules___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_dynlibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_plugins(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkLibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_linkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibs___lam__0(lean_object* v___x_1_, lean_object* v_self_2_, lean_object* v_x1_3_, lean_object* v_x2_4_){
_start:
{
lean_object* v_name_5_; lean_object* v_kind_6_; lean_object* v_config_7_; uint8_t v___x_8_; 
v_name_5_ = lean_ctor_get(v_x2_4_, 1);
v_kind_6_ = lean_ctor_get(v_x2_4_, 2);
v_config_7_ = lean_ctor_get(v_x2_4_, 3);
v___x_8_ = lean_name_eq(v_kind_6_, v___x_1_);
if (v___x_8_ == 0)
{
lean_dec_ref(v_self_2_);
return v_x1_3_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc(v_config_7_);
lean_inc(v_name_5_);
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v_self_2_);
lean_ctor_set(v___x_9_, 1, v_name_5_);
lean_ctor_set(v___x_9_, 2, v_config_7_);
v___x_10_ = lean_array_push(v_x1_3_, v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibs___lam__0___boxed(lean_object* v___x_11_, lean_object* v_self_12_, lean_object* v_x1_13_, lean_object* v_x2_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_Package_leanLibs___lam__0(v___x_11_, v_self_12_, v_x1_13_, v_x2_14_);
lean_dec_ref(v_x2_14_);
lean_dec(v___x_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibs(lean_object* v_self_40_){
_start:
{
lean_object* v_targetDecls_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_targetDecls_41_ = lean_ctor_get(v_self_40_, 15);
lean_inc_ref(v_targetDecls_41_);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = ((lean_object*)(l_Lake_Package_leanLibs___closed__0));
v___x_44_ = lean_array_get_size(v_targetDecls_41_);
v___x_45_ = ((lean_object*)(l_Lake_Package_leanLibs___closed__10));
v___x_46_ = lean_nat_dec_lt(v___x_42_, v___x_44_);
if (v___x_46_ == 0)
{
lean_dec_ref(v_targetDecls_41_);
lean_dec_ref(v_self_40_);
return v___x_43_;
}
else
{
lean_object* v___x_47_; lean_object* v___f_48_; size_t v___x_49_; size_t v___x_50_; lean_object* v___x_51_; 
v___x_47_ = ((lean_object*)(l_Lake_Package_leanLibs___closed__12));
v___f_48_ = lean_alloc_closure((void*)(l_Lake_Package_leanLibs___lam__0___boxed), 4, 2);
lean_closure_set(v___f_48_, 0, v___x_47_);
lean_closure_set(v___f_48_, 1, v_self_40_);
v___x_49_ = ((size_t)0ULL);
v___x_50_ = lean_usize_of_nat(v___x_44_);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_45_, v___f_48_, v_targetDecls_41_, v___x_49_, v___x_50_, v___x_43_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanLib_x3f(lean_object* v_name_52_, lean_object* v_self_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lake_Package_findTargetDecl_x3f(v_name_52_, v_self_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v___x_55_; 
lean_dec_ref(v_self_53_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_70_; 
v_val_56_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_70_ == 0)
{
v___x_58_ = v___x_54_;
v_isShared_59_ = v_isSharedCheck_70_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v___x_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_70_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_name_60_; lean_object* v_kind_61_; lean_object* v_config_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v_name_60_ = lean_ctor_get(v_val_56_, 1);
lean_inc(v_name_60_);
v_kind_61_ = lean_ctor_get(v_val_56_, 2);
lean_inc(v_kind_61_);
v_config_62_ = lean_ctor_get(v_val_56_, 3);
lean_inc(v_config_62_);
lean_dec(v_val_56_);
v___x_63_ = ((lean_object*)(l_Lake_Package_leanLibs___closed__12));
v___x_64_ = lean_name_eq(v_kind_61_, v___x_63_);
lean_dec(v_kind_61_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec(v_config_62_);
lean_dec(v_name_60_);
lean_del_object(v___x_58_);
lean_dec_ref(v_self_53_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_66_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_66_, 0, v_self_53_);
lean_ctor_set(v___x_66_, 1, v_name_60_);
lean_ctor_set(v___x_66_, 2, v_config_62_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_66_);
v___x_68_ = v___x_58_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanLib_x3f___boxed(lean_object* v_name_71_, lean_object* v_self_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lake_Package_findLeanLib_x3f(v_name_71_, v_self_72_);
lean_dec(v_name_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_config(lean_object* v_self_74_){
_start:
{
lean_object* v_config_75_; 
v_config_75_ = lean_ctor_get(v_self_74_, 2);
lean_inc(v_config_75_);
return v_config_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_config___boxed(lean_object* v_self_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lake_LeanLib_config(v_self_76_);
lean_dec_ref(v_self_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_srcDir(lean_object* v_self_78_){
_start:
{
lean_object* v_pkg_79_; lean_object* v_config_80_; lean_object* v_config_81_; lean_object* v_dir_82_; lean_object* v_srcDir_83_; lean_object* v_srcDir_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_pkg_79_ = lean_ctor_get(v_self_78_, 0);
lean_inc_ref(v_pkg_79_);
v_config_80_ = lean_ctor_get(v_pkg_79_, 6);
lean_inc_ref(v_config_80_);
v_config_81_ = lean_ctor_get(v_self_78_, 2);
lean_inc(v_config_81_);
lean_dec_ref(v_self_78_);
v_dir_82_ = lean_ctor_get(v_pkg_79_, 4);
lean_inc_ref(v_dir_82_);
lean_dec_ref(v_pkg_79_);
v_srcDir_83_ = lean_ctor_get(v_config_80_, 4);
lean_inc_ref(v_srcDir_83_);
lean_dec_ref(v_config_80_);
v_srcDir_84_ = lean_ctor_get(v_config_81_, 1);
lean_inc_ref(v_srcDir_84_);
lean_dec(v_config_81_);
v___x_85_ = l_System_FilePath_normalize(v_srcDir_83_);
v___x_86_ = l_Lake_joinRelative(v_dir_82_, v___x_85_);
v___x_87_ = l_System_FilePath_normalize(v_srcDir_84_);
v___x_88_ = l_Lake_joinRelative(v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootDir(lean_object* v_self_89_){
_start:
{
lean_object* v_pkg_90_; lean_object* v_config_91_; lean_object* v_config_92_; lean_object* v_dir_93_; lean_object* v_srcDir_94_; lean_object* v_srcDir_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_pkg_90_ = lean_ctor_get(v_self_89_, 0);
lean_inc_ref(v_pkg_90_);
v_config_91_ = lean_ctor_get(v_pkg_90_, 6);
lean_inc_ref(v_config_91_);
v_config_92_ = lean_ctor_get(v_self_89_, 2);
lean_inc(v_config_92_);
lean_dec_ref(v_self_89_);
v_dir_93_ = lean_ctor_get(v_pkg_90_, 4);
lean_inc_ref(v_dir_93_);
lean_dec_ref(v_pkg_90_);
v_srcDir_94_ = lean_ctor_get(v_config_91_, 4);
lean_inc_ref(v_srcDir_94_);
lean_dec_ref(v_config_91_);
v_srcDir_95_ = lean_ctor_get(v_config_92_, 1);
lean_inc_ref(v_srcDir_95_);
lean_dec(v_config_92_);
v___x_96_ = l_System_FilePath_normalize(v_srcDir_94_);
v___x_97_ = l_Lake_joinRelative(v_dir_93_, v___x_96_);
v___x_98_ = l_System_FilePath_normalize(v_srcDir_95_);
v___x_99_ = l_Lake_joinRelative(v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_roots(lean_object* v_self_100_){
_start:
{
lean_object* v_config_101_; lean_object* v_roots_102_; 
v_config_101_ = lean_ctor_get(v_self_100_, 2);
v_roots_102_ = lean_ctor_get(v_config_101_, 2);
lean_inc_ref(v_roots_102_);
return v_roots_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_roots___boxed(lean_object* v_self_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lake_LeanLib_roots(v_self_103_);
lean_dec_ref(v_self_103_);
return v_res_104_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_isLocalModule(lean_object* v_mod_105_, lean_object* v_self_106_){
_start:
{
lean_object* v_config_107_; uint8_t v___x_108_; 
v_config_107_ = lean_ctor_get(v_self_106_, 2);
v___x_108_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_105_, v_config_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isLocalModule___boxed(lean_object* v_mod_109_, lean_object* v_self_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lake_LeanLib_isLocalModule(v_mod_109_, v_self_110_);
lean_dec_ref(v_self_110_);
lean_dec(v_mod_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_isBuildableModule(lean_object* v_mod_113_, lean_object* v_self_114_){
_start:
{
lean_object* v_config_115_; uint8_t v___x_116_; 
v_config_115_ = lean_ctor_get(v_self_114_, 2);
v___x_116_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_113_, v_config_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isBuildableModule___boxed(lean_object* v_mod_117_, lean_object* v_self_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lake_LeanLib_isBuildableModule(v_mod_117_, v_self_118_);
lean_dec_ref(v_self_118_);
lean_dec(v_mod_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_libPrefixOnWindows(lean_object* v_self_121_){
_start:
{
lean_object* v_config_122_; uint8_t v_libPrefixOnWindows_123_; 
v_config_122_ = lean_ctor_get(v_self_121_, 2);
v_libPrefixOnWindows_123_ = lean_ctor_get_uint8(v_config_122_, sizeof(void*)*9);
if (v_libPrefixOnWindows_123_ == 0)
{
lean_object* v_pkg_124_; lean_object* v_config_125_; uint8_t v_libPrefixOnWindows_126_; 
v_pkg_124_ = lean_ctor_get(v_self_121_, 0);
v_config_125_ = lean_ctor_get(v_pkg_124_, 6);
v_libPrefixOnWindows_126_ = lean_ctor_get_uint8(v_config_125_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_126_;
}
else
{
return v_libPrefixOnWindows_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_libPrefixOnWindows___boxed(lean_object* v_self_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lake_LeanLib_libPrefixOnWindows(v_self_127_);
lean_dec_ref(v_self_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_libName(lean_object* v_self_131_){
_start:
{
lean_object* v___y_133_; lean_object* v_config_137_; lean_object* v_pkg_138_; lean_object* v_name_139_; lean_object* v_libName_140_; uint8_t v_libPrefixOnWindows_141_; lean_object* v___y_143_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_config_137_ = lean_ctor_get(v_self_131_, 2);
lean_inc(v_config_137_);
v_pkg_138_ = lean_ctor_get(v_self_131_, 0);
lean_inc_ref(v_pkg_138_);
v_name_139_ = lean_ctor_get(v_self_131_, 1);
lean_inc(v_name_139_);
lean_dec_ref(v_self_131_);
v_libName_140_ = lean_ctor_get(v_config_137_, 4);
lean_inc_ref(v_libName_140_);
v_libPrefixOnWindows_141_ = lean_ctor_get_uint8(v_config_137_, sizeof(void*)*9);
lean_dec(v_config_137_);
v___x_146_ = lean_string_utf8_byte_size(v_libName_140_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_nat_dec_eq(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_name_139_);
v___y_143_ = v_libName_140_;
goto v___jp_142_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_libName_140_);
lean_inc_ref(v_pkg_138_);
v___x_149_ = l_Lake_Package_id_x3f(v_pkg_138_);
v___x_150_ = l_Lean_mkModuleInitializationStem(v_name_139_, v___x_149_);
lean_dec(v___x_149_);
v___y_143_ = v___x_150_;
goto v___jp_142_;
}
v___jp_132_:
{
uint8_t v___x_134_; 
v___x_134_ = l_System_Platform_isWindows;
if (v___x_134_ == 0)
{
return v___y_133_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lake_LeanLib_libName___closed__0));
v___x_136_ = lean_string_append(v___x_135_, v___y_133_);
lean_dec_ref(v___y_133_);
return v___x_136_;
}
}
v___jp_142_:
{
if (v_libPrefixOnWindows_141_ == 0)
{
lean_object* v_config_144_; uint8_t v_libPrefixOnWindows_145_; 
v_config_144_ = lean_ctor_get(v_pkg_138_, 6);
lean_inc_ref(v_config_144_);
lean_dec_ref(v_pkg_138_);
v_libPrefixOnWindows_145_ = lean_ctor_get_uint8(v_config_144_, sizeof(void*)*28 + 4);
lean_dec_ref(v_config_144_);
if (v_libPrefixOnWindows_145_ == 0)
{
return v___y_143_;
}
else
{
v___y_133_ = v___y_143_;
goto v___jp_132_;
}
}
else
{
lean_dec_ref(v_pkg_138_);
v___y_133_ = v___y_143_;
goto v___jp_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFileName(lean_object* v_self_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = l_Lake_LeanLib_libName(v_self_151_);
v___x_153_ = 0;
v___x_154_ = l_Lake_nameToStaticLib(v___x_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFile(lean_object* v_self_155_){
_start:
{
lean_object* v_pkg_156_; lean_object* v_config_157_; lean_object* v_dir_158_; lean_object* v_buildDir_159_; lean_object* v_nativeLibDir_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_pkg_156_ = lean_ctor_get(v_self_155_, 0);
v_config_157_ = lean_ctor_get(v_pkg_156_, 6);
v_dir_158_ = lean_ctor_get(v_pkg_156_, 4);
v_buildDir_159_ = lean_ctor_get(v_config_157_, 5);
v_nativeLibDir_160_ = lean_ctor_get(v_config_157_, 7);
lean_inc_ref(v_buildDir_159_);
v___x_161_ = l_System_FilePath_normalize(v_buildDir_159_);
lean_inc_ref(v_dir_158_);
v___x_162_ = l_Lake_joinRelative(v_dir_158_, v___x_161_);
lean_inc_ref(v_nativeLibDir_160_);
v___x_163_ = l_System_FilePath_normalize(v_nativeLibDir_160_);
v___x_164_ = l_Lake_joinRelative(v___x_162_, v___x_163_);
v___x_165_ = l_Lake_LeanLib_libName(v_self_155_);
v___x_166_ = 0;
v___x_167_ = l_Lake_nameToStaticLib(v___x_165_, v___x_166_);
v___x_168_ = l_Lake_joinRelative(v___x_164_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportLibFile(lean_object* v_self_170_){
_start:
{
lean_object* v_pkg_171_; lean_object* v_config_172_; lean_object* v_dir_173_; lean_object* v_buildDir_174_; lean_object* v_nativeLibDir_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_pkg_171_ = lean_ctor_get(v_self_170_, 0);
v_config_172_ = lean_ctor_get(v_pkg_171_, 6);
v_dir_173_ = lean_ctor_get(v_pkg_171_, 4);
v_buildDir_174_ = lean_ctor_get(v_config_172_, 5);
v_nativeLibDir_175_ = lean_ctor_get(v_config_172_, 7);
lean_inc_ref(v_buildDir_174_);
v___x_176_ = l_System_FilePath_normalize(v_buildDir_174_);
lean_inc_ref(v_dir_173_);
v___x_177_ = l_Lake_joinRelative(v_dir_173_, v___x_176_);
lean_inc_ref(v_nativeLibDir_175_);
v___x_178_ = l_System_FilePath_normalize(v_nativeLibDir_175_);
v___x_179_ = l_Lake_joinRelative(v___x_177_, v___x_178_);
v___x_180_ = l_Lake_LeanLib_libName(v_self_170_);
v___x_181_ = 0;
v___x_182_ = l_Lake_nameToStaticLib(v___x_180_, v___x_181_);
v___x_183_ = ((lean_object*)(l_Lake_LeanLib_staticExportLibFile___closed__0));
v___x_184_ = l_System_FilePath_addExtension(v___x_182_, v___x_183_);
v___x_185_ = l_Lake_joinRelative(v___x_179_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFileName(lean_object* v_self_186_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; 
v___x_187_ = l_Lake_LeanLib_libName(v_self_186_);
v___x_188_ = 0;
v___x_189_ = l_Lake_nameToSharedLib(v___x_187_, v___x_188_);
lean_dec_ref(v___x_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFile(lean_object* v_self_190_){
_start:
{
lean_object* v_pkg_191_; lean_object* v_config_192_; lean_object* v_dir_193_; lean_object* v_buildDir_194_; lean_object* v_nativeLibDir_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_pkg_191_ = lean_ctor_get(v_self_190_, 0);
v_config_192_ = lean_ctor_get(v_pkg_191_, 6);
v_dir_193_ = lean_ctor_get(v_pkg_191_, 4);
v_buildDir_194_ = lean_ctor_get(v_config_192_, 5);
v_nativeLibDir_195_ = lean_ctor_get(v_config_192_, 7);
lean_inc_ref(v_buildDir_194_);
v___x_196_ = l_System_FilePath_normalize(v_buildDir_194_);
lean_inc_ref(v_dir_193_);
v___x_197_ = l_Lake_joinRelative(v_dir_193_, v___x_196_);
lean_inc_ref(v_nativeLibDir_195_);
v___x_198_ = l_System_FilePath_normalize(v_nativeLibDir_195_);
v___x_199_ = l_Lake_joinRelative(v___x_197_, v___x_198_);
v___x_200_ = l_Lake_LeanLib_libName(v_self_190_);
v___x_201_ = 0;
v___x_202_ = l_Lake_nameToSharedLib(v___x_200_, v___x_201_);
lean_dec_ref(v___x_200_);
v___x_203_ = l_Lake_joinRelative(v___x_199_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_isPlugin(lean_object* v_self_204_){
_start:
{
lean_object* v_config_205_; lean_object* v_pkg_206_; lean_object* v_roots_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_config_205_ = lean_ctor_get(v_self_204_, 2);
v_pkg_206_ = lean_ctor_get(v_self_204_, 0);
lean_inc_ref(v_pkg_206_);
v_roots_207_ = lean_ctor_get(v_config_205_, 2);
lean_inc_ref(v_roots_207_);
v___x_208_ = lean_array_get_size(v_roots_207_);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_dec_eq(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_dec_ref(v_roots_207_);
lean_dec_ref(v_pkg_206_);
lean_dec_ref(v_self_204_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_211_ = l_Lake_LeanLib_libName(v_self_204_);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_array_fget(v_roots_207_, v___x_212_);
lean_dec_ref(v_roots_207_);
v___x_214_ = l_Lake_Package_id_x3f(v_pkg_206_);
v___x_215_ = l_Lean_mkModuleInitializationStem(v___x_213_, v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = lean_string_dec_eq(v___x_211_, v___x_215_);
lean_dec_ref(v___x_215_);
lean_dec_ref(v___x_211_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isPlugin___boxed(lean_object* v_self_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lake_LeanLib_isPlugin(v_self_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepTargets(lean_object* v_self_220_){
_start:
{
lean_object* v_config_221_; lean_object* v_extraDepTargets_222_; 
v_config_221_ = lean_ctor_get(v_self_220_, 2);
v_extraDepTargets_222_ = lean_ctor_get(v_config_221_, 6);
lean_inc_ref(v_extraDepTargets_222_);
return v_extraDepTargets_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepTargets___boxed(lean_object* v_self_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lake_LeanLib_extraDepTargets(v_self_223_);
lean_dec_ref(v_self_223_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_precompileModules(lean_object* v_self_225_){
_start:
{
lean_object* v_pkg_226_; lean_object* v_config_227_; uint8_t v_precompileModules_228_; 
v_pkg_226_ = lean_ctor_get(v_self_225_, 0);
v_config_227_ = lean_ctor_get(v_pkg_226_, 6);
v_precompileModules_228_ = lean_ctor_get_uint8(v_config_227_, sizeof(void*)*28 + 1);
if (v_precompileModules_228_ == 0)
{
lean_object* v_config_229_; uint8_t v_precompileModules_230_; 
v_config_229_ = lean_ctor_get(v_self_225_, 2);
v_precompileModules_230_ = lean_ctor_get_uint8(v_config_229_, sizeof(void*)*9 + 2);
return v_precompileModules_230_;
}
else
{
return v_precompileModules_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileModules___boxed(lean_object* v_self_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lake_LeanLib_precompileModules(v_self_231_);
lean_dec_ref(v_self_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_precompileImports(lean_object* v_self_234_){
_start:
{
lean_object* v_pkg_235_; lean_object* v_config_236_; uint8_t v_precompileModules_237_; 
v_pkg_235_ = lean_ctor_get(v_self_234_, 0);
v_config_236_ = lean_ctor_get(v_pkg_235_, 6);
v_precompileModules_237_ = lean_ctor_get_uint8(v_config_236_, sizeof(void*)*28 + 1);
if (v_precompileModules_237_ == 0)
{
lean_object* v_config_238_; uint8_t v_precompileModules_239_; 
v_config_238_ = lean_ctor_get(v_self_234_, 2);
v_precompileModules_239_ = lean_ctor_get_uint8(v_config_238_, sizeof(void*)*9 + 2);
if (v_precompileModules_239_ == 0)
{
lean_object* v_toLeanConfig_240_; uint8_t v_precompileImports_241_; 
v_toLeanConfig_240_ = lean_ctor_get(v_config_236_, 1);
v_precompileImports_241_ = lean_ctor_get_uint8(v_toLeanConfig_240_, sizeof(void*)*13 + 2);
if (v_precompileImports_241_ == 0)
{
lean_object* v_toLeanConfig_242_; uint8_t v_precompileImports_243_; 
v_toLeanConfig_242_ = lean_ctor_get(v_config_238_, 0);
v_precompileImports_243_ = lean_ctor_get_uint8(v_toLeanConfig_242_, sizeof(void*)*13 + 2);
return v_precompileImports_243_;
}
else
{
return v_precompileImports_241_;
}
}
else
{
return v_precompileModules_239_;
}
}
else
{
return v_precompileModules_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileImports___boxed(lean_object* v_self_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Lake_LeanLib_precompileImports(v_self_244_);
lean_dec_ref(v_self_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_shouldPrecompile(lean_object* v_self_247_){
_start:
{
lean_object* v_pkg_248_; lean_object* v_config_249_; uint8_t v_precompileModules_250_; 
v_pkg_248_ = lean_ctor_get(v_self_247_, 0);
v_config_249_ = lean_ctor_get(v_pkg_248_, 6);
v_precompileModules_250_ = lean_ctor_get_uint8(v_config_249_, sizeof(void*)*28 + 1);
if (v_precompileModules_250_ == 0)
{
lean_object* v_config_251_; uint8_t v_precompileModules_252_; 
v_config_251_ = lean_ctor_get(v_self_247_, 2);
v_precompileModules_252_ = lean_ctor_get_uint8(v_config_251_, sizeof(void*)*9 + 2);
if (v_precompileModules_252_ == 0)
{
uint8_t v_precompileLibrary_253_; 
v_precompileLibrary_253_ = lean_ctor_get_uint8(v_config_251_, sizeof(void*)*9 + 1);
return v_precompileLibrary_253_;
}
else
{
return v_precompileModules_252_;
}
}
else
{
return v_precompileModules_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shouldPrecompile___boxed(lean_object* v_self_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Lake_LeanLib_shouldPrecompile(v_self_254_);
lean_dec_ref(v_self_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent(lean_object* v_self_257_){
_start:
{
lean_object* v_config_258_; lean_object* v_toLeanConfig_259_; lean_object* v_platformIndependent_260_; 
v_config_258_ = lean_ctor_get(v_self_257_, 2);
v_toLeanConfig_259_ = lean_ctor_get(v_config_258_, 0);
v_platformIndependent_260_ = lean_ctor_get(v_toLeanConfig_259_, 10);
if (lean_obj_tag(v_platformIndependent_260_) == 0)
{
lean_object* v_pkg_261_; lean_object* v_config_262_; lean_object* v_toLeanConfig_263_; lean_object* v_platformIndependent_264_; 
v_pkg_261_ = lean_ctor_get(v_self_257_, 0);
v_config_262_ = lean_ctor_get(v_pkg_261_, 6);
v_toLeanConfig_263_ = lean_ctor_get(v_config_262_, 1);
v_platformIndependent_264_ = lean_ctor_get(v_toLeanConfig_263_, 10);
lean_inc(v_platformIndependent_264_);
return v_platformIndependent_264_;
}
else
{
lean_inc_ref(v_platformIndependent_260_);
return v_platformIndependent_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent___boxed(lean_object* v_self_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lake_LeanLib_platformIndependent(v_self_265_);
lean_dec_ref(v_self_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets(lean_object* v_self_267_){
_start:
{
lean_object* v_config_268_; lean_object* v_defaultFacets_269_; 
v_config_268_ = lean_ctor_get(v_self_267_, 2);
v_defaultFacets_269_ = lean_ctor_get(v_config_268_, 7);
lean_inc_ref(v_defaultFacets_269_);
return v_defaultFacets_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets___boxed(lean_object* v_self_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lake_LeanLib_defaultFacets(v_self_270_);
lean_dec_ref(v_self_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets(lean_object* v_self_272_, uint8_t v_shouldExport_273_){
_start:
{
lean_object* v_config_274_; lean_object* v_nativeFacets_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_config_274_ = lean_ctor_get(v_self_272_, 2);
lean_inc(v_config_274_);
lean_dec_ref(v_self_272_);
v_nativeFacets_275_ = lean_ctor_get(v_config_274_, 8);
lean_inc_ref(v_nativeFacets_275_);
lean_dec(v_config_274_);
v___x_276_ = lean_box(v_shouldExport_273_);
v___x_277_ = lean_apply_1(v_nativeFacets_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets___boxed(lean_object* v_self_278_, lean_object* v_shouldExport_279_){
_start:
{
uint8_t v_shouldExport_boxed_280_; lean_object* v_res_281_; 
v_shouldExport_boxed_280_ = lean_unbox(v_shouldExport_279_);
v_res_281_ = l_Lake_LeanLib_nativeFacets(v_self_278_, v_shouldExport_boxed_280_);
return v_res_281_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_buildType(lean_object* v_self_282_){
_start:
{
lean_object* v_pkg_283_; lean_object* v_config_284_; lean_object* v_toLeanConfig_285_; lean_object* v_config_286_; lean_object* v_toLeanConfig_287_; uint8_t v_buildType_288_; uint8_t v_buildType_289_; uint8_t v___x_290_; 
v_pkg_283_ = lean_ctor_get(v_self_282_, 0);
v_config_284_ = lean_ctor_get(v_pkg_283_, 6);
v_toLeanConfig_285_ = lean_ctor_get(v_config_284_, 1);
v_config_286_ = lean_ctor_get(v_self_282_, 2);
v_toLeanConfig_287_ = lean_ctor_get(v_config_286_, 0);
v_buildType_288_ = lean_ctor_get_uint8(v_toLeanConfig_285_, sizeof(void*)*13);
v_buildType_289_ = lean_ctor_get_uint8(v_toLeanConfig_287_, sizeof(void*)*13);
v___x_290_ = l_Lake_instOrdBuildType_ord(v_buildType_288_, v_buildType_289_);
if (v___x_290_ == 2)
{
return v_buildType_289_;
}
else
{
return v_buildType_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_buildType___boxed(lean_object* v_self_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Lake_LeanLib_buildType(v_self_291_);
lean_dec_ref(v_self_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions(lean_object* v_self_294_){
_start:
{
lean_object* v_pkg_295_; lean_object* v_config_296_; lean_object* v_toLeanConfig_297_; lean_object* v_config_298_; lean_object* v_toLeanConfig_299_; uint8_t v_buildType_300_; lean_object* v_leanOptions_301_; lean_object* v_moreServerOptions_302_; uint8_t v_buildType_303_; lean_object* v_leanOptions_304_; lean_object* v_moreServerOptions_305_; lean_object* v___x_306_; uint8_t v___y_308_; uint8_t v___x_316_; 
v_pkg_295_ = lean_ctor_get(v_self_294_, 0);
v_config_296_ = lean_ctor_get(v_pkg_295_, 6);
v_toLeanConfig_297_ = lean_ctor_get(v_config_296_, 1);
v_config_298_ = lean_ctor_get(v_self_294_, 2);
v_toLeanConfig_299_ = lean_ctor_get(v_config_298_, 0);
v_buildType_300_ = lean_ctor_get_uint8(v_toLeanConfig_297_, sizeof(void*)*13);
v_leanOptions_301_ = lean_ctor_get(v_toLeanConfig_297_, 0);
v_moreServerOptions_302_ = lean_ctor_get(v_toLeanConfig_297_, 4);
v_buildType_303_ = lean_ctor_get_uint8(v_toLeanConfig_299_, sizeof(void*)*13);
v_leanOptions_304_ = lean_ctor_get(v_toLeanConfig_299_, 0);
v_moreServerOptions_305_ = lean_ctor_get(v_toLeanConfig_299_, 4);
v___x_306_ = lean_box(1);
v___x_316_ = l_Lake_instOrdBuildType_ord(v_buildType_300_, v_buildType_303_);
if (v___x_316_ == 2)
{
v___y_308_ = v_buildType_303_;
goto v___jp_307_;
}
else
{
v___y_308_ = v_buildType_300_;
goto v___jp_307_;
}
v___jp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_309_ = l_Lake_BuildType_leanOptions(v___y_308_);
v___x_310_ = l_Lean_LeanOptions_append(v___x_306_, v___x_309_);
v___x_311_ = l_Lean_LeanOptions_ofArray(v_leanOptions_301_);
v___x_312_ = l_Lean_LeanOptions_appendArray(v___x_311_, v_moreServerOptions_302_);
v___x_313_ = l_Lean_LeanOptions_append(v___x_310_, v___x_312_);
v___x_314_ = l_Lean_LeanOptions_appendArray(v___x_313_, v_leanOptions_304_);
v___x_315_ = l_Lean_LeanOptions_appendArray(v___x_314_, v_moreServerOptions_305_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions___boxed(lean_object* v_self_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lake_LeanLib_serverOptions(v_self_317_);
lean_dec_ref(v_self_317_);
return v_res_318_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_backend(lean_object* v_self_319_){
_start:
{
lean_object* v_config_320_; lean_object* v_toLeanConfig_321_; lean_object* v_pkg_322_; lean_object* v_config_323_; lean_object* v_toLeanConfig_324_; uint8_t v_backend_325_; uint8_t v_backend_326_; uint8_t v___x_327_; 
v_config_320_ = lean_ctor_get(v_self_319_, 2);
v_toLeanConfig_321_ = lean_ctor_get(v_config_320_, 0);
v_pkg_322_ = lean_ctor_get(v_self_319_, 0);
v_config_323_ = lean_ctor_get(v_pkg_322_, 6);
v_toLeanConfig_324_ = lean_ctor_get(v_config_323_, 1);
v_backend_325_ = lean_ctor_get_uint8(v_toLeanConfig_321_, sizeof(void*)*13 + 1);
v_backend_326_ = lean_ctor_get_uint8(v_toLeanConfig_324_, sizeof(void*)*13 + 1);
v___x_327_ = l_Lake_Backend_orPreferLeft(v_backend_325_, v_backend_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_backend___boxed(lean_object* v_self_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Lake_LeanLib_backend(v_self_328_);
lean_dec_ref(v_self_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowImportAll(lean_object* v_self_331_){
_start:
{
lean_object* v_config_332_; uint8_t v_allowImportAll_333_; 
v_config_332_ = lean_ctor_get(v_self_331_, 2);
v_allowImportAll_333_ = lean_ctor_get_uint8(v_config_332_, sizeof(void*)*9 + 3);
if (v_allowImportAll_333_ == 0)
{
lean_object* v_pkg_334_; lean_object* v_config_335_; uint8_t v_allowImportAll_336_; 
v_pkg_334_ = lean_ctor_get(v_self_331_, 0);
v_config_335_ = lean_ctor_get(v_pkg_334_, 6);
v_allowImportAll_336_ = lean_ctor_get_uint8(v_config_335_, sizeof(void*)*28 + 5);
return v_allowImportAll_336_;
}
else
{
return v_allowImportAll_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowImportAll___boxed(lean_object* v_self_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Lake_LeanLib_allowImportAll(v_self_337_);
lean_dec_ref(v_self_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_requiresModuleSystem(lean_object* v_self_340_){
_start:
{
lean_object* v_config_341_; lean_object* v_toLeanConfig_342_; uint8_t v_requiresModuleSystem_343_; 
v_config_341_ = lean_ctor_get(v_self_340_, 2);
v_toLeanConfig_342_ = lean_ctor_get(v_config_341_, 0);
v_requiresModuleSystem_343_ = lean_ctor_get_uint8(v_toLeanConfig_342_, sizeof(void*)*13 + 3);
if (v_requiresModuleSystem_343_ == 0)
{
lean_object* v_pkg_344_; lean_object* v_config_345_; lean_object* v_toLeanConfig_346_; uint8_t v_requiresModuleSystem_347_; 
v_pkg_344_ = lean_ctor_get(v_self_340_, 0);
v_config_345_ = lean_ctor_get(v_pkg_344_, 6);
v_toLeanConfig_346_ = lean_ctor_get(v_config_345_, 1);
v_requiresModuleSystem_347_ = lean_ctor_get_uint8(v_toLeanConfig_346_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_347_;
}
else
{
return v_requiresModuleSystem_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_requiresModuleSystem___boxed(lean_object* v_self_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lake_LeanLib_requiresModuleSystem(v_self_348_);
lean_dec_ref(v_self_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowNonModules(lean_object* v_self_351_){
_start:
{
lean_object* v_config_352_; lean_object* v_toLeanConfig_353_; uint8_t v_allowNonModules_354_; 
v_config_352_ = lean_ctor_get(v_self_351_, 2);
v_toLeanConfig_353_ = lean_ctor_get(v_config_352_, 0);
v_allowNonModules_354_ = lean_ctor_get_uint8(v_toLeanConfig_353_, sizeof(void*)*13 + 4);
if (v_allowNonModules_354_ == 0)
{
lean_object* v_pkg_355_; lean_object* v_config_356_; lean_object* v_toLeanConfig_357_; uint8_t v_allowNonModules_358_; 
v_pkg_355_ = lean_ctor_get(v_self_351_, 0);
v_config_356_ = lean_ctor_get(v_pkg_355_, 6);
v_toLeanConfig_357_ = lean_ctor_get(v_config_356_, 1);
v_allowNonModules_358_ = lean_ctor_get_uint8(v_toLeanConfig_357_, sizeof(void*)*13 + 4);
return v_allowNonModules_358_;
}
else
{
return v_allowNonModules_354_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowNonModules___boxed(lean_object* v_self_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lake_LeanLib_allowNonModules(v_self_359_);
lean_dec_ref(v_self_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_dynlibs(lean_object* v_self_362_){
_start:
{
lean_object* v_pkg_363_; lean_object* v_config_364_; lean_object* v_toLeanConfig_365_; lean_object* v_config_366_; lean_object* v_toLeanConfig_367_; lean_object* v_dynlibs_368_; lean_object* v_dynlibs_369_; lean_object* v___x_370_; 
v_pkg_363_ = lean_ctor_get(v_self_362_, 0);
v_config_364_ = lean_ctor_get(v_pkg_363_, 6);
v_toLeanConfig_365_ = lean_ctor_get(v_config_364_, 1);
lean_inc_ref(v_toLeanConfig_365_);
v_config_366_ = lean_ctor_get(v_self_362_, 2);
lean_inc(v_config_366_);
lean_dec_ref(v_self_362_);
v_toLeanConfig_367_ = lean_ctor_get(v_config_366_, 0);
lean_inc_ref(v_toLeanConfig_367_);
lean_dec(v_config_366_);
v_dynlibs_368_ = lean_ctor_get(v_toLeanConfig_365_, 11);
lean_inc_ref(v_dynlibs_368_);
lean_dec_ref(v_toLeanConfig_365_);
v_dynlibs_369_ = lean_ctor_get(v_toLeanConfig_367_, 11);
lean_inc_ref(v_dynlibs_369_);
lean_dec_ref(v_toLeanConfig_367_);
v___x_370_ = l_Array_append___redArg(v_dynlibs_368_, v_dynlibs_369_);
lean_dec_ref(v_dynlibs_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_plugins(lean_object* v_self_371_){
_start:
{
lean_object* v_pkg_372_; lean_object* v_config_373_; lean_object* v_toLeanConfig_374_; lean_object* v_config_375_; lean_object* v_toLeanConfig_376_; lean_object* v_plugins_377_; lean_object* v_plugins_378_; lean_object* v___x_379_; 
v_pkg_372_ = lean_ctor_get(v_self_371_, 0);
v_config_373_ = lean_ctor_get(v_pkg_372_, 6);
v_toLeanConfig_374_ = lean_ctor_get(v_config_373_, 1);
lean_inc_ref(v_toLeanConfig_374_);
v_config_375_ = lean_ctor_get(v_self_371_, 2);
lean_inc(v_config_375_);
lean_dec_ref(v_self_371_);
v_toLeanConfig_376_ = lean_ctor_get(v_config_375_, 0);
lean_inc_ref(v_toLeanConfig_376_);
lean_dec(v_config_375_);
v_plugins_377_ = lean_ctor_get(v_toLeanConfig_374_, 12);
lean_inc_ref(v_plugins_377_);
lean_dec_ref(v_toLeanConfig_374_);
v_plugins_378_ = lean_ctor_get(v_toLeanConfig_376_, 12);
lean_inc_ref(v_plugins_378_);
lean_dec_ref(v_toLeanConfig_376_);
v___x_379_ = l_Array_append___redArg(v_plugins_377_, v_plugins_378_);
lean_dec_ref(v_plugins_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions(lean_object* v_self_380_){
_start:
{
lean_object* v_pkg_381_; lean_object* v_config_382_; lean_object* v_toLeanConfig_383_; lean_object* v_config_384_; lean_object* v_toLeanConfig_385_; uint8_t v_buildType_386_; lean_object* v_leanOptions_387_; uint8_t v_buildType_388_; lean_object* v_leanOptions_389_; uint8_t v___y_391_; uint8_t v___x_396_; 
v_pkg_381_ = lean_ctor_get(v_self_380_, 0);
v_config_382_ = lean_ctor_get(v_pkg_381_, 6);
v_toLeanConfig_383_ = lean_ctor_get(v_config_382_, 1);
v_config_384_ = lean_ctor_get(v_self_380_, 2);
v_toLeanConfig_385_ = lean_ctor_get(v_config_384_, 0);
v_buildType_386_ = lean_ctor_get_uint8(v_toLeanConfig_383_, sizeof(void*)*13);
v_leanOptions_387_ = lean_ctor_get(v_toLeanConfig_383_, 0);
v_buildType_388_ = lean_ctor_get_uint8(v_toLeanConfig_385_, sizeof(void*)*13);
v_leanOptions_389_ = lean_ctor_get(v_toLeanConfig_385_, 0);
v___x_396_ = l_Lake_instOrdBuildType_ord(v_buildType_386_, v_buildType_388_);
if (v___x_396_ == 2)
{
v___y_391_ = v_buildType_388_;
goto v___jp_390_;
}
else
{
v___y_391_ = v_buildType_386_;
goto v___jp_390_;
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = l_Lake_BuildType_leanOptions(v___y_391_);
v___x_393_ = l_Lean_LeanOptions_ofArray(v_leanOptions_387_);
v___x_394_ = l_Lean_LeanOptions_append(v___x_392_, v___x_393_);
v___x_395_ = l_Lean_LeanOptions_appendArray(v___x_394_, v_leanOptions_389_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions___boxed(lean_object* v_self_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lake_LeanLib_leanOptions(v_self_397_);
lean_dec_ref(v_self_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs(lean_object* v_self_399_){
_start:
{
lean_object* v_pkg_400_; lean_object* v_config_401_; lean_object* v_toLeanConfig_402_; lean_object* v_config_403_; lean_object* v_toLeanConfig_404_; uint8_t v_buildType_405_; lean_object* v_moreLeanArgs_406_; uint8_t v_buildType_407_; lean_object* v_moreLeanArgs_408_; uint8_t v___y_410_; uint8_t v___x_414_; 
v_pkg_400_ = lean_ctor_get(v_self_399_, 0);
v_config_401_ = lean_ctor_get(v_pkg_400_, 6);
v_toLeanConfig_402_ = lean_ctor_get(v_config_401_, 1);
v_config_403_ = lean_ctor_get(v_self_399_, 2);
v_toLeanConfig_404_ = lean_ctor_get(v_config_403_, 0);
v_buildType_405_ = lean_ctor_get_uint8(v_toLeanConfig_402_, sizeof(void*)*13);
v_moreLeanArgs_406_ = lean_ctor_get(v_toLeanConfig_402_, 1);
v_buildType_407_ = lean_ctor_get_uint8(v_toLeanConfig_404_, sizeof(void*)*13);
v_moreLeanArgs_408_ = lean_ctor_get(v_toLeanConfig_404_, 1);
v___x_414_ = l_Lake_instOrdBuildType_ord(v_buildType_405_, v_buildType_407_);
if (v___x_414_ == 2)
{
v___y_410_ = v_buildType_407_;
goto v___jp_409_;
}
else
{
v___y_410_ = v_buildType_405_;
goto v___jp_409_;
}
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = l_Lake_BuildType_leanArgs(v___y_410_);
v___x_412_ = l_Array_append___redArg(v___x_411_, v_moreLeanArgs_406_);
v___x_413_ = l_Array_append___redArg(v___x_412_, v_moreLeanArgs_408_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs___boxed(lean_object* v_self_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_LeanLib_leanArgs(v_self_415_);
lean_dec_ref(v_self_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeanArgs(lean_object* v_self_417_){
_start:
{
lean_object* v_pkg_418_; lean_object* v_config_419_; lean_object* v_toLeanConfig_420_; lean_object* v_config_421_; lean_object* v_toLeanConfig_422_; lean_object* v_weakLeanArgs_423_; lean_object* v_weakLeanArgs_424_; lean_object* v___x_425_; 
v_pkg_418_ = lean_ctor_get(v_self_417_, 0);
v_config_419_ = lean_ctor_get(v_pkg_418_, 6);
v_toLeanConfig_420_ = lean_ctor_get(v_config_419_, 1);
lean_inc_ref(v_toLeanConfig_420_);
v_config_421_ = lean_ctor_get(v_self_417_, 2);
lean_inc(v_config_421_);
lean_dec_ref(v_self_417_);
v_toLeanConfig_422_ = lean_ctor_get(v_config_421_, 0);
lean_inc_ref(v_toLeanConfig_422_);
lean_dec(v_config_421_);
v_weakLeanArgs_423_ = lean_ctor_get(v_toLeanConfig_420_, 2);
lean_inc_ref(v_weakLeanArgs_423_);
lean_dec_ref(v_toLeanConfig_420_);
v_weakLeanArgs_424_ = lean_ctor_get(v_toLeanConfig_422_, 2);
lean_inc_ref(v_weakLeanArgs_424_);
lean_dec_ref(v_toLeanConfig_422_);
v___x_425_ = l_Array_append___redArg(v_weakLeanArgs_423_, v_weakLeanArgs_424_);
lean_dec_ref(v_weakLeanArgs_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs(lean_object* v_self_426_){
_start:
{
lean_object* v_pkg_427_; lean_object* v_config_428_; lean_object* v_toLeanConfig_429_; lean_object* v_config_430_; lean_object* v_toLeanConfig_431_; uint8_t v_buildType_432_; lean_object* v_moreLeancArgs_433_; uint8_t v_buildType_434_; lean_object* v_moreLeancArgs_435_; uint8_t v___y_437_; uint8_t v___x_441_; 
v_pkg_427_ = lean_ctor_get(v_self_426_, 0);
v_config_428_ = lean_ctor_get(v_pkg_427_, 6);
v_toLeanConfig_429_ = lean_ctor_get(v_config_428_, 1);
v_config_430_ = lean_ctor_get(v_self_426_, 2);
v_toLeanConfig_431_ = lean_ctor_get(v_config_430_, 0);
v_buildType_432_ = lean_ctor_get_uint8(v_toLeanConfig_429_, sizeof(void*)*13);
v_moreLeancArgs_433_ = lean_ctor_get(v_toLeanConfig_429_, 3);
v_buildType_434_ = lean_ctor_get_uint8(v_toLeanConfig_431_, sizeof(void*)*13);
v_moreLeancArgs_435_ = lean_ctor_get(v_toLeanConfig_431_, 3);
v___x_441_ = l_Lake_instOrdBuildType_ord(v_buildType_432_, v_buildType_434_);
if (v___x_441_ == 2)
{
v___y_437_ = v_buildType_434_;
goto v___jp_436_;
}
else
{
v___y_437_ = v_buildType_432_;
goto v___jp_436_;
}
v___jp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = l_Lake_BuildType_leancArgs(v___y_437_);
v___x_439_ = l_Array_append___redArg(v___x_438_, v_moreLeancArgs_433_);
v___x_440_ = l_Array_append___redArg(v___x_439_, v_moreLeancArgs_435_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs___boxed(lean_object* v_self_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lake_LeanLib_leancArgs(v_self_442_);
lean_dec_ref(v_self_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeancArgs(lean_object* v_self_444_){
_start:
{
lean_object* v_pkg_445_; lean_object* v_config_446_; lean_object* v_toLeanConfig_447_; lean_object* v_config_448_; lean_object* v_toLeanConfig_449_; lean_object* v_weakLeancArgs_450_; lean_object* v_weakLeancArgs_451_; lean_object* v___x_452_; 
v_pkg_445_ = lean_ctor_get(v_self_444_, 0);
v_config_446_ = lean_ctor_get(v_pkg_445_, 6);
v_toLeanConfig_447_ = lean_ctor_get(v_config_446_, 1);
lean_inc_ref(v_toLeanConfig_447_);
v_config_448_ = lean_ctor_get(v_self_444_, 2);
lean_inc(v_config_448_);
lean_dec_ref(v_self_444_);
v_toLeanConfig_449_ = lean_ctor_get(v_config_448_, 0);
lean_inc_ref(v_toLeanConfig_449_);
lean_dec(v_config_448_);
v_weakLeancArgs_450_ = lean_ctor_get(v_toLeanConfig_447_, 5);
lean_inc_ref(v_weakLeancArgs_450_);
lean_dec_ref(v_toLeanConfig_447_);
v_weakLeancArgs_451_ = lean_ctor_get(v_toLeanConfig_449_, 5);
lean_inc_ref(v_weakLeancArgs_451_);
lean_dec_ref(v_toLeanConfig_449_);
v___x_452_ = l_Array_append___redArg(v_weakLeancArgs_450_, v_weakLeancArgs_451_);
lean_dec_ref(v_weakLeancArgs_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkObjs(lean_object* v_self_453_){
_start:
{
lean_object* v_pkg_454_; lean_object* v_config_455_; lean_object* v_toLeanConfig_456_; lean_object* v_config_457_; lean_object* v_toLeanConfig_458_; lean_object* v_moreLinkObjs_459_; lean_object* v_moreLinkObjs_460_; lean_object* v___x_461_; 
v_pkg_454_ = lean_ctor_get(v_self_453_, 0);
v_config_455_ = lean_ctor_get(v_pkg_454_, 6);
v_toLeanConfig_456_ = lean_ctor_get(v_config_455_, 1);
lean_inc_ref(v_toLeanConfig_456_);
v_config_457_ = lean_ctor_get(v_self_453_, 2);
lean_inc(v_config_457_);
lean_dec_ref(v_self_453_);
v_toLeanConfig_458_ = lean_ctor_get(v_config_457_, 0);
lean_inc_ref(v_toLeanConfig_458_);
lean_dec(v_config_457_);
v_moreLinkObjs_459_ = lean_ctor_get(v_toLeanConfig_456_, 6);
lean_inc_ref(v_moreLinkObjs_459_);
lean_dec_ref(v_toLeanConfig_456_);
v_moreLinkObjs_460_ = lean_ctor_get(v_toLeanConfig_458_, 6);
lean_inc_ref(v_moreLinkObjs_460_);
lean_dec_ref(v_toLeanConfig_458_);
v___x_461_ = l_Array_append___redArg(v_moreLinkObjs_459_, v_moreLinkObjs_460_);
lean_dec_ref(v_moreLinkObjs_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkLibs(lean_object* v_self_462_){
_start:
{
lean_object* v_pkg_463_; lean_object* v_config_464_; lean_object* v_toLeanConfig_465_; lean_object* v_config_466_; lean_object* v_toLeanConfig_467_; lean_object* v_moreLinkLibs_468_; lean_object* v_moreLinkLibs_469_; lean_object* v___x_470_; 
v_pkg_463_ = lean_ctor_get(v_self_462_, 0);
v_config_464_ = lean_ctor_get(v_pkg_463_, 6);
v_toLeanConfig_465_ = lean_ctor_get(v_config_464_, 1);
lean_inc_ref(v_toLeanConfig_465_);
v_config_466_ = lean_ctor_get(v_self_462_, 2);
lean_inc(v_config_466_);
lean_dec_ref(v_self_462_);
v_toLeanConfig_467_ = lean_ctor_get(v_config_466_, 0);
lean_inc_ref(v_toLeanConfig_467_);
lean_dec(v_config_466_);
v_moreLinkLibs_468_ = lean_ctor_get(v_toLeanConfig_465_, 7);
lean_inc_ref(v_moreLinkLibs_468_);
lean_dec_ref(v_toLeanConfig_465_);
v_moreLinkLibs_469_ = lean_ctor_get(v_toLeanConfig_467_, 7);
lean_inc_ref(v_moreLinkLibs_469_);
lean_dec_ref(v_toLeanConfig_467_);
v___x_470_ = l_Array_append___redArg(v_moreLinkLibs_468_, v_moreLinkLibs_469_);
lean_dec_ref(v_moreLinkLibs_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_linkArgs(lean_object* v_self_471_){
_start:
{
lean_object* v_pkg_472_; lean_object* v_config_473_; lean_object* v_toLeanConfig_474_; lean_object* v_config_475_; lean_object* v_toLeanConfig_476_; lean_object* v_moreLinkArgs_477_; lean_object* v_moreLinkArgs_478_; lean_object* v___x_479_; 
v_pkg_472_ = lean_ctor_get(v_self_471_, 0);
v_config_473_ = lean_ctor_get(v_pkg_472_, 6);
v_toLeanConfig_474_ = lean_ctor_get(v_config_473_, 1);
lean_inc_ref(v_toLeanConfig_474_);
v_config_475_ = lean_ctor_get(v_self_471_, 2);
lean_inc(v_config_475_);
lean_dec_ref(v_self_471_);
v_toLeanConfig_476_ = lean_ctor_get(v_config_475_, 0);
lean_inc_ref(v_toLeanConfig_476_);
lean_dec(v_config_475_);
v_moreLinkArgs_477_ = lean_ctor_get(v_toLeanConfig_474_, 8);
lean_inc_ref(v_moreLinkArgs_477_);
lean_dec_ref(v_toLeanConfig_474_);
v_moreLinkArgs_478_ = lean_ctor_get(v_toLeanConfig_476_, 8);
lean_inc_ref(v_moreLinkArgs_478_);
lean_dec_ref(v_toLeanConfig_476_);
v___x_479_ = l_Array_append___redArg(v_moreLinkArgs_477_, v_moreLinkArgs_478_);
lean_dec_ref(v_moreLinkArgs_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLinkArgs(lean_object* v_self_480_){
_start:
{
lean_object* v_pkg_481_; lean_object* v_config_482_; lean_object* v_toLeanConfig_483_; lean_object* v_config_484_; lean_object* v_toLeanConfig_485_; lean_object* v_weakLinkArgs_486_; lean_object* v_weakLinkArgs_487_; lean_object* v___x_488_; 
v_pkg_481_ = lean_ctor_get(v_self_480_, 0);
v_config_482_ = lean_ctor_get(v_pkg_481_, 6);
v_toLeanConfig_483_ = lean_ctor_get(v_config_482_, 1);
lean_inc_ref(v_toLeanConfig_483_);
v_config_484_ = lean_ctor_get(v_self_480_, 2);
lean_inc(v_config_484_);
lean_dec_ref(v_self_480_);
v_toLeanConfig_485_ = lean_ctor_get(v_config_484_, 0);
lean_inc_ref(v_toLeanConfig_485_);
lean_dec(v_config_484_);
v_weakLinkArgs_486_ = lean_ctor_get(v_toLeanConfig_483_, 9);
lean_inc_ref(v_weakLinkArgs_486_);
lean_dec_ref(v_toLeanConfig_483_);
v_weakLinkArgs_487_ = lean_ctor_get(v_toLeanConfig_485_, 9);
lean_inc_ref(v_weakLinkArgs_487_);
lean_dec_ref(v_toLeanConfig_485_);
v___x_488_ = l_Array_append___redArg(v_weakLinkArgs_486_, v_weakLinkArgs_487_);
lean_dec_ref(v_weakLinkArgs_487_);
return v___x_488_;
}
}
lean_object* runtime_initialize_Lake_Config_ConfigTarget(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanLib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_LeanLib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_ConfigTarget(uint8_t builtin);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LeanLib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_ConfigTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_LeanLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_LeanLib(builtin);
}
#ifdef __cplusplus
}
#endif
