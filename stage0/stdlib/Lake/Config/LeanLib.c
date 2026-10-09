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
lean_object* l_Lake_BuildType_leanArgs___redArg();
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_LeanOptions_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
uint8_t l_Lake_instOrdBuildType_ord(uint8_t, uint8_t);
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
static lean_once_cell_t l_Lake_LeanLib_leanArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_leanArgs___closed__0;
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
uint8_t l_Lake_LeanLib_isLocalModule(lean_object* v_mod_105_, lean_object* v_self_106_){
_start:
{
lean_object* v_config_107_; uint8_t v___x_108_; 
v_config_107_ = lean_ctor_get(v_self_106_, 2);
v___x_108_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_105_, v_config_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_isLocalModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_105_ = stack[0].m_obj;
lean_object* v_self_106_ = stack[1].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_Lake_LeanLib_isLocalModule(v_mod_105_, v_self_106_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isLocalModule___boxed(lean_object* v_mod_110_, lean_object* v_self_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Lake_LeanLib_isLocalModule(v_mod_110_, v_self_111_);
lean_dec_ref(v_self_111_);
lean_dec(v_mod_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l_Lake_LeanLib_isBuildableModule(lean_object* v_mod_114_, lean_object* v_self_115_){
_start:
{
lean_object* v_config_116_; uint8_t v___x_117_; 
v_config_116_ = lean_ctor_get(v_self_115_, 2);
v___x_117_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_114_, v_config_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_isBuildableModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_114_ = stack[0].m_obj;
lean_object* v_self_115_ = stack[1].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_Lake_LeanLib_isBuildableModule(v_mod_114_, v_self_115_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isBuildableModule___boxed(lean_object* v_mod_119_, lean_object* v_self_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Lake_LeanLib_isBuildableModule(v_mod_119_, v_self_120_);
lean_dec_ref(v_self_120_);
lean_dec(v_mod_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
uint8_t l_Lake_LeanLib_libPrefixOnWindows(lean_object* v_self_123_){
_start:
{
lean_object* v_config_124_; uint8_t v_libPrefixOnWindows_125_; 
v_config_124_ = lean_ctor_get(v_self_123_, 2);
v_libPrefixOnWindows_125_ = lean_ctor_get_uint8(v_config_124_, sizeof(void*)*9);
if (v_libPrefixOnWindows_125_ == 0)
{
lean_object* v_pkg_126_; lean_object* v_config_127_; uint8_t v_libPrefixOnWindows_128_; 
v_pkg_126_ = lean_ctor_get(v_self_123_, 0);
v_config_127_ = lean_ctor_get(v_pkg_126_, 6);
v_libPrefixOnWindows_128_ = lean_ctor_get_uint8(v_config_127_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_128_;
}
else
{
return v_libPrefixOnWindows_125_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_libPrefixOnWindows_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_123_ = stack[0].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Lake_LeanLib_libPrefixOnWindows(v_self_123_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_libPrefixOnWindows___boxed(lean_object* v_self_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lake_LeanLib_libPrefixOnWindows(v_self_130_);
lean_dec_ref(v_self_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_libName(lean_object* v_self_134_){
_start:
{
lean_object* v___y_136_; lean_object* v_config_140_; lean_object* v_pkg_141_; lean_object* v_name_142_; lean_object* v_libName_143_; uint8_t v_libPrefixOnWindows_144_; lean_object* v___y_146_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_config_140_ = lean_ctor_get(v_self_134_, 2);
lean_inc(v_config_140_);
v_pkg_141_ = lean_ctor_get(v_self_134_, 0);
lean_inc_ref(v_pkg_141_);
v_name_142_ = lean_ctor_get(v_self_134_, 1);
lean_inc(v_name_142_);
lean_dec_ref(v_self_134_);
v_libName_143_ = lean_ctor_get(v_config_140_, 4);
lean_inc_ref(v_libName_143_);
v_libPrefixOnWindows_144_ = lean_ctor_get_uint8(v_config_140_, sizeof(void*)*9);
lean_dec(v_config_140_);
v___x_149_ = lean_string_utf8_byte_size(v_libName_143_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_nat_dec_eq(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_dec(v_name_142_);
v___y_146_ = v_libName_143_;
goto v___jp_145_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v_libName_143_);
lean_inc_ref(v_pkg_141_);
v___x_152_ = l_Lake_Package_id_x3f(v_pkg_141_);
v___x_153_ = l_Lean_mkModuleInitializationStem(v_name_142_, v___x_152_);
lean_dec(v___x_152_);
v___y_146_ = v___x_153_;
goto v___jp_145_;
}
v___jp_135_:
{
uint8_t v___x_137_; 
v___x_137_ = l_System_Platform_isWindows;
if (v___x_137_ == 0)
{
return v___y_136_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lake_LeanLib_libName___closed__0));
v___x_139_ = lean_string_append(v___x_138_, v___y_136_);
lean_dec_ref(v___y_136_);
return v___x_139_;
}
}
v___jp_145_:
{
if (v_libPrefixOnWindows_144_ == 0)
{
lean_object* v_config_147_; uint8_t v_libPrefixOnWindows_148_; 
v_config_147_ = lean_ctor_get(v_pkg_141_, 6);
lean_inc_ref(v_config_147_);
lean_dec_ref(v_pkg_141_);
v_libPrefixOnWindows_148_ = lean_ctor_get_uint8(v_config_147_, sizeof(void*)*28 + 4);
lean_dec_ref(v_config_147_);
if (v_libPrefixOnWindows_148_ == 0)
{
return v___y_146_;
}
else
{
v___y_136_ = v___y_146_;
goto v___jp_135_;
}
}
else
{
lean_dec_ref(v_pkg_141_);
v___y_136_ = v___y_146_;
goto v___jp_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFileName(lean_object* v_self_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; 
v___x_155_ = l_Lake_LeanLib_libName(v_self_154_);
v___x_156_ = 0;
v___x_157_ = l_Lake_nameToStaticLib(v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFile(lean_object* v_self_158_){
_start:
{
lean_object* v_pkg_159_; lean_object* v_config_160_; lean_object* v_dir_161_; lean_object* v_buildDir_162_; lean_object* v_nativeLibDir_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_pkg_159_ = lean_ctor_get(v_self_158_, 0);
v_config_160_ = lean_ctor_get(v_pkg_159_, 6);
v_dir_161_ = lean_ctor_get(v_pkg_159_, 4);
v_buildDir_162_ = lean_ctor_get(v_config_160_, 5);
v_nativeLibDir_163_ = lean_ctor_get(v_config_160_, 7);
lean_inc_ref(v_buildDir_162_);
v___x_164_ = l_System_FilePath_normalize(v_buildDir_162_);
lean_inc_ref(v_dir_161_);
v___x_165_ = l_Lake_joinRelative(v_dir_161_, v___x_164_);
lean_inc_ref(v_nativeLibDir_163_);
v___x_166_ = l_System_FilePath_normalize(v_nativeLibDir_163_);
v___x_167_ = l_Lake_joinRelative(v___x_165_, v___x_166_);
v___x_168_ = l_Lake_LeanLib_libName(v_self_158_);
v___x_169_ = 0;
v___x_170_ = l_Lake_nameToStaticLib(v___x_168_, v___x_169_);
v___x_171_ = l_Lake_joinRelative(v___x_167_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportLibFile(lean_object* v_self_173_){
_start:
{
lean_object* v_pkg_174_; lean_object* v_config_175_; lean_object* v_dir_176_; lean_object* v_buildDir_177_; lean_object* v_nativeLibDir_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_pkg_174_ = lean_ctor_get(v_self_173_, 0);
v_config_175_ = lean_ctor_get(v_pkg_174_, 6);
v_dir_176_ = lean_ctor_get(v_pkg_174_, 4);
v_buildDir_177_ = lean_ctor_get(v_config_175_, 5);
v_nativeLibDir_178_ = lean_ctor_get(v_config_175_, 7);
lean_inc_ref(v_buildDir_177_);
v___x_179_ = l_System_FilePath_normalize(v_buildDir_177_);
lean_inc_ref(v_dir_176_);
v___x_180_ = l_Lake_joinRelative(v_dir_176_, v___x_179_);
lean_inc_ref(v_nativeLibDir_178_);
v___x_181_ = l_System_FilePath_normalize(v_nativeLibDir_178_);
v___x_182_ = l_Lake_joinRelative(v___x_180_, v___x_181_);
v___x_183_ = l_Lake_LeanLib_libName(v_self_173_);
v___x_184_ = 0;
v___x_185_ = l_Lake_nameToStaticLib(v___x_183_, v___x_184_);
v___x_186_ = ((lean_object*)(l_Lake_LeanLib_staticExportLibFile___closed__0));
v___x_187_ = l_System_FilePath_addExtension(v___x_185_, v___x_186_);
v___x_188_ = l_Lake_joinRelative(v___x_182_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFileName(lean_object* v_self_189_){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = l_Lake_LeanLib_libName(v_self_189_);
v___x_191_ = 0;
v___x_192_ = l_Lake_nameToSharedLib(v___x_190_, v___x_191_);
lean_dec_ref(v___x_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFile(lean_object* v_self_193_){
_start:
{
lean_object* v_pkg_194_; lean_object* v_config_195_; lean_object* v_dir_196_; lean_object* v_buildDir_197_; lean_object* v_nativeLibDir_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_pkg_194_ = lean_ctor_get(v_self_193_, 0);
v_config_195_ = lean_ctor_get(v_pkg_194_, 6);
v_dir_196_ = lean_ctor_get(v_pkg_194_, 4);
v_buildDir_197_ = lean_ctor_get(v_config_195_, 5);
v_nativeLibDir_198_ = lean_ctor_get(v_config_195_, 7);
lean_inc_ref(v_buildDir_197_);
v___x_199_ = l_System_FilePath_normalize(v_buildDir_197_);
lean_inc_ref(v_dir_196_);
v___x_200_ = l_Lake_joinRelative(v_dir_196_, v___x_199_);
lean_inc_ref(v_nativeLibDir_198_);
v___x_201_ = l_System_FilePath_normalize(v_nativeLibDir_198_);
v___x_202_ = l_Lake_joinRelative(v___x_200_, v___x_201_);
v___x_203_ = l_Lake_LeanLib_libName(v_self_193_);
v___x_204_ = 0;
v___x_205_ = l_Lake_nameToSharedLib(v___x_203_, v___x_204_);
lean_dec_ref(v___x_203_);
v___x_206_ = l_Lake_joinRelative(v___x_202_, v___x_205_);
return v___x_206_;
}
}
uint8_t l_Lake_LeanLib_isPlugin(lean_object* v_self_207_){
_start:
{
lean_object* v_config_208_; lean_object* v_pkg_209_; lean_object* v_roots_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_config_208_ = lean_ctor_get(v_self_207_, 2);
v_pkg_209_ = lean_ctor_get(v_self_207_, 0);
lean_inc_ref(v_pkg_209_);
v_roots_210_ = lean_ctor_get(v_config_208_, 2);
lean_inc_ref(v_roots_210_);
v___x_211_ = lean_array_get_size(v_roots_210_);
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_dec_eq(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec_ref(v_roots_210_);
lean_dec_ref(v_pkg_209_);
lean_dec_ref(v_self_207_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_214_ = l_Lake_LeanLib_libName(v_self_207_);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_array_fget(v_roots_210_, v___x_215_);
lean_dec_ref(v_roots_210_);
v___x_217_ = l_Lake_Package_id_x3f(v_pkg_209_);
v___x_218_ = l_Lean_mkModuleInitializationStem(v___x_216_, v___x_217_);
lean_dec(v___x_217_);
v___x_219_ = lean_string_dec_eq(v___x_214_, v___x_218_);
lean_dec_ref(v___x_218_);
lean_dec_ref(v___x_214_);
return v___x_219_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_isPlugin_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_207_ = stack[0].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_Lake_LeanLib_isPlugin(v_self_207_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isPlugin___boxed(lean_object* v_self_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lake_LeanLib_isPlugin(v_self_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepTargets(lean_object* v_self_224_){
_start:
{
lean_object* v_config_225_; lean_object* v_extraDepTargets_226_; 
v_config_225_ = lean_ctor_get(v_self_224_, 2);
v_extraDepTargets_226_ = lean_ctor_get(v_config_225_, 6);
lean_inc_ref(v_extraDepTargets_226_);
return v_extraDepTargets_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepTargets___boxed(lean_object* v_self_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lake_LeanLib_extraDepTargets(v_self_227_);
lean_dec_ref(v_self_227_);
return v_res_228_;
}
}
uint8_t l_Lake_LeanLib_precompileModules(lean_object* v_self_229_){
_start:
{
lean_object* v_pkg_230_; lean_object* v_config_231_; uint8_t v_precompileModules_232_; 
v_pkg_230_ = lean_ctor_get(v_self_229_, 0);
v_config_231_ = lean_ctor_get(v_pkg_230_, 6);
v_precompileModules_232_ = lean_ctor_get_uint8(v_config_231_, sizeof(void*)*28 + 1);
if (v_precompileModules_232_ == 0)
{
lean_object* v_config_233_; uint8_t v_precompileModules_234_; 
v_config_233_ = lean_ctor_get(v_self_229_, 2);
v_precompileModules_234_ = lean_ctor_get_uint8(v_config_233_, sizeof(void*)*9 + 2);
return v_precompileModules_234_;
}
else
{
return v_precompileModules_232_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_precompileModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_229_ = stack[0].m_obj;
uint8_t v_res_235_;
v_res_235_ = l_Lake_LeanLib_precompileModules(v_self_229_);
stack->m_num = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileModules___boxed(lean_object* v_self_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lake_LeanLib_precompileModules(v_self_236_);
lean_dec_ref(v_self_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
uint8_t l_Lake_LeanLib_precompileImports(lean_object* v_self_239_){
_start:
{
lean_object* v_pkg_240_; lean_object* v_config_241_; uint8_t v_precompileModules_242_; 
v_pkg_240_ = lean_ctor_get(v_self_239_, 0);
v_config_241_ = lean_ctor_get(v_pkg_240_, 6);
v_precompileModules_242_ = lean_ctor_get_uint8(v_config_241_, sizeof(void*)*28 + 1);
if (v_precompileModules_242_ == 0)
{
lean_object* v_config_243_; uint8_t v_precompileModules_244_; 
v_config_243_ = lean_ctor_get(v_self_239_, 2);
v_precompileModules_244_ = lean_ctor_get_uint8(v_config_243_, sizeof(void*)*9 + 2);
if (v_precompileModules_244_ == 0)
{
lean_object* v_toLeanConfig_245_; uint8_t v_precompileImports_246_; 
v_toLeanConfig_245_ = lean_ctor_get(v_config_241_, 1);
v_precompileImports_246_ = lean_ctor_get_uint8(v_toLeanConfig_245_, sizeof(void*)*13 + 2);
if (v_precompileImports_246_ == 0)
{
lean_object* v_toLeanConfig_247_; uint8_t v_precompileImports_248_; 
v_toLeanConfig_247_ = lean_ctor_get(v_config_243_, 0);
v_precompileImports_248_ = lean_ctor_get_uint8(v_toLeanConfig_247_, sizeof(void*)*13 + 2);
return v_precompileImports_248_;
}
else
{
return v_precompileImports_246_;
}
}
else
{
return v_precompileModules_244_;
}
}
else
{
return v_precompileModules_242_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_precompileImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_239_ = stack[0].m_obj;
uint8_t v_res_249_;
v_res_249_ = l_Lake_LeanLib_precompileImports(v_self_239_);
stack->m_num = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileImports___boxed(lean_object* v_self_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Lake_LeanLib_precompileImports(v_self_250_);
lean_dec_ref(v_self_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
uint8_t l_Lake_LeanLib_shouldPrecompile(lean_object* v_self_253_){
_start:
{
lean_object* v_pkg_254_; lean_object* v_config_255_; uint8_t v_precompileModules_256_; 
v_pkg_254_ = lean_ctor_get(v_self_253_, 0);
v_config_255_ = lean_ctor_get(v_pkg_254_, 6);
v_precompileModules_256_ = lean_ctor_get_uint8(v_config_255_, sizeof(void*)*28 + 1);
if (v_precompileModules_256_ == 0)
{
lean_object* v_config_257_; uint8_t v_precompileModules_258_; 
v_config_257_ = lean_ctor_get(v_self_253_, 2);
v_precompileModules_258_ = lean_ctor_get_uint8(v_config_257_, sizeof(void*)*9 + 2);
if (v_precompileModules_258_ == 0)
{
uint8_t v_precompileLibrary_259_; 
v_precompileLibrary_259_ = lean_ctor_get_uint8(v_config_257_, sizeof(void*)*9 + 1);
return v_precompileLibrary_259_;
}
else
{
return v_precompileModules_258_;
}
}
else
{
return v_precompileModules_256_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_shouldPrecompile_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_253_ = stack[0].m_obj;
uint8_t v_res_260_;
v_res_260_ = l_Lake_LeanLib_shouldPrecompile(v_self_253_);
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_shouldPrecompile___boxed(lean_object* v_self_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Lake_LeanLib_shouldPrecompile(v_self_261_);
lean_dec_ref(v_self_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent(lean_object* v_self_264_){
_start:
{
lean_object* v_config_265_; lean_object* v_toLeanConfig_266_; lean_object* v_platformIndependent_267_; 
v_config_265_ = lean_ctor_get(v_self_264_, 2);
v_toLeanConfig_266_ = lean_ctor_get(v_config_265_, 0);
v_platformIndependent_267_ = lean_ctor_get(v_toLeanConfig_266_, 10);
if (lean_obj_tag(v_platformIndependent_267_) == 0)
{
lean_object* v_pkg_268_; lean_object* v_config_269_; lean_object* v_toLeanConfig_270_; lean_object* v_platformIndependent_271_; 
v_pkg_268_ = lean_ctor_get(v_self_264_, 0);
v_config_269_ = lean_ctor_get(v_pkg_268_, 6);
v_toLeanConfig_270_ = lean_ctor_get(v_config_269_, 1);
v_platformIndependent_271_ = lean_ctor_get(v_toLeanConfig_270_, 10);
lean_inc(v_platformIndependent_271_);
return v_platformIndependent_271_;
}
else
{
lean_inc_ref(v_platformIndependent_267_);
return v_platformIndependent_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent___boxed(lean_object* v_self_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lake_LeanLib_platformIndependent(v_self_272_);
lean_dec_ref(v_self_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets(lean_object* v_self_274_){
_start:
{
lean_object* v_config_275_; lean_object* v_defaultFacets_276_; 
v_config_275_ = lean_ctor_get(v_self_274_, 2);
v_defaultFacets_276_ = lean_ctor_get(v_config_275_, 7);
lean_inc_ref(v_defaultFacets_276_);
return v_defaultFacets_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets___boxed(lean_object* v_self_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lake_LeanLib_defaultFacets(v_self_277_);
lean_dec_ref(v_self_277_);
return v_res_278_;
}
}
lean_object* l_Lake_LeanLib_nativeFacets(lean_object* v_self_279_, uint8_t v_shouldExport_280_){
_start:
{
lean_object* v_config_281_; lean_object* v_nativeFacets_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_config_281_ = lean_ctor_get(v_self_279_, 2);
lean_inc(v_config_281_);
lean_dec_ref(v_self_279_);
v_nativeFacets_282_ = lean_ctor_get(v_config_281_, 8);
lean_inc_ref(v_nativeFacets_282_);
lean_dec(v_config_281_);
v___x_283_ = lean_box(v_shouldExport_280_);
v___x_284_ = lean_apply_1(v_nativeFacets_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_nativeFacets_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_279_ = stack[0].m_obj;
uint8_t v_shouldExport_280_ = stack[1].m_num;
lean_object* v_res_285_;
v_res_285_ = l_Lake_LeanLib_nativeFacets(v_self_279_, v_shouldExport_280_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets___boxed(lean_object* v_self_286_, lean_object* v_shouldExport_287_){
_start:
{
uint8_t v_shouldExport_boxed_288_; lean_object* v_res_289_; 
v_shouldExport_boxed_288_ = lean_unbox(v_shouldExport_287_);
v_res_289_ = l_Lake_LeanLib_nativeFacets(v_self_286_, v_shouldExport_boxed_288_);
return v_res_289_;
}
}
uint8_t l_Lake_LeanLib_buildType(lean_object* v_self_290_){
_start:
{
lean_object* v_pkg_291_; lean_object* v_config_292_; lean_object* v_toLeanConfig_293_; lean_object* v_config_294_; lean_object* v_toLeanConfig_295_; uint8_t v_buildType_296_; uint8_t v_buildType_297_; uint8_t v___x_298_; 
v_pkg_291_ = lean_ctor_get(v_self_290_, 0);
v_config_292_ = lean_ctor_get(v_pkg_291_, 6);
v_toLeanConfig_293_ = lean_ctor_get(v_config_292_, 1);
v_config_294_ = lean_ctor_get(v_self_290_, 2);
v_toLeanConfig_295_ = lean_ctor_get(v_config_294_, 0);
v_buildType_296_ = lean_ctor_get_uint8(v_toLeanConfig_293_, sizeof(void*)*13);
v_buildType_297_ = lean_ctor_get_uint8(v_toLeanConfig_295_, sizeof(void*)*13);
v___x_298_ = l_Lake_instOrdBuildType_ord(v_buildType_296_, v_buildType_297_);
if (v___x_298_ == 2)
{
return v_buildType_297_;
}
else
{
return v_buildType_296_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_buildType_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_290_ = stack[0].m_obj;
uint8_t v_res_299_;
v_res_299_ = l_Lake_LeanLib_buildType(v_self_290_);
stack->m_num = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_buildType___boxed(lean_object* v_self_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lake_LeanLib_buildType(v_self_300_);
lean_dec_ref(v_self_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions(lean_object* v_self_303_){
_start:
{
lean_object* v_pkg_304_; lean_object* v_config_305_; lean_object* v_toLeanConfig_306_; lean_object* v_config_307_; lean_object* v_toLeanConfig_308_; uint8_t v_buildType_309_; lean_object* v_leanOptions_310_; lean_object* v_moreServerOptions_311_; uint8_t v_buildType_312_; lean_object* v_leanOptions_313_; lean_object* v_moreServerOptions_314_; lean_object* v___x_315_; uint8_t v___y_317_; uint8_t v___x_325_; 
v_pkg_304_ = lean_ctor_get(v_self_303_, 0);
v_config_305_ = lean_ctor_get(v_pkg_304_, 6);
v_toLeanConfig_306_ = lean_ctor_get(v_config_305_, 1);
v_config_307_ = lean_ctor_get(v_self_303_, 2);
v_toLeanConfig_308_ = lean_ctor_get(v_config_307_, 0);
v_buildType_309_ = lean_ctor_get_uint8(v_toLeanConfig_306_, sizeof(void*)*13);
v_leanOptions_310_ = lean_ctor_get(v_toLeanConfig_306_, 0);
v_moreServerOptions_311_ = lean_ctor_get(v_toLeanConfig_306_, 4);
v_buildType_312_ = lean_ctor_get_uint8(v_toLeanConfig_308_, sizeof(void*)*13);
v_leanOptions_313_ = lean_ctor_get(v_toLeanConfig_308_, 0);
v_moreServerOptions_314_ = lean_ctor_get(v_toLeanConfig_308_, 4);
v___x_315_ = lean_box(1);
v___x_325_ = l_Lake_instOrdBuildType_ord(v_buildType_309_, v_buildType_312_);
if (v___x_325_ == 2)
{
v___y_317_ = v_buildType_312_;
goto v___jp_316_;
}
else
{
v___y_317_ = v_buildType_309_;
goto v___jp_316_;
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_318_ = l_Lake_BuildType_leanOptions(v___y_317_);
v___x_319_ = l_Lean_LeanOptions_append(v___x_315_, v___x_318_);
v___x_320_ = l_Lean_LeanOptions_ofArray(v_leanOptions_310_);
v___x_321_ = l_Lean_LeanOptions_appendArray(v___x_320_, v_moreServerOptions_311_);
v___x_322_ = l_Lean_LeanOptions_append(v___x_319_, v___x_321_);
v___x_323_ = l_Lean_LeanOptions_appendArray(v___x_322_, v_leanOptions_313_);
v___x_324_ = l_Lean_LeanOptions_appendArray(v___x_323_, v_moreServerOptions_314_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions___boxed(lean_object* v_self_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lake_LeanLib_serverOptions(v_self_326_);
lean_dec_ref(v_self_326_);
return v_res_327_;
}
}
uint8_t l_Lake_LeanLib_backend(lean_object* v_self_328_){
_start:
{
lean_object* v_config_329_; lean_object* v_toLeanConfig_330_; lean_object* v_pkg_331_; lean_object* v_config_332_; lean_object* v_toLeanConfig_333_; uint8_t v_backend_334_; uint8_t v_backend_335_; uint8_t v___x_336_; 
v_config_329_ = lean_ctor_get(v_self_328_, 2);
v_toLeanConfig_330_ = lean_ctor_get(v_config_329_, 0);
v_pkg_331_ = lean_ctor_get(v_self_328_, 0);
v_config_332_ = lean_ctor_get(v_pkg_331_, 6);
v_toLeanConfig_333_ = lean_ctor_get(v_config_332_, 1);
v_backend_334_ = lean_ctor_get_uint8(v_toLeanConfig_330_, sizeof(void*)*13 + 1);
v_backend_335_ = lean_ctor_get_uint8(v_toLeanConfig_333_, sizeof(void*)*13 + 1);
v___x_336_ = l_Lake_Backend_orPreferLeft(v_backend_334_, v_backend_335_);
return v___x_336_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_backend_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_328_ = stack[0].m_obj;
uint8_t v_res_337_;
v_res_337_ = l_Lake_LeanLib_backend(v_self_328_);
stack->m_num = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_backend___boxed(lean_object* v_self_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Lake_LeanLib_backend(v_self_338_);
lean_dec_ref(v_self_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
uint8_t l_Lake_LeanLib_allowImportAll(lean_object* v_self_341_){
_start:
{
lean_object* v_config_342_; uint8_t v_allowImportAll_343_; 
v_config_342_ = lean_ctor_get(v_self_341_, 2);
v_allowImportAll_343_ = lean_ctor_get_uint8(v_config_342_, sizeof(void*)*9 + 3);
if (v_allowImportAll_343_ == 0)
{
lean_object* v_pkg_344_; lean_object* v_config_345_; uint8_t v_allowImportAll_346_; 
v_pkg_344_ = lean_ctor_get(v_self_341_, 0);
v_config_345_ = lean_ctor_get(v_pkg_344_, 6);
v_allowImportAll_346_ = lean_ctor_get_uint8(v_config_345_, sizeof(void*)*28 + 5);
return v_allowImportAll_346_;
}
else
{
return v_allowImportAll_343_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_allowImportAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_341_ = stack[0].m_obj;
uint8_t v_res_347_;
v_res_347_ = l_Lake_LeanLib_allowImportAll(v_self_341_);
stack->m_num = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowImportAll___boxed(lean_object* v_self_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lake_LeanLib_allowImportAll(v_self_348_);
lean_dec_ref(v_self_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
uint8_t l_Lake_LeanLib_requiresModuleSystem(lean_object* v_self_351_){
_start:
{
lean_object* v_config_352_; lean_object* v_toLeanConfig_353_; uint8_t v_requiresModuleSystem_354_; 
v_config_352_ = lean_ctor_get(v_self_351_, 2);
v_toLeanConfig_353_ = lean_ctor_get(v_config_352_, 0);
v_requiresModuleSystem_354_ = lean_ctor_get_uint8(v_toLeanConfig_353_, sizeof(void*)*13 + 3);
if (v_requiresModuleSystem_354_ == 0)
{
lean_object* v_pkg_355_; lean_object* v_config_356_; lean_object* v_toLeanConfig_357_; uint8_t v_requiresModuleSystem_358_; 
v_pkg_355_ = lean_ctor_get(v_self_351_, 0);
v_config_356_ = lean_ctor_get(v_pkg_355_, 6);
v_toLeanConfig_357_ = lean_ctor_get(v_config_356_, 1);
v_requiresModuleSystem_358_ = lean_ctor_get_uint8(v_toLeanConfig_357_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_358_;
}
else
{
return v_requiresModuleSystem_354_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_requiresModuleSystem_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_351_ = stack[0].m_obj;
uint8_t v_res_359_;
v_res_359_ = l_Lake_LeanLib_requiresModuleSystem(v_self_351_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_requiresModuleSystem___boxed(lean_object* v_self_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lake_LeanLib_requiresModuleSystem(v_self_360_);
lean_dec_ref(v_self_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
uint8_t l_Lake_LeanLib_allowNonModules(lean_object* v_self_363_){
_start:
{
lean_object* v_config_364_; lean_object* v_toLeanConfig_365_; uint8_t v_allowNonModules_366_; 
v_config_364_ = lean_ctor_get(v_self_363_, 2);
v_toLeanConfig_365_ = lean_ctor_get(v_config_364_, 0);
v_allowNonModules_366_ = lean_ctor_get_uint8(v_toLeanConfig_365_, sizeof(void*)*13 + 4);
if (v_allowNonModules_366_ == 0)
{
lean_object* v_pkg_367_; lean_object* v_config_368_; lean_object* v_toLeanConfig_369_; uint8_t v_allowNonModules_370_; 
v_pkg_367_ = lean_ctor_get(v_self_363_, 0);
v_config_368_ = lean_ctor_get(v_pkg_367_, 6);
v_toLeanConfig_369_ = lean_ctor_get(v_config_368_, 1);
v_allowNonModules_370_ = lean_ctor_get_uint8(v_toLeanConfig_369_, sizeof(void*)*13 + 4);
return v_allowNonModules_370_;
}
else
{
return v_allowNonModules_366_;
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_allowNonModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_363_ = stack[0].m_obj;
uint8_t v_res_371_;
v_res_371_ = l_Lake_LeanLib_allowNonModules(v_self_363_);
stack->m_num = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowNonModules___boxed(lean_object* v_self_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lake_LeanLib_allowNonModules(v_self_372_);
lean_dec_ref(v_self_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_dynlibs(lean_object* v_self_375_){
_start:
{
lean_object* v_pkg_376_; lean_object* v_config_377_; lean_object* v_toLeanConfig_378_; lean_object* v_config_379_; lean_object* v_toLeanConfig_380_; lean_object* v_dynlibs_381_; lean_object* v_dynlibs_382_; lean_object* v___x_383_; 
v_pkg_376_ = lean_ctor_get(v_self_375_, 0);
v_config_377_ = lean_ctor_get(v_pkg_376_, 6);
v_toLeanConfig_378_ = lean_ctor_get(v_config_377_, 1);
lean_inc_ref(v_toLeanConfig_378_);
v_config_379_ = lean_ctor_get(v_self_375_, 2);
lean_inc(v_config_379_);
lean_dec_ref(v_self_375_);
v_toLeanConfig_380_ = lean_ctor_get(v_config_379_, 0);
lean_inc_ref(v_toLeanConfig_380_);
lean_dec(v_config_379_);
v_dynlibs_381_ = lean_ctor_get(v_toLeanConfig_378_, 11);
lean_inc_ref(v_dynlibs_381_);
lean_dec_ref(v_toLeanConfig_378_);
v_dynlibs_382_ = lean_ctor_get(v_toLeanConfig_380_, 11);
lean_inc_ref(v_dynlibs_382_);
lean_dec_ref(v_toLeanConfig_380_);
v___x_383_ = l_Array_append___redArg(v_dynlibs_381_, v_dynlibs_382_);
lean_dec_ref(v_dynlibs_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_plugins(lean_object* v_self_384_){
_start:
{
lean_object* v_pkg_385_; lean_object* v_config_386_; lean_object* v_toLeanConfig_387_; lean_object* v_config_388_; lean_object* v_toLeanConfig_389_; lean_object* v_plugins_390_; lean_object* v_plugins_391_; lean_object* v___x_392_; 
v_pkg_385_ = lean_ctor_get(v_self_384_, 0);
v_config_386_ = lean_ctor_get(v_pkg_385_, 6);
v_toLeanConfig_387_ = lean_ctor_get(v_config_386_, 1);
lean_inc_ref(v_toLeanConfig_387_);
v_config_388_ = lean_ctor_get(v_self_384_, 2);
lean_inc(v_config_388_);
lean_dec_ref(v_self_384_);
v_toLeanConfig_389_ = lean_ctor_get(v_config_388_, 0);
lean_inc_ref(v_toLeanConfig_389_);
lean_dec(v_config_388_);
v_plugins_390_ = lean_ctor_get(v_toLeanConfig_387_, 12);
lean_inc_ref(v_plugins_390_);
lean_dec_ref(v_toLeanConfig_387_);
v_plugins_391_ = lean_ctor_get(v_toLeanConfig_389_, 12);
lean_inc_ref(v_plugins_391_);
lean_dec_ref(v_toLeanConfig_389_);
v___x_392_ = l_Array_append___redArg(v_plugins_390_, v_plugins_391_);
lean_dec_ref(v_plugins_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions(lean_object* v_self_393_){
_start:
{
lean_object* v_pkg_394_; lean_object* v_config_395_; lean_object* v_toLeanConfig_396_; lean_object* v_config_397_; lean_object* v_toLeanConfig_398_; uint8_t v_buildType_399_; lean_object* v_leanOptions_400_; uint8_t v_buildType_401_; lean_object* v_leanOptions_402_; uint8_t v___y_404_; uint8_t v___x_409_; 
v_pkg_394_ = lean_ctor_get(v_self_393_, 0);
v_config_395_ = lean_ctor_get(v_pkg_394_, 6);
v_toLeanConfig_396_ = lean_ctor_get(v_config_395_, 1);
v_config_397_ = lean_ctor_get(v_self_393_, 2);
v_toLeanConfig_398_ = lean_ctor_get(v_config_397_, 0);
v_buildType_399_ = lean_ctor_get_uint8(v_toLeanConfig_396_, sizeof(void*)*13);
v_leanOptions_400_ = lean_ctor_get(v_toLeanConfig_396_, 0);
v_buildType_401_ = lean_ctor_get_uint8(v_toLeanConfig_398_, sizeof(void*)*13);
v_leanOptions_402_ = lean_ctor_get(v_toLeanConfig_398_, 0);
v___x_409_ = l_Lake_instOrdBuildType_ord(v_buildType_399_, v_buildType_401_);
if (v___x_409_ == 2)
{
v___y_404_ = v_buildType_401_;
goto v___jp_403_;
}
else
{
v___y_404_ = v_buildType_399_;
goto v___jp_403_;
}
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l_Lake_BuildType_leanOptions(v___y_404_);
v___x_406_ = l_Lean_LeanOptions_ofArray(v_leanOptions_400_);
v___x_407_ = l_Lean_LeanOptions_append(v___x_405_, v___x_406_);
v___x_408_ = l_Lean_LeanOptions_appendArray(v___x_407_, v_leanOptions_402_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions___boxed(lean_object* v_self_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lake_LeanLib_leanOptions(v_self_410_);
lean_dec_ref(v_self_410_);
return v_res_411_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs(lean_object* v_self_413_){
_start:
{
lean_object* v_pkg_414_; lean_object* v_config_415_; lean_object* v_toLeanConfig_416_; lean_object* v_config_417_; lean_object* v_toLeanConfig_418_; lean_object* v_moreLeanArgs_419_; lean_object* v_moreLeanArgs_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_pkg_414_ = lean_ctor_get(v_self_413_, 0);
v_config_415_ = lean_ctor_get(v_pkg_414_, 6);
v_toLeanConfig_416_ = lean_ctor_get(v_config_415_, 1);
v_config_417_ = lean_ctor_get(v_self_413_, 2);
v_toLeanConfig_418_ = lean_ctor_get(v_config_417_, 0);
v_moreLeanArgs_419_ = lean_ctor_get(v_toLeanConfig_416_, 1);
v_moreLeanArgs_420_ = lean_ctor_get(v_toLeanConfig_418_, 1);
v___x_421_ = lean_obj_once(&l_Lake_LeanLib_leanArgs___closed__0, &l_Lake_LeanLib_leanArgs___closed__0_once, _init_l_Lake_LeanLib_leanArgs___closed__0);
v___x_422_ = l_Array_append___redArg(v___x_421_, v_moreLeanArgs_419_);
v___x_423_ = l_Array_append___redArg(v___x_422_, v_moreLeanArgs_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs___boxed(lean_object* v_self_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lake_LeanLib_leanArgs(v_self_424_);
lean_dec_ref(v_self_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeanArgs(lean_object* v_self_426_){
_start:
{
lean_object* v_pkg_427_; lean_object* v_config_428_; lean_object* v_toLeanConfig_429_; lean_object* v_config_430_; lean_object* v_toLeanConfig_431_; lean_object* v_weakLeanArgs_432_; lean_object* v_weakLeanArgs_433_; lean_object* v___x_434_; 
v_pkg_427_ = lean_ctor_get(v_self_426_, 0);
v_config_428_ = lean_ctor_get(v_pkg_427_, 6);
v_toLeanConfig_429_ = lean_ctor_get(v_config_428_, 1);
lean_inc_ref(v_toLeanConfig_429_);
v_config_430_ = lean_ctor_get(v_self_426_, 2);
lean_inc(v_config_430_);
lean_dec_ref(v_self_426_);
v_toLeanConfig_431_ = lean_ctor_get(v_config_430_, 0);
lean_inc_ref(v_toLeanConfig_431_);
lean_dec(v_config_430_);
v_weakLeanArgs_432_ = lean_ctor_get(v_toLeanConfig_429_, 2);
lean_inc_ref(v_weakLeanArgs_432_);
lean_dec_ref(v_toLeanConfig_429_);
v_weakLeanArgs_433_ = lean_ctor_get(v_toLeanConfig_431_, 2);
lean_inc_ref(v_weakLeanArgs_433_);
lean_dec_ref(v_toLeanConfig_431_);
v___x_434_ = l_Array_append___redArg(v_weakLeanArgs_432_, v_weakLeanArgs_433_);
lean_dec_ref(v_weakLeanArgs_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs(lean_object* v_self_435_){
_start:
{
lean_object* v_pkg_436_; lean_object* v_config_437_; lean_object* v_toLeanConfig_438_; lean_object* v_config_439_; lean_object* v_toLeanConfig_440_; uint8_t v_buildType_441_; lean_object* v_moreLeancArgs_442_; uint8_t v_buildType_443_; lean_object* v_moreLeancArgs_444_; uint8_t v___y_446_; uint8_t v___x_450_; 
v_pkg_436_ = lean_ctor_get(v_self_435_, 0);
v_config_437_ = lean_ctor_get(v_pkg_436_, 6);
v_toLeanConfig_438_ = lean_ctor_get(v_config_437_, 1);
v_config_439_ = lean_ctor_get(v_self_435_, 2);
v_toLeanConfig_440_ = lean_ctor_get(v_config_439_, 0);
v_buildType_441_ = lean_ctor_get_uint8(v_toLeanConfig_438_, sizeof(void*)*13);
v_moreLeancArgs_442_ = lean_ctor_get(v_toLeanConfig_438_, 3);
v_buildType_443_ = lean_ctor_get_uint8(v_toLeanConfig_440_, sizeof(void*)*13);
v_moreLeancArgs_444_ = lean_ctor_get(v_toLeanConfig_440_, 3);
v___x_450_ = l_Lake_instOrdBuildType_ord(v_buildType_441_, v_buildType_443_);
if (v___x_450_ == 2)
{
v___y_446_ = v_buildType_443_;
goto v___jp_445_;
}
else
{
v___y_446_ = v_buildType_441_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = l_Lake_BuildType_leancArgs(v___y_446_);
v___x_448_ = l_Array_append___redArg(v___x_447_, v_moreLeancArgs_442_);
v___x_449_ = l_Array_append___redArg(v___x_448_, v_moreLeancArgs_444_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs___boxed(lean_object* v_self_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_LeanLib_leancArgs(v_self_451_);
lean_dec_ref(v_self_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeancArgs(lean_object* v_self_453_){
_start:
{
lean_object* v_pkg_454_; lean_object* v_config_455_; lean_object* v_toLeanConfig_456_; lean_object* v_config_457_; lean_object* v_toLeanConfig_458_; lean_object* v_weakLeancArgs_459_; lean_object* v_weakLeancArgs_460_; lean_object* v___x_461_; 
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
v_weakLeancArgs_459_ = lean_ctor_get(v_toLeanConfig_456_, 5);
lean_inc_ref(v_weakLeancArgs_459_);
lean_dec_ref(v_toLeanConfig_456_);
v_weakLeancArgs_460_ = lean_ctor_get(v_toLeanConfig_458_, 5);
lean_inc_ref(v_weakLeancArgs_460_);
lean_dec_ref(v_toLeanConfig_458_);
v___x_461_ = l_Array_append___redArg(v_weakLeancArgs_459_, v_weakLeancArgs_460_);
lean_dec_ref(v_weakLeancArgs_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkObjs(lean_object* v_self_462_){
_start:
{
lean_object* v_pkg_463_; lean_object* v_config_464_; lean_object* v_toLeanConfig_465_; lean_object* v_config_466_; lean_object* v_toLeanConfig_467_; lean_object* v_moreLinkObjs_468_; lean_object* v_moreLinkObjs_469_; lean_object* v___x_470_; 
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
v_moreLinkObjs_468_ = lean_ctor_get(v_toLeanConfig_465_, 6);
lean_inc_ref(v_moreLinkObjs_468_);
lean_dec_ref(v_toLeanConfig_465_);
v_moreLinkObjs_469_ = lean_ctor_get(v_toLeanConfig_467_, 6);
lean_inc_ref(v_moreLinkObjs_469_);
lean_dec_ref(v_toLeanConfig_467_);
v___x_470_ = l_Array_append___redArg(v_moreLinkObjs_468_, v_moreLinkObjs_469_);
lean_dec_ref(v_moreLinkObjs_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkLibs(lean_object* v_self_471_){
_start:
{
lean_object* v_pkg_472_; lean_object* v_config_473_; lean_object* v_toLeanConfig_474_; lean_object* v_config_475_; lean_object* v_toLeanConfig_476_; lean_object* v_moreLinkLibs_477_; lean_object* v_moreLinkLibs_478_; lean_object* v___x_479_; 
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
v_moreLinkLibs_477_ = lean_ctor_get(v_toLeanConfig_474_, 7);
lean_inc_ref(v_moreLinkLibs_477_);
lean_dec_ref(v_toLeanConfig_474_);
v_moreLinkLibs_478_ = lean_ctor_get(v_toLeanConfig_476_, 7);
lean_inc_ref(v_moreLinkLibs_478_);
lean_dec_ref(v_toLeanConfig_476_);
v___x_479_ = l_Array_append___redArg(v_moreLinkLibs_477_, v_moreLinkLibs_478_);
lean_dec_ref(v_moreLinkLibs_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_linkArgs(lean_object* v_self_480_){
_start:
{
lean_object* v_pkg_481_; lean_object* v_config_482_; lean_object* v_toLeanConfig_483_; lean_object* v_config_484_; lean_object* v_toLeanConfig_485_; lean_object* v_moreLinkArgs_486_; lean_object* v_moreLinkArgs_487_; lean_object* v___x_488_; 
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
v_moreLinkArgs_486_ = lean_ctor_get(v_toLeanConfig_483_, 8);
lean_inc_ref(v_moreLinkArgs_486_);
lean_dec_ref(v_toLeanConfig_483_);
v_moreLinkArgs_487_ = lean_ctor_get(v_toLeanConfig_485_, 8);
lean_inc_ref(v_moreLinkArgs_487_);
lean_dec_ref(v_toLeanConfig_485_);
v___x_488_ = l_Array_append___redArg(v_moreLinkArgs_486_, v_moreLinkArgs_487_);
lean_dec_ref(v_moreLinkArgs_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLinkArgs(lean_object* v_self_489_){
_start:
{
lean_object* v_pkg_490_; lean_object* v_config_491_; lean_object* v_toLeanConfig_492_; lean_object* v_config_493_; lean_object* v_toLeanConfig_494_; lean_object* v_weakLinkArgs_495_; lean_object* v_weakLinkArgs_496_; lean_object* v___x_497_; 
v_pkg_490_ = lean_ctor_get(v_self_489_, 0);
v_config_491_ = lean_ctor_get(v_pkg_490_, 6);
v_toLeanConfig_492_ = lean_ctor_get(v_config_491_, 1);
lean_inc_ref(v_toLeanConfig_492_);
v_config_493_ = lean_ctor_get(v_self_489_, 2);
lean_inc(v_config_493_);
lean_dec_ref(v_self_489_);
v_toLeanConfig_494_ = lean_ctor_get(v_config_493_, 0);
lean_inc_ref(v_toLeanConfig_494_);
lean_dec(v_config_493_);
v_weakLinkArgs_495_ = lean_ctor_get(v_toLeanConfig_492_, 9);
lean_inc_ref(v_weakLinkArgs_495_);
lean_dec_ref(v_toLeanConfig_492_);
v_weakLinkArgs_496_ = lean_ctor_get(v_toLeanConfig_494_, 9);
lean_inc_ref(v_weakLinkArgs_496_);
lean_dec_ref(v_toLeanConfig_494_);
v___x_497_ = l_Array_append___redArg(v_weakLinkArgs_495_, v_weakLinkArgs_496_);
lean_dec_ref(v_weakLinkArgs_496_);
return v___x_497_;
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
