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
v_precompileModules_230_ = lean_ctor_get_uint8(v_config_229_, sizeof(void*)*9 + 1);
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
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent(lean_object* v_self_234_){
_start:
{
lean_object* v_config_235_; lean_object* v_toLeanConfig_236_; lean_object* v_platformIndependent_237_; 
v_config_235_ = lean_ctor_get(v_self_234_, 2);
v_toLeanConfig_236_ = lean_ctor_get(v_config_235_, 0);
v_platformIndependent_237_ = lean_ctor_get(v_toLeanConfig_236_, 10);
if (lean_obj_tag(v_platformIndependent_237_) == 0)
{
lean_object* v_pkg_238_; lean_object* v_config_239_; lean_object* v_toLeanConfig_240_; lean_object* v_platformIndependent_241_; 
v_pkg_238_ = lean_ctor_get(v_self_234_, 0);
v_config_239_ = lean_ctor_get(v_pkg_238_, 6);
v_toLeanConfig_240_ = lean_ctor_get(v_config_239_, 1);
v_platformIndependent_241_ = lean_ctor_get(v_toLeanConfig_240_, 10);
lean_inc(v_platformIndependent_241_);
return v_platformIndependent_241_;
}
else
{
lean_inc_ref(v_platformIndependent_237_);
return v_platformIndependent_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent___boxed(lean_object* v_self_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lake_LeanLib_platformIndependent(v_self_242_);
lean_dec_ref(v_self_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets(lean_object* v_self_244_){
_start:
{
lean_object* v_config_245_; lean_object* v_defaultFacets_246_; 
v_config_245_ = lean_ctor_get(v_self_244_, 2);
v_defaultFacets_246_ = lean_ctor_get(v_config_245_, 7);
lean_inc_ref(v_defaultFacets_246_);
return v_defaultFacets_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets___boxed(lean_object* v_self_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lake_LeanLib_defaultFacets(v_self_247_);
lean_dec_ref(v_self_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets(lean_object* v_self_249_, uint8_t v_shouldExport_250_){
_start:
{
lean_object* v_config_251_; lean_object* v_nativeFacets_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_config_251_ = lean_ctor_get(v_self_249_, 2);
lean_inc(v_config_251_);
lean_dec_ref(v_self_249_);
v_nativeFacets_252_ = lean_ctor_get(v_config_251_, 8);
lean_inc_ref(v_nativeFacets_252_);
lean_dec(v_config_251_);
v___x_253_ = lean_box(v_shouldExport_250_);
v___x_254_ = lean_apply_1(v_nativeFacets_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets___boxed(lean_object* v_self_255_, lean_object* v_shouldExport_256_){
_start:
{
uint8_t v_shouldExport_boxed_257_; lean_object* v_res_258_; 
v_shouldExport_boxed_257_ = lean_unbox(v_shouldExport_256_);
v_res_258_ = l_Lake_LeanLib_nativeFacets(v_self_255_, v_shouldExport_boxed_257_);
return v_res_258_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_buildType(lean_object* v_self_259_){
_start:
{
lean_object* v_pkg_260_; lean_object* v_config_261_; lean_object* v_toLeanConfig_262_; lean_object* v_config_263_; lean_object* v_toLeanConfig_264_; uint8_t v_buildType_265_; uint8_t v_buildType_266_; uint8_t v___x_267_; 
v_pkg_260_ = lean_ctor_get(v_self_259_, 0);
v_config_261_ = lean_ctor_get(v_pkg_260_, 6);
v_toLeanConfig_262_ = lean_ctor_get(v_config_261_, 1);
v_config_263_ = lean_ctor_get(v_self_259_, 2);
v_toLeanConfig_264_ = lean_ctor_get(v_config_263_, 0);
v_buildType_265_ = lean_ctor_get_uint8(v_toLeanConfig_262_, sizeof(void*)*13);
v_buildType_266_ = lean_ctor_get_uint8(v_toLeanConfig_264_, sizeof(void*)*13);
v___x_267_ = l_Lake_instOrdBuildType_ord(v_buildType_265_, v_buildType_266_);
if (v___x_267_ == 2)
{
return v_buildType_266_;
}
else
{
return v_buildType_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_buildType___boxed(lean_object* v_self_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lake_LeanLib_buildType(v_self_268_);
lean_dec_ref(v_self_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions(lean_object* v_self_271_){
_start:
{
lean_object* v_pkg_272_; lean_object* v_config_273_; lean_object* v_toLeanConfig_274_; lean_object* v_config_275_; lean_object* v_toLeanConfig_276_; uint8_t v_buildType_277_; lean_object* v_leanOptions_278_; lean_object* v_moreServerOptions_279_; uint8_t v_buildType_280_; lean_object* v_leanOptions_281_; lean_object* v_moreServerOptions_282_; lean_object* v___x_283_; uint8_t v___y_285_; uint8_t v___x_293_; 
v_pkg_272_ = lean_ctor_get(v_self_271_, 0);
v_config_273_ = lean_ctor_get(v_pkg_272_, 6);
v_toLeanConfig_274_ = lean_ctor_get(v_config_273_, 1);
v_config_275_ = lean_ctor_get(v_self_271_, 2);
v_toLeanConfig_276_ = lean_ctor_get(v_config_275_, 0);
v_buildType_277_ = lean_ctor_get_uint8(v_toLeanConfig_274_, sizeof(void*)*13);
v_leanOptions_278_ = lean_ctor_get(v_toLeanConfig_274_, 0);
v_moreServerOptions_279_ = lean_ctor_get(v_toLeanConfig_274_, 4);
v_buildType_280_ = lean_ctor_get_uint8(v_toLeanConfig_276_, sizeof(void*)*13);
v_leanOptions_281_ = lean_ctor_get(v_toLeanConfig_276_, 0);
v_moreServerOptions_282_ = lean_ctor_get(v_toLeanConfig_276_, 4);
v___x_283_ = lean_box(1);
v___x_293_ = l_Lake_instOrdBuildType_ord(v_buildType_277_, v_buildType_280_);
if (v___x_293_ == 2)
{
v___y_285_ = v_buildType_280_;
goto v___jp_284_;
}
else
{
v___y_285_ = v_buildType_277_;
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_286_ = l_Lake_BuildType_leanOptions(v___y_285_);
v___x_287_ = l_Lean_LeanOptions_append(v___x_283_, v___x_286_);
v___x_288_ = l_Lean_LeanOptions_ofArray(v_leanOptions_278_);
v___x_289_ = l_Lean_LeanOptions_appendArray(v___x_288_, v_moreServerOptions_279_);
v___x_290_ = l_Lean_LeanOptions_append(v___x_287_, v___x_289_);
v___x_291_ = l_Lean_LeanOptions_appendArray(v___x_290_, v_leanOptions_281_);
v___x_292_ = l_Lean_LeanOptions_appendArray(v___x_291_, v_moreServerOptions_282_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions___boxed(lean_object* v_self_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_LeanLib_serverOptions(v_self_294_);
lean_dec_ref(v_self_294_);
return v_res_295_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_backend(lean_object* v_self_296_){
_start:
{
lean_object* v_config_297_; lean_object* v_toLeanConfig_298_; lean_object* v_pkg_299_; lean_object* v_config_300_; lean_object* v_toLeanConfig_301_; uint8_t v_backend_302_; uint8_t v_backend_303_; uint8_t v___x_304_; 
v_config_297_ = lean_ctor_get(v_self_296_, 2);
v_toLeanConfig_298_ = lean_ctor_get(v_config_297_, 0);
v_pkg_299_ = lean_ctor_get(v_self_296_, 0);
v_config_300_ = lean_ctor_get(v_pkg_299_, 6);
v_toLeanConfig_301_ = lean_ctor_get(v_config_300_, 1);
v_backend_302_ = lean_ctor_get_uint8(v_toLeanConfig_298_, sizeof(void*)*13 + 1);
v_backend_303_ = lean_ctor_get_uint8(v_toLeanConfig_301_, sizeof(void*)*13 + 1);
v___x_304_ = l_Lake_Backend_orPreferLeft(v_backend_302_, v_backend_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_backend___boxed(lean_object* v_self_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lake_LeanLib_backend(v_self_305_);
lean_dec_ref(v_self_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowImportAll(lean_object* v_self_308_){
_start:
{
lean_object* v_config_309_; uint8_t v_allowImportAll_310_; 
v_config_309_ = lean_ctor_get(v_self_308_, 2);
v_allowImportAll_310_ = lean_ctor_get_uint8(v_config_309_, sizeof(void*)*9 + 2);
if (v_allowImportAll_310_ == 0)
{
lean_object* v_pkg_311_; lean_object* v_config_312_; uint8_t v_allowImportAll_313_; 
v_pkg_311_ = lean_ctor_get(v_self_308_, 0);
v_config_312_ = lean_ctor_get(v_pkg_311_, 6);
v_allowImportAll_313_ = lean_ctor_get_uint8(v_config_312_, sizeof(void*)*28 + 5);
return v_allowImportAll_313_;
}
else
{
return v_allowImportAll_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowImportAll___boxed(lean_object* v_self_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Lake_LeanLib_allowImportAll(v_self_314_);
lean_dec_ref(v_self_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_requiresModuleSystem(lean_object* v_self_317_){
_start:
{
lean_object* v_config_318_; lean_object* v_toLeanConfig_319_; uint8_t v_requiresModuleSystem_320_; 
v_config_318_ = lean_ctor_get(v_self_317_, 2);
v_toLeanConfig_319_ = lean_ctor_get(v_config_318_, 0);
v_requiresModuleSystem_320_ = lean_ctor_get_uint8(v_toLeanConfig_319_, sizeof(void*)*13 + 2);
if (v_requiresModuleSystem_320_ == 0)
{
lean_object* v_pkg_321_; lean_object* v_config_322_; lean_object* v_toLeanConfig_323_; uint8_t v_requiresModuleSystem_324_; 
v_pkg_321_ = lean_ctor_get(v_self_317_, 0);
v_config_322_ = lean_ctor_get(v_pkg_321_, 6);
v_toLeanConfig_323_ = lean_ctor_get(v_config_322_, 1);
v_requiresModuleSystem_324_ = lean_ctor_get_uint8(v_toLeanConfig_323_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_324_;
}
else
{
return v_requiresModuleSystem_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_requiresModuleSystem___boxed(lean_object* v_self_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Lake_LeanLib_requiresModuleSystem(v_self_325_);
lean_dec_ref(v_self_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowNonModules(lean_object* v_self_328_){
_start:
{
lean_object* v_config_329_; lean_object* v_toLeanConfig_330_; uint8_t v_allowNonModules_331_; 
v_config_329_ = lean_ctor_get(v_self_328_, 2);
v_toLeanConfig_330_ = lean_ctor_get(v_config_329_, 0);
v_allowNonModules_331_ = lean_ctor_get_uint8(v_toLeanConfig_330_, sizeof(void*)*13 + 3);
if (v_allowNonModules_331_ == 0)
{
lean_object* v_pkg_332_; lean_object* v_config_333_; lean_object* v_toLeanConfig_334_; uint8_t v_allowNonModules_335_; 
v_pkg_332_ = lean_ctor_get(v_self_328_, 0);
v_config_333_ = lean_ctor_get(v_pkg_332_, 6);
v_toLeanConfig_334_ = lean_ctor_get(v_config_333_, 1);
v_allowNonModules_335_ = lean_ctor_get_uint8(v_toLeanConfig_334_, sizeof(void*)*13 + 3);
return v_allowNonModules_335_;
}
else
{
return v_allowNonModules_331_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowNonModules___boxed(lean_object* v_self_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lake_LeanLib_allowNonModules(v_self_336_);
lean_dec_ref(v_self_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_dynlibs(lean_object* v_self_339_){
_start:
{
lean_object* v_pkg_340_; lean_object* v_config_341_; lean_object* v_toLeanConfig_342_; lean_object* v_config_343_; lean_object* v_toLeanConfig_344_; lean_object* v_dynlibs_345_; lean_object* v_dynlibs_346_; lean_object* v___x_347_; 
v_pkg_340_ = lean_ctor_get(v_self_339_, 0);
v_config_341_ = lean_ctor_get(v_pkg_340_, 6);
v_toLeanConfig_342_ = lean_ctor_get(v_config_341_, 1);
lean_inc_ref(v_toLeanConfig_342_);
v_config_343_ = lean_ctor_get(v_self_339_, 2);
lean_inc(v_config_343_);
lean_dec_ref(v_self_339_);
v_toLeanConfig_344_ = lean_ctor_get(v_config_343_, 0);
lean_inc_ref(v_toLeanConfig_344_);
lean_dec(v_config_343_);
v_dynlibs_345_ = lean_ctor_get(v_toLeanConfig_342_, 11);
lean_inc_ref(v_dynlibs_345_);
lean_dec_ref(v_toLeanConfig_342_);
v_dynlibs_346_ = lean_ctor_get(v_toLeanConfig_344_, 11);
lean_inc_ref(v_dynlibs_346_);
lean_dec_ref(v_toLeanConfig_344_);
v___x_347_ = l_Array_append___redArg(v_dynlibs_345_, v_dynlibs_346_);
lean_dec_ref(v_dynlibs_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_plugins(lean_object* v_self_348_){
_start:
{
lean_object* v_pkg_349_; lean_object* v_config_350_; lean_object* v_toLeanConfig_351_; lean_object* v_config_352_; lean_object* v_toLeanConfig_353_; lean_object* v_plugins_354_; lean_object* v_plugins_355_; lean_object* v___x_356_; 
v_pkg_349_ = lean_ctor_get(v_self_348_, 0);
v_config_350_ = lean_ctor_get(v_pkg_349_, 6);
v_toLeanConfig_351_ = lean_ctor_get(v_config_350_, 1);
lean_inc_ref(v_toLeanConfig_351_);
v_config_352_ = lean_ctor_get(v_self_348_, 2);
lean_inc(v_config_352_);
lean_dec_ref(v_self_348_);
v_toLeanConfig_353_ = lean_ctor_get(v_config_352_, 0);
lean_inc_ref(v_toLeanConfig_353_);
lean_dec(v_config_352_);
v_plugins_354_ = lean_ctor_get(v_toLeanConfig_351_, 12);
lean_inc_ref(v_plugins_354_);
lean_dec_ref(v_toLeanConfig_351_);
v_plugins_355_ = lean_ctor_get(v_toLeanConfig_353_, 12);
lean_inc_ref(v_plugins_355_);
lean_dec_ref(v_toLeanConfig_353_);
v___x_356_ = l_Array_append___redArg(v_plugins_354_, v_plugins_355_);
lean_dec_ref(v_plugins_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions(lean_object* v_self_357_){
_start:
{
lean_object* v_pkg_358_; lean_object* v_config_359_; lean_object* v_toLeanConfig_360_; lean_object* v_config_361_; lean_object* v_toLeanConfig_362_; uint8_t v_buildType_363_; lean_object* v_leanOptions_364_; uint8_t v_buildType_365_; lean_object* v_leanOptions_366_; uint8_t v___y_368_; uint8_t v___x_373_; 
v_pkg_358_ = lean_ctor_get(v_self_357_, 0);
v_config_359_ = lean_ctor_get(v_pkg_358_, 6);
v_toLeanConfig_360_ = lean_ctor_get(v_config_359_, 1);
v_config_361_ = lean_ctor_get(v_self_357_, 2);
v_toLeanConfig_362_ = lean_ctor_get(v_config_361_, 0);
v_buildType_363_ = lean_ctor_get_uint8(v_toLeanConfig_360_, sizeof(void*)*13);
v_leanOptions_364_ = lean_ctor_get(v_toLeanConfig_360_, 0);
v_buildType_365_ = lean_ctor_get_uint8(v_toLeanConfig_362_, sizeof(void*)*13);
v_leanOptions_366_ = lean_ctor_get(v_toLeanConfig_362_, 0);
v___x_373_ = l_Lake_instOrdBuildType_ord(v_buildType_363_, v_buildType_365_);
if (v___x_373_ == 2)
{
v___y_368_ = v_buildType_365_;
goto v___jp_367_;
}
else
{
v___y_368_ = v_buildType_363_;
goto v___jp_367_;
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = l_Lake_BuildType_leanOptions(v___y_368_);
v___x_370_ = l_Lean_LeanOptions_ofArray(v_leanOptions_364_);
v___x_371_ = l_Lean_LeanOptions_append(v___x_369_, v___x_370_);
v___x_372_ = l_Lean_LeanOptions_appendArray(v___x_371_, v_leanOptions_366_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions___boxed(lean_object* v_self_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lake_LeanLib_leanOptions(v_self_374_);
lean_dec_ref(v_self_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs(lean_object* v_self_376_){
_start:
{
lean_object* v_pkg_377_; lean_object* v_config_378_; lean_object* v_toLeanConfig_379_; lean_object* v_config_380_; lean_object* v_toLeanConfig_381_; uint8_t v_buildType_382_; lean_object* v_moreLeanArgs_383_; uint8_t v_buildType_384_; lean_object* v_moreLeanArgs_385_; uint8_t v___y_387_; uint8_t v___x_391_; 
v_pkg_377_ = lean_ctor_get(v_self_376_, 0);
v_config_378_ = lean_ctor_get(v_pkg_377_, 6);
v_toLeanConfig_379_ = lean_ctor_get(v_config_378_, 1);
v_config_380_ = lean_ctor_get(v_self_376_, 2);
v_toLeanConfig_381_ = lean_ctor_get(v_config_380_, 0);
v_buildType_382_ = lean_ctor_get_uint8(v_toLeanConfig_379_, sizeof(void*)*13);
v_moreLeanArgs_383_ = lean_ctor_get(v_toLeanConfig_379_, 1);
v_buildType_384_ = lean_ctor_get_uint8(v_toLeanConfig_381_, sizeof(void*)*13);
v_moreLeanArgs_385_ = lean_ctor_get(v_toLeanConfig_381_, 1);
v___x_391_ = l_Lake_instOrdBuildType_ord(v_buildType_382_, v_buildType_384_);
if (v___x_391_ == 2)
{
v___y_387_ = v_buildType_384_;
goto v___jp_386_;
}
else
{
v___y_387_ = v_buildType_382_;
goto v___jp_386_;
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = l_Lake_BuildType_leanArgs(v___y_387_);
v___x_389_ = l_Array_append___redArg(v___x_388_, v_moreLeanArgs_383_);
v___x_390_ = l_Array_append___redArg(v___x_389_, v_moreLeanArgs_385_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs___boxed(lean_object* v_self_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_LeanLib_leanArgs(v_self_392_);
lean_dec_ref(v_self_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeanArgs(lean_object* v_self_394_){
_start:
{
lean_object* v_pkg_395_; lean_object* v_config_396_; lean_object* v_toLeanConfig_397_; lean_object* v_config_398_; lean_object* v_toLeanConfig_399_; lean_object* v_weakLeanArgs_400_; lean_object* v_weakLeanArgs_401_; lean_object* v___x_402_; 
v_pkg_395_ = lean_ctor_get(v_self_394_, 0);
v_config_396_ = lean_ctor_get(v_pkg_395_, 6);
v_toLeanConfig_397_ = lean_ctor_get(v_config_396_, 1);
lean_inc_ref(v_toLeanConfig_397_);
v_config_398_ = lean_ctor_get(v_self_394_, 2);
lean_inc(v_config_398_);
lean_dec_ref(v_self_394_);
v_toLeanConfig_399_ = lean_ctor_get(v_config_398_, 0);
lean_inc_ref(v_toLeanConfig_399_);
lean_dec(v_config_398_);
v_weakLeanArgs_400_ = lean_ctor_get(v_toLeanConfig_397_, 2);
lean_inc_ref(v_weakLeanArgs_400_);
lean_dec_ref(v_toLeanConfig_397_);
v_weakLeanArgs_401_ = lean_ctor_get(v_toLeanConfig_399_, 2);
lean_inc_ref(v_weakLeanArgs_401_);
lean_dec_ref(v_toLeanConfig_399_);
v___x_402_ = l_Array_append___redArg(v_weakLeanArgs_400_, v_weakLeanArgs_401_);
lean_dec_ref(v_weakLeanArgs_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs(lean_object* v_self_403_){
_start:
{
lean_object* v_pkg_404_; lean_object* v_config_405_; lean_object* v_toLeanConfig_406_; lean_object* v_config_407_; lean_object* v_toLeanConfig_408_; uint8_t v_buildType_409_; lean_object* v_moreLeancArgs_410_; uint8_t v_buildType_411_; lean_object* v_moreLeancArgs_412_; uint8_t v___y_414_; uint8_t v___x_418_; 
v_pkg_404_ = lean_ctor_get(v_self_403_, 0);
v_config_405_ = lean_ctor_get(v_pkg_404_, 6);
v_toLeanConfig_406_ = lean_ctor_get(v_config_405_, 1);
v_config_407_ = lean_ctor_get(v_self_403_, 2);
v_toLeanConfig_408_ = lean_ctor_get(v_config_407_, 0);
v_buildType_409_ = lean_ctor_get_uint8(v_toLeanConfig_406_, sizeof(void*)*13);
v_moreLeancArgs_410_ = lean_ctor_get(v_toLeanConfig_406_, 3);
v_buildType_411_ = lean_ctor_get_uint8(v_toLeanConfig_408_, sizeof(void*)*13);
v_moreLeancArgs_412_ = lean_ctor_get(v_toLeanConfig_408_, 3);
v___x_418_ = l_Lake_instOrdBuildType_ord(v_buildType_409_, v_buildType_411_);
if (v___x_418_ == 2)
{
v___y_414_ = v_buildType_411_;
goto v___jp_413_;
}
else
{
v___y_414_ = v_buildType_409_;
goto v___jp_413_;
}
v___jp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = l_Lake_BuildType_leancArgs(v___y_414_);
v___x_416_ = l_Array_append___redArg(v___x_415_, v_moreLeancArgs_410_);
v___x_417_ = l_Array_append___redArg(v___x_416_, v_moreLeancArgs_412_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs___boxed(lean_object* v_self_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lake_LeanLib_leancArgs(v_self_419_);
lean_dec_ref(v_self_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeancArgs(lean_object* v_self_421_){
_start:
{
lean_object* v_pkg_422_; lean_object* v_config_423_; lean_object* v_toLeanConfig_424_; lean_object* v_config_425_; lean_object* v_toLeanConfig_426_; lean_object* v_weakLeancArgs_427_; lean_object* v_weakLeancArgs_428_; lean_object* v___x_429_; 
v_pkg_422_ = lean_ctor_get(v_self_421_, 0);
v_config_423_ = lean_ctor_get(v_pkg_422_, 6);
v_toLeanConfig_424_ = lean_ctor_get(v_config_423_, 1);
lean_inc_ref(v_toLeanConfig_424_);
v_config_425_ = lean_ctor_get(v_self_421_, 2);
lean_inc(v_config_425_);
lean_dec_ref(v_self_421_);
v_toLeanConfig_426_ = lean_ctor_get(v_config_425_, 0);
lean_inc_ref(v_toLeanConfig_426_);
lean_dec(v_config_425_);
v_weakLeancArgs_427_ = lean_ctor_get(v_toLeanConfig_424_, 5);
lean_inc_ref(v_weakLeancArgs_427_);
lean_dec_ref(v_toLeanConfig_424_);
v_weakLeancArgs_428_ = lean_ctor_get(v_toLeanConfig_426_, 5);
lean_inc_ref(v_weakLeancArgs_428_);
lean_dec_ref(v_toLeanConfig_426_);
v___x_429_ = l_Array_append___redArg(v_weakLeancArgs_427_, v_weakLeancArgs_428_);
lean_dec_ref(v_weakLeancArgs_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkObjs(lean_object* v_self_430_){
_start:
{
lean_object* v_pkg_431_; lean_object* v_config_432_; lean_object* v_toLeanConfig_433_; lean_object* v_config_434_; lean_object* v_toLeanConfig_435_; lean_object* v_moreLinkObjs_436_; lean_object* v_moreLinkObjs_437_; lean_object* v___x_438_; 
v_pkg_431_ = lean_ctor_get(v_self_430_, 0);
v_config_432_ = lean_ctor_get(v_pkg_431_, 6);
v_toLeanConfig_433_ = lean_ctor_get(v_config_432_, 1);
lean_inc_ref(v_toLeanConfig_433_);
v_config_434_ = lean_ctor_get(v_self_430_, 2);
lean_inc(v_config_434_);
lean_dec_ref(v_self_430_);
v_toLeanConfig_435_ = lean_ctor_get(v_config_434_, 0);
lean_inc_ref(v_toLeanConfig_435_);
lean_dec(v_config_434_);
v_moreLinkObjs_436_ = lean_ctor_get(v_toLeanConfig_433_, 6);
lean_inc_ref(v_moreLinkObjs_436_);
lean_dec_ref(v_toLeanConfig_433_);
v_moreLinkObjs_437_ = lean_ctor_get(v_toLeanConfig_435_, 6);
lean_inc_ref(v_moreLinkObjs_437_);
lean_dec_ref(v_toLeanConfig_435_);
v___x_438_ = l_Array_append___redArg(v_moreLinkObjs_436_, v_moreLinkObjs_437_);
lean_dec_ref(v_moreLinkObjs_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkLibs(lean_object* v_self_439_){
_start:
{
lean_object* v_pkg_440_; lean_object* v_config_441_; lean_object* v_toLeanConfig_442_; lean_object* v_config_443_; lean_object* v_toLeanConfig_444_; lean_object* v_moreLinkLibs_445_; lean_object* v_moreLinkLibs_446_; lean_object* v___x_447_; 
v_pkg_440_ = lean_ctor_get(v_self_439_, 0);
v_config_441_ = lean_ctor_get(v_pkg_440_, 6);
v_toLeanConfig_442_ = lean_ctor_get(v_config_441_, 1);
lean_inc_ref(v_toLeanConfig_442_);
v_config_443_ = lean_ctor_get(v_self_439_, 2);
lean_inc(v_config_443_);
lean_dec_ref(v_self_439_);
v_toLeanConfig_444_ = lean_ctor_get(v_config_443_, 0);
lean_inc_ref(v_toLeanConfig_444_);
lean_dec(v_config_443_);
v_moreLinkLibs_445_ = lean_ctor_get(v_toLeanConfig_442_, 7);
lean_inc_ref(v_moreLinkLibs_445_);
lean_dec_ref(v_toLeanConfig_442_);
v_moreLinkLibs_446_ = lean_ctor_get(v_toLeanConfig_444_, 7);
lean_inc_ref(v_moreLinkLibs_446_);
lean_dec_ref(v_toLeanConfig_444_);
v___x_447_ = l_Array_append___redArg(v_moreLinkLibs_445_, v_moreLinkLibs_446_);
lean_dec_ref(v_moreLinkLibs_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_linkArgs(lean_object* v_self_448_){
_start:
{
lean_object* v_pkg_449_; lean_object* v_config_450_; lean_object* v_toLeanConfig_451_; lean_object* v_config_452_; lean_object* v_toLeanConfig_453_; lean_object* v_moreLinkArgs_454_; lean_object* v_moreLinkArgs_455_; lean_object* v___x_456_; 
v_pkg_449_ = lean_ctor_get(v_self_448_, 0);
v_config_450_ = lean_ctor_get(v_pkg_449_, 6);
v_toLeanConfig_451_ = lean_ctor_get(v_config_450_, 1);
lean_inc_ref(v_toLeanConfig_451_);
v_config_452_ = lean_ctor_get(v_self_448_, 2);
lean_inc(v_config_452_);
lean_dec_ref(v_self_448_);
v_toLeanConfig_453_ = lean_ctor_get(v_config_452_, 0);
lean_inc_ref(v_toLeanConfig_453_);
lean_dec(v_config_452_);
v_moreLinkArgs_454_ = lean_ctor_get(v_toLeanConfig_451_, 8);
lean_inc_ref(v_moreLinkArgs_454_);
lean_dec_ref(v_toLeanConfig_451_);
v_moreLinkArgs_455_ = lean_ctor_get(v_toLeanConfig_453_, 8);
lean_inc_ref(v_moreLinkArgs_455_);
lean_dec_ref(v_toLeanConfig_453_);
v___x_456_ = l_Array_append___redArg(v_moreLinkArgs_454_, v_moreLinkArgs_455_);
lean_dec_ref(v_moreLinkArgs_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLinkArgs(lean_object* v_self_457_){
_start:
{
lean_object* v_pkg_458_; lean_object* v_config_459_; lean_object* v_toLeanConfig_460_; lean_object* v_config_461_; lean_object* v_toLeanConfig_462_; lean_object* v_weakLinkArgs_463_; lean_object* v_weakLinkArgs_464_; lean_object* v___x_465_; 
v_pkg_458_ = lean_ctor_get(v_self_457_, 0);
v_config_459_ = lean_ctor_get(v_pkg_458_, 6);
v_toLeanConfig_460_ = lean_ctor_get(v_config_459_, 1);
lean_inc_ref(v_toLeanConfig_460_);
v_config_461_ = lean_ctor_get(v_self_457_, 2);
lean_inc(v_config_461_);
lean_dec_ref(v_self_457_);
v_toLeanConfig_462_ = lean_ctor_get(v_config_461_, 0);
lean_inc_ref(v_toLeanConfig_462_);
lean_dec(v_config_461_);
v_weakLinkArgs_463_ = lean_ctor_get(v_toLeanConfig_460_, 9);
lean_inc_ref(v_weakLinkArgs_463_);
lean_dec_ref(v_toLeanConfig_460_);
v_weakLinkArgs_464_ = lean_ctor_get(v_toLeanConfig_462_, 9);
lean_inc_ref(v_weakLinkArgs_464_);
lean_dec_ref(v_toLeanConfig_462_);
v___x_465_ = l_Array_append___redArg(v_weakLinkArgs_463_, v_weakLinkArgs_464_);
lean_dec_ref(v_weakLinkArgs_464_);
return v___x_465_;
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
