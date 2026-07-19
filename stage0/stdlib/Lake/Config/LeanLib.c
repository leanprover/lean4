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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v___x_47_; lean_object* v___f_48_; uint8_t v___x_49_; 
v___x_47_ = ((lean_object*)(l_Lake_Package_leanLibs___closed__12));
v___f_48_ = lean_alloc_closure((void*)(l_Lake_Package_leanLibs___lam__0___boxed), 4, 2);
lean_closure_set(v___f_48_, 0, v___x_47_);
lean_closure_set(v___f_48_, 1, v_self_40_);
v___x_49_ = lean_nat_dec_le(v___x_44_, v___x_44_);
if (v___x_49_ == 0)
{
if (v___x_46_ == 0)
{
lean_dec_ref(v___f_48_);
lean_dec_ref(v_targetDecls_41_);
return v___x_43_;
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_44_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_45_, v___f_48_, v_targetDecls_41_, v___x_50_, v___x_51_, v___x_43_);
return v___x_52_;
}
}
else
{
size_t v___x_53_; size_t v___x_54_; lean_object* v___x_55_; 
v___x_53_ = ((size_t)0ULL);
v___x_54_ = lean_usize_of_nat(v___x_44_);
v___x_55_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_45_, v___f_48_, v_targetDecls_41_, v___x_53_, v___x_54_, v___x_43_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanLib_x3f(lean_object* v_name_56_, lean_object* v_self_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lake_Package_findTargetDecl_x3f(v_name_56_, v_self_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v___x_59_; 
lean_dec_ref(v_self_57_);
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_74_; 
v_val_60_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_62_ = v___x_58_;
v_isShared_63_ = v_isSharedCheck_74_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v___x_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_74_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_name_64_; lean_object* v_kind_65_; lean_object* v_config_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_name_64_ = lean_ctor_get(v_val_60_, 1);
lean_inc(v_name_64_);
v_kind_65_ = lean_ctor_get(v_val_60_, 2);
lean_inc(v_kind_65_);
v_config_66_ = lean_ctor_get(v_val_60_, 3);
lean_inc(v_config_66_);
lean_dec(v_val_60_);
v___x_67_ = ((lean_object*)(l_Lake_Package_leanLibs___closed__12));
v___x_68_ = lean_name_eq(v_kind_65_, v___x_67_);
lean_dec(v_kind_65_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec(v_config_66_);
lean_dec(v_name_64_);
lean_del_object(v___x_62_);
lean_dec_ref(v_self_57_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v_self_57_);
lean_ctor_set(v___x_70_, 1, v_name_64_);
lean_ctor_set(v___x_70_, 2, v_config_66_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_70_);
v___x_72_ = v___x_62_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findLeanLib_x3f___boxed(lean_object* v_name_75_, lean_object* v_self_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lake_Package_findLeanLib_x3f(v_name_75_, v_self_76_);
lean_dec(v_name_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_config(lean_object* v_self_78_){
_start:
{
lean_object* v_config_79_; 
v_config_79_ = lean_ctor_get(v_self_78_, 2);
lean_inc(v_config_79_);
return v_config_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_config___boxed(lean_object* v_self_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lake_LeanLib_config(v_self_80_);
lean_dec_ref(v_self_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_srcDir(lean_object* v_self_82_){
_start:
{
lean_object* v_pkg_83_; lean_object* v_config_84_; lean_object* v_config_85_; lean_object* v_dir_86_; lean_object* v_srcDir_87_; lean_object* v_srcDir_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_pkg_83_ = lean_ctor_get(v_self_82_, 0);
lean_inc_ref(v_pkg_83_);
v_config_84_ = lean_ctor_get(v_pkg_83_, 6);
lean_inc_ref(v_config_84_);
v_config_85_ = lean_ctor_get(v_self_82_, 2);
lean_inc(v_config_85_);
lean_dec_ref(v_self_82_);
v_dir_86_ = lean_ctor_get(v_pkg_83_, 4);
lean_inc_ref(v_dir_86_);
lean_dec_ref(v_pkg_83_);
v_srcDir_87_ = lean_ctor_get(v_config_84_, 4);
lean_inc_ref(v_srcDir_87_);
lean_dec_ref(v_config_84_);
v_srcDir_88_ = lean_ctor_get(v_config_85_, 1);
lean_inc_ref(v_srcDir_88_);
lean_dec(v_config_85_);
v___x_89_ = l_System_FilePath_normalize(v_srcDir_87_);
v___x_90_ = l_Lake_joinRelative(v_dir_86_, v___x_89_);
v___x_91_ = l_System_FilePath_normalize(v_srcDir_88_);
v___x_92_ = l_Lake_joinRelative(v___x_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootDir(lean_object* v_self_93_){
_start:
{
lean_object* v_pkg_94_; lean_object* v_config_95_; lean_object* v_config_96_; lean_object* v_dir_97_; lean_object* v_srcDir_98_; lean_object* v_srcDir_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_pkg_94_ = lean_ctor_get(v_self_93_, 0);
lean_inc_ref(v_pkg_94_);
v_config_95_ = lean_ctor_get(v_pkg_94_, 6);
lean_inc_ref(v_config_95_);
v_config_96_ = lean_ctor_get(v_self_93_, 2);
lean_inc(v_config_96_);
lean_dec_ref(v_self_93_);
v_dir_97_ = lean_ctor_get(v_pkg_94_, 4);
lean_inc_ref(v_dir_97_);
lean_dec_ref(v_pkg_94_);
v_srcDir_98_ = lean_ctor_get(v_config_95_, 4);
lean_inc_ref(v_srcDir_98_);
lean_dec_ref(v_config_95_);
v_srcDir_99_ = lean_ctor_get(v_config_96_, 1);
lean_inc_ref(v_srcDir_99_);
lean_dec(v_config_96_);
v___x_100_ = l_System_FilePath_normalize(v_srcDir_98_);
v___x_101_ = l_Lake_joinRelative(v_dir_97_, v___x_100_);
v___x_102_ = l_System_FilePath_normalize(v_srcDir_99_);
v___x_103_ = l_Lake_joinRelative(v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_roots(lean_object* v_self_104_){
_start:
{
lean_object* v_config_105_; lean_object* v_roots_106_; 
v_config_105_ = lean_ctor_get(v_self_104_, 2);
v_roots_106_ = lean_ctor_get(v_config_105_, 2);
lean_inc_ref(v_roots_106_);
return v_roots_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_roots___boxed(lean_object* v_self_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lake_LeanLib_roots(v_self_107_);
lean_dec_ref(v_self_107_);
return v_res_108_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_isLocalModule(lean_object* v_mod_109_, lean_object* v_self_110_){
_start:
{
lean_object* v_config_111_; uint8_t v___x_112_; 
v_config_111_ = lean_ctor_get(v_self_110_, 2);
v___x_112_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_109_, v_config_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isLocalModule___boxed(lean_object* v_mod_113_, lean_object* v_self_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lake_LeanLib_isLocalModule(v_mod_113_, v_self_114_);
lean_dec_ref(v_self_114_);
lean_dec(v_mod_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_isBuildableModule(lean_object* v_mod_117_, lean_object* v_self_118_){
_start:
{
lean_object* v_config_119_; uint8_t v___x_120_; 
v_config_119_ = lean_ctor_get(v_self_118_, 2);
v___x_120_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_117_, v_config_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_isBuildableModule___boxed(lean_object* v_mod_121_, lean_object* v_self_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lake_LeanLib_isBuildableModule(v_mod_121_, v_self_122_);
lean_dec_ref(v_self_122_);
lean_dec(v_mod_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_libPrefixOnWindows(lean_object* v_self_125_){
_start:
{
lean_object* v_config_126_; uint8_t v_libPrefixOnWindows_127_; 
v_config_126_ = lean_ctor_get(v_self_125_, 2);
v_libPrefixOnWindows_127_ = lean_ctor_get_uint8(v_config_126_, sizeof(void*)*9);
if (v_libPrefixOnWindows_127_ == 0)
{
lean_object* v_pkg_128_; lean_object* v_config_129_; uint8_t v_libPrefixOnWindows_130_; 
v_pkg_128_ = lean_ctor_get(v_self_125_, 0);
v_config_129_ = lean_ctor_get(v_pkg_128_, 6);
v_libPrefixOnWindows_130_ = lean_ctor_get_uint8(v_config_129_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_130_;
}
else
{
return v_libPrefixOnWindows_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_libPrefixOnWindows___boxed(lean_object* v_self_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lake_LeanLib_libPrefixOnWindows(v_self_131_);
lean_dec_ref(v_self_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_libName(lean_object* v_self_135_){
_start:
{
lean_object* v___y_137_; lean_object* v_config_141_; lean_object* v_pkg_142_; lean_object* v_name_143_; lean_object* v_libName_144_; uint8_t v_libPrefixOnWindows_145_; lean_object* v___y_147_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_config_141_ = lean_ctor_get(v_self_135_, 2);
lean_inc(v_config_141_);
v_pkg_142_ = lean_ctor_get(v_self_135_, 0);
lean_inc_ref(v_pkg_142_);
v_name_143_ = lean_ctor_get(v_self_135_, 1);
lean_inc(v_name_143_);
lean_dec_ref(v_self_135_);
v_libName_144_ = lean_ctor_get(v_config_141_, 4);
lean_inc_ref(v_libName_144_);
v_libPrefixOnWindows_145_ = lean_ctor_get_uint8(v_config_141_, sizeof(void*)*9);
lean_dec(v_config_141_);
v___x_150_ = lean_string_utf8_byte_size(v_libName_144_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_nat_dec_eq(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_name_143_);
v___y_147_ = v_libName_144_;
goto v___jp_146_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v_libName_144_);
lean_inc_ref(v_pkg_142_);
v___x_153_ = l_Lake_Package_id_x3f(v_pkg_142_);
v___x_154_ = l_Lean_mkModuleInitializationStem(v_name_143_, v___x_153_);
lean_dec(v___x_153_);
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
v___jp_136_:
{
uint8_t v___x_138_; 
v___x_138_ = l_System_Platform_isWindows;
if (v___x_138_ == 0)
{
return v___y_137_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lake_LeanLib_libName___closed__0));
v___x_140_ = lean_string_append(v___x_139_, v___y_137_);
lean_dec_ref(v___y_137_);
return v___x_140_;
}
}
v___jp_146_:
{
if (v_libPrefixOnWindows_145_ == 0)
{
lean_object* v_config_148_; uint8_t v_libPrefixOnWindows_149_; 
v_config_148_ = lean_ctor_get(v_pkg_142_, 6);
lean_inc_ref(v_config_148_);
lean_dec_ref(v_pkg_142_);
v_libPrefixOnWindows_149_ = lean_ctor_get_uint8(v_config_148_, sizeof(void*)*27 + 4);
lean_dec_ref(v_config_148_);
if (v_libPrefixOnWindows_149_ == 0)
{
return v___y_147_;
}
else
{
v___y_137_ = v___y_147_;
goto v___jp_136_;
}
}
else
{
lean_dec_ref(v_pkg_142_);
v___y_137_ = v___y_147_;
goto v___jp_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFileName(lean_object* v_self_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; 
v___x_156_ = l_Lake_LeanLib_libName(v_self_155_);
v___x_157_ = 0;
v___x_158_ = l_Lake_nameToStaticLib(v___x_156_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticLibFile(lean_object* v_self_159_){
_start:
{
lean_object* v_pkg_160_; lean_object* v_config_161_; lean_object* v_dir_162_; lean_object* v_buildDir_163_; lean_object* v_nativeLibDir_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_pkg_160_ = lean_ctor_get(v_self_159_, 0);
v_config_161_ = lean_ctor_get(v_pkg_160_, 6);
v_dir_162_ = lean_ctor_get(v_pkg_160_, 4);
v_buildDir_163_ = lean_ctor_get(v_config_161_, 5);
v_nativeLibDir_164_ = lean_ctor_get(v_config_161_, 7);
lean_inc_ref(v_buildDir_163_);
v___x_165_ = l_System_FilePath_normalize(v_buildDir_163_);
lean_inc_ref(v_dir_162_);
v___x_166_ = l_Lake_joinRelative(v_dir_162_, v___x_165_);
lean_inc_ref(v_nativeLibDir_164_);
v___x_167_ = l_System_FilePath_normalize(v_nativeLibDir_164_);
v___x_168_ = l_Lake_joinRelative(v___x_166_, v___x_167_);
v___x_169_ = l_Lake_LeanLib_libName(v_self_159_);
v___x_170_ = 0;
v___x_171_ = l_Lake_nameToStaticLib(v___x_169_, v___x_170_);
v___x_172_ = l_Lake_joinRelative(v___x_168_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportLibFile(lean_object* v_self_174_){
_start:
{
lean_object* v_pkg_175_; lean_object* v_config_176_; lean_object* v_dir_177_; lean_object* v_buildDir_178_; lean_object* v_nativeLibDir_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_pkg_175_ = lean_ctor_get(v_self_174_, 0);
v_config_176_ = lean_ctor_get(v_pkg_175_, 6);
v_dir_177_ = lean_ctor_get(v_pkg_175_, 4);
v_buildDir_178_ = lean_ctor_get(v_config_176_, 5);
v_nativeLibDir_179_ = lean_ctor_get(v_config_176_, 7);
lean_inc_ref(v_buildDir_178_);
v___x_180_ = l_System_FilePath_normalize(v_buildDir_178_);
lean_inc_ref(v_dir_177_);
v___x_181_ = l_Lake_joinRelative(v_dir_177_, v___x_180_);
lean_inc_ref(v_nativeLibDir_179_);
v___x_182_ = l_System_FilePath_normalize(v_nativeLibDir_179_);
v___x_183_ = l_Lake_joinRelative(v___x_181_, v___x_182_);
v___x_184_ = l_Lake_LeanLib_libName(v_self_174_);
v___x_185_ = 0;
v___x_186_ = l_Lake_nameToStaticLib(v___x_184_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lake_LeanLib_staticExportLibFile___closed__0));
v___x_188_ = l_System_FilePath_addExtension(v___x_186_, v___x_187_);
v___x_189_ = l_Lake_joinRelative(v___x_183_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFileName(lean_object* v_self_190_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; 
v___x_191_ = l_Lake_LeanLib_libName(v_self_190_);
v___x_192_ = 0;
v___x_193_ = l_Lake_nameToSharedLib(v___x_191_, v___x_192_);
lean_dec_ref(v___x_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedLibFile(lean_object* v_self_194_){
_start:
{
lean_object* v_pkg_195_; lean_object* v_config_196_; lean_object* v_dir_197_; lean_object* v_buildDir_198_; lean_object* v_nativeLibDir_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_pkg_195_ = lean_ctor_get(v_self_194_, 0);
v_config_196_ = lean_ctor_get(v_pkg_195_, 6);
v_dir_197_ = lean_ctor_get(v_pkg_195_, 4);
v_buildDir_198_ = lean_ctor_get(v_config_196_, 5);
v_nativeLibDir_199_ = lean_ctor_get(v_config_196_, 7);
lean_inc_ref(v_buildDir_198_);
v___x_200_ = l_System_FilePath_normalize(v_buildDir_198_);
lean_inc_ref(v_dir_197_);
v___x_201_ = l_Lake_joinRelative(v_dir_197_, v___x_200_);
lean_inc_ref(v_nativeLibDir_199_);
v___x_202_ = l_System_FilePath_normalize(v_nativeLibDir_199_);
v___x_203_ = l_Lake_joinRelative(v___x_201_, v___x_202_);
v___x_204_ = l_Lake_LeanLib_libName(v_self_194_);
v___x_205_ = 0;
v___x_206_ = l_Lake_nameToSharedLib(v___x_204_, v___x_205_);
lean_dec_ref(v___x_204_);
v___x_207_ = l_Lake_joinRelative(v___x_203_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_isPlugin(lean_object* v_self_208_){
_start:
{
lean_object* v_config_209_; lean_object* v_pkg_210_; lean_object* v_roots_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_config_209_ = lean_ctor_get(v_self_208_, 2);
v_pkg_210_ = lean_ctor_get(v_self_208_, 0);
lean_inc_ref(v_pkg_210_);
v_roots_211_ = lean_ctor_get(v_config_209_, 2);
lean_inc_ref(v_roots_211_);
v___x_212_ = lean_array_get_size(v_roots_211_);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_dec_eq(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec_ref(v_roots_211_);
lean_dec_ref(v_pkg_210_);
lean_dec_ref(v_self_208_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_215_ = l_Lake_LeanLib_libName(v_self_208_);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_fget(v_roots_211_, v___x_216_);
lean_dec_ref(v_roots_211_);
v___x_218_ = l_Lake_Package_id_x3f(v_pkg_210_);
v___x_219_ = l_Lean_mkModuleInitializationStem(v___x_217_, v___x_218_);
lean_dec(v___x_218_);
v___x_220_ = lean_string_dec_eq(v___x_215_, v___x_219_);
lean_dec_ref(v___x_219_);
lean_dec_ref(v___x_215_);
return v___x_220_;
}
}
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
LEAN_EXPORT uint8_t l_Lake_LeanLib_precompileModules(lean_object* v_self_229_){
_start:
{
lean_object* v_pkg_230_; lean_object* v_config_231_; uint8_t v_precompileModules_232_; 
v_pkg_230_ = lean_ctor_get(v_self_229_, 0);
v_config_231_ = lean_ctor_get(v_pkg_230_, 6);
v_precompileModules_232_ = lean_ctor_get_uint8(v_config_231_, sizeof(void*)*27 + 1);
if (v_precompileModules_232_ == 0)
{
lean_object* v_config_233_; uint8_t v_precompileModules_234_; 
v_config_233_ = lean_ctor_get(v_self_229_, 2);
v_precompileModules_234_ = lean_ctor_get_uint8(v_config_233_, sizeof(void*)*9 + 1);
return v_precompileModules_234_;
}
else
{
return v_precompileModules_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_precompileModules___boxed(lean_object* v_self_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lake_LeanLib_precompileModules(v_self_235_);
lean_dec_ref(v_self_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent(lean_object* v_self_238_){
_start:
{
lean_object* v_config_239_; lean_object* v_toLeanConfig_240_; lean_object* v_platformIndependent_241_; 
v_config_239_ = lean_ctor_get(v_self_238_, 2);
v_toLeanConfig_240_ = lean_ctor_get(v_config_239_, 0);
v_platformIndependent_241_ = lean_ctor_get(v_toLeanConfig_240_, 10);
if (lean_obj_tag(v_platformIndependent_241_) == 0)
{
lean_object* v_pkg_242_; lean_object* v_config_243_; lean_object* v_toLeanConfig_244_; lean_object* v_platformIndependent_245_; 
v_pkg_242_ = lean_ctor_get(v_self_238_, 0);
v_config_243_ = lean_ctor_get(v_pkg_242_, 6);
v_toLeanConfig_244_ = lean_ctor_get(v_config_243_, 1);
v_platformIndependent_245_ = lean_ctor_get(v_toLeanConfig_244_, 10);
lean_inc(v_platformIndependent_245_);
return v_platformIndependent_245_;
}
else
{
lean_inc_ref(v_platformIndependent_241_);
return v_platformIndependent_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_platformIndependent___boxed(lean_object* v_self_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_LeanLib_platformIndependent(v_self_246_);
lean_dec_ref(v_self_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets(lean_object* v_self_248_){
_start:
{
lean_object* v_config_249_; lean_object* v_defaultFacets_250_; 
v_config_249_ = lean_ctor_get(v_self_248_, 2);
v_defaultFacets_250_ = lean_ctor_get(v_config_249_, 7);
lean_inc_ref(v_defaultFacets_250_);
return v_defaultFacets_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacets___boxed(lean_object* v_self_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_LeanLib_defaultFacets(v_self_251_);
lean_dec_ref(v_self_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets(lean_object* v_self_253_, uint8_t v_shouldExport_254_){
_start:
{
lean_object* v_config_255_; lean_object* v_nativeFacets_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_config_255_ = lean_ctor_get(v_self_253_, 2);
lean_inc(v_config_255_);
lean_dec_ref(v_self_253_);
v_nativeFacets_256_ = lean_ctor_get(v_config_255_, 8);
lean_inc_ref(v_nativeFacets_256_);
lean_dec(v_config_255_);
v___x_257_ = lean_box(v_shouldExport_254_);
v___x_258_ = lean_apply_1(v_nativeFacets_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_nativeFacets___boxed(lean_object* v_self_259_, lean_object* v_shouldExport_260_){
_start:
{
uint8_t v_shouldExport_boxed_261_; lean_object* v_res_262_; 
v_shouldExport_boxed_261_ = lean_unbox(v_shouldExport_260_);
v_res_262_ = l_Lake_LeanLib_nativeFacets(v_self_259_, v_shouldExport_boxed_261_);
return v_res_262_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_buildType(lean_object* v_self_263_){
_start:
{
lean_object* v_pkg_264_; lean_object* v_config_265_; lean_object* v_toLeanConfig_266_; lean_object* v_config_267_; lean_object* v_toLeanConfig_268_; uint8_t v_buildType_269_; uint8_t v_buildType_270_; uint8_t v___x_271_; 
v_pkg_264_ = lean_ctor_get(v_self_263_, 0);
v_config_265_ = lean_ctor_get(v_pkg_264_, 6);
v_toLeanConfig_266_ = lean_ctor_get(v_config_265_, 1);
v_config_267_ = lean_ctor_get(v_self_263_, 2);
v_toLeanConfig_268_ = lean_ctor_get(v_config_267_, 0);
v_buildType_269_ = lean_ctor_get_uint8(v_toLeanConfig_266_, sizeof(void*)*13);
v_buildType_270_ = lean_ctor_get_uint8(v_toLeanConfig_268_, sizeof(void*)*13);
v___x_271_ = l_Lake_instOrdBuildType_ord(v_buildType_269_, v_buildType_270_);
if (v___x_271_ == 2)
{
return v_buildType_270_;
}
else
{
return v_buildType_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_buildType___boxed(lean_object* v_self_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Lake_LeanLib_buildType(v_self_272_);
lean_dec_ref(v_self_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions(lean_object* v_self_275_){
_start:
{
lean_object* v_pkg_276_; lean_object* v_config_277_; lean_object* v_toLeanConfig_278_; lean_object* v_config_279_; lean_object* v_toLeanConfig_280_; uint8_t v_buildType_281_; lean_object* v_leanOptions_282_; lean_object* v_moreServerOptions_283_; uint8_t v_buildType_284_; lean_object* v_leanOptions_285_; lean_object* v_moreServerOptions_286_; lean_object* v___x_287_; uint8_t v___y_289_; uint8_t v___x_297_; 
v_pkg_276_ = lean_ctor_get(v_self_275_, 0);
v_config_277_ = lean_ctor_get(v_pkg_276_, 6);
v_toLeanConfig_278_ = lean_ctor_get(v_config_277_, 1);
v_config_279_ = lean_ctor_get(v_self_275_, 2);
v_toLeanConfig_280_ = lean_ctor_get(v_config_279_, 0);
v_buildType_281_ = lean_ctor_get_uint8(v_toLeanConfig_278_, sizeof(void*)*13);
v_leanOptions_282_ = lean_ctor_get(v_toLeanConfig_278_, 0);
v_moreServerOptions_283_ = lean_ctor_get(v_toLeanConfig_278_, 4);
v_buildType_284_ = lean_ctor_get_uint8(v_toLeanConfig_280_, sizeof(void*)*13);
v_leanOptions_285_ = lean_ctor_get(v_toLeanConfig_280_, 0);
v_moreServerOptions_286_ = lean_ctor_get(v_toLeanConfig_280_, 4);
v___x_287_ = lean_box(1);
v___x_297_ = l_Lake_instOrdBuildType_ord(v_buildType_281_, v_buildType_284_);
if (v___x_297_ == 2)
{
v___y_289_ = v_buildType_284_;
goto v___jp_288_;
}
else
{
v___y_289_ = v_buildType_281_;
goto v___jp_288_;
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_290_ = l_Lake_BuildType_leanOptions(v___y_289_);
v___x_291_ = l_Lean_LeanOptions_append(v___x_287_, v___x_290_);
v___x_292_ = l_Lean_LeanOptions_ofArray(v_leanOptions_282_);
v___x_293_ = l_Lean_LeanOptions_appendArray(v___x_292_, v_moreServerOptions_283_);
v___x_294_ = l_Lean_LeanOptions_append(v___x_291_, v___x_293_);
v___x_295_ = l_Lean_LeanOptions_appendArray(v___x_294_, v_leanOptions_285_);
v___x_296_ = l_Lean_LeanOptions_appendArray(v___x_295_, v_moreServerOptions_286_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_serverOptions___boxed(lean_object* v_self_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lake_LeanLib_serverOptions(v_self_298_);
lean_dec_ref(v_self_298_);
return v_res_299_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_backend(lean_object* v_self_300_){
_start:
{
lean_object* v_config_301_; lean_object* v_toLeanConfig_302_; lean_object* v_pkg_303_; lean_object* v_config_304_; lean_object* v_toLeanConfig_305_; uint8_t v_backend_306_; uint8_t v_backend_307_; uint8_t v___x_308_; 
v_config_301_ = lean_ctor_get(v_self_300_, 2);
v_toLeanConfig_302_ = lean_ctor_get(v_config_301_, 0);
v_pkg_303_ = lean_ctor_get(v_self_300_, 0);
v_config_304_ = lean_ctor_get(v_pkg_303_, 6);
v_toLeanConfig_305_ = lean_ctor_get(v_config_304_, 1);
v_backend_306_ = lean_ctor_get_uint8(v_toLeanConfig_302_, sizeof(void*)*13 + 1);
v_backend_307_ = lean_ctor_get_uint8(v_toLeanConfig_305_, sizeof(void*)*13 + 1);
v___x_308_ = l_Lake_Backend_orPreferLeft(v_backend_306_, v_backend_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_backend___boxed(lean_object* v_self_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lake_LeanLib_backend(v_self_309_);
lean_dec_ref(v_self_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowImportAll(lean_object* v_self_312_){
_start:
{
lean_object* v_config_313_; uint8_t v_allowImportAll_314_; 
v_config_313_ = lean_ctor_get(v_self_312_, 2);
v_allowImportAll_314_ = lean_ctor_get_uint8(v_config_313_, sizeof(void*)*9 + 2);
if (v_allowImportAll_314_ == 0)
{
lean_object* v_pkg_315_; lean_object* v_config_316_; uint8_t v_allowImportAll_317_; 
v_pkg_315_ = lean_ctor_get(v_self_312_, 0);
v_config_316_ = lean_ctor_get(v_pkg_315_, 6);
v_allowImportAll_317_ = lean_ctor_get_uint8(v_config_316_, sizeof(void*)*27 + 5);
return v_allowImportAll_317_;
}
else
{
return v_allowImportAll_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowImportAll___boxed(lean_object* v_self_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Lake_LeanLib_allowImportAll(v_self_318_);
lean_dec_ref(v_self_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_requiresModuleSystem(lean_object* v_self_321_){
_start:
{
lean_object* v_config_322_; lean_object* v_toLeanConfig_323_; uint8_t v_requiresModuleSystem_324_; 
v_config_322_ = lean_ctor_get(v_self_321_, 2);
v_toLeanConfig_323_ = lean_ctor_get(v_config_322_, 0);
v_requiresModuleSystem_324_ = lean_ctor_get_uint8(v_toLeanConfig_323_, sizeof(void*)*13 + 2);
if (v_requiresModuleSystem_324_ == 0)
{
lean_object* v_pkg_325_; lean_object* v_config_326_; lean_object* v_toLeanConfig_327_; uint8_t v_requiresModuleSystem_328_; 
v_pkg_325_ = lean_ctor_get(v_self_321_, 0);
v_config_326_ = lean_ctor_get(v_pkg_325_, 6);
v_toLeanConfig_327_ = lean_ctor_get(v_config_326_, 1);
v_requiresModuleSystem_328_ = lean_ctor_get_uint8(v_toLeanConfig_327_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_328_;
}
else
{
return v_requiresModuleSystem_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_requiresModuleSystem___boxed(lean_object* v_self_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Lake_LeanLib_requiresModuleSystem(v_self_329_);
lean_dec_ref(v_self_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_allowNonModules(lean_object* v_self_332_){
_start:
{
lean_object* v_config_333_; lean_object* v_toLeanConfig_334_; uint8_t v_allowNonModules_335_; 
v_config_333_ = lean_ctor_get(v_self_332_, 2);
v_toLeanConfig_334_ = lean_ctor_get(v_config_333_, 0);
v_allowNonModules_335_ = lean_ctor_get_uint8(v_toLeanConfig_334_, sizeof(void*)*13 + 3);
if (v_allowNonModules_335_ == 0)
{
lean_object* v_pkg_336_; lean_object* v_config_337_; lean_object* v_toLeanConfig_338_; uint8_t v_allowNonModules_339_; 
v_pkg_336_ = lean_ctor_get(v_self_332_, 0);
v_config_337_ = lean_ctor_get(v_pkg_336_, 6);
v_toLeanConfig_338_ = lean_ctor_get(v_config_337_, 1);
v_allowNonModules_339_ = lean_ctor_get_uint8(v_toLeanConfig_338_, sizeof(void*)*13 + 3);
return v_allowNonModules_339_;
}
else
{
return v_allowNonModules_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_allowNonModules___boxed(lean_object* v_self_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Lake_LeanLib_allowNonModules(v_self_340_);
lean_dec_ref(v_self_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_dynlibs(lean_object* v_self_343_){
_start:
{
lean_object* v_pkg_344_; lean_object* v_config_345_; lean_object* v_toLeanConfig_346_; lean_object* v_config_347_; lean_object* v_toLeanConfig_348_; lean_object* v_dynlibs_349_; lean_object* v_dynlibs_350_; lean_object* v___x_351_; 
v_pkg_344_ = lean_ctor_get(v_self_343_, 0);
v_config_345_ = lean_ctor_get(v_pkg_344_, 6);
v_toLeanConfig_346_ = lean_ctor_get(v_config_345_, 1);
lean_inc_ref(v_toLeanConfig_346_);
v_config_347_ = lean_ctor_get(v_self_343_, 2);
lean_inc(v_config_347_);
lean_dec_ref(v_self_343_);
v_toLeanConfig_348_ = lean_ctor_get(v_config_347_, 0);
lean_inc_ref(v_toLeanConfig_348_);
lean_dec(v_config_347_);
v_dynlibs_349_ = lean_ctor_get(v_toLeanConfig_346_, 11);
lean_inc_ref(v_dynlibs_349_);
lean_dec_ref(v_toLeanConfig_346_);
v_dynlibs_350_ = lean_ctor_get(v_toLeanConfig_348_, 11);
lean_inc_ref(v_dynlibs_350_);
lean_dec_ref(v_toLeanConfig_348_);
v___x_351_ = l_Array_append___redArg(v_dynlibs_349_, v_dynlibs_350_);
lean_dec_ref(v_dynlibs_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_plugins(lean_object* v_self_352_){
_start:
{
lean_object* v_pkg_353_; lean_object* v_config_354_; lean_object* v_toLeanConfig_355_; lean_object* v_config_356_; lean_object* v_toLeanConfig_357_; lean_object* v_plugins_358_; lean_object* v_plugins_359_; lean_object* v___x_360_; 
v_pkg_353_ = lean_ctor_get(v_self_352_, 0);
v_config_354_ = lean_ctor_get(v_pkg_353_, 6);
v_toLeanConfig_355_ = lean_ctor_get(v_config_354_, 1);
lean_inc_ref(v_toLeanConfig_355_);
v_config_356_ = lean_ctor_get(v_self_352_, 2);
lean_inc(v_config_356_);
lean_dec_ref(v_self_352_);
v_toLeanConfig_357_ = lean_ctor_get(v_config_356_, 0);
lean_inc_ref(v_toLeanConfig_357_);
lean_dec(v_config_356_);
v_plugins_358_ = lean_ctor_get(v_toLeanConfig_355_, 12);
lean_inc_ref(v_plugins_358_);
lean_dec_ref(v_toLeanConfig_355_);
v_plugins_359_ = lean_ctor_get(v_toLeanConfig_357_, 12);
lean_inc_ref(v_plugins_359_);
lean_dec_ref(v_toLeanConfig_357_);
v___x_360_ = l_Array_append___redArg(v_plugins_358_, v_plugins_359_);
lean_dec_ref(v_plugins_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions(lean_object* v_self_361_){
_start:
{
lean_object* v_pkg_362_; lean_object* v_config_363_; lean_object* v_toLeanConfig_364_; lean_object* v_config_365_; lean_object* v_toLeanConfig_366_; uint8_t v_buildType_367_; lean_object* v_leanOptions_368_; uint8_t v_buildType_369_; lean_object* v_leanOptions_370_; uint8_t v___y_372_; uint8_t v___x_377_; 
v_pkg_362_ = lean_ctor_get(v_self_361_, 0);
v_config_363_ = lean_ctor_get(v_pkg_362_, 6);
v_toLeanConfig_364_ = lean_ctor_get(v_config_363_, 1);
v_config_365_ = lean_ctor_get(v_self_361_, 2);
v_toLeanConfig_366_ = lean_ctor_get(v_config_365_, 0);
v_buildType_367_ = lean_ctor_get_uint8(v_toLeanConfig_364_, sizeof(void*)*13);
v_leanOptions_368_ = lean_ctor_get(v_toLeanConfig_364_, 0);
v_buildType_369_ = lean_ctor_get_uint8(v_toLeanConfig_366_, sizeof(void*)*13);
v_leanOptions_370_ = lean_ctor_get(v_toLeanConfig_366_, 0);
v___x_377_ = l_Lake_instOrdBuildType_ord(v_buildType_367_, v_buildType_369_);
if (v___x_377_ == 2)
{
v___y_372_ = v_buildType_369_;
goto v___jp_371_;
}
else
{
v___y_372_ = v_buildType_367_;
goto v___jp_371_;
}
v___jp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = l_Lake_BuildType_leanOptions(v___y_372_);
v___x_374_ = l_Lean_LeanOptions_ofArray(v_leanOptions_368_);
v___x_375_ = l_Lean_LeanOptions_append(v___x_373_, v___x_374_);
v___x_376_ = l_Lean_LeanOptions_appendArray(v___x_375_, v_leanOptions_370_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanOptions___boxed(lean_object* v_self_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_LeanLib_leanOptions(v_self_378_);
lean_dec_ref(v_self_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs(lean_object* v_self_380_){
_start:
{
lean_object* v_pkg_381_; lean_object* v_config_382_; lean_object* v_toLeanConfig_383_; lean_object* v_config_384_; lean_object* v_toLeanConfig_385_; uint8_t v_buildType_386_; lean_object* v_moreLeanArgs_387_; uint8_t v_buildType_388_; lean_object* v_moreLeanArgs_389_; uint8_t v___y_391_; uint8_t v___x_395_; 
v_pkg_381_ = lean_ctor_get(v_self_380_, 0);
v_config_382_ = lean_ctor_get(v_pkg_381_, 6);
v_toLeanConfig_383_ = lean_ctor_get(v_config_382_, 1);
v_config_384_ = lean_ctor_get(v_self_380_, 2);
v_toLeanConfig_385_ = lean_ctor_get(v_config_384_, 0);
v_buildType_386_ = lean_ctor_get_uint8(v_toLeanConfig_383_, sizeof(void*)*13);
v_moreLeanArgs_387_ = lean_ctor_get(v_toLeanConfig_383_, 1);
v_buildType_388_ = lean_ctor_get_uint8(v_toLeanConfig_385_, sizeof(void*)*13);
v_moreLeanArgs_389_ = lean_ctor_get(v_toLeanConfig_385_, 1);
v___x_395_ = l_Lake_instOrdBuildType_ord(v_buildType_386_, v_buildType_388_);
if (v___x_395_ == 2)
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
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = l_Lake_BuildType_leanArgs(v___y_391_);
v___x_393_ = l_Array_append___redArg(v___x_392_, v_moreLeanArgs_387_);
v___x_394_ = l_Array_append___redArg(v___x_393_, v_moreLeanArgs_389_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArgs___boxed(lean_object* v_self_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lake_LeanLib_leanArgs(v_self_396_);
lean_dec_ref(v_self_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeanArgs(lean_object* v_self_398_){
_start:
{
lean_object* v_pkg_399_; lean_object* v_config_400_; lean_object* v_toLeanConfig_401_; lean_object* v_config_402_; lean_object* v_toLeanConfig_403_; lean_object* v_weakLeanArgs_404_; lean_object* v_weakLeanArgs_405_; lean_object* v___x_406_; 
v_pkg_399_ = lean_ctor_get(v_self_398_, 0);
v_config_400_ = lean_ctor_get(v_pkg_399_, 6);
v_toLeanConfig_401_ = lean_ctor_get(v_config_400_, 1);
lean_inc_ref(v_toLeanConfig_401_);
v_config_402_ = lean_ctor_get(v_self_398_, 2);
lean_inc(v_config_402_);
lean_dec_ref(v_self_398_);
v_toLeanConfig_403_ = lean_ctor_get(v_config_402_, 0);
lean_inc_ref(v_toLeanConfig_403_);
lean_dec(v_config_402_);
v_weakLeanArgs_404_ = lean_ctor_get(v_toLeanConfig_401_, 2);
lean_inc_ref(v_weakLeanArgs_404_);
lean_dec_ref(v_toLeanConfig_401_);
v_weakLeanArgs_405_ = lean_ctor_get(v_toLeanConfig_403_, 2);
lean_inc_ref(v_weakLeanArgs_405_);
lean_dec_ref(v_toLeanConfig_403_);
v___x_406_ = l_Array_append___redArg(v_weakLeanArgs_404_, v_weakLeanArgs_405_);
lean_dec_ref(v_weakLeanArgs_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs(lean_object* v_self_407_){
_start:
{
lean_object* v_pkg_408_; lean_object* v_config_409_; lean_object* v_toLeanConfig_410_; lean_object* v_config_411_; lean_object* v_toLeanConfig_412_; uint8_t v_buildType_413_; lean_object* v_moreLeancArgs_414_; uint8_t v_buildType_415_; lean_object* v_moreLeancArgs_416_; uint8_t v___y_418_; uint8_t v___x_422_; 
v_pkg_408_ = lean_ctor_get(v_self_407_, 0);
v_config_409_ = lean_ctor_get(v_pkg_408_, 6);
v_toLeanConfig_410_ = lean_ctor_get(v_config_409_, 1);
v_config_411_ = lean_ctor_get(v_self_407_, 2);
v_toLeanConfig_412_ = lean_ctor_get(v_config_411_, 0);
v_buildType_413_ = lean_ctor_get_uint8(v_toLeanConfig_410_, sizeof(void*)*13);
v_moreLeancArgs_414_ = lean_ctor_get(v_toLeanConfig_410_, 3);
v_buildType_415_ = lean_ctor_get_uint8(v_toLeanConfig_412_, sizeof(void*)*13);
v_moreLeancArgs_416_ = lean_ctor_get(v_toLeanConfig_412_, 3);
v___x_422_ = l_Lake_instOrdBuildType_ord(v_buildType_413_, v_buildType_415_);
if (v___x_422_ == 2)
{
v___y_418_ = v_buildType_415_;
goto v___jp_417_;
}
else
{
v___y_418_ = v_buildType_413_;
goto v___jp_417_;
}
v___jp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = l_Lake_BuildType_leancArgs(v___y_418_);
v___x_420_ = l_Array_append___redArg(v___x_419_, v_moreLeancArgs_414_);
v___x_421_ = l_Array_append___redArg(v___x_420_, v_moreLeancArgs_416_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leancArgs___boxed(lean_object* v_self_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lake_LeanLib_leancArgs(v_self_423_);
lean_dec_ref(v_self_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLeancArgs(lean_object* v_self_425_){
_start:
{
lean_object* v_pkg_426_; lean_object* v_config_427_; lean_object* v_toLeanConfig_428_; lean_object* v_config_429_; lean_object* v_toLeanConfig_430_; lean_object* v_weakLeancArgs_431_; lean_object* v_weakLeancArgs_432_; lean_object* v___x_433_; 
v_pkg_426_ = lean_ctor_get(v_self_425_, 0);
v_config_427_ = lean_ctor_get(v_pkg_426_, 6);
v_toLeanConfig_428_ = lean_ctor_get(v_config_427_, 1);
lean_inc_ref(v_toLeanConfig_428_);
v_config_429_ = lean_ctor_get(v_self_425_, 2);
lean_inc(v_config_429_);
lean_dec_ref(v_self_425_);
v_toLeanConfig_430_ = lean_ctor_get(v_config_429_, 0);
lean_inc_ref(v_toLeanConfig_430_);
lean_dec(v_config_429_);
v_weakLeancArgs_431_ = lean_ctor_get(v_toLeanConfig_428_, 5);
lean_inc_ref(v_weakLeancArgs_431_);
lean_dec_ref(v_toLeanConfig_428_);
v_weakLeancArgs_432_ = lean_ctor_get(v_toLeanConfig_430_, 5);
lean_inc_ref(v_weakLeancArgs_432_);
lean_dec_ref(v_toLeanConfig_430_);
v___x_433_ = l_Array_append___redArg(v_weakLeancArgs_431_, v_weakLeancArgs_432_);
lean_dec_ref(v_weakLeancArgs_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkObjs(lean_object* v_self_434_){
_start:
{
lean_object* v_pkg_435_; lean_object* v_config_436_; lean_object* v_toLeanConfig_437_; lean_object* v_config_438_; lean_object* v_toLeanConfig_439_; lean_object* v_moreLinkObjs_440_; lean_object* v_moreLinkObjs_441_; lean_object* v___x_442_; 
v_pkg_435_ = lean_ctor_get(v_self_434_, 0);
v_config_436_ = lean_ctor_get(v_pkg_435_, 6);
v_toLeanConfig_437_ = lean_ctor_get(v_config_436_, 1);
lean_inc_ref(v_toLeanConfig_437_);
v_config_438_ = lean_ctor_get(v_self_434_, 2);
lean_inc(v_config_438_);
lean_dec_ref(v_self_434_);
v_toLeanConfig_439_ = lean_ctor_get(v_config_438_, 0);
lean_inc_ref(v_toLeanConfig_439_);
lean_dec(v_config_438_);
v_moreLinkObjs_440_ = lean_ctor_get(v_toLeanConfig_437_, 6);
lean_inc_ref(v_moreLinkObjs_440_);
lean_dec_ref(v_toLeanConfig_437_);
v_moreLinkObjs_441_ = lean_ctor_get(v_toLeanConfig_439_, 6);
lean_inc_ref(v_moreLinkObjs_441_);
lean_dec_ref(v_toLeanConfig_439_);
v___x_442_ = l_Array_append___redArg(v_moreLinkObjs_440_, v_moreLinkObjs_441_);
lean_dec_ref(v_moreLinkObjs_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_moreLinkLibs(lean_object* v_self_443_){
_start:
{
lean_object* v_pkg_444_; lean_object* v_config_445_; lean_object* v_toLeanConfig_446_; lean_object* v_config_447_; lean_object* v_toLeanConfig_448_; lean_object* v_moreLinkLibs_449_; lean_object* v_moreLinkLibs_450_; lean_object* v___x_451_; 
v_pkg_444_ = lean_ctor_get(v_self_443_, 0);
v_config_445_ = lean_ctor_get(v_pkg_444_, 6);
v_toLeanConfig_446_ = lean_ctor_get(v_config_445_, 1);
lean_inc_ref(v_toLeanConfig_446_);
v_config_447_ = lean_ctor_get(v_self_443_, 2);
lean_inc(v_config_447_);
lean_dec_ref(v_self_443_);
v_toLeanConfig_448_ = lean_ctor_get(v_config_447_, 0);
lean_inc_ref(v_toLeanConfig_448_);
lean_dec(v_config_447_);
v_moreLinkLibs_449_ = lean_ctor_get(v_toLeanConfig_446_, 7);
lean_inc_ref(v_moreLinkLibs_449_);
lean_dec_ref(v_toLeanConfig_446_);
v_moreLinkLibs_450_ = lean_ctor_get(v_toLeanConfig_448_, 7);
lean_inc_ref(v_moreLinkLibs_450_);
lean_dec_ref(v_toLeanConfig_448_);
v___x_451_ = l_Array_append___redArg(v_moreLinkLibs_449_, v_moreLinkLibs_450_);
lean_dec_ref(v_moreLinkLibs_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_linkArgs(lean_object* v_self_452_){
_start:
{
lean_object* v_pkg_453_; lean_object* v_config_454_; lean_object* v_toLeanConfig_455_; lean_object* v_config_456_; lean_object* v_toLeanConfig_457_; lean_object* v_moreLinkArgs_458_; lean_object* v_moreLinkArgs_459_; lean_object* v___x_460_; 
v_pkg_453_ = lean_ctor_get(v_self_452_, 0);
v_config_454_ = lean_ctor_get(v_pkg_453_, 6);
v_toLeanConfig_455_ = lean_ctor_get(v_config_454_, 1);
lean_inc_ref(v_toLeanConfig_455_);
v_config_456_ = lean_ctor_get(v_self_452_, 2);
lean_inc(v_config_456_);
lean_dec_ref(v_self_452_);
v_toLeanConfig_457_ = lean_ctor_get(v_config_456_, 0);
lean_inc_ref(v_toLeanConfig_457_);
lean_dec(v_config_456_);
v_moreLinkArgs_458_ = lean_ctor_get(v_toLeanConfig_455_, 8);
lean_inc_ref(v_moreLinkArgs_458_);
lean_dec_ref(v_toLeanConfig_455_);
v_moreLinkArgs_459_ = lean_ctor_get(v_toLeanConfig_457_, 8);
lean_inc_ref(v_moreLinkArgs_459_);
lean_dec_ref(v_toLeanConfig_457_);
v___x_460_ = l_Array_append___redArg(v_moreLinkArgs_458_, v_moreLinkArgs_459_);
lean_dec_ref(v_moreLinkArgs_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_weakLinkArgs(lean_object* v_self_461_){
_start:
{
lean_object* v_pkg_462_; lean_object* v_config_463_; lean_object* v_toLeanConfig_464_; lean_object* v_config_465_; lean_object* v_toLeanConfig_466_; lean_object* v_weakLinkArgs_467_; lean_object* v_weakLinkArgs_468_; lean_object* v___x_469_; 
v_pkg_462_ = lean_ctor_get(v_self_461_, 0);
v_config_463_ = lean_ctor_get(v_pkg_462_, 6);
v_toLeanConfig_464_ = lean_ctor_get(v_config_463_, 1);
lean_inc_ref(v_toLeanConfig_464_);
v_config_465_ = lean_ctor_get(v_self_461_, 2);
lean_inc(v_config_465_);
lean_dec_ref(v_self_461_);
v_toLeanConfig_466_ = lean_ctor_get(v_config_465_, 0);
lean_inc_ref(v_toLeanConfig_466_);
lean_dec(v_config_465_);
v_weakLinkArgs_467_ = lean_ctor_get(v_toLeanConfig_464_, 9);
lean_inc_ref(v_weakLinkArgs_467_);
lean_dec_ref(v_toLeanConfig_464_);
v_weakLinkArgs_468_ = lean_ctor_get(v_toLeanConfig_466_, 9);
lean_inc_ref(v_weakLinkArgs_468_);
lean_dec_ref(v_toLeanConfig_466_);
v___x_469_ = l_Array_append___redArg(v_weakLinkArgs_467_, v_weakLinkArgs_468_);
lean_dec_ref(v_weakLinkArgs_468_);
return v___x_469_;
}
}
lean_object* runtime_initialize_Lake_Config_ConfigTarget(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanLib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
