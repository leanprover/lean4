// Lean compiler output
// Module: Lake.Config.PackageConfig
// Imports: public import Init.Dynamic public import Lake.Util.Version public import Lake.Config.Pattern public import Lake.Config.LeanConfig public import Lake.Config.WorkspaceConfig meta import all Lake.Config.Meta public import Init.System.Platform import Lake.Config.Meta
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lake_defaultBinDir;
extern lean_object* l_Lake_defaultVersionTags;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_defaultIrDir;
extern lean_object* l_Lake_defaultNativeLibDir;
extern lean_object* l_Lake_defaultLeanLibDir;
extern lean_object* l_Lake_defaultBuildDir;
extern lean_object* l_Lake_defaultPackagesDir;
extern lean_object* l_Lake_LeanConfig___fields;
extern lean_object* l_Lake_WorkspaceConfig___fields;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_instInhabitedPattern_default__1(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedStdVer_default;
extern lean_object* l_System_instInhabitedFilePath_default;
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
extern lean_object* l_Lake_instInhabitedWorkspaceConfig_default;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static const lean_string_object l_Lake_defaultBuildArchive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_defaultBuildArchive___closed__0 = (const lean_object*)&l_Lake_defaultBuildArchive___closed__0_value;
static const lean_string_object l_Lake_defaultBuildArchive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".tar.gz"};
static const lean_object* l_Lake_defaultBuildArchive___closed__1 = (const lean_object*)&l_Lake_defaultBuildArchive___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_defaultBuildArchive(lean_object*);
static const lean_array_object l_Lake_instInhabitedPackageConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedPackageConfig_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__2;
static lean_once_cell_t l_Lake_instInhabitedPackageConfig_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_bootstrap___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_extraDepTargets___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_precompileModules___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_precompileModules___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_precompileModules___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_precompileModules___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_precompileModules___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_srcDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_srcDir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_buildDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_buildDir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_leanLibDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_nativeLibDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_binDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_binDir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_irDir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_irDir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_releaseRepo___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_buildArchive___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_buildArchive___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildArchive___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_buildArchive___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildArchive___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_buildArchive___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_preferReleaseBuild___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_preferReleaseBuild___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_testDriver___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_testDriver___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_testDriverArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_testDriverArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriverArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_testDriverArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriverArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_testDriverArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_lintDriver___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriver___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriver___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriver___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriver___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_lintDriver___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriverArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriverArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriverArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriverArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_lintDriverArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_PackageConfig_version___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_PackageConfig_version___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_version___proj___lam__3___closed__0_value;
static const lean_ctor_object l_Lake_PackageConfig_version___proj___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_version___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__1_value)}};
static const lean_object* l_Lake_PackageConfig_version___proj___lam__3___closed__1 = (const lean_object*)&l_Lake_PackageConfig_version___proj___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_version___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_version___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_version___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_version___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_version___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_version___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_version___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_version___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_version___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_version___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_version___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_version___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_version___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_version___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_version___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_versionTags___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_versionTags___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_description___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_description___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_description___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_description___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_description___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_description___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_description___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_description___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_description___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_description___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_description___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_description___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_description___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_description___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_description___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_description___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_description___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_description___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_keywords___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_keywords___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_keywords___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_keywords___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_keywords___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_keywords___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_keywords___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_keywords___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_keywords___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_keywords___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_keywords___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_homepage___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_homepage___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_homepage___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_homepage___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_homepage___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_homepage___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_homepage___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_homepage___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_homepage___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_homepage___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_homepage___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_license___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_license___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_license___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_license___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_license___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_license___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_license___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_license___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_license___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_license___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_license___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_license___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_license___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_license___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_license___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_license___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_license___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_license___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LICENSE"};
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__0_value;
static const lean_array_object l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__0_value)}};
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_licenseFiles___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_readmeFile___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_reservoir___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_reservoir___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_allowImportAll___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_allowImportAll___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_allowImportAll___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_allowImportAll___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_allowImportAll___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_fixedToolchain___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_fixedToolchain___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_fixedToolchain___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_fixedToolchain___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_fixedToolchain___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value;
static const lean_ctor_object l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_toLeanConfig___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_PackageConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PackageConfig___fields___closed__0 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__0_value;
static const lean_string_object l_Lake_PackageConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bootstrap"};
static const lean_object* l_Lake_PackageConfig___fields___closed__1 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 243, 17, 14, 190, 232, 38, 153)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__2 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__2_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__3 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__3_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__4;
static const lean_string_object l_Lake_PackageConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "extraDepTargets"};
static const lean_object* l_Lake_PackageConfig___fields___closed__5 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(232, 29, 68, 154, 160, 50, 56, 5)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__6 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__6_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__6_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__6_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__7 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__7_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__8;
static const lean_string_object l_Lake_PackageConfig___fields___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileModules"};
static const lean_object* l_Lake_PackageConfig___fields___closed__9 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__9_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__9_value),LEAN_SCALAR_PTR_LITERAL(210, 72, 98, 56, 225, 29, 247, 45)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__10 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__10_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__10_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__10_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__11 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__11_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__12;
static const lean_string_object l_Lake_PackageConfig___fields___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "moreGlobalServerArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__13 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__13_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__13_value),LEAN_SCALAR_PTR_LITERAL(217, 219, 52, 240, 88, 87, 45, 147)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__14 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__14_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__14_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__15 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__15_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__16;
static const lean_string_object l_Lake_PackageConfig___fields___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moreServerArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__17 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__17_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__17_value),LEAN_SCALAR_PTR_LITERAL(48, 197, 113, 7, 119, 120, 175, 89)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__18 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__18_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__18_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__14_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__19 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__19_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__20;
static const lean_string_object l_Lake_PackageConfig___fields___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__21 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__21_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__21_value),LEAN_SCALAR_PTR_LITERAL(82, 241, 97, 48, 55, 77, 36, 145)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__22 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__22_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__22_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__22_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__23 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__23_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__24;
static const lean_string_object l_Lake_PackageConfig___fields___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "buildDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__25 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__25_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__25_value),LEAN_SCALAR_PTR_LITERAL(249, 192, 208, 78, 51, 18, 78, 228)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__26 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__26_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__26_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__26_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__27 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__27_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__28;
static const lean_string_object l_Lake_PackageConfig___fields___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanLibDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__29 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__29_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__29_value),LEAN_SCALAR_PTR_LITERAL(1, 89, 218, 214, 52, 197, 188, 252)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__30 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__30_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__30_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__30_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__31 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__31_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__32;
static const lean_string_object l_Lake_PackageConfig___fields___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeLibDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__33 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__33_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__33_value),LEAN_SCALAR_PTR_LITERAL(82, 8, 215, 104, 60, 212, 87, 97)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__34 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__34_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__34_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__34_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__35 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__35_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__36;
static const lean_string_object l_Lake_PackageConfig___fields___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__37 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__37_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__37_value),LEAN_SCALAR_PTR_LITERAL(76, 64, 142, 71, 135, 199, 112, 75)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__38 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__38_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__38_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__38_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__39 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__39_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__40;
static const lean_string_object l_Lake_PackageConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "irDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__41 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__41_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 157, 139, 154, 172, 117, 115, 135)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__42 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__42_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__42_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__42_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__43 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__43_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__44;
static const lean_string_object l_Lake_PackageConfig___fields___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "releaseRepo"};
static const lean_object* l_Lake_PackageConfig___fields___closed__45 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__45_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__45_value),LEAN_SCALAR_PTR_LITERAL(200, 115, 184, 27, 119, 80, 150, 143)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__46 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__46_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__46_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__46_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__47 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__47_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__48;
static const lean_string_object l_Lake_PackageConfig___fields___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "releaseRepo\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__49 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__49_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__49_value),LEAN_SCALAR_PTR_LITERAL(110, 119, 158, 92, 2, 186, 119, 253)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__50 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__50_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__50_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__46_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__51 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__51_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__52;
static const lean_string_object l_Lake_PackageConfig___fields___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildArchive"};
static const lean_object* l_Lake_PackageConfig___fields___closed__53 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__53_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__53_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 176, 165, 88, 62, 216, 20)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__54 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__54_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__54_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__54_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__55 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__55_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__56;
static const lean_string_object l_Lake_PackageConfig___fields___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "buildArchive\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__57 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__57_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__57_value),LEAN_SCALAR_PTR_LITERAL(206, 154, 251, 129, 245, 231, 210, 109)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__58 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__58_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__58_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__54_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__59 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__59_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__60;
static const lean_string_object l_Lake_PackageConfig___fields___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "preferReleaseBuild"};
static const lean_object* l_Lake_PackageConfig___fields___closed__61 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__61_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__61_value),LEAN_SCALAR_PTR_LITERAL(75, 209, 233, 233, 163, 174, 95, 235)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__62 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__62_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__62_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__62_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__63 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__63_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__64;
static const lean_string_object l_Lake_PackageConfig___fields___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__65 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__65_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__65_value),LEAN_SCALAR_PTR_LITERAL(187, 40, 173, 233, 223, 78, 220, 191)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__66 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__66_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__66_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__66_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__67 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__67_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__68;
static const lean_string_object l_Lake_PackageConfig___fields___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testRunner"};
static const lean_object* l_Lake_PackageConfig___fields___closed__69 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__69_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__69_value),LEAN_SCALAR_PTR_LITERAL(58, 61, 59, 86, 150, 111, 127, 182)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__70 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__70_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__70_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__66_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__71 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__71_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__72;
static const lean_string_object l_Lake_PackageConfig___fields___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__73 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__73_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__73_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 168, 214, 71, 6, 72, 93)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__74 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__74_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__75 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__75_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__76;
static const lean_string_object l_Lake_PackageConfig___fields___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__77 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__77_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__77_value),LEAN_SCALAR_PTR_LITERAL(164, 80, 113, 139, 118, 238, 67, 240)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__78 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__78_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__78_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__78_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__79 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__79_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__80;
static const lean_string_object l_Lake_PackageConfig___fields___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__81 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__81_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__81_value),LEAN_SCALAR_PTR_LITERAL(102, 206, 227, 73, 236, 117, 156, 150)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__82 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__82_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__82_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__82_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__83 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__83_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__84;
static const lean_string_object l_Lake_PackageConfig___fields___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_PackageConfig___fields___closed__85 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__85_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__85_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__86 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__86_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__86_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__86_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__87 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__87_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__88;
static const lean_string_object l_Lake_PackageConfig___fields___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "versionTags"};
static const lean_object* l_Lake_PackageConfig___fields___closed__89 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__89_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__89_value),LEAN_SCALAR_PTR_LITERAL(76, 44, 235, 102, 59, 70, 79, 98)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__90 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__90_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__90_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__90_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__91 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__91_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__92;
static const lean_string_object l_Lake_PackageConfig___fields___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "description"};
static const lean_object* l_Lake_PackageConfig___fields___closed__93 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__93_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__93_value),LEAN_SCALAR_PTR_LITERAL(85, 116, 204, 74, 85, 134, 17, 161)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__94 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__94_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__94_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__94_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__95 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__95_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__96;
static const lean_string_object l_Lake_PackageConfig___fields___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "keywords"};
static const lean_object* l_Lake_PackageConfig___fields___closed__97 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__97_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__97_value),LEAN_SCALAR_PTR_LITERAL(84, 45, 198, 62, 56, 187, 72, 125)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__98 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__98_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__98_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__98_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__99 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__99_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__100;
static const lean_string_object l_Lake_PackageConfig___fields___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "homepage"};
static const lean_object* l_Lake_PackageConfig___fields___closed__101 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__101_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__101_value),LEAN_SCALAR_PTR_LITERAL(73, 148, 206, 183, 90, 222, 74, 16)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__102 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__102_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__102_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__102_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__103 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__103_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__104;
static const lean_string_object l_Lake_PackageConfig___fields___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "license"};
static const lean_object* l_Lake_PackageConfig___fields___closed__105 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__105_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__105_value),LEAN_SCALAR_PTR_LITERAL(149, 142, 81, 8, 241, 47, 83, 51)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__106 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__106_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__106_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__106_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__107 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__107_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__108;
static const lean_string_object l_Lake_PackageConfig___fields___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "licenseFiles"};
static const lean_object* l_Lake_PackageConfig___fields___closed__109 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__109_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__109_value),LEAN_SCALAR_PTR_LITERAL(115, 188, 70, 201, 62, 96, 76, 55)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__110 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__110_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__110_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__110_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__111 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__111_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__112;
static const lean_string_object l_Lake_PackageConfig___fields___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "readmeFile"};
static const lean_object* l_Lake_PackageConfig___fields___closed__113 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__113_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__113_value),LEAN_SCALAR_PTR_LITERAL(86, 68, 195, 254, 204, 64, 41, 249)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__114 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__114_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__114_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__114_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__115 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__115_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__116_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__116;
static const lean_string_object l_Lake_PackageConfig___fields___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__117 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__117_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__117_value),LEAN_SCALAR_PTR_LITERAL(98, 62, 227, 196, 233, 158, 105, 168)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__118 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__118_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__118_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__118_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__119 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__119_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__120;
static const lean_string_object l_Lake_PackageConfig___fields___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "enableArtifactCache\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__121 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__121_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__121_value),LEAN_SCALAR_PTR_LITERAL(190, 150, 150, 100, 20, 242, 199, 174)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__122 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__122_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__122_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__122_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__123 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__123_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__124;
static const lean_string_object l_Lake_PackageConfig___fields___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "enableArtifactCache"};
static const lean_object* l_Lake_PackageConfig___fields___closed__125 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__125_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__125_value),LEAN_SCALAR_PTR_LITERAL(69, 183, 189, 255, 13, 235, 31, 38)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__126 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__126_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__126_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__122_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__127 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__127_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__128;
static const lean_string_object l_Lake_PackageConfig___fields___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "restoreAllArtifacts\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__129 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__129_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__129_value),LEAN_SCALAR_PTR_LITERAL(2, 1, 41, 192, 97, 8, 217, 82)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__130 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__130_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__130_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__130_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__131 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__131_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__132;
static const lean_string_object l_Lake_PackageConfig___fields___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "restoreAllArtifacts"};
static const lean_object* l_Lake_PackageConfig___fields___closed__133 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__133_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__133_value),LEAN_SCALAR_PTR_LITERAL(172, 122, 225, 122, 213, 189, 222, 165)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__134 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__134_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__134_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__130_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__135 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__135_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__136;
static const lean_string_object l_Lake_PackageConfig___fields___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libPrefixOnWindows"};
static const lean_object* l_Lake_PackageConfig___fields___closed__137 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__137_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__137_value),LEAN_SCALAR_PTR_LITERAL(26, 75, 58, 45, 181, 132, 175, 34)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__138 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__138_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__138_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__138_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__139 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__139_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__140;
static const lean_string_object l_Lake_PackageConfig___fields___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l_Lake_PackageConfig___fields___closed__141 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__141_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__141_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__142 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__142_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__142_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__142_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__143 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__143_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__144;
static const lean_string_object l_Lake_PackageConfig___fields___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fixedToolchain"};
static const lean_object* l_Lake_PackageConfig___fields___closed__145 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__145_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__145_value),LEAN_SCALAR_PTR_LITERAL(248, 4, 88, 39, 97, 195, 130, 156)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__146 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__146_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__147 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__147_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__148;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__149;
static const lean_string_object l_Lake_PackageConfig___fields___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toWorkspaceConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__150 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__150_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__150_value),LEAN_SCALAR_PTR_LITERAL(135, 228, 155, 156, 156, 252, 46, 118)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__151 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__151_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__151_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__151_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__152 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__152_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__153;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__154_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__154;
static const lean_string_object l_Lake_PackageConfig___fields___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__155 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__155_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__155_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__156 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__156_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__156_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__156_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__157 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__157_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__158_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__158;
LEAN_EXPORT lean_object* l_Lake_PackageConfig___fields;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_instConfigInfo___closed__0;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__3_value;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__4_value;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__5_value;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__6_value;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_PackageConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_PackageConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_PackageConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__10_value;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_PackageConfig_instConfigInfo___closed__11;
static const lean_closure_object l_Lake_PackageConfig_instConfigInfo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_instConfigInfo___closed__12 = (const lean_object*)&l_Lake_PackageConfig_instConfigInfo___closed__12_value;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_PackageConfig_instConfigInfo___closed__13;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_PackageConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_instConfigInfo___closed__15;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo;
static lean_once_cell_t l_Lake_PackageConfig_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PackageDecl"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(253, 117, 189, 141, 218, 132, 90, 198)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNamePackageDecl = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l_Lake_defaultBuildArchive(lean_object* v_name_3_){
_start:
{
uint8_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_4_ = 0;
v___x_5_ = l_Lean_Name_toString(v_name_3_, v___x_4_);
v___x_6_ = ((lean_object*)(l_Lake_defaultBuildArchive___closed__0));
v___x_7_ = lean_string_append(v___x_5_, v___x_6_);
v___x_8_ = l_System_Platform_target;
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
v___x_10_ = ((lean_object*)(l_Lake_defaultBuildArchive___closed__1));
v___x_11_ = lean_string_append(v___x_9_, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__2(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lake_instInhabitedPattern_default__1(lean_box(0), lean_box(0));
return v___x_15_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__3(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_16_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__2, &l_Lake_instInhabitedPackageConfig_default___closed__2_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__2);
v___x_17_ = l_Lake_instInhabitedStdVer_default;
v___x_18_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_19_ = lean_box(0);
v___x_20_ = l_System_instInhabitedFilePath_default;
v___x_21_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
v___x_22_ = 0;
v___x_23_ = l_Lake_instInhabitedLeanConfig_default;
v___x_24_ = l_Lake_instInhabitedWorkspaceConfig_default;
v___x_25_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_23_);
lean_ctor_set(v___x_25_, 2, v___x_21_);
lean_ctor_set(v___x_25_, 3, v___x_21_);
lean_ctor_set(v___x_25_, 4, v___x_20_);
lean_ctor_set(v___x_25_, 5, v___x_20_);
lean_ctor_set(v___x_25_, 6, v___x_20_);
lean_ctor_set(v___x_25_, 7, v___x_20_);
lean_ctor_set(v___x_25_, 8, v___x_20_);
lean_ctor_set(v___x_25_, 9, v___x_20_);
lean_ctor_set(v___x_25_, 10, v___x_19_);
lean_ctor_set(v___x_25_, 11, v___x_19_);
lean_ctor_set(v___x_25_, 12, v___x_18_);
lean_ctor_set(v___x_25_, 13, v___x_21_);
lean_ctor_set(v___x_25_, 14, v___x_18_);
lean_ctor_set(v___x_25_, 15, v___x_21_);
lean_ctor_set(v___x_25_, 16, v___x_17_);
lean_ctor_set(v___x_25_, 17, v___x_16_);
lean_ctor_set(v___x_25_, 18, v___x_18_);
lean_ctor_set(v___x_25_, 19, v___x_21_);
lean_ctor_set(v___x_25_, 20, v___x_18_);
lean_ctor_set(v___x_25_, 21, v___x_18_);
lean_ctor_set(v___x_25_, 22, v___x_21_);
lean_ctor_set(v___x_25_, 23, v___x_20_);
lean_ctor_set(v___x_25_, 24, v___x_19_);
lean_ctor_set(v___x_25_, 25, v___x_19_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26 + 1, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26 + 2, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26 + 3, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26 + 4, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26 + 5, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*26 + 6, v___x_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__3, &l_Lake_instInhabitedPackageConfig_default___closed__3_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__3);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lake_instInhabitedPackageConfig_default(v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec(v_a_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lake_instInhabitedPackageConfig_default(v_a_32_, v_a_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_instInhabitedPackageConfig(v_a_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec(v_a_35_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__0(lean_object* v_cfg_38_){
_start:
{
uint8_t v_bootstrap_39_; 
v_bootstrap_39_ = lean_ctor_get_uint8(v_cfg_38_, sizeof(void*)*26);
return v_bootstrap_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__0___boxed(lean_object* v_cfg_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lake_PackageConfig_bootstrap___proj___lam__0(v_cfg_40_);
lean_dec_ref(v_cfg_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1(uint8_t v_val_43_, lean_object* v_cfg_44_){
_start:
{
lean_object* v_toWorkspaceConfig_45_; lean_object* v_toLeanConfig_46_; lean_object* v_extraDepTargets_47_; uint8_t v_precompileModules_48_; lean_object* v_moreGlobalServerArgs_49_; lean_object* v_srcDir_50_; lean_object* v_buildDir_51_; lean_object* v_leanLibDir_52_; lean_object* v_nativeLibDir_53_; lean_object* v_binDir_54_; lean_object* v_irDir_55_; lean_object* v_releaseRepo_56_; lean_object* v_buildArchive_57_; uint8_t v_preferReleaseBuild_58_; lean_object* v_testDriver_59_; lean_object* v_testDriverArgs_60_; lean_object* v_lintDriver_61_; lean_object* v_lintDriverArgs_62_; lean_object* v_version_63_; lean_object* v_versionTags_64_; lean_object* v_description_65_; lean_object* v_keywords_66_; lean_object* v_homepage_67_; lean_object* v_license_68_; lean_object* v_licenseFiles_69_; lean_object* v_readmeFile_70_; uint8_t v_reservoir_71_; lean_object* v_enableArtifactCache_x3f_72_; lean_object* v_restoreAllArtifacts_x3f_73_; uint8_t v_libPrefixOnWindows_74_; uint8_t v_allowImportAll_75_; uint8_t v_fixedToolchain_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v_toWorkspaceConfig_45_ = lean_ctor_get(v_cfg_44_, 0);
v_toLeanConfig_46_ = lean_ctor_get(v_cfg_44_, 1);
v_extraDepTargets_47_ = lean_ctor_get(v_cfg_44_, 2);
v_precompileModules_48_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_49_ = lean_ctor_get(v_cfg_44_, 3);
v_srcDir_50_ = lean_ctor_get(v_cfg_44_, 4);
v_buildDir_51_ = lean_ctor_get(v_cfg_44_, 5);
v_leanLibDir_52_ = lean_ctor_get(v_cfg_44_, 6);
v_nativeLibDir_53_ = lean_ctor_get(v_cfg_44_, 7);
v_binDir_54_ = lean_ctor_get(v_cfg_44_, 8);
v_irDir_55_ = lean_ctor_get(v_cfg_44_, 9);
v_releaseRepo_56_ = lean_ctor_get(v_cfg_44_, 10);
v_buildArchive_57_ = lean_ctor_get(v_cfg_44_, 11);
v_preferReleaseBuild_58_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*26 + 2);
v_testDriver_59_ = lean_ctor_get(v_cfg_44_, 12);
v_testDriverArgs_60_ = lean_ctor_get(v_cfg_44_, 13);
v_lintDriver_61_ = lean_ctor_get(v_cfg_44_, 14);
v_lintDriverArgs_62_ = lean_ctor_get(v_cfg_44_, 15);
v_version_63_ = lean_ctor_get(v_cfg_44_, 16);
v_versionTags_64_ = lean_ctor_get(v_cfg_44_, 17);
v_description_65_ = lean_ctor_get(v_cfg_44_, 18);
v_keywords_66_ = lean_ctor_get(v_cfg_44_, 19);
v_homepage_67_ = lean_ctor_get(v_cfg_44_, 20);
v_license_68_ = lean_ctor_get(v_cfg_44_, 21);
v_licenseFiles_69_ = lean_ctor_get(v_cfg_44_, 22);
v_readmeFile_70_ = lean_ctor_get(v_cfg_44_, 23);
v_reservoir_71_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_72_ = lean_ctor_get(v_cfg_44_, 24);
v_restoreAllArtifacts_x3f_73_ = lean_ctor_get(v_cfg_44_, 25);
v_libPrefixOnWindows_74_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*26 + 4);
v_allowImportAll_75_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*26 + 5);
v_fixedToolchain_76_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*26 + 6);
v_isSharedCheck_83_ = !lean_is_exclusive(v_cfg_44_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v_cfg_44_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_73_);
lean_inc(v_enableArtifactCache_x3f_72_);
lean_inc(v_readmeFile_70_);
lean_inc(v_licenseFiles_69_);
lean_inc(v_license_68_);
lean_inc(v_homepage_67_);
lean_inc(v_keywords_66_);
lean_inc(v_description_65_);
lean_inc(v_versionTags_64_);
lean_inc(v_version_63_);
lean_inc(v_lintDriverArgs_62_);
lean_inc(v_lintDriver_61_);
lean_inc(v_testDriverArgs_60_);
lean_inc(v_testDriver_59_);
lean_inc(v_buildArchive_57_);
lean_inc(v_releaseRepo_56_);
lean_inc(v_irDir_55_);
lean_inc(v_binDir_54_);
lean_inc(v_nativeLibDir_53_);
lean_inc(v_leanLibDir_52_);
lean_inc(v_buildDir_51_);
lean_inc(v_srcDir_50_);
lean_inc(v_moreGlobalServerArgs_49_);
lean_inc(v_extraDepTargets_47_);
lean_inc(v_toLeanConfig_46_);
lean_inc(v_toWorkspaceConfig_45_);
lean_dec(v_cfg_44_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_toWorkspaceConfig_45_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_toLeanConfig_46_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_extraDepTargets_47_);
lean_ctor_set(v_reuseFailAlloc_82_, 3, v_moreGlobalServerArgs_49_);
lean_ctor_set(v_reuseFailAlloc_82_, 4, v_srcDir_50_);
lean_ctor_set(v_reuseFailAlloc_82_, 5, v_buildDir_51_);
lean_ctor_set(v_reuseFailAlloc_82_, 6, v_leanLibDir_52_);
lean_ctor_set(v_reuseFailAlloc_82_, 7, v_nativeLibDir_53_);
lean_ctor_set(v_reuseFailAlloc_82_, 8, v_binDir_54_);
lean_ctor_set(v_reuseFailAlloc_82_, 9, v_irDir_55_);
lean_ctor_set(v_reuseFailAlloc_82_, 10, v_releaseRepo_56_);
lean_ctor_set(v_reuseFailAlloc_82_, 11, v_buildArchive_57_);
lean_ctor_set(v_reuseFailAlloc_82_, 12, v_testDriver_59_);
lean_ctor_set(v_reuseFailAlloc_82_, 13, v_testDriverArgs_60_);
lean_ctor_set(v_reuseFailAlloc_82_, 14, v_lintDriver_61_);
lean_ctor_set(v_reuseFailAlloc_82_, 15, v_lintDriverArgs_62_);
lean_ctor_set(v_reuseFailAlloc_82_, 16, v_version_63_);
lean_ctor_set(v_reuseFailAlloc_82_, 17, v_versionTags_64_);
lean_ctor_set(v_reuseFailAlloc_82_, 18, v_description_65_);
lean_ctor_set(v_reuseFailAlloc_82_, 19, v_keywords_66_);
lean_ctor_set(v_reuseFailAlloc_82_, 20, v_homepage_67_);
lean_ctor_set(v_reuseFailAlloc_82_, 21, v_license_68_);
lean_ctor_set(v_reuseFailAlloc_82_, 22, v_licenseFiles_69_);
lean_ctor_set(v_reuseFailAlloc_82_, 23, v_readmeFile_70_);
lean_ctor_set(v_reuseFailAlloc_82_, 24, v_enableArtifactCache_x3f_72_);
lean_ctor_set(v_reuseFailAlloc_82_, 25, v_restoreAllArtifacts_x3f_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*26 + 1, v_precompileModules_48_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*26 + 2, v_preferReleaseBuild_58_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*26 + 3, v_reservoir_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_74_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*26 + 5, v_allowImportAll_75_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*26 + 6, v_fixedToolchain_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*26, v_val_43_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object* v_val_84_, lean_object* v_cfg_85_){
_start:
{
uint8_t v_val_134__boxed_86_; lean_object* v_res_87_; 
v_val_134__boxed_86_ = lean_unbox(v_val_84_);
v_res_87_ = l_Lake_PackageConfig_bootstrap___proj___lam__1(v_val_134__boxed_86_, v_cfg_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object* v_f_88_, lean_object* v_cfg_89_){
_start:
{
lean_object* v_toWorkspaceConfig_90_; lean_object* v_toLeanConfig_91_; uint8_t v_bootstrap_92_; lean_object* v_extraDepTargets_93_; uint8_t v_precompileModules_94_; lean_object* v_moreGlobalServerArgs_95_; lean_object* v_srcDir_96_; lean_object* v_buildDir_97_; lean_object* v_leanLibDir_98_; lean_object* v_nativeLibDir_99_; lean_object* v_binDir_100_; lean_object* v_irDir_101_; lean_object* v_releaseRepo_102_; lean_object* v_buildArchive_103_; uint8_t v_preferReleaseBuild_104_; lean_object* v_testDriver_105_; lean_object* v_testDriverArgs_106_; lean_object* v_lintDriver_107_; lean_object* v_lintDriverArgs_108_; lean_object* v_version_109_; lean_object* v_versionTags_110_; lean_object* v_description_111_; lean_object* v_keywords_112_; lean_object* v_homepage_113_; lean_object* v_license_114_; lean_object* v_licenseFiles_115_; lean_object* v_readmeFile_116_; uint8_t v_reservoir_117_; lean_object* v_enableArtifactCache_x3f_118_; lean_object* v_restoreAllArtifacts_x3f_119_; uint8_t v_libPrefixOnWindows_120_; uint8_t v_allowImportAll_121_; uint8_t v_fixedToolchain_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_toWorkspaceConfig_90_ = lean_ctor_get(v_cfg_89_, 0);
v_toLeanConfig_91_ = lean_ctor_get(v_cfg_89_, 1);
v_bootstrap_92_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26);
v_extraDepTargets_93_ = lean_ctor_get(v_cfg_89_, 2);
v_precompileModules_94_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_95_ = lean_ctor_get(v_cfg_89_, 3);
v_srcDir_96_ = lean_ctor_get(v_cfg_89_, 4);
v_buildDir_97_ = lean_ctor_get(v_cfg_89_, 5);
v_leanLibDir_98_ = lean_ctor_get(v_cfg_89_, 6);
v_nativeLibDir_99_ = lean_ctor_get(v_cfg_89_, 7);
v_binDir_100_ = lean_ctor_get(v_cfg_89_, 8);
v_irDir_101_ = lean_ctor_get(v_cfg_89_, 9);
v_releaseRepo_102_ = lean_ctor_get(v_cfg_89_, 10);
v_buildArchive_103_ = lean_ctor_get(v_cfg_89_, 11);
v_preferReleaseBuild_104_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26 + 2);
v_testDriver_105_ = lean_ctor_get(v_cfg_89_, 12);
v_testDriverArgs_106_ = lean_ctor_get(v_cfg_89_, 13);
v_lintDriver_107_ = lean_ctor_get(v_cfg_89_, 14);
v_lintDriverArgs_108_ = lean_ctor_get(v_cfg_89_, 15);
v_version_109_ = lean_ctor_get(v_cfg_89_, 16);
v_versionTags_110_ = lean_ctor_get(v_cfg_89_, 17);
v_description_111_ = lean_ctor_get(v_cfg_89_, 18);
v_keywords_112_ = lean_ctor_get(v_cfg_89_, 19);
v_homepage_113_ = lean_ctor_get(v_cfg_89_, 20);
v_license_114_ = lean_ctor_get(v_cfg_89_, 21);
v_licenseFiles_115_ = lean_ctor_get(v_cfg_89_, 22);
v_readmeFile_116_ = lean_ctor_get(v_cfg_89_, 23);
v_reservoir_117_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_118_ = lean_ctor_get(v_cfg_89_, 24);
v_restoreAllArtifacts_x3f_119_ = lean_ctor_get(v_cfg_89_, 25);
v_libPrefixOnWindows_120_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26 + 4);
v_allowImportAll_121_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26 + 5);
v_fixedToolchain_122_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*26 + 6);
v_isSharedCheck_132_ = !lean_is_exclusive(v_cfg_89_);
if (v_isSharedCheck_132_ == 0)
{
v___x_124_ = v_cfg_89_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_119_);
lean_inc(v_enableArtifactCache_x3f_118_);
lean_inc(v_readmeFile_116_);
lean_inc(v_licenseFiles_115_);
lean_inc(v_license_114_);
lean_inc(v_homepage_113_);
lean_inc(v_keywords_112_);
lean_inc(v_description_111_);
lean_inc(v_versionTags_110_);
lean_inc(v_version_109_);
lean_inc(v_lintDriverArgs_108_);
lean_inc(v_lintDriver_107_);
lean_inc(v_testDriverArgs_106_);
lean_inc(v_testDriver_105_);
lean_inc(v_buildArchive_103_);
lean_inc(v_releaseRepo_102_);
lean_inc(v_irDir_101_);
lean_inc(v_binDir_100_);
lean_inc(v_nativeLibDir_99_);
lean_inc(v_leanLibDir_98_);
lean_inc(v_buildDir_97_);
lean_inc(v_srcDir_96_);
lean_inc(v_moreGlobalServerArgs_95_);
lean_inc(v_extraDepTargets_93_);
lean_inc(v_toLeanConfig_91_);
lean_inc(v_toWorkspaceConfig_90_);
lean_dec(v_cfg_89_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_126_ = lean_box(v_bootstrap_92_);
v___x_127_ = lean_apply_1(v_f_88_, v___x_126_);
if (v_isShared_125_ == 0)
{
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_toWorkspaceConfig_90_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_toLeanConfig_91_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_extraDepTargets_93_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_moreGlobalServerArgs_95_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_srcDir_96_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_buildDir_97_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_leanLibDir_98_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_nativeLibDir_99_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_binDir_100_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_irDir_101_);
lean_ctor_set(v_reuseFailAlloc_131_, 10, v_releaseRepo_102_);
lean_ctor_set(v_reuseFailAlloc_131_, 11, v_buildArchive_103_);
lean_ctor_set(v_reuseFailAlloc_131_, 12, v_testDriver_105_);
lean_ctor_set(v_reuseFailAlloc_131_, 13, v_testDriverArgs_106_);
lean_ctor_set(v_reuseFailAlloc_131_, 14, v_lintDriver_107_);
lean_ctor_set(v_reuseFailAlloc_131_, 15, v_lintDriverArgs_108_);
lean_ctor_set(v_reuseFailAlloc_131_, 16, v_version_109_);
lean_ctor_set(v_reuseFailAlloc_131_, 17, v_versionTags_110_);
lean_ctor_set(v_reuseFailAlloc_131_, 18, v_description_111_);
lean_ctor_set(v_reuseFailAlloc_131_, 19, v_keywords_112_);
lean_ctor_set(v_reuseFailAlloc_131_, 20, v_homepage_113_);
lean_ctor_set(v_reuseFailAlloc_131_, 21, v_license_114_);
lean_ctor_set(v_reuseFailAlloc_131_, 22, v_licenseFiles_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 23, v_readmeFile_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 24, v_enableArtifactCache_x3f_118_);
lean_ctor_set(v_reuseFailAlloc_131_, 25, v_restoreAllArtifacts_x3f_119_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
uint8_t v___x_130_; 
v___x_130_ = lean_unbox(v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26, v___x_130_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26 + 1, v_precompileModules_94_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26 + 2, v_preferReleaseBuild_104_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26 + 3, v_reservoir_117_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_120_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26 + 5, v_allowImportAll_121_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*26 + 6, v_fixedToolchain_122_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object* v_x_133_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lake_PackageConfig_bootstrap___proj___lam__3(v_x_135_);
lean_dec_ref(v_x_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_147_, lean_object* v_n_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___closed__4));
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_150_, lean_object* v_n_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lake_PackageConfig_bootstrap___proj(v_p_150_, v_n_151_);
lean_dec(v_n_151_);
lean_dec(v_p_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_153_, lean_object* v_n_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lake_PackageConfig_bootstrap___proj(v_p_153_, v_n_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_156_, lean_object* v_n_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_156_, v_n_157_);
lean_dec(v_n_157_);
lean_dec(v_p_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_159_){
_start:
{
lean_object* v_extraDepTargets_160_; 
v_extraDepTargets_160_ = lean_ctor_get(v_cfg_159_, 2);
lean_inc_ref(v_extraDepTargets_160_);
return v_extraDepTargets_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(v_cfg_161_);
lean_dec_ref(v_cfg_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* v_val_163_, lean_object* v_cfg_164_){
_start:
{
lean_object* v_toWorkspaceConfig_165_; lean_object* v_toLeanConfig_166_; uint8_t v_bootstrap_167_; uint8_t v_precompileModules_168_; lean_object* v_moreGlobalServerArgs_169_; lean_object* v_srcDir_170_; lean_object* v_buildDir_171_; lean_object* v_leanLibDir_172_; lean_object* v_nativeLibDir_173_; lean_object* v_binDir_174_; lean_object* v_irDir_175_; lean_object* v_releaseRepo_176_; lean_object* v_buildArchive_177_; uint8_t v_preferReleaseBuild_178_; lean_object* v_testDriver_179_; lean_object* v_testDriverArgs_180_; lean_object* v_lintDriver_181_; lean_object* v_lintDriverArgs_182_; lean_object* v_version_183_; lean_object* v_versionTags_184_; lean_object* v_description_185_; lean_object* v_keywords_186_; lean_object* v_homepage_187_; lean_object* v_license_188_; lean_object* v_licenseFiles_189_; lean_object* v_readmeFile_190_; uint8_t v_reservoir_191_; lean_object* v_enableArtifactCache_x3f_192_; lean_object* v_restoreAllArtifacts_x3f_193_; uint8_t v_libPrefixOnWindows_194_; uint8_t v_allowImportAll_195_; uint8_t v_fixedToolchain_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_toWorkspaceConfig_165_ = lean_ctor_get(v_cfg_164_, 0);
v_toLeanConfig_166_ = lean_ctor_get(v_cfg_164_, 1);
v_bootstrap_167_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26);
v_precompileModules_168_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_169_ = lean_ctor_get(v_cfg_164_, 3);
v_srcDir_170_ = lean_ctor_get(v_cfg_164_, 4);
v_buildDir_171_ = lean_ctor_get(v_cfg_164_, 5);
v_leanLibDir_172_ = lean_ctor_get(v_cfg_164_, 6);
v_nativeLibDir_173_ = lean_ctor_get(v_cfg_164_, 7);
v_binDir_174_ = lean_ctor_get(v_cfg_164_, 8);
v_irDir_175_ = lean_ctor_get(v_cfg_164_, 9);
v_releaseRepo_176_ = lean_ctor_get(v_cfg_164_, 10);
v_buildArchive_177_ = lean_ctor_get(v_cfg_164_, 11);
v_preferReleaseBuild_178_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26 + 2);
v_testDriver_179_ = lean_ctor_get(v_cfg_164_, 12);
v_testDriverArgs_180_ = lean_ctor_get(v_cfg_164_, 13);
v_lintDriver_181_ = lean_ctor_get(v_cfg_164_, 14);
v_lintDriverArgs_182_ = lean_ctor_get(v_cfg_164_, 15);
v_version_183_ = lean_ctor_get(v_cfg_164_, 16);
v_versionTags_184_ = lean_ctor_get(v_cfg_164_, 17);
v_description_185_ = lean_ctor_get(v_cfg_164_, 18);
v_keywords_186_ = lean_ctor_get(v_cfg_164_, 19);
v_homepage_187_ = lean_ctor_get(v_cfg_164_, 20);
v_license_188_ = lean_ctor_get(v_cfg_164_, 21);
v_licenseFiles_189_ = lean_ctor_get(v_cfg_164_, 22);
v_readmeFile_190_ = lean_ctor_get(v_cfg_164_, 23);
v_reservoir_191_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_192_ = lean_ctor_get(v_cfg_164_, 24);
v_restoreAllArtifacts_x3f_193_ = lean_ctor_get(v_cfg_164_, 25);
v_libPrefixOnWindows_194_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26 + 4);
v_allowImportAll_195_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26 + 5);
v_fixedToolchain_196_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*26 + 6);
v_isSharedCheck_203_ = !lean_is_exclusive(v_cfg_164_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_cfg_164_, 2);
lean_dec(v_unused_204_);
v___x_198_ = v_cfg_164_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_193_);
lean_inc(v_enableArtifactCache_x3f_192_);
lean_inc(v_readmeFile_190_);
lean_inc(v_licenseFiles_189_);
lean_inc(v_license_188_);
lean_inc(v_homepage_187_);
lean_inc(v_keywords_186_);
lean_inc(v_description_185_);
lean_inc(v_versionTags_184_);
lean_inc(v_version_183_);
lean_inc(v_lintDriverArgs_182_);
lean_inc(v_lintDriver_181_);
lean_inc(v_testDriverArgs_180_);
lean_inc(v_testDriver_179_);
lean_inc(v_buildArchive_177_);
lean_inc(v_releaseRepo_176_);
lean_inc(v_irDir_175_);
lean_inc(v_binDir_174_);
lean_inc(v_nativeLibDir_173_);
lean_inc(v_leanLibDir_172_);
lean_inc(v_buildDir_171_);
lean_inc(v_srcDir_170_);
lean_inc(v_moreGlobalServerArgs_169_);
lean_inc(v_toLeanConfig_166_);
lean_inc(v_toWorkspaceConfig_165_);
lean_dec(v_cfg_164_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 2, v_val_163_);
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_toWorkspaceConfig_165_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_toLeanConfig_166_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_val_163_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_moreGlobalServerArgs_169_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_srcDir_170_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_buildDir_171_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_leanLibDir_172_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_nativeLibDir_173_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v_binDir_174_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_irDir_175_);
lean_ctor_set(v_reuseFailAlloc_202_, 10, v_releaseRepo_176_);
lean_ctor_set(v_reuseFailAlloc_202_, 11, v_buildArchive_177_);
lean_ctor_set(v_reuseFailAlloc_202_, 12, v_testDriver_179_);
lean_ctor_set(v_reuseFailAlloc_202_, 13, v_testDriverArgs_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 14, v_lintDriver_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 15, v_lintDriverArgs_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 16, v_version_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 17, v_versionTags_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 18, v_description_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 19, v_keywords_186_);
lean_ctor_set(v_reuseFailAlloc_202_, 20, v_homepage_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 21, v_license_188_);
lean_ctor_set(v_reuseFailAlloc_202_, 22, v_licenseFiles_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 23, v_readmeFile_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 24, v_enableArtifactCache_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_202_, 25, v_restoreAllArtifacts_x3f_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26, v_bootstrap_167_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26 + 1, v_precompileModules_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26 + 2, v_preferReleaseBuild_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26 + 3, v_reservoir_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26 + 5, v_allowImportAll_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*26 + 6, v_fixedToolchain_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* v_f_205_, lean_object* v_cfg_206_){
_start:
{
lean_object* v_toWorkspaceConfig_207_; lean_object* v_toLeanConfig_208_; uint8_t v_bootstrap_209_; lean_object* v_extraDepTargets_210_; uint8_t v_precompileModules_211_; lean_object* v_moreGlobalServerArgs_212_; lean_object* v_srcDir_213_; lean_object* v_buildDir_214_; lean_object* v_leanLibDir_215_; lean_object* v_nativeLibDir_216_; lean_object* v_binDir_217_; lean_object* v_irDir_218_; lean_object* v_releaseRepo_219_; lean_object* v_buildArchive_220_; uint8_t v_preferReleaseBuild_221_; lean_object* v_testDriver_222_; lean_object* v_testDriverArgs_223_; lean_object* v_lintDriver_224_; lean_object* v_lintDriverArgs_225_; lean_object* v_version_226_; lean_object* v_versionTags_227_; lean_object* v_description_228_; lean_object* v_keywords_229_; lean_object* v_homepage_230_; lean_object* v_license_231_; lean_object* v_licenseFiles_232_; lean_object* v_readmeFile_233_; uint8_t v_reservoir_234_; lean_object* v_enableArtifactCache_x3f_235_; lean_object* v_restoreAllArtifacts_x3f_236_; uint8_t v_libPrefixOnWindows_237_; uint8_t v_allowImportAll_238_; uint8_t v_fixedToolchain_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_toWorkspaceConfig_207_ = lean_ctor_get(v_cfg_206_, 0);
v_toLeanConfig_208_ = lean_ctor_get(v_cfg_206_, 1);
v_bootstrap_209_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26);
v_extraDepTargets_210_ = lean_ctor_get(v_cfg_206_, 2);
v_precompileModules_211_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_212_ = lean_ctor_get(v_cfg_206_, 3);
v_srcDir_213_ = lean_ctor_get(v_cfg_206_, 4);
v_buildDir_214_ = lean_ctor_get(v_cfg_206_, 5);
v_leanLibDir_215_ = lean_ctor_get(v_cfg_206_, 6);
v_nativeLibDir_216_ = lean_ctor_get(v_cfg_206_, 7);
v_binDir_217_ = lean_ctor_get(v_cfg_206_, 8);
v_irDir_218_ = lean_ctor_get(v_cfg_206_, 9);
v_releaseRepo_219_ = lean_ctor_get(v_cfg_206_, 10);
v_buildArchive_220_ = lean_ctor_get(v_cfg_206_, 11);
v_preferReleaseBuild_221_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26 + 2);
v_testDriver_222_ = lean_ctor_get(v_cfg_206_, 12);
v_testDriverArgs_223_ = lean_ctor_get(v_cfg_206_, 13);
v_lintDriver_224_ = lean_ctor_get(v_cfg_206_, 14);
v_lintDriverArgs_225_ = lean_ctor_get(v_cfg_206_, 15);
v_version_226_ = lean_ctor_get(v_cfg_206_, 16);
v_versionTags_227_ = lean_ctor_get(v_cfg_206_, 17);
v_description_228_ = lean_ctor_get(v_cfg_206_, 18);
v_keywords_229_ = lean_ctor_get(v_cfg_206_, 19);
v_homepage_230_ = lean_ctor_get(v_cfg_206_, 20);
v_license_231_ = lean_ctor_get(v_cfg_206_, 21);
v_licenseFiles_232_ = lean_ctor_get(v_cfg_206_, 22);
v_readmeFile_233_ = lean_ctor_get(v_cfg_206_, 23);
v_reservoir_234_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_235_ = lean_ctor_get(v_cfg_206_, 24);
v_restoreAllArtifacts_x3f_236_ = lean_ctor_get(v_cfg_206_, 25);
v_libPrefixOnWindows_237_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26 + 4);
v_allowImportAll_238_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26 + 5);
v_fixedToolchain_239_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*26 + 6);
v_isSharedCheck_247_ = !lean_is_exclusive(v_cfg_206_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v_cfg_206_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_236_);
lean_inc(v_enableArtifactCache_x3f_235_);
lean_inc(v_readmeFile_233_);
lean_inc(v_licenseFiles_232_);
lean_inc(v_license_231_);
lean_inc(v_homepage_230_);
lean_inc(v_keywords_229_);
lean_inc(v_description_228_);
lean_inc(v_versionTags_227_);
lean_inc(v_version_226_);
lean_inc(v_lintDriverArgs_225_);
lean_inc(v_lintDriver_224_);
lean_inc(v_testDriverArgs_223_);
lean_inc(v_testDriver_222_);
lean_inc(v_buildArchive_220_);
lean_inc(v_releaseRepo_219_);
lean_inc(v_irDir_218_);
lean_inc(v_binDir_217_);
lean_inc(v_nativeLibDir_216_);
lean_inc(v_leanLibDir_215_);
lean_inc(v_buildDir_214_);
lean_inc(v_srcDir_213_);
lean_inc(v_moreGlobalServerArgs_212_);
lean_inc(v_extraDepTargets_210_);
lean_inc(v_toLeanConfig_208_);
lean_inc(v_toWorkspaceConfig_207_);
lean_dec(v_cfg_206_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_apply_1(v_f_205_, v_extraDepTargets_210_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_toWorkspaceConfig_207_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_toLeanConfig_208_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_moreGlobalServerArgs_212_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_srcDir_213_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v_buildDir_214_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_leanLibDir_215_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_nativeLibDir_216_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_binDir_217_);
lean_ctor_set(v_reuseFailAlloc_246_, 9, v_irDir_218_);
lean_ctor_set(v_reuseFailAlloc_246_, 10, v_releaseRepo_219_);
lean_ctor_set(v_reuseFailAlloc_246_, 11, v_buildArchive_220_);
lean_ctor_set(v_reuseFailAlloc_246_, 12, v_testDriver_222_);
lean_ctor_set(v_reuseFailAlloc_246_, 13, v_testDriverArgs_223_);
lean_ctor_set(v_reuseFailAlloc_246_, 14, v_lintDriver_224_);
lean_ctor_set(v_reuseFailAlloc_246_, 15, v_lintDriverArgs_225_);
lean_ctor_set(v_reuseFailAlloc_246_, 16, v_version_226_);
lean_ctor_set(v_reuseFailAlloc_246_, 17, v_versionTags_227_);
lean_ctor_set(v_reuseFailAlloc_246_, 18, v_description_228_);
lean_ctor_set(v_reuseFailAlloc_246_, 19, v_keywords_229_);
lean_ctor_set(v_reuseFailAlloc_246_, 20, v_homepage_230_);
lean_ctor_set(v_reuseFailAlloc_246_, 21, v_license_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 22, v_licenseFiles_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 23, v_readmeFile_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 24, v_enableArtifactCache_x3f_235_);
lean_ctor_set(v_reuseFailAlloc_246_, 25, v_restoreAllArtifacts_x3f_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26, v_bootstrap_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26 + 1, v_precompileModules_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26 + 2, v_preferReleaseBuild_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26 + 3, v_reservoir_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26 + 5, v_allowImportAll_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*26 + 6, v_fixedToolchain_239_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(v_x_252_);
lean_dec_ref(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_263_, lean_object* v_n_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_266_, lean_object* v_n_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_266_, v_n_267_);
lean_dec(v_n_267_);
lean_dec(v_p_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_269_, lean_object* v_n_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_269_, v_n_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_272_, lean_object* v_n_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_272_, v_n_273_);
lean_dec(v_n_273_);
lean_dec(v_p_272_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* v_cfg_275_){
_start:
{
uint8_t v_precompileModules_276_; 
v_precompileModules_276_ = lean_ctor_get_uint8(v_cfg_275_, sizeof(void*)*26 + 1);
return v_precompileModules_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Lake_PackageConfig_precompileModules___proj___lam__0(v_cfg_277_);
lean_dec_ref(v_cfg_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t v_val_280_, lean_object* v_cfg_281_){
_start:
{
lean_object* v_toWorkspaceConfig_282_; lean_object* v_toLeanConfig_283_; uint8_t v_bootstrap_284_; lean_object* v_extraDepTargets_285_; lean_object* v_moreGlobalServerArgs_286_; lean_object* v_srcDir_287_; lean_object* v_buildDir_288_; lean_object* v_leanLibDir_289_; lean_object* v_nativeLibDir_290_; lean_object* v_binDir_291_; lean_object* v_irDir_292_; lean_object* v_releaseRepo_293_; lean_object* v_buildArchive_294_; uint8_t v_preferReleaseBuild_295_; lean_object* v_testDriver_296_; lean_object* v_testDriverArgs_297_; lean_object* v_lintDriver_298_; lean_object* v_lintDriverArgs_299_; lean_object* v_version_300_; lean_object* v_versionTags_301_; lean_object* v_description_302_; lean_object* v_keywords_303_; lean_object* v_homepage_304_; lean_object* v_license_305_; lean_object* v_licenseFiles_306_; lean_object* v_readmeFile_307_; uint8_t v_reservoir_308_; lean_object* v_enableArtifactCache_x3f_309_; lean_object* v_restoreAllArtifacts_x3f_310_; uint8_t v_libPrefixOnWindows_311_; uint8_t v_allowImportAll_312_; uint8_t v_fixedToolchain_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_toWorkspaceConfig_282_ = lean_ctor_get(v_cfg_281_, 0);
v_toLeanConfig_283_ = lean_ctor_get(v_cfg_281_, 1);
v_bootstrap_284_ = lean_ctor_get_uint8(v_cfg_281_, sizeof(void*)*26);
v_extraDepTargets_285_ = lean_ctor_get(v_cfg_281_, 2);
v_moreGlobalServerArgs_286_ = lean_ctor_get(v_cfg_281_, 3);
v_srcDir_287_ = lean_ctor_get(v_cfg_281_, 4);
v_buildDir_288_ = lean_ctor_get(v_cfg_281_, 5);
v_leanLibDir_289_ = lean_ctor_get(v_cfg_281_, 6);
v_nativeLibDir_290_ = lean_ctor_get(v_cfg_281_, 7);
v_binDir_291_ = lean_ctor_get(v_cfg_281_, 8);
v_irDir_292_ = lean_ctor_get(v_cfg_281_, 9);
v_releaseRepo_293_ = lean_ctor_get(v_cfg_281_, 10);
v_buildArchive_294_ = lean_ctor_get(v_cfg_281_, 11);
v_preferReleaseBuild_295_ = lean_ctor_get_uint8(v_cfg_281_, sizeof(void*)*26 + 2);
v_testDriver_296_ = lean_ctor_get(v_cfg_281_, 12);
v_testDriverArgs_297_ = lean_ctor_get(v_cfg_281_, 13);
v_lintDriver_298_ = lean_ctor_get(v_cfg_281_, 14);
v_lintDriverArgs_299_ = lean_ctor_get(v_cfg_281_, 15);
v_version_300_ = lean_ctor_get(v_cfg_281_, 16);
v_versionTags_301_ = lean_ctor_get(v_cfg_281_, 17);
v_description_302_ = lean_ctor_get(v_cfg_281_, 18);
v_keywords_303_ = lean_ctor_get(v_cfg_281_, 19);
v_homepage_304_ = lean_ctor_get(v_cfg_281_, 20);
v_license_305_ = lean_ctor_get(v_cfg_281_, 21);
v_licenseFiles_306_ = lean_ctor_get(v_cfg_281_, 22);
v_readmeFile_307_ = lean_ctor_get(v_cfg_281_, 23);
v_reservoir_308_ = lean_ctor_get_uint8(v_cfg_281_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_309_ = lean_ctor_get(v_cfg_281_, 24);
v_restoreAllArtifacts_x3f_310_ = lean_ctor_get(v_cfg_281_, 25);
v_libPrefixOnWindows_311_ = lean_ctor_get_uint8(v_cfg_281_, sizeof(void*)*26 + 4);
v_allowImportAll_312_ = lean_ctor_get_uint8(v_cfg_281_, sizeof(void*)*26 + 5);
v_fixedToolchain_313_ = lean_ctor_get_uint8(v_cfg_281_, sizeof(void*)*26 + 6);
v_isSharedCheck_320_ = !lean_is_exclusive(v_cfg_281_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v_cfg_281_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_310_);
lean_inc(v_enableArtifactCache_x3f_309_);
lean_inc(v_readmeFile_307_);
lean_inc(v_licenseFiles_306_);
lean_inc(v_license_305_);
lean_inc(v_homepage_304_);
lean_inc(v_keywords_303_);
lean_inc(v_description_302_);
lean_inc(v_versionTags_301_);
lean_inc(v_version_300_);
lean_inc(v_lintDriverArgs_299_);
lean_inc(v_lintDriver_298_);
lean_inc(v_testDriverArgs_297_);
lean_inc(v_testDriver_296_);
lean_inc(v_buildArchive_294_);
lean_inc(v_releaseRepo_293_);
lean_inc(v_irDir_292_);
lean_inc(v_binDir_291_);
lean_inc(v_nativeLibDir_290_);
lean_inc(v_leanLibDir_289_);
lean_inc(v_buildDir_288_);
lean_inc(v_srcDir_287_);
lean_inc(v_moreGlobalServerArgs_286_);
lean_inc(v_extraDepTargets_285_);
lean_inc(v_toLeanConfig_283_);
lean_inc(v_toWorkspaceConfig_282_);
lean_dec(v_cfg_281_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_toWorkspaceConfig_282_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_toLeanConfig_283_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_extraDepTargets_285_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_moreGlobalServerArgs_286_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_srcDir_287_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v_buildDir_288_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_leanLibDir_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_nativeLibDir_290_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_binDir_291_);
lean_ctor_set(v_reuseFailAlloc_319_, 9, v_irDir_292_);
lean_ctor_set(v_reuseFailAlloc_319_, 10, v_releaseRepo_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 11, v_buildArchive_294_);
lean_ctor_set(v_reuseFailAlloc_319_, 12, v_testDriver_296_);
lean_ctor_set(v_reuseFailAlloc_319_, 13, v_testDriverArgs_297_);
lean_ctor_set(v_reuseFailAlloc_319_, 14, v_lintDriver_298_);
lean_ctor_set(v_reuseFailAlloc_319_, 15, v_lintDriverArgs_299_);
lean_ctor_set(v_reuseFailAlloc_319_, 16, v_version_300_);
lean_ctor_set(v_reuseFailAlloc_319_, 17, v_versionTags_301_);
lean_ctor_set(v_reuseFailAlloc_319_, 18, v_description_302_);
lean_ctor_set(v_reuseFailAlloc_319_, 19, v_keywords_303_);
lean_ctor_set(v_reuseFailAlloc_319_, 20, v_homepage_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 21, v_license_305_);
lean_ctor_set(v_reuseFailAlloc_319_, 22, v_licenseFiles_306_);
lean_ctor_set(v_reuseFailAlloc_319_, 23, v_readmeFile_307_);
lean_ctor_set(v_reuseFailAlloc_319_, 24, v_enableArtifactCache_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_319_, 25, v_restoreAllArtifacts_x3f_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*26, v_bootstrap_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*26 + 2, v_preferReleaseBuild_295_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*26 + 3, v_reservoir_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*26 + 5, v_allowImportAll_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*26 + 6, v_fixedToolchain_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*26 + 1, v_val_280_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_321_, lean_object* v_cfg_322_){
_start:
{
uint8_t v_val_134__boxed_323_; lean_object* v_res_324_; 
v_val_134__boxed_323_ = lean_unbox(v_val_321_);
v_res_324_ = l_Lake_PackageConfig_precompileModules___proj___lam__1(v_val_134__boxed_323_, v_cfg_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* v_f_325_, lean_object* v_cfg_326_){
_start:
{
lean_object* v_toWorkspaceConfig_327_; lean_object* v_toLeanConfig_328_; uint8_t v_bootstrap_329_; lean_object* v_extraDepTargets_330_; uint8_t v_precompileModules_331_; lean_object* v_moreGlobalServerArgs_332_; lean_object* v_srcDir_333_; lean_object* v_buildDir_334_; lean_object* v_leanLibDir_335_; lean_object* v_nativeLibDir_336_; lean_object* v_binDir_337_; lean_object* v_irDir_338_; lean_object* v_releaseRepo_339_; lean_object* v_buildArchive_340_; uint8_t v_preferReleaseBuild_341_; lean_object* v_testDriver_342_; lean_object* v_testDriverArgs_343_; lean_object* v_lintDriver_344_; lean_object* v_lintDriverArgs_345_; lean_object* v_version_346_; lean_object* v_versionTags_347_; lean_object* v_description_348_; lean_object* v_keywords_349_; lean_object* v_homepage_350_; lean_object* v_license_351_; lean_object* v_licenseFiles_352_; lean_object* v_readmeFile_353_; uint8_t v_reservoir_354_; lean_object* v_enableArtifactCache_x3f_355_; lean_object* v_restoreAllArtifacts_x3f_356_; uint8_t v_libPrefixOnWindows_357_; uint8_t v_allowImportAll_358_; uint8_t v_fixedToolchain_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_369_; 
v_toWorkspaceConfig_327_ = lean_ctor_get(v_cfg_326_, 0);
v_toLeanConfig_328_ = lean_ctor_get(v_cfg_326_, 1);
v_bootstrap_329_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26);
v_extraDepTargets_330_ = lean_ctor_get(v_cfg_326_, 2);
v_precompileModules_331_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_332_ = lean_ctor_get(v_cfg_326_, 3);
v_srcDir_333_ = lean_ctor_get(v_cfg_326_, 4);
v_buildDir_334_ = lean_ctor_get(v_cfg_326_, 5);
v_leanLibDir_335_ = lean_ctor_get(v_cfg_326_, 6);
v_nativeLibDir_336_ = lean_ctor_get(v_cfg_326_, 7);
v_binDir_337_ = lean_ctor_get(v_cfg_326_, 8);
v_irDir_338_ = lean_ctor_get(v_cfg_326_, 9);
v_releaseRepo_339_ = lean_ctor_get(v_cfg_326_, 10);
v_buildArchive_340_ = lean_ctor_get(v_cfg_326_, 11);
v_preferReleaseBuild_341_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26 + 2);
v_testDriver_342_ = lean_ctor_get(v_cfg_326_, 12);
v_testDriverArgs_343_ = lean_ctor_get(v_cfg_326_, 13);
v_lintDriver_344_ = lean_ctor_get(v_cfg_326_, 14);
v_lintDriverArgs_345_ = lean_ctor_get(v_cfg_326_, 15);
v_version_346_ = lean_ctor_get(v_cfg_326_, 16);
v_versionTags_347_ = lean_ctor_get(v_cfg_326_, 17);
v_description_348_ = lean_ctor_get(v_cfg_326_, 18);
v_keywords_349_ = lean_ctor_get(v_cfg_326_, 19);
v_homepage_350_ = lean_ctor_get(v_cfg_326_, 20);
v_license_351_ = lean_ctor_get(v_cfg_326_, 21);
v_licenseFiles_352_ = lean_ctor_get(v_cfg_326_, 22);
v_readmeFile_353_ = lean_ctor_get(v_cfg_326_, 23);
v_reservoir_354_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_355_ = lean_ctor_get(v_cfg_326_, 24);
v_restoreAllArtifacts_x3f_356_ = lean_ctor_get(v_cfg_326_, 25);
v_libPrefixOnWindows_357_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26 + 4);
v_allowImportAll_358_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26 + 5);
v_fixedToolchain_359_ = lean_ctor_get_uint8(v_cfg_326_, sizeof(void*)*26 + 6);
v_isSharedCheck_369_ = !lean_is_exclusive(v_cfg_326_);
if (v_isSharedCheck_369_ == 0)
{
v___x_361_ = v_cfg_326_;
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_356_);
lean_inc(v_enableArtifactCache_x3f_355_);
lean_inc(v_readmeFile_353_);
lean_inc(v_licenseFiles_352_);
lean_inc(v_license_351_);
lean_inc(v_homepage_350_);
lean_inc(v_keywords_349_);
lean_inc(v_description_348_);
lean_inc(v_versionTags_347_);
lean_inc(v_version_346_);
lean_inc(v_lintDriverArgs_345_);
lean_inc(v_lintDriver_344_);
lean_inc(v_testDriverArgs_343_);
lean_inc(v_testDriver_342_);
lean_inc(v_buildArchive_340_);
lean_inc(v_releaseRepo_339_);
lean_inc(v_irDir_338_);
lean_inc(v_binDir_337_);
lean_inc(v_nativeLibDir_336_);
lean_inc(v_leanLibDir_335_);
lean_inc(v_buildDir_334_);
lean_inc(v_srcDir_333_);
lean_inc(v_moreGlobalServerArgs_332_);
lean_inc(v_extraDepTargets_330_);
lean_inc(v_toLeanConfig_328_);
lean_inc(v_toWorkspaceConfig_327_);
lean_dec(v_cfg_326_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_box(v_precompileModules_331_);
v___x_364_ = lean_apply_1(v_f_325_, v___x_363_);
if (v_isShared_362_ == 0)
{
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_toWorkspaceConfig_327_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_toLeanConfig_328_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_extraDepTargets_330_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_moreGlobalServerArgs_332_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_srcDir_333_);
lean_ctor_set(v_reuseFailAlloc_368_, 5, v_buildDir_334_);
lean_ctor_set(v_reuseFailAlloc_368_, 6, v_leanLibDir_335_);
lean_ctor_set(v_reuseFailAlloc_368_, 7, v_nativeLibDir_336_);
lean_ctor_set(v_reuseFailAlloc_368_, 8, v_binDir_337_);
lean_ctor_set(v_reuseFailAlloc_368_, 9, v_irDir_338_);
lean_ctor_set(v_reuseFailAlloc_368_, 10, v_releaseRepo_339_);
lean_ctor_set(v_reuseFailAlloc_368_, 11, v_buildArchive_340_);
lean_ctor_set(v_reuseFailAlloc_368_, 12, v_testDriver_342_);
lean_ctor_set(v_reuseFailAlloc_368_, 13, v_testDriverArgs_343_);
lean_ctor_set(v_reuseFailAlloc_368_, 14, v_lintDriver_344_);
lean_ctor_set(v_reuseFailAlloc_368_, 15, v_lintDriverArgs_345_);
lean_ctor_set(v_reuseFailAlloc_368_, 16, v_version_346_);
lean_ctor_set(v_reuseFailAlloc_368_, 17, v_versionTags_347_);
lean_ctor_set(v_reuseFailAlloc_368_, 18, v_description_348_);
lean_ctor_set(v_reuseFailAlloc_368_, 19, v_keywords_349_);
lean_ctor_set(v_reuseFailAlloc_368_, 20, v_homepage_350_);
lean_ctor_set(v_reuseFailAlloc_368_, 21, v_license_351_);
lean_ctor_set(v_reuseFailAlloc_368_, 22, v_licenseFiles_352_);
lean_ctor_set(v_reuseFailAlloc_368_, 23, v_readmeFile_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 24, v_enableArtifactCache_x3f_355_);
lean_ctor_set(v_reuseFailAlloc_368_, 25, v_restoreAllArtifacts_x3f_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_368_, sizeof(void*)*26, v_bootstrap_329_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
uint8_t v___x_367_; 
v___x_367_ = lean_unbox(v___x_364_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*26 + 1, v___x_367_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*26 + 2, v_preferReleaseBuild_341_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*26 + 3, v_reservoir_354_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_357_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*26 + 5, v_allowImportAll_358_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*26 + 6, v_fixedToolchain_359_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_378_, lean_object* v_n_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_381_, lean_object* v_n_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lake_PackageConfig_precompileModules___proj(v_p_381_, v_n_382_);
lean_dec(v_n_382_);
lean_dec(v_p_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_384_, lean_object* v_n_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lake_PackageConfig_precompileModules___proj(v_p_384_, v_n_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_387_, lean_object* v_n_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_387_, v_n_388_);
lean_dec(v_n_388_);
lean_dec(v_p_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* v_cfg_390_){
_start:
{
lean_object* v_moreGlobalServerArgs_391_; 
v_moreGlobalServerArgs_391_ = lean_ctor_get(v_cfg_390_, 3);
lean_inc_ref(v_moreGlobalServerArgs_391_);
return v_moreGlobalServerArgs_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* v_cfg_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(v_cfg_392_);
lean_dec_ref(v_cfg_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* v_val_394_, lean_object* v_cfg_395_){
_start:
{
lean_object* v_toWorkspaceConfig_396_; lean_object* v_toLeanConfig_397_; uint8_t v_bootstrap_398_; lean_object* v_extraDepTargets_399_; uint8_t v_precompileModules_400_; lean_object* v_srcDir_401_; lean_object* v_buildDir_402_; lean_object* v_leanLibDir_403_; lean_object* v_nativeLibDir_404_; lean_object* v_binDir_405_; lean_object* v_irDir_406_; lean_object* v_releaseRepo_407_; lean_object* v_buildArchive_408_; uint8_t v_preferReleaseBuild_409_; lean_object* v_testDriver_410_; lean_object* v_testDriverArgs_411_; lean_object* v_lintDriver_412_; lean_object* v_lintDriverArgs_413_; lean_object* v_version_414_; lean_object* v_versionTags_415_; lean_object* v_description_416_; lean_object* v_keywords_417_; lean_object* v_homepage_418_; lean_object* v_license_419_; lean_object* v_licenseFiles_420_; lean_object* v_readmeFile_421_; uint8_t v_reservoir_422_; lean_object* v_enableArtifactCache_x3f_423_; lean_object* v_restoreAllArtifacts_x3f_424_; uint8_t v_libPrefixOnWindows_425_; uint8_t v_allowImportAll_426_; uint8_t v_fixedToolchain_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_toWorkspaceConfig_396_ = lean_ctor_get(v_cfg_395_, 0);
v_toLeanConfig_397_ = lean_ctor_get(v_cfg_395_, 1);
v_bootstrap_398_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26);
v_extraDepTargets_399_ = lean_ctor_get(v_cfg_395_, 2);
v_precompileModules_400_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26 + 1);
v_srcDir_401_ = lean_ctor_get(v_cfg_395_, 4);
v_buildDir_402_ = lean_ctor_get(v_cfg_395_, 5);
v_leanLibDir_403_ = lean_ctor_get(v_cfg_395_, 6);
v_nativeLibDir_404_ = lean_ctor_get(v_cfg_395_, 7);
v_binDir_405_ = lean_ctor_get(v_cfg_395_, 8);
v_irDir_406_ = lean_ctor_get(v_cfg_395_, 9);
v_releaseRepo_407_ = lean_ctor_get(v_cfg_395_, 10);
v_buildArchive_408_ = lean_ctor_get(v_cfg_395_, 11);
v_preferReleaseBuild_409_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26 + 2);
v_testDriver_410_ = lean_ctor_get(v_cfg_395_, 12);
v_testDriverArgs_411_ = lean_ctor_get(v_cfg_395_, 13);
v_lintDriver_412_ = lean_ctor_get(v_cfg_395_, 14);
v_lintDriverArgs_413_ = lean_ctor_get(v_cfg_395_, 15);
v_version_414_ = lean_ctor_get(v_cfg_395_, 16);
v_versionTags_415_ = lean_ctor_get(v_cfg_395_, 17);
v_description_416_ = lean_ctor_get(v_cfg_395_, 18);
v_keywords_417_ = lean_ctor_get(v_cfg_395_, 19);
v_homepage_418_ = lean_ctor_get(v_cfg_395_, 20);
v_license_419_ = lean_ctor_get(v_cfg_395_, 21);
v_licenseFiles_420_ = lean_ctor_get(v_cfg_395_, 22);
v_readmeFile_421_ = lean_ctor_get(v_cfg_395_, 23);
v_reservoir_422_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_423_ = lean_ctor_get(v_cfg_395_, 24);
v_restoreAllArtifacts_x3f_424_ = lean_ctor_get(v_cfg_395_, 25);
v_libPrefixOnWindows_425_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26 + 4);
v_allowImportAll_426_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26 + 5);
v_fixedToolchain_427_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*26 + 6);
v_isSharedCheck_434_ = !lean_is_exclusive(v_cfg_395_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_cfg_395_, 3);
lean_dec(v_unused_435_);
v___x_429_ = v_cfg_395_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_424_);
lean_inc(v_enableArtifactCache_x3f_423_);
lean_inc(v_readmeFile_421_);
lean_inc(v_licenseFiles_420_);
lean_inc(v_license_419_);
lean_inc(v_homepage_418_);
lean_inc(v_keywords_417_);
lean_inc(v_description_416_);
lean_inc(v_versionTags_415_);
lean_inc(v_version_414_);
lean_inc(v_lintDriverArgs_413_);
lean_inc(v_lintDriver_412_);
lean_inc(v_testDriverArgs_411_);
lean_inc(v_testDriver_410_);
lean_inc(v_buildArchive_408_);
lean_inc(v_releaseRepo_407_);
lean_inc(v_irDir_406_);
lean_inc(v_binDir_405_);
lean_inc(v_nativeLibDir_404_);
lean_inc(v_leanLibDir_403_);
lean_inc(v_buildDir_402_);
lean_inc(v_srcDir_401_);
lean_inc(v_extraDepTargets_399_);
lean_inc(v_toLeanConfig_397_);
lean_inc(v_toWorkspaceConfig_396_);
lean_dec(v_cfg_395_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 3, v_val_394_);
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_toWorkspaceConfig_396_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_toLeanConfig_397_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_extraDepTargets_399_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_val_394_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_srcDir_401_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_buildDir_402_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_leanLibDir_403_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_nativeLibDir_404_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_binDir_405_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_irDir_406_);
lean_ctor_set(v_reuseFailAlloc_433_, 10, v_releaseRepo_407_);
lean_ctor_set(v_reuseFailAlloc_433_, 11, v_buildArchive_408_);
lean_ctor_set(v_reuseFailAlloc_433_, 12, v_testDriver_410_);
lean_ctor_set(v_reuseFailAlloc_433_, 13, v_testDriverArgs_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 14, v_lintDriver_412_);
lean_ctor_set(v_reuseFailAlloc_433_, 15, v_lintDriverArgs_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 16, v_version_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 17, v_versionTags_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 18, v_description_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 19, v_keywords_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 20, v_homepage_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 21, v_license_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 22, v_licenseFiles_420_);
lean_ctor_set(v_reuseFailAlloc_433_, 23, v_readmeFile_421_);
lean_ctor_set(v_reuseFailAlloc_433_, 24, v_enableArtifactCache_x3f_423_);
lean_ctor_set(v_reuseFailAlloc_433_, 25, v_restoreAllArtifacts_x3f_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26, v_bootstrap_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26 + 1, v_precompileModules_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26 + 2, v_preferReleaseBuild_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26 + 3, v_reservoir_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26 + 5, v_allowImportAll_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*26 + 6, v_fixedToolchain_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object* v_f_436_, lean_object* v_cfg_437_){
_start:
{
lean_object* v_toWorkspaceConfig_438_; lean_object* v_toLeanConfig_439_; uint8_t v_bootstrap_440_; lean_object* v_extraDepTargets_441_; uint8_t v_precompileModules_442_; lean_object* v_moreGlobalServerArgs_443_; lean_object* v_srcDir_444_; lean_object* v_buildDir_445_; lean_object* v_leanLibDir_446_; lean_object* v_nativeLibDir_447_; lean_object* v_binDir_448_; lean_object* v_irDir_449_; lean_object* v_releaseRepo_450_; lean_object* v_buildArchive_451_; uint8_t v_preferReleaseBuild_452_; lean_object* v_testDriver_453_; lean_object* v_testDriverArgs_454_; lean_object* v_lintDriver_455_; lean_object* v_lintDriverArgs_456_; lean_object* v_version_457_; lean_object* v_versionTags_458_; lean_object* v_description_459_; lean_object* v_keywords_460_; lean_object* v_homepage_461_; lean_object* v_license_462_; lean_object* v_licenseFiles_463_; lean_object* v_readmeFile_464_; uint8_t v_reservoir_465_; lean_object* v_enableArtifactCache_x3f_466_; lean_object* v_restoreAllArtifacts_x3f_467_; uint8_t v_libPrefixOnWindows_468_; uint8_t v_allowImportAll_469_; uint8_t v_fixedToolchain_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_toWorkspaceConfig_438_ = lean_ctor_get(v_cfg_437_, 0);
v_toLeanConfig_439_ = lean_ctor_get(v_cfg_437_, 1);
v_bootstrap_440_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26);
v_extraDepTargets_441_ = lean_ctor_get(v_cfg_437_, 2);
v_precompileModules_442_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_443_ = lean_ctor_get(v_cfg_437_, 3);
v_srcDir_444_ = lean_ctor_get(v_cfg_437_, 4);
v_buildDir_445_ = lean_ctor_get(v_cfg_437_, 5);
v_leanLibDir_446_ = lean_ctor_get(v_cfg_437_, 6);
v_nativeLibDir_447_ = lean_ctor_get(v_cfg_437_, 7);
v_binDir_448_ = lean_ctor_get(v_cfg_437_, 8);
v_irDir_449_ = lean_ctor_get(v_cfg_437_, 9);
v_releaseRepo_450_ = lean_ctor_get(v_cfg_437_, 10);
v_buildArchive_451_ = lean_ctor_get(v_cfg_437_, 11);
v_preferReleaseBuild_452_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26 + 2);
v_testDriver_453_ = lean_ctor_get(v_cfg_437_, 12);
v_testDriverArgs_454_ = lean_ctor_get(v_cfg_437_, 13);
v_lintDriver_455_ = lean_ctor_get(v_cfg_437_, 14);
v_lintDriverArgs_456_ = lean_ctor_get(v_cfg_437_, 15);
v_version_457_ = lean_ctor_get(v_cfg_437_, 16);
v_versionTags_458_ = lean_ctor_get(v_cfg_437_, 17);
v_description_459_ = lean_ctor_get(v_cfg_437_, 18);
v_keywords_460_ = lean_ctor_get(v_cfg_437_, 19);
v_homepage_461_ = lean_ctor_get(v_cfg_437_, 20);
v_license_462_ = lean_ctor_get(v_cfg_437_, 21);
v_licenseFiles_463_ = lean_ctor_get(v_cfg_437_, 22);
v_readmeFile_464_ = lean_ctor_get(v_cfg_437_, 23);
v_reservoir_465_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_466_ = lean_ctor_get(v_cfg_437_, 24);
v_restoreAllArtifacts_x3f_467_ = lean_ctor_get(v_cfg_437_, 25);
v_libPrefixOnWindows_468_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26 + 4);
v_allowImportAll_469_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26 + 5);
v_fixedToolchain_470_ = lean_ctor_get_uint8(v_cfg_437_, sizeof(void*)*26 + 6);
v_isSharedCheck_478_ = !lean_is_exclusive(v_cfg_437_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v_cfg_437_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_467_);
lean_inc(v_enableArtifactCache_x3f_466_);
lean_inc(v_readmeFile_464_);
lean_inc(v_licenseFiles_463_);
lean_inc(v_license_462_);
lean_inc(v_homepage_461_);
lean_inc(v_keywords_460_);
lean_inc(v_description_459_);
lean_inc(v_versionTags_458_);
lean_inc(v_version_457_);
lean_inc(v_lintDriverArgs_456_);
lean_inc(v_lintDriver_455_);
lean_inc(v_testDriverArgs_454_);
lean_inc(v_testDriver_453_);
lean_inc(v_buildArchive_451_);
lean_inc(v_releaseRepo_450_);
lean_inc(v_irDir_449_);
lean_inc(v_binDir_448_);
lean_inc(v_nativeLibDir_447_);
lean_inc(v_leanLibDir_446_);
lean_inc(v_buildDir_445_);
lean_inc(v_srcDir_444_);
lean_inc(v_moreGlobalServerArgs_443_);
lean_inc(v_extraDepTargets_441_);
lean_inc(v_toLeanConfig_439_);
lean_inc(v_toWorkspaceConfig_438_);
lean_dec(v_cfg_437_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_apply_1(v_f_436_, v_moreGlobalServerArgs_443_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 3, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_toWorkspaceConfig_438_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_toLeanConfig_439_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_extraDepTargets_441_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_srcDir_444_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v_buildDir_445_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v_leanLibDir_446_);
lean_ctor_set(v_reuseFailAlloc_477_, 7, v_nativeLibDir_447_);
lean_ctor_set(v_reuseFailAlloc_477_, 8, v_binDir_448_);
lean_ctor_set(v_reuseFailAlloc_477_, 9, v_irDir_449_);
lean_ctor_set(v_reuseFailAlloc_477_, 10, v_releaseRepo_450_);
lean_ctor_set(v_reuseFailAlloc_477_, 11, v_buildArchive_451_);
lean_ctor_set(v_reuseFailAlloc_477_, 12, v_testDriver_453_);
lean_ctor_set(v_reuseFailAlloc_477_, 13, v_testDriverArgs_454_);
lean_ctor_set(v_reuseFailAlloc_477_, 14, v_lintDriver_455_);
lean_ctor_set(v_reuseFailAlloc_477_, 15, v_lintDriverArgs_456_);
lean_ctor_set(v_reuseFailAlloc_477_, 16, v_version_457_);
lean_ctor_set(v_reuseFailAlloc_477_, 17, v_versionTags_458_);
lean_ctor_set(v_reuseFailAlloc_477_, 18, v_description_459_);
lean_ctor_set(v_reuseFailAlloc_477_, 19, v_keywords_460_);
lean_ctor_set(v_reuseFailAlloc_477_, 20, v_homepage_461_);
lean_ctor_set(v_reuseFailAlloc_477_, 21, v_license_462_);
lean_ctor_set(v_reuseFailAlloc_477_, 22, v_licenseFiles_463_);
lean_ctor_set(v_reuseFailAlloc_477_, 23, v_readmeFile_464_);
lean_ctor_set(v_reuseFailAlloc_477_, 24, v_enableArtifactCache_x3f_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 25, v_restoreAllArtifacts_x3f_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26, v_bootstrap_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26 + 1, v_precompileModules_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26 + 2, v_preferReleaseBuild_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26 + 3, v_reservoir_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26 + 5, v_allowImportAll_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*26 + 6, v_fixedToolchain_470_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* v_x_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(v_x_483_);
lean_dec_ref(v_x_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_494_, lean_object* v_n_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_497_, lean_object* v_n_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_497_, v_n_498_);
lean_dec(v_n_498_);
lean_dec(v_p_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_500_, lean_object* v_n_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_500_, v_n_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_503_, lean_object* v_n_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_503_, v_n_504_);
lean_dec(v_n_504_);
lean_dec(v_p_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_506_, lean_object* v_n_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_506_, v_n_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_509_, lean_object* v_n_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_509_, v_n_510_);
lean_dec(v_n_510_);
lean_dec(v_p_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* v_cfg_512_){
_start:
{
lean_object* v_srcDir_513_; 
v_srcDir_513_ = lean_ctor_get(v_cfg_512_, 4);
lean_inc_ref(v_srcDir_513_);
return v_srcDir_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lake_PackageConfig_srcDir___proj___lam__0(v_cfg_514_);
lean_dec_ref(v_cfg_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* v_val_516_, lean_object* v_cfg_517_){
_start:
{
lean_object* v_toWorkspaceConfig_518_; lean_object* v_toLeanConfig_519_; uint8_t v_bootstrap_520_; lean_object* v_extraDepTargets_521_; uint8_t v_precompileModules_522_; lean_object* v_moreGlobalServerArgs_523_; lean_object* v_buildDir_524_; lean_object* v_leanLibDir_525_; lean_object* v_nativeLibDir_526_; lean_object* v_binDir_527_; lean_object* v_irDir_528_; lean_object* v_releaseRepo_529_; lean_object* v_buildArchive_530_; uint8_t v_preferReleaseBuild_531_; lean_object* v_testDriver_532_; lean_object* v_testDriverArgs_533_; lean_object* v_lintDriver_534_; lean_object* v_lintDriverArgs_535_; lean_object* v_version_536_; lean_object* v_versionTags_537_; lean_object* v_description_538_; lean_object* v_keywords_539_; lean_object* v_homepage_540_; lean_object* v_license_541_; lean_object* v_licenseFiles_542_; lean_object* v_readmeFile_543_; uint8_t v_reservoir_544_; lean_object* v_enableArtifactCache_x3f_545_; lean_object* v_restoreAllArtifacts_x3f_546_; uint8_t v_libPrefixOnWindows_547_; uint8_t v_allowImportAll_548_; uint8_t v_fixedToolchain_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_toWorkspaceConfig_518_ = lean_ctor_get(v_cfg_517_, 0);
v_toLeanConfig_519_ = lean_ctor_get(v_cfg_517_, 1);
v_bootstrap_520_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26);
v_extraDepTargets_521_ = lean_ctor_get(v_cfg_517_, 2);
v_precompileModules_522_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_523_ = lean_ctor_get(v_cfg_517_, 3);
v_buildDir_524_ = lean_ctor_get(v_cfg_517_, 5);
v_leanLibDir_525_ = lean_ctor_get(v_cfg_517_, 6);
v_nativeLibDir_526_ = lean_ctor_get(v_cfg_517_, 7);
v_binDir_527_ = lean_ctor_get(v_cfg_517_, 8);
v_irDir_528_ = lean_ctor_get(v_cfg_517_, 9);
v_releaseRepo_529_ = lean_ctor_get(v_cfg_517_, 10);
v_buildArchive_530_ = lean_ctor_get(v_cfg_517_, 11);
v_preferReleaseBuild_531_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26 + 2);
v_testDriver_532_ = lean_ctor_get(v_cfg_517_, 12);
v_testDriverArgs_533_ = lean_ctor_get(v_cfg_517_, 13);
v_lintDriver_534_ = lean_ctor_get(v_cfg_517_, 14);
v_lintDriverArgs_535_ = lean_ctor_get(v_cfg_517_, 15);
v_version_536_ = lean_ctor_get(v_cfg_517_, 16);
v_versionTags_537_ = lean_ctor_get(v_cfg_517_, 17);
v_description_538_ = lean_ctor_get(v_cfg_517_, 18);
v_keywords_539_ = lean_ctor_get(v_cfg_517_, 19);
v_homepage_540_ = lean_ctor_get(v_cfg_517_, 20);
v_license_541_ = lean_ctor_get(v_cfg_517_, 21);
v_licenseFiles_542_ = lean_ctor_get(v_cfg_517_, 22);
v_readmeFile_543_ = lean_ctor_get(v_cfg_517_, 23);
v_reservoir_544_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_545_ = lean_ctor_get(v_cfg_517_, 24);
v_restoreAllArtifacts_x3f_546_ = lean_ctor_get(v_cfg_517_, 25);
v_libPrefixOnWindows_547_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26 + 4);
v_allowImportAll_548_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26 + 5);
v_fixedToolchain_549_ = lean_ctor_get_uint8(v_cfg_517_, sizeof(void*)*26 + 6);
v_isSharedCheck_556_ = !lean_is_exclusive(v_cfg_517_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_cfg_517_, 4);
lean_dec(v_unused_557_);
v___x_551_ = v_cfg_517_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_546_);
lean_inc(v_enableArtifactCache_x3f_545_);
lean_inc(v_readmeFile_543_);
lean_inc(v_licenseFiles_542_);
lean_inc(v_license_541_);
lean_inc(v_homepage_540_);
lean_inc(v_keywords_539_);
lean_inc(v_description_538_);
lean_inc(v_versionTags_537_);
lean_inc(v_version_536_);
lean_inc(v_lintDriverArgs_535_);
lean_inc(v_lintDriver_534_);
lean_inc(v_testDriverArgs_533_);
lean_inc(v_testDriver_532_);
lean_inc(v_buildArchive_530_);
lean_inc(v_releaseRepo_529_);
lean_inc(v_irDir_528_);
lean_inc(v_binDir_527_);
lean_inc(v_nativeLibDir_526_);
lean_inc(v_leanLibDir_525_);
lean_inc(v_buildDir_524_);
lean_inc(v_moreGlobalServerArgs_523_);
lean_inc(v_extraDepTargets_521_);
lean_inc(v_toLeanConfig_519_);
lean_inc(v_toWorkspaceConfig_518_);
lean_dec(v_cfg_517_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 4, v_val_516_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_toWorkspaceConfig_518_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_toLeanConfig_519_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_extraDepTargets_521_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_moreGlobalServerArgs_523_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_val_516_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_buildDir_524_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_leanLibDir_525_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_nativeLibDir_526_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_binDir_527_);
lean_ctor_set(v_reuseFailAlloc_555_, 9, v_irDir_528_);
lean_ctor_set(v_reuseFailAlloc_555_, 10, v_releaseRepo_529_);
lean_ctor_set(v_reuseFailAlloc_555_, 11, v_buildArchive_530_);
lean_ctor_set(v_reuseFailAlloc_555_, 12, v_testDriver_532_);
lean_ctor_set(v_reuseFailAlloc_555_, 13, v_testDriverArgs_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 14, v_lintDriver_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 15, v_lintDriverArgs_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 16, v_version_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 17, v_versionTags_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 18, v_description_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 19, v_keywords_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 20, v_homepage_540_);
lean_ctor_set(v_reuseFailAlloc_555_, 21, v_license_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 22, v_licenseFiles_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 23, v_readmeFile_543_);
lean_ctor_set(v_reuseFailAlloc_555_, 24, v_enableArtifactCache_x3f_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 25, v_restoreAllArtifacts_x3f_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26, v_bootstrap_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26 + 1, v_precompileModules_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26 + 2, v_preferReleaseBuild_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26 + 3, v_reservoir_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26 + 5, v_allowImportAll_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*26 + 6, v_fixedToolchain_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* v_f_558_, lean_object* v_cfg_559_){
_start:
{
lean_object* v_toWorkspaceConfig_560_; lean_object* v_toLeanConfig_561_; uint8_t v_bootstrap_562_; lean_object* v_extraDepTargets_563_; uint8_t v_precompileModules_564_; lean_object* v_moreGlobalServerArgs_565_; lean_object* v_srcDir_566_; lean_object* v_buildDir_567_; lean_object* v_leanLibDir_568_; lean_object* v_nativeLibDir_569_; lean_object* v_binDir_570_; lean_object* v_irDir_571_; lean_object* v_releaseRepo_572_; lean_object* v_buildArchive_573_; uint8_t v_preferReleaseBuild_574_; lean_object* v_testDriver_575_; lean_object* v_testDriverArgs_576_; lean_object* v_lintDriver_577_; lean_object* v_lintDriverArgs_578_; lean_object* v_version_579_; lean_object* v_versionTags_580_; lean_object* v_description_581_; lean_object* v_keywords_582_; lean_object* v_homepage_583_; lean_object* v_license_584_; lean_object* v_licenseFiles_585_; lean_object* v_readmeFile_586_; uint8_t v_reservoir_587_; lean_object* v_enableArtifactCache_x3f_588_; lean_object* v_restoreAllArtifacts_x3f_589_; uint8_t v_libPrefixOnWindows_590_; uint8_t v_allowImportAll_591_; uint8_t v_fixedToolchain_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_toWorkspaceConfig_560_ = lean_ctor_get(v_cfg_559_, 0);
v_toLeanConfig_561_ = lean_ctor_get(v_cfg_559_, 1);
v_bootstrap_562_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26);
v_extraDepTargets_563_ = lean_ctor_get(v_cfg_559_, 2);
v_precompileModules_564_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_565_ = lean_ctor_get(v_cfg_559_, 3);
v_srcDir_566_ = lean_ctor_get(v_cfg_559_, 4);
v_buildDir_567_ = lean_ctor_get(v_cfg_559_, 5);
v_leanLibDir_568_ = lean_ctor_get(v_cfg_559_, 6);
v_nativeLibDir_569_ = lean_ctor_get(v_cfg_559_, 7);
v_binDir_570_ = lean_ctor_get(v_cfg_559_, 8);
v_irDir_571_ = lean_ctor_get(v_cfg_559_, 9);
v_releaseRepo_572_ = lean_ctor_get(v_cfg_559_, 10);
v_buildArchive_573_ = lean_ctor_get(v_cfg_559_, 11);
v_preferReleaseBuild_574_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26 + 2);
v_testDriver_575_ = lean_ctor_get(v_cfg_559_, 12);
v_testDriverArgs_576_ = lean_ctor_get(v_cfg_559_, 13);
v_lintDriver_577_ = lean_ctor_get(v_cfg_559_, 14);
v_lintDriverArgs_578_ = lean_ctor_get(v_cfg_559_, 15);
v_version_579_ = lean_ctor_get(v_cfg_559_, 16);
v_versionTags_580_ = lean_ctor_get(v_cfg_559_, 17);
v_description_581_ = lean_ctor_get(v_cfg_559_, 18);
v_keywords_582_ = lean_ctor_get(v_cfg_559_, 19);
v_homepage_583_ = lean_ctor_get(v_cfg_559_, 20);
v_license_584_ = lean_ctor_get(v_cfg_559_, 21);
v_licenseFiles_585_ = lean_ctor_get(v_cfg_559_, 22);
v_readmeFile_586_ = lean_ctor_get(v_cfg_559_, 23);
v_reservoir_587_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_588_ = lean_ctor_get(v_cfg_559_, 24);
v_restoreAllArtifacts_x3f_589_ = lean_ctor_get(v_cfg_559_, 25);
v_libPrefixOnWindows_590_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26 + 4);
v_allowImportAll_591_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26 + 5);
v_fixedToolchain_592_ = lean_ctor_get_uint8(v_cfg_559_, sizeof(void*)*26 + 6);
v_isSharedCheck_600_ = !lean_is_exclusive(v_cfg_559_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v_cfg_559_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_589_);
lean_inc(v_enableArtifactCache_x3f_588_);
lean_inc(v_readmeFile_586_);
lean_inc(v_licenseFiles_585_);
lean_inc(v_license_584_);
lean_inc(v_homepage_583_);
lean_inc(v_keywords_582_);
lean_inc(v_description_581_);
lean_inc(v_versionTags_580_);
lean_inc(v_version_579_);
lean_inc(v_lintDriverArgs_578_);
lean_inc(v_lintDriver_577_);
lean_inc(v_testDriverArgs_576_);
lean_inc(v_testDriver_575_);
lean_inc(v_buildArchive_573_);
lean_inc(v_releaseRepo_572_);
lean_inc(v_irDir_571_);
lean_inc(v_binDir_570_);
lean_inc(v_nativeLibDir_569_);
lean_inc(v_leanLibDir_568_);
lean_inc(v_buildDir_567_);
lean_inc(v_srcDir_566_);
lean_inc(v_moreGlobalServerArgs_565_);
lean_inc(v_extraDepTargets_563_);
lean_inc(v_toLeanConfig_561_);
lean_inc(v_toWorkspaceConfig_560_);
lean_dec(v_cfg_559_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_apply_1(v_f_558_, v_srcDir_566_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_toWorkspaceConfig_560_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_toLeanConfig_561_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_extraDepTargets_563_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_moreGlobalServerArgs_565_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_buildDir_567_);
lean_ctor_set(v_reuseFailAlloc_599_, 6, v_leanLibDir_568_);
lean_ctor_set(v_reuseFailAlloc_599_, 7, v_nativeLibDir_569_);
lean_ctor_set(v_reuseFailAlloc_599_, 8, v_binDir_570_);
lean_ctor_set(v_reuseFailAlloc_599_, 9, v_irDir_571_);
lean_ctor_set(v_reuseFailAlloc_599_, 10, v_releaseRepo_572_);
lean_ctor_set(v_reuseFailAlloc_599_, 11, v_buildArchive_573_);
lean_ctor_set(v_reuseFailAlloc_599_, 12, v_testDriver_575_);
lean_ctor_set(v_reuseFailAlloc_599_, 13, v_testDriverArgs_576_);
lean_ctor_set(v_reuseFailAlloc_599_, 14, v_lintDriver_577_);
lean_ctor_set(v_reuseFailAlloc_599_, 15, v_lintDriverArgs_578_);
lean_ctor_set(v_reuseFailAlloc_599_, 16, v_version_579_);
lean_ctor_set(v_reuseFailAlloc_599_, 17, v_versionTags_580_);
lean_ctor_set(v_reuseFailAlloc_599_, 18, v_description_581_);
lean_ctor_set(v_reuseFailAlloc_599_, 19, v_keywords_582_);
lean_ctor_set(v_reuseFailAlloc_599_, 20, v_homepage_583_);
lean_ctor_set(v_reuseFailAlloc_599_, 21, v_license_584_);
lean_ctor_set(v_reuseFailAlloc_599_, 22, v_licenseFiles_585_);
lean_ctor_set(v_reuseFailAlloc_599_, 23, v_readmeFile_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 24, v_enableArtifactCache_x3f_588_);
lean_ctor_set(v_reuseFailAlloc_599_, 25, v_restoreAllArtifacts_x3f_589_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26, v_bootstrap_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26 + 1, v_precompileModules_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26 + 2, v_preferReleaseBuild_574_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26 + 3, v_reservoir_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_590_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26 + 5, v_allowImportAll_591_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*26 + 6, v_fixedToolchain_592_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0));
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lake_PackageConfig_srcDir___proj___lam__3(v_x_604_);
lean_dec_ref(v_x_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_615_, lean_object* v_n_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_618_, lean_object* v_n_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lake_PackageConfig_srcDir___proj(v_p_618_, v_n_619_);
lean_dec(v_n_619_);
lean_dec(v_p_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_621_, lean_object* v_n_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lake_PackageConfig_srcDir___proj(v_p_621_, v_n_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_624_, lean_object* v_n_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_624_, v_n_625_);
lean_dec(v_n_625_);
lean_dec(v_p_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* v_cfg_627_){
_start:
{
lean_object* v_buildDir_628_; 
v_buildDir_628_ = lean_ctor_get(v_cfg_627_, 5);
lean_inc_ref(v_buildDir_628_);
return v_buildDir_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* v_cfg_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lake_PackageConfig_buildDir___proj___lam__0(v_cfg_629_);
lean_dec_ref(v_cfg_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* v_val_631_, lean_object* v_cfg_632_){
_start:
{
lean_object* v_toWorkspaceConfig_633_; lean_object* v_toLeanConfig_634_; uint8_t v_bootstrap_635_; lean_object* v_extraDepTargets_636_; uint8_t v_precompileModules_637_; lean_object* v_moreGlobalServerArgs_638_; lean_object* v_srcDir_639_; lean_object* v_leanLibDir_640_; lean_object* v_nativeLibDir_641_; lean_object* v_binDir_642_; lean_object* v_irDir_643_; lean_object* v_releaseRepo_644_; lean_object* v_buildArchive_645_; uint8_t v_preferReleaseBuild_646_; lean_object* v_testDriver_647_; lean_object* v_testDriverArgs_648_; lean_object* v_lintDriver_649_; lean_object* v_lintDriverArgs_650_; lean_object* v_version_651_; lean_object* v_versionTags_652_; lean_object* v_description_653_; lean_object* v_keywords_654_; lean_object* v_homepage_655_; lean_object* v_license_656_; lean_object* v_licenseFiles_657_; lean_object* v_readmeFile_658_; uint8_t v_reservoir_659_; lean_object* v_enableArtifactCache_x3f_660_; lean_object* v_restoreAllArtifacts_x3f_661_; uint8_t v_libPrefixOnWindows_662_; uint8_t v_allowImportAll_663_; uint8_t v_fixedToolchain_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_toWorkspaceConfig_633_ = lean_ctor_get(v_cfg_632_, 0);
v_toLeanConfig_634_ = lean_ctor_get(v_cfg_632_, 1);
v_bootstrap_635_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26);
v_extraDepTargets_636_ = lean_ctor_get(v_cfg_632_, 2);
v_precompileModules_637_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_638_ = lean_ctor_get(v_cfg_632_, 3);
v_srcDir_639_ = lean_ctor_get(v_cfg_632_, 4);
v_leanLibDir_640_ = lean_ctor_get(v_cfg_632_, 6);
v_nativeLibDir_641_ = lean_ctor_get(v_cfg_632_, 7);
v_binDir_642_ = lean_ctor_get(v_cfg_632_, 8);
v_irDir_643_ = lean_ctor_get(v_cfg_632_, 9);
v_releaseRepo_644_ = lean_ctor_get(v_cfg_632_, 10);
v_buildArchive_645_ = lean_ctor_get(v_cfg_632_, 11);
v_preferReleaseBuild_646_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26 + 2);
v_testDriver_647_ = lean_ctor_get(v_cfg_632_, 12);
v_testDriverArgs_648_ = lean_ctor_get(v_cfg_632_, 13);
v_lintDriver_649_ = lean_ctor_get(v_cfg_632_, 14);
v_lintDriverArgs_650_ = lean_ctor_get(v_cfg_632_, 15);
v_version_651_ = lean_ctor_get(v_cfg_632_, 16);
v_versionTags_652_ = lean_ctor_get(v_cfg_632_, 17);
v_description_653_ = lean_ctor_get(v_cfg_632_, 18);
v_keywords_654_ = lean_ctor_get(v_cfg_632_, 19);
v_homepage_655_ = lean_ctor_get(v_cfg_632_, 20);
v_license_656_ = lean_ctor_get(v_cfg_632_, 21);
v_licenseFiles_657_ = lean_ctor_get(v_cfg_632_, 22);
v_readmeFile_658_ = lean_ctor_get(v_cfg_632_, 23);
v_reservoir_659_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_660_ = lean_ctor_get(v_cfg_632_, 24);
v_restoreAllArtifacts_x3f_661_ = lean_ctor_get(v_cfg_632_, 25);
v_libPrefixOnWindows_662_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26 + 4);
v_allowImportAll_663_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26 + 5);
v_fixedToolchain_664_ = lean_ctor_get_uint8(v_cfg_632_, sizeof(void*)*26 + 6);
v_isSharedCheck_671_ = !lean_is_exclusive(v_cfg_632_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_cfg_632_, 5);
lean_dec(v_unused_672_);
v___x_666_ = v_cfg_632_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_661_);
lean_inc(v_enableArtifactCache_x3f_660_);
lean_inc(v_readmeFile_658_);
lean_inc(v_licenseFiles_657_);
lean_inc(v_license_656_);
lean_inc(v_homepage_655_);
lean_inc(v_keywords_654_);
lean_inc(v_description_653_);
lean_inc(v_versionTags_652_);
lean_inc(v_version_651_);
lean_inc(v_lintDriverArgs_650_);
lean_inc(v_lintDriver_649_);
lean_inc(v_testDriverArgs_648_);
lean_inc(v_testDriver_647_);
lean_inc(v_buildArchive_645_);
lean_inc(v_releaseRepo_644_);
lean_inc(v_irDir_643_);
lean_inc(v_binDir_642_);
lean_inc(v_nativeLibDir_641_);
lean_inc(v_leanLibDir_640_);
lean_inc(v_srcDir_639_);
lean_inc(v_moreGlobalServerArgs_638_);
lean_inc(v_extraDepTargets_636_);
lean_inc(v_toLeanConfig_634_);
lean_inc(v_toWorkspaceConfig_633_);
lean_dec(v_cfg_632_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v_val_631_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_toWorkspaceConfig_633_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_toLeanConfig_634_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_extraDepTargets_636_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_moreGlobalServerArgs_638_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_srcDir_639_);
lean_ctor_set(v_reuseFailAlloc_670_, 5, v_val_631_);
lean_ctor_set(v_reuseFailAlloc_670_, 6, v_leanLibDir_640_);
lean_ctor_set(v_reuseFailAlloc_670_, 7, v_nativeLibDir_641_);
lean_ctor_set(v_reuseFailAlloc_670_, 8, v_binDir_642_);
lean_ctor_set(v_reuseFailAlloc_670_, 9, v_irDir_643_);
lean_ctor_set(v_reuseFailAlloc_670_, 10, v_releaseRepo_644_);
lean_ctor_set(v_reuseFailAlloc_670_, 11, v_buildArchive_645_);
lean_ctor_set(v_reuseFailAlloc_670_, 12, v_testDriver_647_);
lean_ctor_set(v_reuseFailAlloc_670_, 13, v_testDriverArgs_648_);
lean_ctor_set(v_reuseFailAlloc_670_, 14, v_lintDriver_649_);
lean_ctor_set(v_reuseFailAlloc_670_, 15, v_lintDriverArgs_650_);
lean_ctor_set(v_reuseFailAlloc_670_, 16, v_version_651_);
lean_ctor_set(v_reuseFailAlloc_670_, 17, v_versionTags_652_);
lean_ctor_set(v_reuseFailAlloc_670_, 18, v_description_653_);
lean_ctor_set(v_reuseFailAlloc_670_, 19, v_keywords_654_);
lean_ctor_set(v_reuseFailAlloc_670_, 20, v_homepage_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 21, v_license_656_);
lean_ctor_set(v_reuseFailAlloc_670_, 22, v_licenseFiles_657_);
lean_ctor_set(v_reuseFailAlloc_670_, 23, v_readmeFile_658_);
lean_ctor_set(v_reuseFailAlloc_670_, 24, v_enableArtifactCache_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 25, v_restoreAllArtifacts_x3f_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26, v_bootstrap_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26 + 1, v_precompileModules_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26 + 2, v_preferReleaseBuild_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26 + 3, v_reservoir_659_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26 + 5, v_allowImportAll_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*26 + 6, v_fixedToolchain_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* v_f_673_, lean_object* v_cfg_674_){
_start:
{
lean_object* v_toWorkspaceConfig_675_; lean_object* v_toLeanConfig_676_; uint8_t v_bootstrap_677_; lean_object* v_extraDepTargets_678_; uint8_t v_precompileModules_679_; lean_object* v_moreGlobalServerArgs_680_; lean_object* v_srcDir_681_; lean_object* v_buildDir_682_; lean_object* v_leanLibDir_683_; lean_object* v_nativeLibDir_684_; lean_object* v_binDir_685_; lean_object* v_irDir_686_; lean_object* v_releaseRepo_687_; lean_object* v_buildArchive_688_; uint8_t v_preferReleaseBuild_689_; lean_object* v_testDriver_690_; lean_object* v_testDriverArgs_691_; lean_object* v_lintDriver_692_; lean_object* v_lintDriverArgs_693_; lean_object* v_version_694_; lean_object* v_versionTags_695_; lean_object* v_description_696_; lean_object* v_keywords_697_; lean_object* v_homepage_698_; lean_object* v_license_699_; lean_object* v_licenseFiles_700_; lean_object* v_readmeFile_701_; uint8_t v_reservoir_702_; lean_object* v_enableArtifactCache_x3f_703_; lean_object* v_restoreAllArtifacts_x3f_704_; uint8_t v_libPrefixOnWindows_705_; uint8_t v_allowImportAll_706_; uint8_t v_fixedToolchain_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_toWorkspaceConfig_675_ = lean_ctor_get(v_cfg_674_, 0);
v_toLeanConfig_676_ = lean_ctor_get(v_cfg_674_, 1);
v_bootstrap_677_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26);
v_extraDepTargets_678_ = lean_ctor_get(v_cfg_674_, 2);
v_precompileModules_679_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_680_ = lean_ctor_get(v_cfg_674_, 3);
v_srcDir_681_ = lean_ctor_get(v_cfg_674_, 4);
v_buildDir_682_ = lean_ctor_get(v_cfg_674_, 5);
v_leanLibDir_683_ = lean_ctor_get(v_cfg_674_, 6);
v_nativeLibDir_684_ = lean_ctor_get(v_cfg_674_, 7);
v_binDir_685_ = lean_ctor_get(v_cfg_674_, 8);
v_irDir_686_ = lean_ctor_get(v_cfg_674_, 9);
v_releaseRepo_687_ = lean_ctor_get(v_cfg_674_, 10);
v_buildArchive_688_ = lean_ctor_get(v_cfg_674_, 11);
v_preferReleaseBuild_689_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26 + 2);
v_testDriver_690_ = lean_ctor_get(v_cfg_674_, 12);
v_testDriverArgs_691_ = lean_ctor_get(v_cfg_674_, 13);
v_lintDriver_692_ = lean_ctor_get(v_cfg_674_, 14);
v_lintDriverArgs_693_ = lean_ctor_get(v_cfg_674_, 15);
v_version_694_ = lean_ctor_get(v_cfg_674_, 16);
v_versionTags_695_ = lean_ctor_get(v_cfg_674_, 17);
v_description_696_ = lean_ctor_get(v_cfg_674_, 18);
v_keywords_697_ = lean_ctor_get(v_cfg_674_, 19);
v_homepage_698_ = lean_ctor_get(v_cfg_674_, 20);
v_license_699_ = lean_ctor_get(v_cfg_674_, 21);
v_licenseFiles_700_ = lean_ctor_get(v_cfg_674_, 22);
v_readmeFile_701_ = lean_ctor_get(v_cfg_674_, 23);
v_reservoir_702_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_703_ = lean_ctor_get(v_cfg_674_, 24);
v_restoreAllArtifacts_x3f_704_ = lean_ctor_get(v_cfg_674_, 25);
v_libPrefixOnWindows_705_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26 + 4);
v_allowImportAll_706_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26 + 5);
v_fixedToolchain_707_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*26 + 6);
v_isSharedCheck_715_ = !lean_is_exclusive(v_cfg_674_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v_cfg_674_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_704_);
lean_inc(v_enableArtifactCache_x3f_703_);
lean_inc(v_readmeFile_701_);
lean_inc(v_licenseFiles_700_);
lean_inc(v_license_699_);
lean_inc(v_homepage_698_);
lean_inc(v_keywords_697_);
lean_inc(v_description_696_);
lean_inc(v_versionTags_695_);
lean_inc(v_version_694_);
lean_inc(v_lintDriverArgs_693_);
lean_inc(v_lintDriver_692_);
lean_inc(v_testDriverArgs_691_);
lean_inc(v_testDriver_690_);
lean_inc(v_buildArchive_688_);
lean_inc(v_releaseRepo_687_);
lean_inc(v_irDir_686_);
lean_inc(v_binDir_685_);
lean_inc(v_nativeLibDir_684_);
lean_inc(v_leanLibDir_683_);
lean_inc(v_buildDir_682_);
lean_inc(v_srcDir_681_);
lean_inc(v_moreGlobalServerArgs_680_);
lean_inc(v_extraDepTargets_678_);
lean_inc(v_toLeanConfig_676_);
lean_inc(v_toWorkspaceConfig_675_);
lean_dec(v_cfg_674_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_apply_1(v_f_673_, v_buildDir_682_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 5, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_toWorkspaceConfig_675_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_toLeanConfig_676_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_extraDepTargets_678_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_moreGlobalServerArgs_680_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_srcDir_681_);
lean_ctor_set(v_reuseFailAlloc_714_, 5, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_714_, 6, v_leanLibDir_683_);
lean_ctor_set(v_reuseFailAlloc_714_, 7, v_nativeLibDir_684_);
lean_ctor_set(v_reuseFailAlloc_714_, 8, v_binDir_685_);
lean_ctor_set(v_reuseFailAlloc_714_, 9, v_irDir_686_);
lean_ctor_set(v_reuseFailAlloc_714_, 10, v_releaseRepo_687_);
lean_ctor_set(v_reuseFailAlloc_714_, 11, v_buildArchive_688_);
lean_ctor_set(v_reuseFailAlloc_714_, 12, v_testDriver_690_);
lean_ctor_set(v_reuseFailAlloc_714_, 13, v_testDriverArgs_691_);
lean_ctor_set(v_reuseFailAlloc_714_, 14, v_lintDriver_692_);
lean_ctor_set(v_reuseFailAlloc_714_, 15, v_lintDriverArgs_693_);
lean_ctor_set(v_reuseFailAlloc_714_, 16, v_version_694_);
lean_ctor_set(v_reuseFailAlloc_714_, 17, v_versionTags_695_);
lean_ctor_set(v_reuseFailAlloc_714_, 18, v_description_696_);
lean_ctor_set(v_reuseFailAlloc_714_, 19, v_keywords_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 20, v_homepage_698_);
lean_ctor_set(v_reuseFailAlloc_714_, 21, v_license_699_);
lean_ctor_set(v_reuseFailAlloc_714_, 22, v_licenseFiles_700_);
lean_ctor_set(v_reuseFailAlloc_714_, 23, v_readmeFile_701_);
lean_ctor_set(v_reuseFailAlloc_714_, 24, v_enableArtifactCache_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_714_, 25, v_restoreAllArtifacts_x3f_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26, v_bootstrap_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26 + 1, v_precompileModules_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26 + 2, v_preferReleaseBuild_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26 + 3, v_reservoir_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26 + 5, v_allowImportAll_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*26 + 6, v_fixedToolchain_707_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lake_defaultBuildDir;
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lake_PackageConfig_buildDir___proj___lam__3(v_x_718_);
lean_dec_ref(v_x_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_729_, lean_object* v_n_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_732_, lean_object* v_n_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lake_PackageConfig_buildDir___proj(v_p_732_, v_n_733_);
lean_dec(v_n_733_);
lean_dec(v_p_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_735_, lean_object* v_n_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lake_PackageConfig_buildDir___proj(v_p_735_, v_n_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_738_, lean_object* v_n_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_738_, v_n_739_);
lean_dec(v_n_739_);
lean_dec(v_p_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* v_cfg_741_){
_start:
{
lean_object* v_leanLibDir_742_; 
v_leanLibDir_742_ = lean_ctor_get(v_cfg_741_, 6);
lean_inc_ref(v_leanLibDir_742_);
return v_leanLibDir_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* v_cfg_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lake_PackageConfig_leanLibDir___proj___lam__0(v_cfg_743_);
lean_dec_ref(v_cfg_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* v_val_745_, lean_object* v_cfg_746_){
_start:
{
lean_object* v_toWorkspaceConfig_747_; lean_object* v_toLeanConfig_748_; uint8_t v_bootstrap_749_; lean_object* v_extraDepTargets_750_; uint8_t v_precompileModules_751_; lean_object* v_moreGlobalServerArgs_752_; lean_object* v_srcDir_753_; lean_object* v_buildDir_754_; lean_object* v_nativeLibDir_755_; lean_object* v_binDir_756_; lean_object* v_irDir_757_; lean_object* v_releaseRepo_758_; lean_object* v_buildArchive_759_; uint8_t v_preferReleaseBuild_760_; lean_object* v_testDriver_761_; lean_object* v_testDriverArgs_762_; lean_object* v_lintDriver_763_; lean_object* v_lintDriverArgs_764_; lean_object* v_version_765_; lean_object* v_versionTags_766_; lean_object* v_description_767_; lean_object* v_keywords_768_; lean_object* v_homepage_769_; lean_object* v_license_770_; lean_object* v_licenseFiles_771_; lean_object* v_readmeFile_772_; uint8_t v_reservoir_773_; lean_object* v_enableArtifactCache_x3f_774_; lean_object* v_restoreAllArtifacts_x3f_775_; uint8_t v_libPrefixOnWindows_776_; uint8_t v_allowImportAll_777_; uint8_t v_fixedToolchain_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_toWorkspaceConfig_747_ = lean_ctor_get(v_cfg_746_, 0);
v_toLeanConfig_748_ = lean_ctor_get(v_cfg_746_, 1);
v_bootstrap_749_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26);
v_extraDepTargets_750_ = lean_ctor_get(v_cfg_746_, 2);
v_precompileModules_751_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_752_ = lean_ctor_get(v_cfg_746_, 3);
v_srcDir_753_ = lean_ctor_get(v_cfg_746_, 4);
v_buildDir_754_ = lean_ctor_get(v_cfg_746_, 5);
v_nativeLibDir_755_ = lean_ctor_get(v_cfg_746_, 7);
v_binDir_756_ = lean_ctor_get(v_cfg_746_, 8);
v_irDir_757_ = lean_ctor_get(v_cfg_746_, 9);
v_releaseRepo_758_ = lean_ctor_get(v_cfg_746_, 10);
v_buildArchive_759_ = lean_ctor_get(v_cfg_746_, 11);
v_preferReleaseBuild_760_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26 + 2);
v_testDriver_761_ = lean_ctor_get(v_cfg_746_, 12);
v_testDriverArgs_762_ = lean_ctor_get(v_cfg_746_, 13);
v_lintDriver_763_ = lean_ctor_get(v_cfg_746_, 14);
v_lintDriverArgs_764_ = lean_ctor_get(v_cfg_746_, 15);
v_version_765_ = lean_ctor_get(v_cfg_746_, 16);
v_versionTags_766_ = lean_ctor_get(v_cfg_746_, 17);
v_description_767_ = lean_ctor_get(v_cfg_746_, 18);
v_keywords_768_ = lean_ctor_get(v_cfg_746_, 19);
v_homepage_769_ = lean_ctor_get(v_cfg_746_, 20);
v_license_770_ = lean_ctor_get(v_cfg_746_, 21);
v_licenseFiles_771_ = lean_ctor_get(v_cfg_746_, 22);
v_readmeFile_772_ = lean_ctor_get(v_cfg_746_, 23);
v_reservoir_773_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_774_ = lean_ctor_get(v_cfg_746_, 24);
v_restoreAllArtifacts_x3f_775_ = lean_ctor_get(v_cfg_746_, 25);
v_libPrefixOnWindows_776_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26 + 4);
v_allowImportAll_777_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26 + 5);
v_fixedToolchain_778_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*26 + 6);
v_isSharedCheck_785_ = !lean_is_exclusive(v_cfg_746_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_cfg_746_, 6);
lean_dec(v_unused_786_);
v___x_780_ = v_cfg_746_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_775_);
lean_inc(v_enableArtifactCache_x3f_774_);
lean_inc(v_readmeFile_772_);
lean_inc(v_licenseFiles_771_);
lean_inc(v_license_770_);
lean_inc(v_homepage_769_);
lean_inc(v_keywords_768_);
lean_inc(v_description_767_);
lean_inc(v_versionTags_766_);
lean_inc(v_version_765_);
lean_inc(v_lintDriverArgs_764_);
lean_inc(v_lintDriver_763_);
lean_inc(v_testDriverArgs_762_);
lean_inc(v_testDriver_761_);
lean_inc(v_buildArchive_759_);
lean_inc(v_releaseRepo_758_);
lean_inc(v_irDir_757_);
lean_inc(v_binDir_756_);
lean_inc(v_nativeLibDir_755_);
lean_inc(v_buildDir_754_);
lean_inc(v_srcDir_753_);
lean_inc(v_moreGlobalServerArgs_752_);
lean_inc(v_extraDepTargets_750_);
lean_inc(v_toLeanConfig_748_);
lean_inc(v_toWorkspaceConfig_747_);
lean_dec(v_cfg_746_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 6, v_val_745_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_toWorkspaceConfig_747_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_toLeanConfig_748_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_extraDepTargets_750_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_moreGlobalServerArgs_752_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_srcDir_753_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_buildDir_754_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_val_745_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_nativeLibDir_755_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_binDir_756_);
lean_ctor_set(v_reuseFailAlloc_784_, 9, v_irDir_757_);
lean_ctor_set(v_reuseFailAlloc_784_, 10, v_releaseRepo_758_);
lean_ctor_set(v_reuseFailAlloc_784_, 11, v_buildArchive_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 12, v_testDriver_761_);
lean_ctor_set(v_reuseFailAlloc_784_, 13, v_testDriverArgs_762_);
lean_ctor_set(v_reuseFailAlloc_784_, 14, v_lintDriver_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 15, v_lintDriverArgs_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 16, v_version_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 17, v_versionTags_766_);
lean_ctor_set(v_reuseFailAlloc_784_, 18, v_description_767_);
lean_ctor_set(v_reuseFailAlloc_784_, 19, v_keywords_768_);
lean_ctor_set(v_reuseFailAlloc_784_, 20, v_homepage_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 21, v_license_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 22, v_licenseFiles_771_);
lean_ctor_set(v_reuseFailAlloc_784_, 23, v_readmeFile_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 24, v_enableArtifactCache_x3f_774_);
lean_ctor_set(v_reuseFailAlloc_784_, 25, v_restoreAllArtifacts_x3f_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26, v_bootstrap_749_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26 + 1, v_precompileModules_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26 + 2, v_preferReleaseBuild_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26 + 3, v_reservoir_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26 + 5, v_allowImportAll_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*26 + 6, v_fixedToolchain_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* v_f_787_, lean_object* v_cfg_788_){
_start:
{
lean_object* v_toWorkspaceConfig_789_; lean_object* v_toLeanConfig_790_; uint8_t v_bootstrap_791_; lean_object* v_extraDepTargets_792_; uint8_t v_precompileModules_793_; lean_object* v_moreGlobalServerArgs_794_; lean_object* v_srcDir_795_; lean_object* v_buildDir_796_; lean_object* v_leanLibDir_797_; lean_object* v_nativeLibDir_798_; lean_object* v_binDir_799_; lean_object* v_irDir_800_; lean_object* v_releaseRepo_801_; lean_object* v_buildArchive_802_; uint8_t v_preferReleaseBuild_803_; lean_object* v_testDriver_804_; lean_object* v_testDriverArgs_805_; lean_object* v_lintDriver_806_; lean_object* v_lintDriverArgs_807_; lean_object* v_version_808_; lean_object* v_versionTags_809_; lean_object* v_description_810_; lean_object* v_keywords_811_; lean_object* v_homepage_812_; lean_object* v_license_813_; lean_object* v_licenseFiles_814_; lean_object* v_readmeFile_815_; uint8_t v_reservoir_816_; lean_object* v_enableArtifactCache_x3f_817_; lean_object* v_restoreAllArtifacts_x3f_818_; uint8_t v_libPrefixOnWindows_819_; uint8_t v_allowImportAll_820_; uint8_t v_fixedToolchain_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_toWorkspaceConfig_789_ = lean_ctor_get(v_cfg_788_, 0);
v_toLeanConfig_790_ = lean_ctor_get(v_cfg_788_, 1);
v_bootstrap_791_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26);
v_extraDepTargets_792_ = lean_ctor_get(v_cfg_788_, 2);
v_precompileModules_793_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_794_ = lean_ctor_get(v_cfg_788_, 3);
v_srcDir_795_ = lean_ctor_get(v_cfg_788_, 4);
v_buildDir_796_ = lean_ctor_get(v_cfg_788_, 5);
v_leanLibDir_797_ = lean_ctor_get(v_cfg_788_, 6);
v_nativeLibDir_798_ = lean_ctor_get(v_cfg_788_, 7);
v_binDir_799_ = lean_ctor_get(v_cfg_788_, 8);
v_irDir_800_ = lean_ctor_get(v_cfg_788_, 9);
v_releaseRepo_801_ = lean_ctor_get(v_cfg_788_, 10);
v_buildArchive_802_ = lean_ctor_get(v_cfg_788_, 11);
v_preferReleaseBuild_803_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26 + 2);
v_testDriver_804_ = lean_ctor_get(v_cfg_788_, 12);
v_testDriverArgs_805_ = lean_ctor_get(v_cfg_788_, 13);
v_lintDriver_806_ = lean_ctor_get(v_cfg_788_, 14);
v_lintDriverArgs_807_ = lean_ctor_get(v_cfg_788_, 15);
v_version_808_ = lean_ctor_get(v_cfg_788_, 16);
v_versionTags_809_ = lean_ctor_get(v_cfg_788_, 17);
v_description_810_ = lean_ctor_get(v_cfg_788_, 18);
v_keywords_811_ = lean_ctor_get(v_cfg_788_, 19);
v_homepage_812_ = lean_ctor_get(v_cfg_788_, 20);
v_license_813_ = lean_ctor_get(v_cfg_788_, 21);
v_licenseFiles_814_ = lean_ctor_get(v_cfg_788_, 22);
v_readmeFile_815_ = lean_ctor_get(v_cfg_788_, 23);
v_reservoir_816_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_817_ = lean_ctor_get(v_cfg_788_, 24);
v_restoreAllArtifacts_x3f_818_ = lean_ctor_get(v_cfg_788_, 25);
v_libPrefixOnWindows_819_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26 + 4);
v_allowImportAll_820_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26 + 5);
v_fixedToolchain_821_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*26 + 6);
v_isSharedCheck_829_ = !lean_is_exclusive(v_cfg_788_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v_cfg_788_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_818_);
lean_inc(v_enableArtifactCache_x3f_817_);
lean_inc(v_readmeFile_815_);
lean_inc(v_licenseFiles_814_);
lean_inc(v_license_813_);
lean_inc(v_homepage_812_);
lean_inc(v_keywords_811_);
lean_inc(v_description_810_);
lean_inc(v_versionTags_809_);
lean_inc(v_version_808_);
lean_inc(v_lintDriverArgs_807_);
lean_inc(v_lintDriver_806_);
lean_inc(v_testDriverArgs_805_);
lean_inc(v_testDriver_804_);
lean_inc(v_buildArchive_802_);
lean_inc(v_releaseRepo_801_);
lean_inc(v_irDir_800_);
lean_inc(v_binDir_799_);
lean_inc(v_nativeLibDir_798_);
lean_inc(v_leanLibDir_797_);
lean_inc(v_buildDir_796_);
lean_inc(v_srcDir_795_);
lean_inc(v_moreGlobalServerArgs_794_);
lean_inc(v_extraDepTargets_792_);
lean_inc(v_toLeanConfig_790_);
lean_inc(v_toWorkspaceConfig_789_);
lean_dec(v_cfg_788_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_apply_1(v_f_787_, v_leanLibDir_797_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 6, v___x_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_toWorkspaceConfig_789_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_toLeanConfig_790_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_extraDepTargets_792_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_moreGlobalServerArgs_794_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_srcDir_795_);
lean_ctor_set(v_reuseFailAlloc_828_, 5, v_buildDir_796_);
lean_ctor_set(v_reuseFailAlloc_828_, 6, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 7, v_nativeLibDir_798_);
lean_ctor_set(v_reuseFailAlloc_828_, 8, v_binDir_799_);
lean_ctor_set(v_reuseFailAlloc_828_, 9, v_irDir_800_);
lean_ctor_set(v_reuseFailAlloc_828_, 10, v_releaseRepo_801_);
lean_ctor_set(v_reuseFailAlloc_828_, 11, v_buildArchive_802_);
lean_ctor_set(v_reuseFailAlloc_828_, 12, v_testDriver_804_);
lean_ctor_set(v_reuseFailAlloc_828_, 13, v_testDriverArgs_805_);
lean_ctor_set(v_reuseFailAlloc_828_, 14, v_lintDriver_806_);
lean_ctor_set(v_reuseFailAlloc_828_, 15, v_lintDriverArgs_807_);
lean_ctor_set(v_reuseFailAlloc_828_, 16, v_version_808_);
lean_ctor_set(v_reuseFailAlloc_828_, 17, v_versionTags_809_);
lean_ctor_set(v_reuseFailAlloc_828_, 18, v_description_810_);
lean_ctor_set(v_reuseFailAlloc_828_, 19, v_keywords_811_);
lean_ctor_set(v_reuseFailAlloc_828_, 20, v_homepage_812_);
lean_ctor_set(v_reuseFailAlloc_828_, 21, v_license_813_);
lean_ctor_set(v_reuseFailAlloc_828_, 22, v_licenseFiles_814_);
lean_ctor_set(v_reuseFailAlloc_828_, 23, v_readmeFile_815_);
lean_ctor_set(v_reuseFailAlloc_828_, 24, v_enableArtifactCache_x3f_817_);
lean_ctor_set(v_reuseFailAlloc_828_, 25, v_restoreAllArtifacts_x3f_818_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26, v_bootstrap_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26 + 1, v_precompileModules_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26 + 2, v_preferReleaseBuild_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26 + 3, v_reservoir_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26 + 5, v_allowImportAll_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*26 + 6, v_fixedToolchain_821_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lake_defaultLeanLibDir;
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_PackageConfig_leanLibDir___proj___lam__3(v_x_832_);
lean_dec_ref(v_x_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_843_, lean_object* v_n_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_846_, lean_object* v_n_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_846_, v_n_847_);
lean_dec(v_n_847_);
lean_dec(v_p_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_849_, lean_object* v_n_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_849_, v_n_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_852_, lean_object* v_n_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_852_, v_n_853_);
lean_dec(v_n_853_);
lean_dec(v_p_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* v_cfg_855_){
_start:
{
lean_object* v_nativeLibDir_856_; 
v_nativeLibDir_856_ = lean_ctor_get(v_cfg_855_, 7);
lean_inc_ref(v_nativeLibDir_856_);
return v_nativeLibDir_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* v_cfg_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(v_cfg_857_);
lean_dec_ref(v_cfg_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* v_val_859_, lean_object* v_cfg_860_){
_start:
{
lean_object* v_toWorkspaceConfig_861_; lean_object* v_toLeanConfig_862_; uint8_t v_bootstrap_863_; lean_object* v_extraDepTargets_864_; uint8_t v_precompileModules_865_; lean_object* v_moreGlobalServerArgs_866_; lean_object* v_srcDir_867_; lean_object* v_buildDir_868_; lean_object* v_leanLibDir_869_; lean_object* v_binDir_870_; lean_object* v_irDir_871_; lean_object* v_releaseRepo_872_; lean_object* v_buildArchive_873_; uint8_t v_preferReleaseBuild_874_; lean_object* v_testDriver_875_; lean_object* v_testDriverArgs_876_; lean_object* v_lintDriver_877_; lean_object* v_lintDriverArgs_878_; lean_object* v_version_879_; lean_object* v_versionTags_880_; lean_object* v_description_881_; lean_object* v_keywords_882_; lean_object* v_homepage_883_; lean_object* v_license_884_; lean_object* v_licenseFiles_885_; lean_object* v_readmeFile_886_; uint8_t v_reservoir_887_; lean_object* v_enableArtifactCache_x3f_888_; lean_object* v_restoreAllArtifacts_x3f_889_; uint8_t v_libPrefixOnWindows_890_; uint8_t v_allowImportAll_891_; uint8_t v_fixedToolchain_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_toWorkspaceConfig_861_ = lean_ctor_get(v_cfg_860_, 0);
v_toLeanConfig_862_ = lean_ctor_get(v_cfg_860_, 1);
v_bootstrap_863_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26);
v_extraDepTargets_864_ = lean_ctor_get(v_cfg_860_, 2);
v_precompileModules_865_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_866_ = lean_ctor_get(v_cfg_860_, 3);
v_srcDir_867_ = lean_ctor_get(v_cfg_860_, 4);
v_buildDir_868_ = lean_ctor_get(v_cfg_860_, 5);
v_leanLibDir_869_ = lean_ctor_get(v_cfg_860_, 6);
v_binDir_870_ = lean_ctor_get(v_cfg_860_, 8);
v_irDir_871_ = lean_ctor_get(v_cfg_860_, 9);
v_releaseRepo_872_ = lean_ctor_get(v_cfg_860_, 10);
v_buildArchive_873_ = lean_ctor_get(v_cfg_860_, 11);
v_preferReleaseBuild_874_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26 + 2);
v_testDriver_875_ = lean_ctor_get(v_cfg_860_, 12);
v_testDriverArgs_876_ = lean_ctor_get(v_cfg_860_, 13);
v_lintDriver_877_ = lean_ctor_get(v_cfg_860_, 14);
v_lintDriverArgs_878_ = lean_ctor_get(v_cfg_860_, 15);
v_version_879_ = lean_ctor_get(v_cfg_860_, 16);
v_versionTags_880_ = lean_ctor_get(v_cfg_860_, 17);
v_description_881_ = lean_ctor_get(v_cfg_860_, 18);
v_keywords_882_ = lean_ctor_get(v_cfg_860_, 19);
v_homepage_883_ = lean_ctor_get(v_cfg_860_, 20);
v_license_884_ = lean_ctor_get(v_cfg_860_, 21);
v_licenseFiles_885_ = lean_ctor_get(v_cfg_860_, 22);
v_readmeFile_886_ = lean_ctor_get(v_cfg_860_, 23);
v_reservoir_887_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_888_ = lean_ctor_get(v_cfg_860_, 24);
v_restoreAllArtifacts_x3f_889_ = lean_ctor_get(v_cfg_860_, 25);
v_libPrefixOnWindows_890_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26 + 4);
v_allowImportAll_891_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26 + 5);
v_fixedToolchain_892_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*26 + 6);
v_isSharedCheck_899_ = !lean_is_exclusive(v_cfg_860_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_cfg_860_, 7);
lean_dec(v_unused_900_);
v___x_894_ = v_cfg_860_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_889_);
lean_inc(v_enableArtifactCache_x3f_888_);
lean_inc(v_readmeFile_886_);
lean_inc(v_licenseFiles_885_);
lean_inc(v_license_884_);
lean_inc(v_homepage_883_);
lean_inc(v_keywords_882_);
lean_inc(v_description_881_);
lean_inc(v_versionTags_880_);
lean_inc(v_version_879_);
lean_inc(v_lintDriverArgs_878_);
lean_inc(v_lintDriver_877_);
lean_inc(v_testDriverArgs_876_);
lean_inc(v_testDriver_875_);
lean_inc(v_buildArchive_873_);
lean_inc(v_releaseRepo_872_);
lean_inc(v_irDir_871_);
lean_inc(v_binDir_870_);
lean_inc(v_leanLibDir_869_);
lean_inc(v_buildDir_868_);
lean_inc(v_srcDir_867_);
lean_inc(v_moreGlobalServerArgs_866_);
lean_inc(v_extraDepTargets_864_);
lean_inc(v_toLeanConfig_862_);
lean_inc(v_toWorkspaceConfig_861_);
lean_dec(v_cfg_860_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 7, v_val_859_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_toWorkspaceConfig_861_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_toLeanConfig_862_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_extraDepTargets_864_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_moreGlobalServerArgs_866_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_srcDir_867_);
lean_ctor_set(v_reuseFailAlloc_898_, 5, v_buildDir_868_);
lean_ctor_set(v_reuseFailAlloc_898_, 6, v_leanLibDir_869_);
lean_ctor_set(v_reuseFailAlloc_898_, 7, v_val_859_);
lean_ctor_set(v_reuseFailAlloc_898_, 8, v_binDir_870_);
lean_ctor_set(v_reuseFailAlloc_898_, 9, v_irDir_871_);
lean_ctor_set(v_reuseFailAlloc_898_, 10, v_releaseRepo_872_);
lean_ctor_set(v_reuseFailAlloc_898_, 11, v_buildArchive_873_);
lean_ctor_set(v_reuseFailAlloc_898_, 12, v_testDriver_875_);
lean_ctor_set(v_reuseFailAlloc_898_, 13, v_testDriverArgs_876_);
lean_ctor_set(v_reuseFailAlloc_898_, 14, v_lintDriver_877_);
lean_ctor_set(v_reuseFailAlloc_898_, 15, v_lintDriverArgs_878_);
lean_ctor_set(v_reuseFailAlloc_898_, 16, v_version_879_);
lean_ctor_set(v_reuseFailAlloc_898_, 17, v_versionTags_880_);
lean_ctor_set(v_reuseFailAlloc_898_, 18, v_description_881_);
lean_ctor_set(v_reuseFailAlloc_898_, 19, v_keywords_882_);
lean_ctor_set(v_reuseFailAlloc_898_, 20, v_homepage_883_);
lean_ctor_set(v_reuseFailAlloc_898_, 21, v_license_884_);
lean_ctor_set(v_reuseFailAlloc_898_, 22, v_licenseFiles_885_);
lean_ctor_set(v_reuseFailAlloc_898_, 23, v_readmeFile_886_);
lean_ctor_set(v_reuseFailAlloc_898_, 24, v_enableArtifactCache_x3f_888_);
lean_ctor_set(v_reuseFailAlloc_898_, 25, v_restoreAllArtifacts_x3f_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26, v_bootstrap_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26 + 1, v_precompileModules_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26 + 2, v_preferReleaseBuild_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26 + 3, v_reservoir_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26 + 5, v_allowImportAll_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*26 + 6, v_fixedToolchain_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* v_f_901_, lean_object* v_cfg_902_){
_start:
{
lean_object* v_toWorkspaceConfig_903_; lean_object* v_toLeanConfig_904_; uint8_t v_bootstrap_905_; lean_object* v_extraDepTargets_906_; uint8_t v_precompileModules_907_; lean_object* v_moreGlobalServerArgs_908_; lean_object* v_srcDir_909_; lean_object* v_buildDir_910_; lean_object* v_leanLibDir_911_; lean_object* v_nativeLibDir_912_; lean_object* v_binDir_913_; lean_object* v_irDir_914_; lean_object* v_releaseRepo_915_; lean_object* v_buildArchive_916_; uint8_t v_preferReleaseBuild_917_; lean_object* v_testDriver_918_; lean_object* v_testDriverArgs_919_; lean_object* v_lintDriver_920_; lean_object* v_lintDriverArgs_921_; lean_object* v_version_922_; lean_object* v_versionTags_923_; lean_object* v_description_924_; lean_object* v_keywords_925_; lean_object* v_homepage_926_; lean_object* v_license_927_; lean_object* v_licenseFiles_928_; lean_object* v_readmeFile_929_; uint8_t v_reservoir_930_; lean_object* v_enableArtifactCache_x3f_931_; lean_object* v_restoreAllArtifacts_x3f_932_; uint8_t v_libPrefixOnWindows_933_; uint8_t v_allowImportAll_934_; uint8_t v_fixedToolchain_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_943_; 
v_toWorkspaceConfig_903_ = lean_ctor_get(v_cfg_902_, 0);
v_toLeanConfig_904_ = lean_ctor_get(v_cfg_902_, 1);
v_bootstrap_905_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26);
v_extraDepTargets_906_ = lean_ctor_get(v_cfg_902_, 2);
v_precompileModules_907_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_908_ = lean_ctor_get(v_cfg_902_, 3);
v_srcDir_909_ = lean_ctor_get(v_cfg_902_, 4);
v_buildDir_910_ = lean_ctor_get(v_cfg_902_, 5);
v_leanLibDir_911_ = lean_ctor_get(v_cfg_902_, 6);
v_nativeLibDir_912_ = lean_ctor_get(v_cfg_902_, 7);
v_binDir_913_ = lean_ctor_get(v_cfg_902_, 8);
v_irDir_914_ = lean_ctor_get(v_cfg_902_, 9);
v_releaseRepo_915_ = lean_ctor_get(v_cfg_902_, 10);
v_buildArchive_916_ = lean_ctor_get(v_cfg_902_, 11);
v_preferReleaseBuild_917_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26 + 2);
v_testDriver_918_ = lean_ctor_get(v_cfg_902_, 12);
v_testDriverArgs_919_ = lean_ctor_get(v_cfg_902_, 13);
v_lintDriver_920_ = lean_ctor_get(v_cfg_902_, 14);
v_lintDriverArgs_921_ = lean_ctor_get(v_cfg_902_, 15);
v_version_922_ = lean_ctor_get(v_cfg_902_, 16);
v_versionTags_923_ = lean_ctor_get(v_cfg_902_, 17);
v_description_924_ = lean_ctor_get(v_cfg_902_, 18);
v_keywords_925_ = lean_ctor_get(v_cfg_902_, 19);
v_homepage_926_ = lean_ctor_get(v_cfg_902_, 20);
v_license_927_ = lean_ctor_get(v_cfg_902_, 21);
v_licenseFiles_928_ = lean_ctor_get(v_cfg_902_, 22);
v_readmeFile_929_ = lean_ctor_get(v_cfg_902_, 23);
v_reservoir_930_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_931_ = lean_ctor_get(v_cfg_902_, 24);
v_restoreAllArtifacts_x3f_932_ = lean_ctor_get(v_cfg_902_, 25);
v_libPrefixOnWindows_933_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26 + 4);
v_allowImportAll_934_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26 + 5);
v_fixedToolchain_935_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*26 + 6);
v_isSharedCheck_943_ = !lean_is_exclusive(v_cfg_902_);
if (v_isSharedCheck_943_ == 0)
{
v___x_937_ = v_cfg_902_;
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_932_);
lean_inc(v_enableArtifactCache_x3f_931_);
lean_inc(v_readmeFile_929_);
lean_inc(v_licenseFiles_928_);
lean_inc(v_license_927_);
lean_inc(v_homepage_926_);
lean_inc(v_keywords_925_);
lean_inc(v_description_924_);
lean_inc(v_versionTags_923_);
lean_inc(v_version_922_);
lean_inc(v_lintDriverArgs_921_);
lean_inc(v_lintDriver_920_);
lean_inc(v_testDriverArgs_919_);
lean_inc(v_testDriver_918_);
lean_inc(v_buildArchive_916_);
lean_inc(v_releaseRepo_915_);
lean_inc(v_irDir_914_);
lean_inc(v_binDir_913_);
lean_inc(v_nativeLibDir_912_);
lean_inc(v_leanLibDir_911_);
lean_inc(v_buildDir_910_);
lean_inc(v_srcDir_909_);
lean_inc(v_moreGlobalServerArgs_908_);
lean_inc(v_extraDepTargets_906_);
lean_inc(v_toLeanConfig_904_);
lean_inc(v_toWorkspaceConfig_903_);
lean_dec(v_cfg_902_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_apply_1(v_f_901_, v_nativeLibDir_912_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 7, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_toWorkspaceConfig_903_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_toLeanConfig_904_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_extraDepTargets_906_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_moreGlobalServerArgs_908_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_srcDir_909_);
lean_ctor_set(v_reuseFailAlloc_942_, 5, v_buildDir_910_);
lean_ctor_set(v_reuseFailAlloc_942_, 6, v_leanLibDir_911_);
lean_ctor_set(v_reuseFailAlloc_942_, 7, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 8, v_binDir_913_);
lean_ctor_set(v_reuseFailAlloc_942_, 9, v_irDir_914_);
lean_ctor_set(v_reuseFailAlloc_942_, 10, v_releaseRepo_915_);
lean_ctor_set(v_reuseFailAlloc_942_, 11, v_buildArchive_916_);
lean_ctor_set(v_reuseFailAlloc_942_, 12, v_testDriver_918_);
lean_ctor_set(v_reuseFailAlloc_942_, 13, v_testDriverArgs_919_);
lean_ctor_set(v_reuseFailAlloc_942_, 14, v_lintDriver_920_);
lean_ctor_set(v_reuseFailAlloc_942_, 15, v_lintDriverArgs_921_);
lean_ctor_set(v_reuseFailAlloc_942_, 16, v_version_922_);
lean_ctor_set(v_reuseFailAlloc_942_, 17, v_versionTags_923_);
lean_ctor_set(v_reuseFailAlloc_942_, 18, v_description_924_);
lean_ctor_set(v_reuseFailAlloc_942_, 19, v_keywords_925_);
lean_ctor_set(v_reuseFailAlloc_942_, 20, v_homepage_926_);
lean_ctor_set(v_reuseFailAlloc_942_, 21, v_license_927_);
lean_ctor_set(v_reuseFailAlloc_942_, 22, v_licenseFiles_928_);
lean_ctor_set(v_reuseFailAlloc_942_, 23, v_readmeFile_929_);
lean_ctor_set(v_reuseFailAlloc_942_, 24, v_enableArtifactCache_x3f_931_);
lean_ctor_set(v_reuseFailAlloc_942_, 25, v_restoreAllArtifacts_x3f_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26, v_bootstrap_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26 + 1, v_precompileModules_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26 + 2, v_preferReleaseBuild_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26 + 3, v_reservoir_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26 + 5, v_allowImportAll_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*26 + 6, v_fixedToolchain_935_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lake_defaultNativeLibDir;
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* v_x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(v_x_946_);
lean_dec_ref(v_x_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_957_, lean_object* v_n_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_960_, lean_object* v_n_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_960_, v_n_961_);
lean_dec(v_n_961_);
lean_dec(v_p_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_963_, lean_object* v_n_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_963_, v_n_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_966_, lean_object* v_n_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_966_, v_n_967_);
lean_dec(v_n_967_);
lean_dec(v_p_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* v_cfg_969_){
_start:
{
lean_object* v_binDir_970_; 
v_binDir_970_ = lean_ctor_get(v_cfg_969_, 8);
lean_inc_ref(v_binDir_970_);
return v_binDir_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* v_cfg_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lake_PackageConfig_binDir___proj___lam__0(v_cfg_971_);
lean_dec_ref(v_cfg_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* v_val_973_, lean_object* v_cfg_974_){
_start:
{
lean_object* v_toWorkspaceConfig_975_; lean_object* v_toLeanConfig_976_; uint8_t v_bootstrap_977_; lean_object* v_extraDepTargets_978_; uint8_t v_precompileModules_979_; lean_object* v_moreGlobalServerArgs_980_; lean_object* v_srcDir_981_; lean_object* v_buildDir_982_; lean_object* v_leanLibDir_983_; lean_object* v_nativeLibDir_984_; lean_object* v_irDir_985_; lean_object* v_releaseRepo_986_; lean_object* v_buildArchive_987_; uint8_t v_preferReleaseBuild_988_; lean_object* v_testDriver_989_; lean_object* v_testDriverArgs_990_; lean_object* v_lintDriver_991_; lean_object* v_lintDriverArgs_992_; lean_object* v_version_993_; lean_object* v_versionTags_994_; lean_object* v_description_995_; lean_object* v_keywords_996_; lean_object* v_homepage_997_; lean_object* v_license_998_; lean_object* v_licenseFiles_999_; lean_object* v_readmeFile_1000_; uint8_t v_reservoir_1001_; lean_object* v_enableArtifactCache_x3f_1002_; lean_object* v_restoreAllArtifacts_x3f_1003_; uint8_t v_libPrefixOnWindows_1004_; uint8_t v_allowImportAll_1005_; uint8_t v_fixedToolchain_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_toWorkspaceConfig_975_ = lean_ctor_get(v_cfg_974_, 0);
v_toLeanConfig_976_ = lean_ctor_get(v_cfg_974_, 1);
v_bootstrap_977_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26);
v_extraDepTargets_978_ = lean_ctor_get(v_cfg_974_, 2);
v_precompileModules_979_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_980_ = lean_ctor_get(v_cfg_974_, 3);
v_srcDir_981_ = lean_ctor_get(v_cfg_974_, 4);
v_buildDir_982_ = lean_ctor_get(v_cfg_974_, 5);
v_leanLibDir_983_ = lean_ctor_get(v_cfg_974_, 6);
v_nativeLibDir_984_ = lean_ctor_get(v_cfg_974_, 7);
v_irDir_985_ = lean_ctor_get(v_cfg_974_, 9);
v_releaseRepo_986_ = lean_ctor_get(v_cfg_974_, 10);
v_buildArchive_987_ = lean_ctor_get(v_cfg_974_, 11);
v_preferReleaseBuild_988_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26 + 2);
v_testDriver_989_ = lean_ctor_get(v_cfg_974_, 12);
v_testDriverArgs_990_ = lean_ctor_get(v_cfg_974_, 13);
v_lintDriver_991_ = lean_ctor_get(v_cfg_974_, 14);
v_lintDriverArgs_992_ = lean_ctor_get(v_cfg_974_, 15);
v_version_993_ = lean_ctor_get(v_cfg_974_, 16);
v_versionTags_994_ = lean_ctor_get(v_cfg_974_, 17);
v_description_995_ = lean_ctor_get(v_cfg_974_, 18);
v_keywords_996_ = lean_ctor_get(v_cfg_974_, 19);
v_homepage_997_ = lean_ctor_get(v_cfg_974_, 20);
v_license_998_ = lean_ctor_get(v_cfg_974_, 21);
v_licenseFiles_999_ = lean_ctor_get(v_cfg_974_, 22);
v_readmeFile_1000_ = lean_ctor_get(v_cfg_974_, 23);
v_reservoir_1001_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1002_ = lean_ctor_get(v_cfg_974_, 24);
v_restoreAllArtifacts_x3f_1003_ = lean_ctor_get(v_cfg_974_, 25);
v_libPrefixOnWindows_1004_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26 + 4);
v_allowImportAll_1005_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26 + 5);
v_fixedToolchain_1006_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*26 + 6);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_cfg_974_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v_cfg_974_, 8);
lean_dec(v_unused_1014_);
v___x_1008_ = v_cfg_974_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1003_);
lean_inc(v_enableArtifactCache_x3f_1002_);
lean_inc(v_readmeFile_1000_);
lean_inc(v_licenseFiles_999_);
lean_inc(v_license_998_);
lean_inc(v_homepage_997_);
lean_inc(v_keywords_996_);
lean_inc(v_description_995_);
lean_inc(v_versionTags_994_);
lean_inc(v_version_993_);
lean_inc(v_lintDriverArgs_992_);
lean_inc(v_lintDriver_991_);
lean_inc(v_testDriverArgs_990_);
lean_inc(v_testDriver_989_);
lean_inc(v_buildArchive_987_);
lean_inc(v_releaseRepo_986_);
lean_inc(v_irDir_985_);
lean_inc(v_nativeLibDir_984_);
lean_inc(v_leanLibDir_983_);
lean_inc(v_buildDir_982_);
lean_inc(v_srcDir_981_);
lean_inc(v_moreGlobalServerArgs_980_);
lean_inc(v_extraDepTargets_978_);
lean_inc(v_toLeanConfig_976_);
lean_inc(v_toWorkspaceConfig_975_);
lean_dec(v_cfg_974_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 8, v_val_973_);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_toWorkspaceConfig_975_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_toLeanConfig_976_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_extraDepTargets_978_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_moreGlobalServerArgs_980_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_srcDir_981_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_buildDir_982_);
lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_leanLibDir_983_);
lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_nativeLibDir_984_);
lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_val_973_);
lean_ctor_set(v_reuseFailAlloc_1012_, 9, v_irDir_985_);
lean_ctor_set(v_reuseFailAlloc_1012_, 10, v_releaseRepo_986_);
lean_ctor_set(v_reuseFailAlloc_1012_, 11, v_buildArchive_987_);
lean_ctor_set(v_reuseFailAlloc_1012_, 12, v_testDriver_989_);
lean_ctor_set(v_reuseFailAlloc_1012_, 13, v_testDriverArgs_990_);
lean_ctor_set(v_reuseFailAlloc_1012_, 14, v_lintDriver_991_);
lean_ctor_set(v_reuseFailAlloc_1012_, 15, v_lintDriverArgs_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 16, v_version_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 17, v_versionTags_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 18, v_description_995_);
lean_ctor_set(v_reuseFailAlloc_1012_, 19, v_keywords_996_);
lean_ctor_set(v_reuseFailAlloc_1012_, 20, v_homepage_997_);
lean_ctor_set(v_reuseFailAlloc_1012_, 21, v_license_998_);
lean_ctor_set(v_reuseFailAlloc_1012_, 22, v_licenseFiles_999_);
lean_ctor_set(v_reuseFailAlloc_1012_, 23, v_readmeFile_1000_);
lean_ctor_set(v_reuseFailAlloc_1012_, 24, v_enableArtifactCache_x3f_1002_);
lean_ctor_set(v_reuseFailAlloc_1012_, 25, v_restoreAllArtifacts_x3f_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26, v_bootstrap_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26 + 1, v_precompileModules_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26 + 2, v_preferReleaseBuild_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26 + 3, v_reservoir_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26 + 5, v_allowImportAll_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*26 + 6, v_fixedToolchain_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* v_f_1015_, lean_object* v_cfg_1016_){
_start:
{
lean_object* v_toWorkspaceConfig_1017_; lean_object* v_toLeanConfig_1018_; uint8_t v_bootstrap_1019_; lean_object* v_extraDepTargets_1020_; uint8_t v_precompileModules_1021_; lean_object* v_moreGlobalServerArgs_1022_; lean_object* v_srcDir_1023_; lean_object* v_buildDir_1024_; lean_object* v_leanLibDir_1025_; lean_object* v_nativeLibDir_1026_; lean_object* v_binDir_1027_; lean_object* v_irDir_1028_; lean_object* v_releaseRepo_1029_; lean_object* v_buildArchive_1030_; uint8_t v_preferReleaseBuild_1031_; lean_object* v_testDriver_1032_; lean_object* v_testDriverArgs_1033_; lean_object* v_lintDriver_1034_; lean_object* v_lintDriverArgs_1035_; lean_object* v_version_1036_; lean_object* v_versionTags_1037_; lean_object* v_description_1038_; lean_object* v_keywords_1039_; lean_object* v_homepage_1040_; lean_object* v_license_1041_; lean_object* v_licenseFiles_1042_; lean_object* v_readmeFile_1043_; uint8_t v_reservoir_1044_; lean_object* v_enableArtifactCache_x3f_1045_; lean_object* v_restoreAllArtifacts_x3f_1046_; uint8_t v_libPrefixOnWindows_1047_; uint8_t v_allowImportAll_1048_; uint8_t v_fixedToolchain_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_toWorkspaceConfig_1017_ = lean_ctor_get(v_cfg_1016_, 0);
v_toLeanConfig_1018_ = lean_ctor_get(v_cfg_1016_, 1);
v_bootstrap_1019_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26);
v_extraDepTargets_1020_ = lean_ctor_get(v_cfg_1016_, 2);
v_precompileModules_1021_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1022_ = lean_ctor_get(v_cfg_1016_, 3);
v_srcDir_1023_ = lean_ctor_get(v_cfg_1016_, 4);
v_buildDir_1024_ = lean_ctor_get(v_cfg_1016_, 5);
v_leanLibDir_1025_ = lean_ctor_get(v_cfg_1016_, 6);
v_nativeLibDir_1026_ = lean_ctor_get(v_cfg_1016_, 7);
v_binDir_1027_ = lean_ctor_get(v_cfg_1016_, 8);
v_irDir_1028_ = lean_ctor_get(v_cfg_1016_, 9);
v_releaseRepo_1029_ = lean_ctor_get(v_cfg_1016_, 10);
v_buildArchive_1030_ = lean_ctor_get(v_cfg_1016_, 11);
v_preferReleaseBuild_1031_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26 + 2);
v_testDriver_1032_ = lean_ctor_get(v_cfg_1016_, 12);
v_testDriverArgs_1033_ = lean_ctor_get(v_cfg_1016_, 13);
v_lintDriver_1034_ = lean_ctor_get(v_cfg_1016_, 14);
v_lintDriverArgs_1035_ = lean_ctor_get(v_cfg_1016_, 15);
v_version_1036_ = lean_ctor_get(v_cfg_1016_, 16);
v_versionTags_1037_ = lean_ctor_get(v_cfg_1016_, 17);
v_description_1038_ = lean_ctor_get(v_cfg_1016_, 18);
v_keywords_1039_ = lean_ctor_get(v_cfg_1016_, 19);
v_homepage_1040_ = lean_ctor_get(v_cfg_1016_, 20);
v_license_1041_ = lean_ctor_get(v_cfg_1016_, 21);
v_licenseFiles_1042_ = lean_ctor_get(v_cfg_1016_, 22);
v_readmeFile_1043_ = lean_ctor_get(v_cfg_1016_, 23);
v_reservoir_1044_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1045_ = lean_ctor_get(v_cfg_1016_, 24);
v_restoreAllArtifacts_x3f_1046_ = lean_ctor_get(v_cfg_1016_, 25);
v_libPrefixOnWindows_1047_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26 + 4);
v_allowImportAll_1048_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26 + 5);
v_fixedToolchain_1049_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*26 + 6);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_cfg_1016_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1051_ = v_cfg_1016_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1046_);
lean_inc(v_enableArtifactCache_x3f_1045_);
lean_inc(v_readmeFile_1043_);
lean_inc(v_licenseFiles_1042_);
lean_inc(v_license_1041_);
lean_inc(v_homepage_1040_);
lean_inc(v_keywords_1039_);
lean_inc(v_description_1038_);
lean_inc(v_versionTags_1037_);
lean_inc(v_version_1036_);
lean_inc(v_lintDriverArgs_1035_);
lean_inc(v_lintDriver_1034_);
lean_inc(v_testDriverArgs_1033_);
lean_inc(v_testDriver_1032_);
lean_inc(v_buildArchive_1030_);
lean_inc(v_releaseRepo_1029_);
lean_inc(v_irDir_1028_);
lean_inc(v_binDir_1027_);
lean_inc(v_nativeLibDir_1026_);
lean_inc(v_leanLibDir_1025_);
lean_inc(v_buildDir_1024_);
lean_inc(v_srcDir_1023_);
lean_inc(v_moreGlobalServerArgs_1022_);
lean_inc(v_extraDepTargets_1020_);
lean_inc(v_toLeanConfig_1018_);
lean_inc(v_toWorkspaceConfig_1017_);
lean_dec(v_cfg_1016_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = lean_apply_1(v_f_1015_, v_binDir_1027_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 8, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_toWorkspaceConfig_1017_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_toLeanConfig_1018_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_extraDepTargets_1020_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_moreGlobalServerArgs_1022_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v_srcDir_1023_);
lean_ctor_set(v_reuseFailAlloc_1056_, 5, v_buildDir_1024_);
lean_ctor_set(v_reuseFailAlloc_1056_, 6, v_leanLibDir_1025_);
lean_ctor_set(v_reuseFailAlloc_1056_, 7, v_nativeLibDir_1026_);
lean_ctor_set(v_reuseFailAlloc_1056_, 8, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 9, v_irDir_1028_);
lean_ctor_set(v_reuseFailAlloc_1056_, 10, v_releaseRepo_1029_);
lean_ctor_set(v_reuseFailAlloc_1056_, 11, v_buildArchive_1030_);
lean_ctor_set(v_reuseFailAlloc_1056_, 12, v_testDriver_1032_);
lean_ctor_set(v_reuseFailAlloc_1056_, 13, v_testDriverArgs_1033_);
lean_ctor_set(v_reuseFailAlloc_1056_, 14, v_lintDriver_1034_);
lean_ctor_set(v_reuseFailAlloc_1056_, 15, v_lintDriverArgs_1035_);
lean_ctor_set(v_reuseFailAlloc_1056_, 16, v_version_1036_);
lean_ctor_set(v_reuseFailAlloc_1056_, 17, v_versionTags_1037_);
lean_ctor_set(v_reuseFailAlloc_1056_, 18, v_description_1038_);
lean_ctor_set(v_reuseFailAlloc_1056_, 19, v_keywords_1039_);
lean_ctor_set(v_reuseFailAlloc_1056_, 20, v_homepage_1040_);
lean_ctor_set(v_reuseFailAlloc_1056_, 21, v_license_1041_);
lean_ctor_set(v_reuseFailAlloc_1056_, 22, v_licenseFiles_1042_);
lean_ctor_set(v_reuseFailAlloc_1056_, 23, v_readmeFile_1043_);
lean_ctor_set(v_reuseFailAlloc_1056_, 24, v_enableArtifactCache_x3f_1045_);
lean_ctor_set(v_reuseFailAlloc_1056_, 25, v_restoreAllArtifacts_x3f_1046_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26, v_bootstrap_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26 + 1, v_precompileModules_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1031_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26 + 3, v_reservoir_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26 + 5, v_allowImportAll_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*26 + 6, v_fixedToolchain_1049_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lake_defaultBinDir;
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* v_x_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lake_PackageConfig_binDir___proj___lam__3(v_x_1060_);
lean_dec_ref(v_x_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1071_, lean_object* v_n_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1074_, lean_object* v_n_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lake_PackageConfig_binDir___proj(v_p_1074_, v_n_1075_);
lean_dec(v_n_1075_);
lean_dec(v_p_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1077_, lean_object* v_n_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lake_PackageConfig_binDir___proj(v_p_1077_, v_n_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1080_, lean_object* v_n_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1080_, v_n_1081_);
lean_dec(v_n_1081_);
lean_dec(v_p_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* v_cfg_1083_){
_start:
{
lean_object* v_irDir_1084_; 
v_irDir_1084_ = lean_ctor_get(v_cfg_1083_, 9);
lean_inc_ref(v_irDir_1084_);
return v_irDir_1084_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* v_cfg_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lake_PackageConfig_irDir___proj___lam__0(v_cfg_1085_);
lean_dec_ref(v_cfg_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* v_val_1087_, lean_object* v_cfg_1088_){
_start:
{
lean_object* v_toWorkspaceConfig_1089_; lean_object* v_toLeanConfig_1090_; uint8_t v_bootstrap_1091_; lean_object* v_extraDepTargets_1092_; uint8_t v_precompileModules_1093_; lean_object* v_moreGlobalServerArgs_1094_; lean_object* v_srcDir_1095_; lean_object* v_buildDir_1096_; lean_object* v_leanLibDir_1097_; lean_object* v_nativeLibDir_1098_; lean_object* v_binDir_1099_; lean_object* v_releaseRepo_1100_; lean_object* v_buildArchive_1101_; uint8_t v_preferReleaseBuild_1102_; lean_object* v_testDriver_1103_; lean_object* v_testDriverArgs_1104_; lean_object* v_lintDriver_1105_; lean_object* v_lintDriverArgs_1106_; lean_object* v_version_1107_; lean_object* v_versionTags_1108_; lean_object* v_description_1109_; lean_object* v_keywords_1110_; lean_object* v_homepage_1111_; lean_object* v_license_1112_; lean_object* v_licenseFiles_1113_; lean_object* v_readmeFile_1114_; uint8_t v_reservoir_1115_; lean_object* v_enableArtifactCache_x3f_1116_; lean_object* v_restoreAllArtifacts_x3f_1117_; uint8_t v_libPrefixOnWindows_1118_; uint8_t v_allowImportAll_1119_; uint8_t v_fixedToolchain_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_toWorkspaceConfig_1089_ = lean_ctor_get(v_cfg_1088_, 0);
v_toLeanConfig_1090_ = lean_ctor_get(v_cfg_1088_, 1);
v_bootstrap_1091_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26);
v_extraDepTargets_1092_ = lean_ctor_get(v_cfg_1088_, 2);
v_precompileModules_1093_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1094_ = lean_ctor_get(v_cfg_1088_, 3);
v_srcDir_1095_ = lean_ctor_get(v_cfg_1088_, 4);
v_buildDir_1096_ = lean_ctor_get(v_cfg_1088_, 5);
v_leanLibDir_1097_ = lean_ctor_get(v_cfg_1088_, 6);
v_nativeLibDir_1098_ = lean_ctor_get(v_cfg_1088_, 7);
v_binDir_1099_ = lean_ctor_get(v_cfg_1088_, 8);
v_releaseRepo_1100_ = lean_ctor_get(v_cfg_1088_, 10);
v_buildArchive_1101_ = lean_ctor_get(v_cfg_1088_, 11);
v_preferReleaseBuild_1102_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26 + 2);
v_testDriver_1103_ = lean_ctor_get(v_cfg_1088_, 12);
v_testDriverArgs_1104_ = lean_ctor_get(v_cfg_1088_, 13);
v_lintDriver_1105_ = lean_ctor_get(v_cfg_1088_, 14);
v_lintDriverArgs_1106_ = lean_ctor_get(v_cfg_1088_, 15);
v_version_1107_ = lean_ctor_get(v_cfg_1088_, 16);
v_versionTags_1108_ = lean_ctor_get(v_cfg_1088_, 17);
v_description_1109_ = lean_ctor_get(v_cfg_1088_, 18);
v_keywords_1110_ = lean_ctor_get(v_cfg_1088_, 19);
v_homepage_1111_ = lean_ctor_get(v_cfg_1088_, 20);
v_license_1112_ = lean_ctor_get(v_cfg_1088_, 21);
v_licenseFiles_1113_ = lean_ctor_get(v_cfg_1088_, 22);
v_readmeFile_1114_ = lean_ctor_get(v_cfg_1088_, 23);
v_reservoir_1115_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1116_ = lean_ctor_get(v_cfg_1088_, 24);
v_restoreAllArtifacts_x3f_1117_ = lean_ctor_get(v_cfg_1088_, 25);
v_libPrefixOnWindows_1118_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26 + 4);
v_allowImportAll_1119_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26 + 5);
v_fixedToolchain_1120_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*26 + 6);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_cfg_1088_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_cfg_1088_, 9);
lean_dec(v_unused_1128_);
v___x_1122_ = v_cfg_1088_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1117_);
lean_inc(v_enableArtifactCache_x3f_1116_);
lean_inc(v_readmeFile_1114_);
lean_inc(v_licenseFiles_1113_);
lean_inc(v_license_1112_);
lean_inc(v_homepage_1111_);
lean_inc(v_keywords_1110_);
lean_inc(v_description_1109_);
lean_inc(v_versionTags_1108_);
lean_inc(v_version_1107_);
lean_inc(v_lintDriverArgs_1106_);
lean_inc(v_lintDriver_1105_);
lean_inc(v_testDriverArgs_1104_);
lean_inc(v_testDriver_1103_);
lean_inc(v_buildArchive_1101_);
lean_inc(v_releaseRepo_1100_);
lean_inc(v_binDir_1099_);
lean_inc(v_nativeLibDir_1098_);
lean_inc(v_leanLibDir_1097_);
lean_inc(v_buildDir_1096_);
lean_inc(v_srcDir_1095_);
lean_inc(v_moreGlobalServerArgs_1094_);
lean_inc(v_extraDepTargets_1092_);
lean_inc(v_toLeanConfig_1090_);
lean_inc(v_toWorkspaceConfig_1089_);
lean_dec(v_cfg_1088_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 9, v_val_1087_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_toWorkspaceConfig_1089_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_toLeanConfig_1090_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_extraDepTargets_1092_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_moreGlobalServerArgs_1094_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_srcDir_1095_);
lean_ctor_set(v_reuseFailAlloc_1126_, 5, v_buildDir_1096_);
lean_ctor_set(v_reuseFailAlloc_1126_, 6, v_leanLibDir_1097_);
lean_ctor_set(v_reuseFailAlloc_1126_, 7, v_nativeLibDir_1098_);
lean_ctor_set(v_reuseFailAlloc_1126_, 8, v_binDir_1099_);
lean_ctor_set(v_reuseFailAlloc_1126_, 9, v_val_1087_);
lean_ctor_set(v_reuseFailAlloc_1126_, 10, v_releaseRepo_1100_);
lean_ctor_set(v_reuseFailAlloc_1126_, 11, v_buildArchive_1101_);
lean_ctor_set(v_reuseFailAlloc_1126_, 12, v_testDriver_1103_);
lean_ctor_set(v_reuseFailAlloc_1126_, 13, v_testDriverArgs_1104_);
lean_ctor_set(v_reuseFailAlloc_1126_, 14, v_lintDriver_1105_);
lean_ctor_set(v_reuseFailAlloc_1126_, 15, v_lintDriverArgs_1106_);
lean_ctor_set(v_reuseFailAlloc_1126_, 16, v_version_1107_);
lean_ctor_set(v_reuseFailAlloc_1126_, 17, v_versionTags_1108_);
lean_ctor_set(v_reuseFailAlloc_1126_, 18, v_description_1109_);
lean_ctor_set(v_reuseFailAlloc_1126_, 19, v_keywords_1110_);
lean_ctor_set(v_reuseFailAlloc_1126_, 20, v_homepage_1111_);
lean_ctor_set(v_reuseFailAlloc_1126_, 21, v_license_1112_);
lean_ctor_set(v_reuseFailAlloc_1126_, 22, v_licenseFiles_1113_);
lean_ctor_set(v_reuseFailAlloc_1126_, 23, v_readmeFile_1114_);
lean_ctor_set(v_reuseFailAlloc_1126_, 24, v_enableArtifactCache_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1126_, 25, v_restoreAllArtifacts_x3f_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26, v_bootstrap_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26 + 1, v_precompileModules_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26 + 3, v_reservoir_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26 + 5, v_allowImportAll_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*26 + 6, v_fixedToolchain_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* v_f_1129_, lean_object* v_cfg_1130_){
_start:
{
lean_object* v_toWorkspaceConfig_1131_; lean_object* v_toLeanConfig_1132_; uint8_t v_bootstrap_1133_; lean_object* v_extraDepTargets_1134_; uint8_t v_precompileModules_1135_; lean_object* v_moreGlobalServerArgs_1136_; lean_object* v_srcDir_1137_; lean_object* v_buildDir_1138_; lean_object* v_leanLibDir_1139_; lean_object* v_nativeLibDir_1140_; lean_object* v_binDir_1141_; lean_object* v_irDir_1142_; lean_object* v_releaseRepo_1143_; lean_object* v_buildArchive_1144_; uint8_t v_preferReleaseBuild_1145_; lean_object* v_testDriver_1146_; lean_object* v_testDriverArgs_1147_; lean_object* v_lintDriver_1148_; lean_object* v_lintDriverArgs_1149_; lean_object* v_version_1150_; lean_object* v_versionTags_1151_; lean_object* v_description_1152_; lean_object* v_keywords_1153_; lean_object* v_homepage_1154_; lean_object* v_license_1155_; lean_object* v_licenseFiles_1156_; lean_object* v_readmeFile_1157_; uint8_t v_reservoir_1158_; lean_object* v_enableArtifactCache_x3f_1159_; lean_object* v_restoreAllArtifacts_x3f_1160_; uint8_t v_libPrefixOnWindows_1161_; uint8_t v_allowImportAll_1162_; uint8_t v_fixedToolchain_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_toWorkspaceConfig_1131_ = lean_ctor_get(v_cfg_1130_, 0);
v_toLeanConfig_1132_ = lean_ctor_get(v_cfg_1130_, 1);
v_bootstrap_1133_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26);
v_extraDepTargets_1134_ = lean_ctor_get(v_cfg_1130_, 2);
v_precompileModules_1135_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1136_ = lean_ctor_get(v_cfg_1130_, 3);
v_srcDir_1137_ = lean_ctor_get(v_cfg_1130_, 4);
v_buildDir_1138_ = lean_ctor_get(v_cfg_1130_, 5);
v_leanLibDir_1139_ = lean_ctor_get(v_cfg_1130_, 6);
v_nativeLibDir_1140_ = lean_ctor_get(v_cfg_1130_, 7);
v_binDir_1141_ = lean_ctor_get(v_cfg_1130_, 8);
v_irDir_1142_ = lean_ctor_get(v_cfg_1130_, 9);
v_releaseRepo_1143_ = lean_ctor_get(v_cfg_1130_, 10);
v_buildArchive_1144_ = lean_ctor_get(v_cfg_1130_, 11);
v_preferReleaseBuild_1145_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26 + 2);
v_testDriver_1146_ = lean_ctor_get(v_cfg_1130_, 12);
v_testDriverArgs_1147_ = lean_ctor_get(v_cfg_1130_, 13);
v_lintDriver_1148_ = lean_ctor_get(v_cfg_1130_, 14);
v_lintDriverArgs_1149_ = lean_ctor_get(v_cfg_1130_, 15);
v_version_1150_ = lean_ctor_get(v_cfg_1130_, 16);
v_versionTags_1151_ = lean_ctor_get(v_cfg_1130_, 17);
v_description_1152_ = lean_ctor_get(v_cfg_1130_, 18);
v_keywords_1153_ = lean_ctor_get(v_cfg_1130_, 19);
v_homepage_1154_ = lean_ctor_get(v_cfg_1130_, 20);
v_license_1155_ = lean_ctor_get(v_cfg_1130_, 21);
v_licenseFiles_1156_ = lean_ctor_get(v_cfg_1130_, 22);
v_readmeFile_1157_ = lean_ctor_get(v_cfg_1130_, 23);
v_reservoir_1158_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1159_ = lean_ctor_get(v_cfg_1130_, 24);
v_restoreAllArtifacts_x3f_1160_ = lean_ctor_get(v_cfg_1130_, 25);
v_libPrefixOnWindows_1161_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26 + 4);
v_allowImportAll_1162_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26 + 5);
v_fixedToolchain_1163_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*26 + 6);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_cfg_1130_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v_cfg_1130_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1160_);
lean_inc(v_enableArtifactCache_x3f_1159_);
lean_inc(v_readmeFile_1157_);
lean_inc(v_licenseFiles_1156_);
lean_inc(v_license_1155_);
lean_inc(v_homepage_1154_);
lean_inc(v_keywords_1153_);
lean_inc(v_description_1152_);
lean_inc(v_versionTags_1151_);
lean_inc(v_version_1150_);
lean_inc(v_lintDriverArgs_1149_);
lean_inc(v_lintDriver_1148_);
lean_inc(v_testDriverArgs_1147_);
lean_inc(v_testDriver_1146_);
lean_inc(v_buildArchive_1144_);
lean_inc(v_releaseRepo_1143_);
lean_inc(v_irDir_1142_);
lean_inc(v_binDir_1141_);
lean_inc(v_nativeLibDir_1140_);
lean_inc(v_leanLibDir_1139_);
lean_inc(v_buildDir_1138_);
lean_inc(v_srcDir_1137_);
lean_inc(v_moreGlobalServerArgs_1136_);
lean_inc(v_extraDepTargets_1134_);
lean_inc(v_toLeanConfig_1132_);
lean_inc(v_toWorkspaceConfig_1131_);
lean_dec(v_cfg_1130_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_apply_1(v_f_1129_, v_irDir_1142_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 9, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_toWorkspaceConfig_1131_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_toLeanConfig_1132_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_extraDepTargets_1134_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_moreGlobalServerArgs_1136_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_srcDir_1137_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_buildDir_1138_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_leanLibDir_1139_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_nativeLibDir_1140_);
lean_ctor_set(v_reuseFailAlloc_1170_, 8, v_binDir_1141_);
lean_ctor_set(v_reuseFailAlloc_1170_, 9, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 10, v_releaseRepo_1143_);
lean_ctor_set(v_reuseFailAlloc_1170_, 11, v_buildArchive_1144_);
lean_ctor_set(v_reuseFailAlloc_1170_, 12, v_testDriver_1146_);
lean_ctor_set(v_reuseFailAlloc_1170_, 13, v_testDriverArgs_1147_);
lean_ctor_set(v_reuseFailAlloc_1170_, 14, v_lintDriver_1148_);
lean_ctor_set(v_reuseFailAlloc_1170_, 15, v_lintDriverArgs_1149_);
lean_ctor_set(v_reuseFailAlloc_1170_, 16, v_version_1150_);
lean_ctor_set(v_reuseFailAlloc_1170_, 17, v_versionTags_1151_);
lean_ctor_set(v_reuseFailAlloc_1170_, 18, v_description_1152_);
lean_ctor_set(v_reuseFailAlloc_1170_, 19, v_keywords_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 20, v_homepage_1154_);
lean_ctor_set(v_reuseFailAlloc_1170_, 21, v_license_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 22, v_licenseFiles_1156_);
lean_ctor_set(v_reuseFailAlloc_1170_, 23, v_readmeFile_1157_);
lean_ctor_set(v_reuseFailAlloc_1170_, 24, v_enableArtifactCache_x3f_1159_);
lean_ctor_set(v_reuseFailAlloc_1170_, 25, v_restoreAllArtifacts_x3f_1160_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26, v_bootstrap_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26 + 1, v_precompileModules_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26 + 3, v_reservoir_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26 + 5, v_allowImportAll_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*26 + 6, v_fixedToolchain_1163_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* v_x_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lake_defaultIrDir;
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lake_PackageConfig_irDir___proj___lam__3(v_x_1174_);
lean_dec_ref(v_x_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1185_, lean_object* v_n_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1188_, lean_object* v_n_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_PackageConfig_irDir___proj(v_p_1188_, v_n_1189_);
lean_dec(v_n_1189_);
lean_dec(v_p_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1191_, lean_object* v_n_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lake_PackageConfig_irDir___proj(v_p_1191_, v_n_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1194_, lean_object* v_n_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1194_, v_n_1195_);
lean_dec(v_n_1195_);
lean_dec(v_p_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* v_cfg_1197_){
_start:
{
lean_object* v_releaseRepo_1198_; 
v_releaseRepo_1198_ = lean_ctor_get(v_cfg_1197_, 10);
lean_inc(v_releaseRepo_1198_);
return v_releaseRepo_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* v_cfg_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lake_PackageConfig_releaseRepo___proj___lam__0(v_cfg_1199_);
lean_dec_ref(v_cfg_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* v_val_1201_, lean_object* v_cfg_1202_){
_start:
{
lean_object* v_toWorkspaceConfig_1203_; lean_object* v_toLeanConfig_1204_; uint8_t v_bootstrap_1205_; lean_object* v_extraDepTargets_1206_; uint8_t v_precompileModules_1207_; lean_object* v_moreGlobalServerArgs_1208_; lean_object* v_srcDir_1209_; lean_object* v_buildDir_1210_; lean_object* v_leanLibDir_1211_; lean_object* v_nativeLibDir_1212_; lean_object* v_binDir_1213_; lean_object* v_irDir_1214_; lean_object* v_buildArchive_1215_; uint8_t v_preferReleaseBuild_1216_; lean_object* v_testDriver_1217_; lean_object* v_testDriverArgs_1218_; lean_object* v_lintDriver_1219_; lean_object* v_lintDriverArgs_1220_; lean_object* v_version_1221_; lean_object* v_versionTags_1222_; lean_object* v_description_1223_; lean_object* v_keywords_1224_; lean_object* v_homepage_1225_; lean_object* v_license_1226_; lean_object* v_licenseFiles_1227_; lean_object* v_readmeFile_1228_; uint8_t v_reservoir_1229_; lean_object* v_enableArtifactCache_x3f_1230_; lean_object* v_restoreAllArtifacts_x3f_1231_; uint8_t v_libPrefixOnWindows_1232_; uint8_t v_allowImportAll_1233_; uint8_t v_fixedToolchain_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_toWorkspaceConfig_1203_ = lean_ctor_get(v_cfg_1202_, 0);
v_toLeanConfig_1204_ = lean_ctor_get(v_cfg_1202_, 1);
v_bootstrap_1205_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26);
v_extraDepTargets_1206_ = lean_ctor_get(v_cfg_1202_, 2);
v_precompileModules_1207_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1208_ = lean_ctor_get(v_cfg_1202_, 3);
v_srcDir_1209_ = lean_ctor_get(v_cfg_1202_, 4);
v_buildDir_1210_ = lean_ctor_get(v_cfg_1202_, 5);
v_leanLibDir_1211_ = lean_ctor_get(v_cfg_1202_, 6);
v_nativeLibDir_1212_ = lean_ctor_get(v_cfg_1202_, 7);
v_binDir_1213_ = lean_ctor_get(v_cfg_1202_, 8);
v_irDir_1214_ = lean_ctor_get(v_cfg_1202_, 9);
v_buildArchive_1215_ = lean_ctor_get(v_cfg_1202_, 11);
v_preferReleaseBuild_1216_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26 + 2);
v_testDriver_1217_ = lean_ctor_get(v_cfg_1202_, 12);
v_testDriverArgs_1218_ = lean_ctor_get(v_cfg_1202_, 13);
v_lintDriver_1219_ = lean_ctor_get(v_cfg_1202_, 14);
v_lintDriverArgs_1220_ = lean_ctor_get(v_cfg_1202_, 15);
v_version_1221_ = lean_ctor_get(v_cfg_1202_, 16);
v_versionTags_1222_ = lean_ctor_get(v_cfg_1202_, 17);
v_description_1223_ = lean_ctor_get(v_cfg_1202_, 18);
v_keywords_1224_ = lean_ctor_get(v_cfg_1202_, 19);
v_homepage_1225_ = lean_ctor_get(v_cfg_1202_, 20);
v_license_1226_ = lean_ctor_get(v_cfg_1202_, 21);
v_licenseFiles_1227_ = lean_ctor_get(v_cfg_1202_, 22);
v_readmeFile_1228_ = lean_ctor_get(v_cfg_1202_, 23);
v_reservoir_1229_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1230_ = lean_ctor_get(v_cfg_1202_, 24);
v_restoreAllArtifacts_x3f_1231_ = lean_ctor_get(v_cfg_1202_, 25);
v_libPrefixOnWindows_1232_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26 + 4);
v_allowImportAll_1233_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26 + 5);
v_fixedToolchain_1234_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*26 + 6);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_cfg_1202_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_cfg_1202_, 10);
lean_dec(v_unused_1242_);
v___x_1236_ = v_cfg_1202_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1231_);
lean_inc(v_enableArtifactCache_x3f_1230_);
lean_inc(v_readmeFile_1228_);
lean_inc(v_licenseFiles_1227_);
lean_inc(v_license_1226_);
lean_inc(v_homepage_1225_);
lean_inc(v_keywords_1224_);
lean_inc(v_description_1223_);
lean_inc(v_versionTags_1222_);
lean_inc(v_version_1221_);
lean_inc(v_lintDriverArgs_1220_);
lean_inc(v_lintDriver_1219_);
lean_inc(v_testDriverArgs_1218_);
lean_inc(v_testDriver_1217_);
lean_inc(v_buildArchive_1215_);
lean_inc(v_irDir_1214_);
lean_inc(v_binDir_1213_);
lean_inc(v_nativeLibDir_1212_);
lean_inc(v_leanLibDir_1211_);
lean_inc(v_buildDir_1210_);
lean_inc(v_srcDir_1209_);
lean_inc(v_moreGlobalServerArgs_1208_);
lean_inc(v_extraDepTargets_1206_);
lean_inc(v_toLeanConfig_1204_);
lean_inc(v_toWorkspaceConfig_1203_);
lean_dec(v_cfg_1202_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 10, v_val_1201_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_toWorkspaceConfig_1203_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_toLeanConfig_1204_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_extraDepTargets_1206_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_moreGlobalServerArgs_1208_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_srcDir_1209_);
lean_ctor_set(v_reuseFailAlloc_1240_, 5, v_buildDir_1210_);
lean_ctor_set(v_reuseFailAlloc_1240_, 6, v_leanLibDir_1211_);
lean_ctor_set(v_reuseFailAlloc_1240_, 7, v_nativeLibDir_1212_);
lean_ctor_set(v_reuseFailAlloc_1240_, 8, v_binDir_1213_);
lean_ctor_set(v_reuseFailAlloc_1240_, 9, v_irDir_1214_);
lean_ctor_set(v_reuseFailAlloc_1240_, 10, v_val_1201_);
lean_ctor_set(v_reuseFailAlloc_1240_, 11, v_buildArchive_1215_);
lean_ctor_set(v_reuseFailAlloc_1240_, 12, v_testDriver_1217_);
lean_ctor_set(v_reuseFailAlloc_1240_, 13, v_testDriverArgs_1218_);
lean_ctor_set(v_reuseFailAlloc_1240_, 14, v_lintDriver_1219_);
lean_ctor_set(v_reuseFailAlloc_1240_, 15, v_lintDriverArgs_1220_);
lean_ctor_set(v_reuseFailAlloc_1240_, 16, v_version_1221_);
lean_ctor_set(v_reuseFailAlloc_1240_, 17, v_versionTags_1222_);
lean_ctor_set(v_reuseFailAlloc_1240_, 18, v_description_1223_);
lean_ctor_set(v_reuseFailAlloc_1240_, 19, v_keywords_1224_);
lean_ctor_set(v_reuseFailAlloc_1240_, 20, v_homepage_1225_);
lean_ctor_set(v_reuseFailAlloc_1240_, 21, v_license_1226_);
lean_ctor_set(v_reuseFailAlloc_1240_, 22, v_licenseFiles_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 23, v_readmeFile_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 24, v_enableArtifactCache_x3f_1230_);
lean_ctor_set(v_reuseFailAlloc_1240_, 25, v_restoreAllArtifacts_x3f_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26, v_bootstrap_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26 + 1, v_precompileModules_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26 + 3, v_reservoir_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26 + 5, v_allowImportAll_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*26 + 6, v_fixedToolchain_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* v_f_1243_, lean_object* v_cfg_1244_){
_start:
{
lean_object* v_toWorkspaceConfig_1245_; lean_object* v_toLeanConfig_1246_; uint8_t v_bootstrap_1247_; lean_object* v_extraDepTargets_1248_; uint8_t v_precompileModules_1249_; lean_object* v_moreGlobalServerArgs_1250_; lean_object* v_srcDir_1251_; lean_object* v_buildDir_1252_; lean_object* v_leanLibDir_1253_; lean_object* v_nativeLibDir_1254_; lean_object* v_binDir_1255_; lean_object* v_irDir_1256_; lean_object* v_releaseRepo_1257_; lean_object* v_buildArchive_1258_; uint8_t v_preferReleaseBuild_1259_; lean_object* v_testDriver_1260_; lean_object* v_testDriverArgs_1261_; lean_object* v_lintDriver_1262_; lean_object* v_lintDriverArgs_1263_; lean_object* v_version_1264_; lean_object* v_versionTags_1265_; lean_object* v_description_1266_; lean_object* v_keywords_1267_; lean_object* v_homepage_1268_; lean_object* v_license_1269_; lean_object* v_licenseFiles_1270_; lean_object* v_readmeFile_1271_; uint8_t v_reservoir_1272_; lean_object* v_enableArtifactCache_x3f_1273_; lean_object* v_restoreAllArtifacts_x3f_1274_; uint8_t v_libPrefixOnWindows_1275_; uint8_t v_allowImportAll_1276_; uint8_t v_fixedToolchain_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_toWorkspaceConfig_1245_ = lean_ctor_get(v_cfg_1244_, 0);
v_toLeanConfig_1246_ = lean_ctor_get(v_cfg_1244_, 1);
v_bootstrap_1247_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26);
v_extraDepTargets_1248_ = lean_ctor_get(v_cfg_1244_, 2);
v_precompileModules_1249_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1250_ = lean_ctor_get(v_cfg_1244_, 3);
v_srcDir_1251_ = lean_ctor_get(v_cfg_1244_, 4);
v_buildDir_1252_ = lean_ctor_get(v_cfg_1244_, 5);
v_leanLibDir_1253_ = lean_ctor_get(v_cfg_1244_, 6);
v_nativeLibDir_1254_ = lean_ctor_get(v_cfg_1244_, 7);
v_binDir_1255_ = lean_ctor_get(v_cfg_1244_, 8);
v_irDir_1256_ = lean_ctor_get(v_cfg_1244_, 9);
v_releaseRepo_1257_ = lean_ctor_get(v_cfg_1244_, 10);
v_buildArchive_1258_ = lean_ctor_get(v_cfg_1244_, 11);
v_preferReleaseBuild_1259_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26 + 2);
v_testDriver_1260_ = lean_ctor_get(v_cfg_1244_, 12);
v_testDriverArgs_1261_ = lean_ctor_get(v_cfg_1244_, 13);
v_lintDriver_1262_ = lean_ctor_get(v_cfg_1244_, 14);
v_lintDriverArgs_1263_ = lean_ctor_get(v_cfg_1244_, 15);
v_version_1264_ = lean_ctor_get(v_cfg_1244_, 16);
v_versionTags_1265_ = lean_ctor_get(v_cfg_1244_, 17);
v_description_1266_ = lean_ctor_get(v_cfg_1244_, 18);
v_keywords_1267_ = lean_ctor_get(v_cfg_1244_, 19);
v_homepage_1268_ = lean_ctor_get(v_cfg_1244_, 20);
v_license_1269_ = lean_ctor_get(v_cfg_1244_, 21);
v_licenseFiles_1270_ = lean_ctor_get(v_cfg_1244_, 22);
v_readmeFile_1271_ = lean_ctor_get(v_cfg_1244_, 23);
v_reservoir_1272_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1273_ = lean_ctor_get(v_cfg_1244_, 24);
v_restoreAllArtifacts_x3f_1274_ = lean_ctor_get(v_cfg_1244_, 25);
v_libPrefixOnWindows_1275_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26 + 4);
v_allowImportAll_1276_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26 + 5);
v_fixedToolchain_1277_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*26 + 6);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_cfg_1244_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v_cfg_1244_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1274_);
lean_inc(v_enableArtifactCache_x3f_1273_);
lean_inc(v_readmeFile_1271_);
lean_inc(v_licenseFiles_1270_);
lean_inc(v_license_1269_);
lean_inc(v_homepage_1268_);
lean_inc(v_keywords_1267_);
lean_inc(v_description_1266_);
lean_inc(v_versionTags_1265_);
lean_inc(v_version_1264_);
lean_inc(v_lintDriverArgs_1263_);
lean_inc(v_lintDriver_1262_);
lean_inc(v_testDriverArgs_1261_);
lean_inc(v_testDriver_1260_);
lean_inc(v_buildArchive_1258_);
lean_inc(v_releaseRepo_1257_);
lean_inc(v_irDir_1256_);
lean_inc(v_binDir_1255_);
lean_inc(v_nativeLibDir_1254_);
lean_inc(v_leanLibDir_1253_);
lean_inc(v_buildDir_1252_);
lean_inc(v_srcDir_1251_);
lean_inc(v_moreGlobalServerArgs_1250_);
lean_inc(v_extraDepTargets_1248_);
lean_inc(v_toLeanConfig_1246_);
lean_inc(v_toWorkspaceConfig_1245_);
lean_dec(v_cfg_1244_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_apply_1(v_f_1243_, v_releaseRepo_1257_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 10, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_toWorkspaceConfig_1245_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_toLeanConfig_1246_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_extraDepTargets_1248_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_moreGlobalServerArgs_1250_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_srcDir_1251_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_buildDir_1252_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_leanLibDir_1253_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_nativeLibDir_1254_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_binDir_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_irDir_1256_);
lean_ctor_set(v_reuseFailAlloc_1284_, 10, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1284_, 11, v_buildArchive_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 12, v_testDriver_1260_);
lean_ctor_set(v_reuseFailAlloc_1284_, 13, v_testDriverArgs_1261_);
lean_ctor_set(v_reuseFailAlloc_1284_, 14, v_lintDriver_1262_);
lean_ctor_set(v_reuseFailAlloc_1284_, 15, v_lintDriverArgs_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 16, v_version_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 17, v_versionTags_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 18, v_description_1266_);
lean_ctor_set(v_reuseFailAlloc_1284_, 19, v_keywords_1267_);
lean_ctor_set(v_reuseFailAlloc_1284_, 20, v_homepage_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 21, v_license_1269_);
lean_ctor_set(v_reuseFailAlloc_1284_, 22, v_licenseFiles_1270_);
lean_ctor_set(v_reuseFailAlloc_1284_, 23, v_readmeFile_1271_);
lean_ctor_set(v_reuseFailAlloc_1284_, 24, v_enableArtifactCache_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1284_, 25, v_restoreAllArtifacts_x3f_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26, v_bootstrap_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26 + 1, v_precompileModules_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26 + 3, v_reservoir_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26 + 5, v_allowImportAll_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*26 + 6, v_fixedToolchain_1277_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3(lean_object* v_x_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_box(0);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed(lean_object* v_x_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lake_PackageConfig_releaseRepo___proj___lam__3(v_x_1288_);
lean_dec_ref(v_x_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1299_, lean_object* v_n_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__4));
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1302_, lean_object* v_n_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1302_, v_n_1303_);
lean_dec(v_n_1303_);
lean_dec(v_p_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1305_, lean_object* v_n_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1305_, v_n_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1308_, lean_object* v_n_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1308_, v_n_1309_);
lean_dec(v_n_1309_);
lean_dec(v_p_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1311_, lean_object* v_n_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1311_, v_n_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1314_, lean_object* v_n_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1314_, v_n_1315_);
lean_dec(v_n_1315_);
lean_dec(v_p_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* v_cfg_1317_){
_start:
{
lean_object* v_buildArchive_1318_; 
v_buildArchive_1318_ = lean_ctor_get(v_cfg_1317_, 11);
lean_inc(v_buildArchive_1318_);
return v_buildArchive_1318_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* v_cfg_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lake_PackageConfig_buildArchive___proj___lam__0(v_cfg_1319_);
lean_dec_ref(v_cfg_1319_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* v_val_1321_, lean_object* v_cfg_1322_){
_start:
{
lean_object* v_toWorkspaceConfig_1323_; lean_object* v_toLeanConfig_1324_; uint8_t v_bootstrap_1325_; lean_object* v_extraDepTargets_1326_; uint8_t v_precompileModules_1327_; lean_object* v_moreGlobalServerArgs_1328_; lean_object* v_srcDir_1329_; lean_object* v_buildDir_1330_; lean_object* v_leanLibDir_1331_; lean_object* v_nativeLibDir_1332_; lean_object* v_binDir_1333_; lean_object* v_irDir_1334_; lean_object* v_releaseRepo_1335_; uint8_t v_preferReleaseBuild_1336_; lean_object* v_testDriver_1337_; lean_object* v_testDriverArgs_1338_; lean_object* v_lintDriver_1339_; lean_object* v_lintDriverArgs_1340_; lean_object* v_version_1341_; lean_object* v_versionTags_1342_; lean_object* v_description_1343_; lean_object* v_keywords_1344_; lean_object* v_homepage_1345_; lean_object* v_license_1346_; lean_object* v_licenseFiles_1347_; lean_object* v_readmeFile_1348_; uint8_t v_reservoir_1349_; lean_object* v_enableArtifactCache_x3f_1350_; lean_object* v_restoreAllArtifacts_x3f_1351_; uint8_t v_libPrefixOnWindows_1352_; uint8_t v_allowImportAll_1353_; uint8_t v_fixedToolchain_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_toWorkspaceConfig_1323_ = lean_ctor_get(v_cfg_1322_, 0);
v_toLeanConfig_1324_ = lean_ctor_get(v_cfg_1322_, 1);
v_bootstrap_1325_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26);
v_extraDepTargets_1326_ = lean_ctor_get(v_cfg_1322_, 2);
v_precompileModules_1327_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1328_ = lean_ctor_get(v_cfg_1322_, 3);
v_srcDir_1329_ = lean_ctor_get(v_cfg_1322_, 4);
v_buildDir_1330_ = lean_ctor_get(v_cfg_1322_, 5);
v_leanLibDir_1331_ = lean_ctor_get(v_cfg_1322_, 6);
v_nativeLibDir_1332_ = lean_ctor_get(v_cfg_1322_, 7);
v_binDir_1333_ = lean_ctor_get(v_cfg_1322_, 8);
v_irDir_1334_ = lean_ctor_get(v_cfg_1322_, 9);
v_releaseRepo_1335_ = lean_ctor_get(v_cfg_1322_, 10);
v_preferReleaseBuild_1336_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26 + 2);
v_testDriver_1337_ = lean_ctor_get(v_cfg_1322_, 12);
v_testDriverArgs_1338_ = lean_ctor_get(v_cfg_1322_, 13);
v_lintDriver_1339_ = lean_ctor_get(v_cfg_1322_, 14);
v_lintDriverArgs_1340_ = lean_ctor_get(v_cfg_1322_, 15);
v_version_1341_ = lean_ctor_get(v_cfg_1322_, 16);
v_versionTags_1342_ = lean_ctor_get(v_cfg_1322_, 17);
v_description_1343_ = lean_ctor_get(v_cfg_1322_, 18);
v_keywords_1344_ = lean_ctor_get(v_cfg_1322_, 19);
v_homepage_1345_ = lean_ctor_get(v_cfg_1322_, 20);
v_license_1346_ = lean_ctor_get(v_cfg_1322_, 21);
v_licenseFiles_1347_ = lean_ctor_get(v_cfg_1322_, 22);
v_readmeFile_1348_ = lean_ctor_get(v_cfg_1322_, 23);
v_reservoir_1349_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1350_ = lean_ctor_get(v_cfg_1322_, 24);
v_restoreAllArtifacts_x3f_1351_ = lean_ctor_get(v_cfg_1322_, 25);
v_libPrefixOnWindows_1352_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26 + 4);
v_allowImportAll_1353_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26 + 5);
v_fixedToolchain_1354_ = lean_ctor_get_uint8(v_cfg_1322_, sizeof(void*)*26 + 6);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_cfg_1322_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_cfg_1322_, 11);
lean_dec(v_unused_1362_);
v___x_1356_ = v_cfg_1322_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1351_);
lean_inc(v_enableArtifactCache_x3f_1350_);
lean_inc(v_readmeFile_1348_);
lean_inc(v_licenseFiles_1347_);
lean_inc(v_license_1346_);
lean_inc(v_homepage_1345_);
lean_inc(v_keywords_1344_);
lean_inc(v_description_1343_);
lean_inc(v_versionTags_1342_);
lean_inc(v_version_1341_);
lean_inc(v_lintDriverArgs_1340_);
lean_inc(v_lintDriver_1339_);
lean_inc(v_testDriverArgs_1338_);
lean_inc(v_testDriver_1337_);
lean_inc(v_releaseRepo_1335_);
lean_inc(v_irDir_1334_);
lean_inc(v_binDir_1333_);
lean_inc(v_nativeLibDir_1332_);
lean_inc(v_leanLibDir_1331_);
lean_inc(v_buildDir_1330_);
lean_inc(v_srcDir_1329_);
lean_inc(v_moreGlobalServerArgs_1328_);
lean_inc(v_extraDepTargets_1326_);
lean_inc(v_toLeanConfig_1324_);
lean_inc(v_toWorkspaceConfig_1323_);
lean_dec(v_cfg_1322_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 11, v_val_1321_);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_toWorkspaceConfig_1323_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_toLeanConfig_1324_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_extraDepTargets_1326_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_moreGlobalServerArgs_1328_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_srcDir_1329_);
lean_ctor_set(v_reuseFailAlloc_1360_, 5, v_buildDir_1330_);
lean_ctor_set(v_reuseFailAlloc_1360_, 6, v_leanLibDir_1331_);
lean_ctor_set(v_reuseFailAlloc_1360_, 7, v_nativeLibDir_1332_);
lean_ctor_set(v_reuseFailAlloc_1360_, 8, v_binDir_1333_);
lean_ctor_set(v_reuseFailAlloc_1360_, 9, v_irDir_1334_);
lean_ctor_set(v_reuseFailAlloc_1360_, 10, v_releaseRepo_1335_);
lean_ctor_set(v_reuseFailAlloc_1360_, 11, v_val_1321_);
lean_ctor_set(v_reuseFailAlloc_1360_, 12, v_testDriver_1337_);
lean_ctor_set(v_reuseFailAlloc_1360_, 13, v_testDriverArgs_1338_);
lean_ctor_set(v_reuseFailAlloc_1360_, 14, v_lintDriver_1339_);
lean_ctor_set(v_reuseFailAlloc_1360_, 15, v_lintDriverArgs_1340_);
lean_ctor_set(v_reuseFailAlloc_1360_, 16, v_version_1341_);
lean_ctor_set(v_reuseFailAlloc_1360_, 17, v_versionTags_1342_);
lean_ctor_set(v_reuseFailAlloc_1360_, 18, v_description_1343_);
lean_ctor_set(v_reuseFailAlloc_1360_, 19, v_keywords_1344_);
lean_ctor_set(v_reuseFailAlloc_1360_, 20, v_homepage_1345_);
lean_ctor_set(v_reuseFailAlloc_1360_, 21, v_license_1346_);
lean_ctor_set(v_reuseFailAlloc_1360_, 22, v_licenseFiles_1347_);
lean_ctor_set(v_reuseFailAlloc_1360_, 23, v_readmeFile_1348_);
lean_ctor_set(v_reuseFailAlloc_1360_, 24, v_enableArtifactCache_x3f_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 25, v_restoreAllArtifacts_x3f_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26, v_bootstrap_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26 + 1, v_precompileModules_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26 + 3, v_reservoir_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26 + 5, v_allowImportAll_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*26 + 6, v_fixedToolchain_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* v_f_1363_, lean_object* v_cfg_1364_){
_start:
{
lean_object* v_toWorkspaceConfig_1365_; lean_object* v_toLeanConfig_1366_; uint8_t v_bootstrap_1367_; lean_object* v_extraDepTargets_1368_; uint8_t v_precompileModules_1369_; lean_object* v_moreGlobalServerArgs_1370_; lean_object* v_srcDir_1371_; lean_object* v_buildDir_1372_; lean_object* v_leanLibDir_1373_; lean_object* v_nativeLibDir_1374_; lean_object* v_binDir_1375_; lean_object* v_irDir_1376_; lean_object* v_releaseRepo_1377_; lean_object* v_buildArchive_1378_; uint8_t v_preferReleaseBuild_1379_; lean_object* v_testDriver_1380_; lean_object* v_testDriverArgs_1381_; lean_object* v_lintDriver_1382_; lean_object* v_lintDriverArgs_1383_; lean_object* v_version_1384_; lean_object* v_versionTags_1385_; lean_object* v_description_1386_; lean_object* v_keywords_1387_; lean_object* v_homepage_1388_; lean_object* v_license_1389_; lean_object* v_licenseFiles_1390_; lean_object* v_readmeFile_1391_; uint8_t v_reservoir_1392_; lean_object* v_enableArtifactCache_x3f_1393_; lean_object* v_restoreAllArtifacts_x3f_1394_; uint8_t v_libPrefixOnWindows_1395_; uint8_t v_allowImportAll_1396_; uint8_t v_fixedToolchain_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1405_; 
v_toWorkspaceConfig_1365_ = lean_ctor_get(v_cfg_1364_, 0);
v_toLeanConfig_1366_ = lean_ctor_get(v_cfg_1364_, 1);
v_bootstrap_1367_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26);
v_extraDepTargets_1368_ = lean_ctor_get(v_cfg_1364_, 2);
v_precompileModules_1369_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1370_ = lean_ctor_get(v_cfg_1364_, 3);
v_srcDir_1371_ = lean_ctor_get(v_cfg_1364_, 4);
v_buildDir_1372_ = lean_ctor_get(v_cfg_1364_, 5);
v_leanLibDir_1373_ = lean_ctor_get(v_cfg_1364_, 6);
v_nativeLibDir_1374_ = lean_ctor_get(v_cfg_1364_, 7);
v_binDir_1375_ = lean_ctor_get(v_cfg_1364_, 8);
v_irDir_1376_ = lean_ctor_get(v_cfg_1364_, 9);
v_releaseRepo_1377_ = lean_ctor_get(v_cfg_1364_, 10);
v_buildArchive_1378_ = lean_ctor_get(v_cfg_1364_, 11);
v_preferReleaseBuild_1379_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26 + 2);
v_testDriver_1380_ = lean_ctor_get(v_cfg_1364_, 12);
v_testDriverArgs_1381_ = lean_ctor_get(v_cfg_1364_, 13);
v_lintDriver_1382_ = lean_ctor_get(v_cfg_1364_, 14);
v_lintDriverArgs_1383_ = lean_ctor_get(v_cfg_1364_, 15);
v_version_1384_ = lean_ctor_get(v_cfg_1364_, 16);
v_versionTags_1385_ = lean_ctor_get(v_cfg_1364_, 17);
v_description_1386_ = lean_ctor_get(v_cfg_1364_, 18);
v_keywords_1387_ = lean_ctor_get(v_cfg_1364_, 19);
v_homepage_1388_ = lean_ctor_get(v_cfg_1364_, 20);
v_license_1389_ = lean_ctor_get(v_cfg_1364_, 21);
v_licenseFiles_1390_ = lean_ctor_get(v_cfg_1364_, 22);
v_readmeFile_1391_ = lean_ctor_get(v_cfg_1364_, 23);
v_reservoir_1392_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1393_ = lean_ctor_get(v_cfg_1364_, 24);
v_restoreAllArtifacts_x3f_1394_ = lean_ctor_get(v_cfg_1364_, 25);
v_libPrefixOnWindows_1395_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26 + 4);
v_allowImportAll_1396_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26 + 5);
v_fixedToolchain_1397_ = lean_ctor_get_uint8(v_cfg_1364_, sizeof(void*)*26 + 6);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_cfg_1364_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1399_ = v_cfg_1364_;
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1394_);
lean_inc(v_enableArtifactCache_x3f_1393_);
lean_inc(v_readmeFile_1391_);
lean_inc(v_licenseFiles_1390_);
lean_inc(v_license_1389_);
lean_inc(v_homepage_1388_);
lean_inc(v_keywords_1387_);
lean_inc(v_description_1386_);
lean_inc(v_versionTags_1385_);
lean_inc(v_version_1384_);
lean_inc(v_lintDriverArgs_1383_);
lean_inc(v_lintDriver_1382_);
lean_inc(v_testDriverArgs_1381_);
lean_inc(v_testDriver_1380_);
lean_inc(v_buildArchive_1378_);
lean_inc(v_releaseRepo_1377_);
lean_inc(v_irDir_1376_);
lean_inc(v_binDir_1375_);
lean_inc(v_nativeLibDir_1374_);
lean_inc(v_leanLibDir_1373_);
lean_inc(v_buildDir_1372_);
lean_inc(v_srcDir_1371_);
lean_inc(v_moreGlobalServerArgs_1370_);
lean_inc(v_extraDepTargets_1368_);
lean_inc(v_toLeanConfig_1366_);
lean_inc(v_toWorkspaceConfig_1365_);
lean_dec(v_cfg_1364_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_apply_1(v_f_1363_, v_buildArchive_1378_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 11, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_toWorkspaceConfig_1365_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_toLeanConfig_1366_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_extraDepTargets_1368_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_moreGlobalServerArgs_1370_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_srcDir_1371_);
lean_ctor_set(v_reuseFailAlloc_1404_, 5, v_buildDir_1372_);
lean_ctor_set(v_reuseFailAlloc_1404_, 6, v_leanLibDir_1373_);
lean_ctor_set(v_reuseFailAlloc_1404_, 7, v_nativeLibDir_1374_);
lean_ctor_set(v_reuseFailAlloc_1404_, 8, v_binDir_1375_);
lean_ctor_set(v_reuseFailAlloc_1404_, 9, v_irDir_1376_);
lean_ctor_set(v_reuseFailAlloc_1404_, 10, v_releaseRepo_1377_);
lean_ctor_set(v_reuseFailAlloc_1404_, 11, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1404_, 12, v_testDriver_1380_);
lean_ctor_set(v_reuseFailAlloc_1404_, 13, v_testDriverArgs_1381_);
lean_ctor_set(v_reuseFailAlloc_1404_, 14, v_lintDriver_1382_);
lean_ctor_set(v_reuseFailAlloc_1404_, 15, v_lintDriverArgs_1383_);
lean_ctor_set(v_reuseFailAlloc_1404_, 16, v_version_1384_);
lean_ctor_set(v_reuseFailAlloc_1404_, 17, v_versionTags_1385_);
lean_ctor_set(v_reuseFailAlloc_1404_, 18, v_description_1386_);
lean_ctor_set(v_reuseFailAlloc_1404_, 19, v_keywords_1387_);
lean_ctor_set(v_reuseFailAlloc_1404_, 20, v_homepage_1388_);
lean_ctor_set(v_reuseFailAlloc_1404_, 21, v_license_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 22, v_licenseFiles_1390_);
lean_ctor_set(v_reuseFailAlloc_1404_, 23, v_readmeFile_1391_);
lean_ctor_set(v_reuseFailAlloc_1404_, 24, v_enableArtifactCache_x3f_1393_);
lean_ctor_set(v_reuseFailAlloc_1404_, 25, v_restoreAllArtifacts_x3f_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26, v_bootstrap_1367_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26 + 1, v_precompileModules_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1379_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26 + 3, v_reservoir_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26 + 5, v_allowImportAll_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1404_, sizeof(void*)*26 + 6, v_fixedToolchain_1397_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1414_, lean_object* v_n_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1417_, lean_object* v_n_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1417_, v_n_1418_);
lean_dec(v_n_1418_);
lean_dec(v_p_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1420_, lean_object* v_n_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1420_, v_n_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1423_, lean_object* v_n_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1423_, v_n_1424_);
lean_dec(v_n_1424_);
lean_dec(v_p_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1426_, lean_object* v_n_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1426_, v_n_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1429_, lean_object* v_n_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1429_, v_n_1430_);
lean_dec(v_n_1430_);
lean_dec(v_p_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* v_cfg_1432_){
_start:
{
uint8_t v_preferReleaseBuild_1433_; 
v_preferReleaseBuild_1433_ = lean_ctor_get_uint8(v_cfg_1432_, sizeof(void*)*26 + 2);
return v_preferReleaseBuild_1433_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* v_cfg_1434_){
_start:
{
uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_res_1435_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(v_cfg_1434_);
lean_dec_ref(v_cfg_1434_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t v_val_1437_, lean_object* v_cfg_1438_){
_start:
{
lean_object* v_toWorkspaceConfig_1439_; lean_object* v_toLeanConfig_1440_; uint8_t v_bootstrap_1441_; lean_object* v_extraDepTargets_1442_; uint8_t v_precompileModules_1443_; lean_object* v_moreGlobalServerArgs_1444_; lean_object* v_srcDir_1445_; lean_object* v_buildDir_1446_; lean_object* v_leanLibDir_1447_; lean_object* v_nativeLibDir_1448_; lean_object* v_binDir_1449_; lean_object* v_irDir_1450_; lean_object* v_releaseRepo_1451_; lean_object* v_buildArchive_1452_; lean_object* v_testDriver_1453_; lean_object* v_testDriverArgs_1454_; lean_object* v_lintDriver_1455_; lean_object* v_lintDriverArgs_1456_; lean_object* v_version_1457_; lean_object* v_versionTags_1458_; lean_object* v_description_1459_; lean_object* v_keywords_1460_; lean_object* v_homepage_1461_; lean_object* v_license_1462_; lean_object* v_licenseFiles_1463_; lean_object* v_readmeFile_1464_; uint8_t v_reservoir_1465_; lean_object* v_enableArtifactCache_x3f_1466_; lean_object* v_restoreAllArtifacts_x3f_1467_; uint8_t v_libPrefixOnWindows_1468_; uint8_t v_allowImportAll_1469_; uint8_t v_fixedToolchain_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_toWorkspaceConfig_1439_ = lean_ctor_get(v_cfg_1438_, 0);
v_toLeanConfig_1440_ = lean_ctor_get(v_cfg_1438_, 1);
v_bootstrap_1441_ = lean_ctor_get_uint8(v_cfg_1438_, sizeof(void*)*26);
v_extraDepTargets_1442_ = lean_ctor_get(v_cfg_1438_, 2);
v_precompileModules_1443_ = lean_ctor_get_uint8(v_cfg_1438_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1444_ = lean_ctor_get(v_cfg_1438_, 3);
v_srcDir_1445_ = lean_ctor_get(v_cfg_1438_, 4);
v_buildDir_1446_ = lean_ctor_get(v_cfg_1438_, 5);
v_leanLibDir_1447_ = lean_ctor_get(v_cfg_1438_, 6);
v_nativeLibDir_1448_ = lean_ctor_get(v_cfg_1438_, 7);
v_binDir_1449_ = lean_ctor_get(v_cfg_1438_, 8);
v_irDir_1450_ = lean_ctor_get(v_cfg_1438_, 9);
v_releaseRepo_1451_ = lean_ctor_get(v_cfg_1438_, 10);
v_buildArchive_1452_ = lean_ctor_get(v_cfg_1438_, 11);
v_testDriver_1453_ = lean_ctor_get(v_cfg_1438_, 12);
v_testDriverArgs_1454_ = lean_ctor_get(v_cfg_1438_, 13);
v_lintDriver_1455_ = lean_ctor_get(v_cfg_1438_, 14);
v_lintDriverArgs_1456_ = lean_ctor_get(v_cfg_1438_, 15);
v_version_1457_ = lean_ctor_get(v_cfg_1438_, 16);
v_versionTags_1458_ = lean_ctor_get(v_cfg_1438_, 17);
v_description_1459_ = lean_ctor_get(v_cfg_1438_, 18);
v_keywords_1460_ = lean_ctor_get(v_cfg_1438_, 19);
v_homepage_1461_ = lean_ctor_get(v_cfg_1438_, 20);
v_license_1462_ = lean_ctor_get(v_cfg_1438_, 21);
v_licenseFiles_1463_ = lean_ctor_get(v_cfg_1438_, 22);
v_readmeFile_1464_ = lean_ctor_get(v_cfg_1438_, 23);
v_reservoir_1465_ = lean_ctor_get_uint8(v_cfg_1438_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1466_ = lean_ctor_get(v_cfg_1438_, 24);
v_restoreAllArtifacts_x3f_1467_ = lean_ctor_get(v_cfg_1438_, 25);
v_libPrefixOnWindows_1468_ = lean_ctor_get_uint8(v_cfg_1438_, sizeof(void*)*26 + 4);
v_allowImportAll_1469_ = lean_ctor_get_uint8(v_cfg_1438_, sizeof(void*)*26 + 5);
v_fixedToolchain_1470_ = lean_ctor_get_uint8(v_cfg_1438_, sizeof(void*)*26 + 6);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_cfg_1438_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v_cfg_1438_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1467_);
lean_inc(v_enableArtifactCache_x3f_1466_);
lean_inc(v_readmeFile_1464_);
lean_inc(v_licenseFiles_1463_);
lean_inc(v_license_1462_);
lean_inc(v_homepage_1461_);
lean_inc(v_keywords_1460_);
lean_inc(v_description_1459_);
lean_inc(v_versionTags_1458_);
lean_inc(v_version_1457_);
lean_inc(v_lintDriverArgs_1456_);
lean_inc(v_lintDriver_1455_);
lean_inc(v_testDriverArgs_1454_);
lean_inc(v_testDriver_1453_);
lean_inc(v_buildArchive_1452_);
lean_inc(v_releaseRepo_1451_);
lean_inc(v_irDir_1450_);
lean_inc(v_binDir_1449_);
lean_inc(v_nativeLibDir_1448_);
lean_inc(v_leanLibDir_1447_);
lean_inc(v_buildDir_1446_);
lean_inc(v_srcDir_1445_);
lean_inc(v_moreGlobalServerArgs_1444_);
lean_inc(v_extraDepTargets_1442_);
lean_inc(v_toLeanConfig_1440_);
lean_inc(v_toWorkspaceConfig_1439_);
lean_dec(v_cfg_1438_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_toWorkspaceConfig_1439_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_toLeanConfig_1440_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_extraDepTargets_1442_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_moreGlobalServerArgs_1444_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_srcDir_1445_);
lean_ctor_set(v_reuseFailAlloc_1476_, 5, v_buildDir_1446_);
lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_leanLibDir_1447_);
lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_nativeLibDir_1448_);
lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_binDir_1449_);
lean_ctor_set(v_reuseFailAlloc_1476_, 9, v_irDir_1450_);
lean_ctor_set(v_reuseFailAlloc_1476_, 10, v_releaseRepo_1451_);
lean_ctor_set(v_reuseFailAlloc_1476_, 11, v_buildArchive_1452_);
lean_ctor_set(v_reuseFailAlloc_1476_, 12, v_testDriver_1453_);
lean_ctor_set(v_reuseFailAlloc_1476_, 13, v_testDriverArgs_1454_);
lean_ctor_set(v_reuseFailAlloc_1476_, 14, v_lintDriver_1455_);
lean_ctor_set(v_reuseFailAlloc_1476_, 15, v_lintDriverArgs_1456_);
lean_ctor_set(v_reuseFailAlloc_1476_, 16, v_version_1457_);
lean_ctor_set(v_reuseFailAlloc_1476_, 17, v_versionTags_1458_);
lean_ctor_set(v_reuseFailAlloc_1476_, 18, v_description_1459_);
lean_ctor_set(v_reuseFailAlloc_1476_, 19, v_keywords_1460_);
lean_ctor_set(v_reuseFailAlloc_1476_, 20, v_homepage_1461_);
lean_ctor_set(v_reuseFailAlloc_1476_, 21, v_license_1462_);
lean_ctor_set(v_reuseFailAlloc_1476_, 22, v_licenseFiles_1463_);
lean_ctor_set(v_reuseFailAlloc_1476_, 23, v_readmeFile_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 24, v_enableArtifactCache_x3f_1466_);
lean_ctor_set(v_reuseFailAlloc_1476_, 25, v_restoreAllArtifacts_x3f_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*26, v_bootstrap_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*26 + 1, v_precompileModules_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*26 + 3, v_reservoir_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*26 + 5, v_allowImportAll_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*26 + 6, v_fixedToolchain_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*26 + 2, v_val_1437_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* v_val_1478_, lean_object* v_cfg_1479_){
_start:
{
uint8_t v_val_134__boxed_1480_; lean_object* v_res_1481_; 
v_val_134__boxed_1480_ = lean_unbox(v_val_1478_);
v_res_1481_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(v_val_134__boxed_1480_, v_cfg_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* v_f_1482_, lean_object* v_cfg_1483_){
_start:
{
lean_object* v_toWorkspaceConfig_1484_; lean_object* v_toLeanConfig_1485_; uint8_t v_bootstrap_1486_; lean_object* v_extraDepTargets_1487_; uint8_t v_precompileModules_1488_; lean_object* v_moreGlobalServerArgs_1489_; lean_object* v_srcDir_1490_; lean_object* v_buildDir_1491_; lean_object* v_leanLibDir_1492_; lean_object* v_nativeLibDir_1493_; lean_object* v_binDir_1494_; lean_object* v_irDir_1495_; lean_object* v_releaseRepo_1496_; lean_object* v_buildArchive_1497_; uint8_t v_preferReleaseBuild_1498_; lean_object* v_testDriver_1499_; lean_object* v_testDriverArgs_1500_; lean_object* v_lintDriver_1501_; lean_object* v_lintDriverArgs_1502_; lean_object* v_version_1503_; lean_object* v_versionTags_1504_; lean_object* v_description_1505_; lean_object* v_keywords_1506_; lean_object* v_homepage_1507_; lean_object* v_license_1508_; lean_object* v_licenseFiles_1509_; lean_object* v_readmeFile_1510_; uint8_t v_reservoir_1511_; lean_object* v_enableArtifactCache_x3f_1512_; lean_object* v_restoreAllArtifacts_x3f_1513_; uint8_t v_libPrefixOnWindows_1514_; uint8_t v_allowImportAll_1515_; uint8_t v_fixedToolchain_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1526_; 
v_toWorkspaceConfig_1484_ = lean_ctor_get(v_cfg_1483_, 0);
v_toLeanConfig_1485_ = lean_ctor_get(v_cfg_1483_, 1);
v_bootstrap_1486_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26);
v_extraDepTargets_1487_ = lean_ctor_get(v_cfg_1483_, 2);
v_precompileModules_1488_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1489_ = lean_ctor_get(v_cfg_1483_, 3);
v_srcDir_1490_ = lean_ctor_get(v_cfg_1483_, 4);
v_buildDir_1491_ = lean_ctor_get(v_cfg_1483_, 5);
v_leanLibDir_1492_ = lean_ctor_get(v_cfg_1483_, 6);
v_nativeLibDir_1493_ = lean_ctor_get(v_cfg_1483_, 7);
v_binDir_1494_ = lean_ctor_get(v_cfg_1483_, 8);
v_irDir_1495_ = lean_ctor_get(v_cfg_1483_, 9);
v_releaseRepo_1496_ = lean_ctor_get(v_cfg_1483_, 10);
v_buildArchive_1497_ = lean_ctor_get(v_cfg_1483_, 11);
v_preferReleaseBuild_1498_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26 + 2);
v_testDriver_1499_ = lean_ctor_get(v_cfg_1483_, 12);
v_testDriverArgs_1500_ = lean_ctor_get(v_cfg_1483_, 13);
v_lintDriver_1501_ = lean_ctor_get(v_cfg_1483_, 14);
v_lintDriverArgs_1502_ = lean_ctor_get(v_cfg_1483_, 15);
v_version_1503_ = lean_ctor_get(v_cfg_1483_, 16);
v_versionTags_1504_ = lean_ctor_get(v_cfg_1483_, 17);
v_description_1505_ = lean_ctor_get(v_cfg_1483_, 18);
v_keywords_1506_ = lean_ctor_get(v_cfg_1483_, 19);
v_homepage_1507_ = lean_ctor_get(v_cfg_1483_, 20);
v_license_1508_ = lean_ctor_get(v_cfg_1483_, 21);
v_licenseFiles_1509_ = lean_ctor_get(v_cfg_1483_, 22);
v_readmeFile_1510_ = lean_ctor_get(v_cfg_1483_, 23);
v_reservoir_1511_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1512_ = lean_ctor_get(v_cfg_1483_, 24);
v_restoreAllArtifacts_x3f_1513_ = lean_ctor_get(v_cfg_1483_, 25);
v_libPrefixOnWindows_1514_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26 + 4);
v_allowImportAll_1515_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26 + 5);
v_fixedToolchain_1516_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*26 + 6);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_cfg_1483_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1518_ = v_cfg_1483_;
v_isShared_1519_ = v_isSharedCheck_1526_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1513_);
lean_inc(v_enableArtifactCache_x3f_1512_);
lean_inc(v_readmeFile_1510_);
lean_inc(v_licenseFiles_1509_);
lean_inc(v_license_1508_);
lean_inc(v_homepage_1507_);
lean_inc(v_keywords_1506_);
lean_inc(v_description_1505_);
lean_inc(v_versionTags_1504_);
lean_inc(v_version_1503_);
lean_inc(v_lintDriverArgs_1502_);
lean_inc(v_lintDriver_1501_);
lean_inc(v_testDriverArgs_1500_);
lean_inc(v_testDriver_1499_);
lean_inc(v_buildArchive_1497_);
lean_inc(v_releaseRepo_1496_);
lean_inc(v_irDir_1495_);
lean_inc(v_binDir_1494_);
lean_inc(v_nativeLibDir_1493_);
lean_inc(v_leanLibDir_1492_);
lean_inc(v_buildDir_1491_);
lean_inc(v_srcDir_1490_);
lean_inc(v_moreGlobalServerArgs_1489_);
lean_inc(v_extraDepTargets_1487_);
lean_inc(v_toLeanConfig_1485_);
lean_inc(v_toWorkspaceConfig_1484_);
lean_dec(v_cfg_1483_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1526_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = lean_box(v_preferReleaseBuild_1498_);
v___x_1521_ = lean_apply_1(v_f_1482_, v___x_1520_);
if (v_isShared_1519_ == 0)
{
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_toWorkspaceConfig_1484_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_toLeanConfig_1485_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_extraDepTargets_1487_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_moreGlobalServerArgs_1489_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_srcDir_1490_);
lean_ctor_set(v_reuseFailAlloc_1525_, 5, v_buildDir_1491_);
lean_ctor_set(v_reuseFailAlloc_1525_, 6, v_leanLibDir_1492_);
lean_ctor_set(v_reuseFailAlloc_1525_, 7, v_nativeLibDir_1493_);
lean_ctor_set(v_reuseFailAlloc_1525_, 8, v_binDir_1494_);
lean_ctor_set(v_reuseFailAlloc_1525_, 9, v_irDir_1495_);
lean_ctor_set(v_reuseFailAlloc_1525_, 10, v_releaseRepo_1496_);
lean_ctor_set(v_reuseFailAlloc_1525_, 11, v_buildArchive_1497_);
lean_ctor_set(v_reuseFailAlloc_1525_, 12, v_testDriver_1499_);
lean_ctor_set(v_reuseFailAlloc_1525_, 13, v_testDriverArgs_1500_);
lean_ctor_set(v_reuseFailAlloc_1525_, 14, v_lintDriver_1501_);
lean_ctor_set(v_reuseFailAlloc_1525_, 15, v_lintDriverArgs_1502_);
lean_ctor_set(v_reuseFailAlloc_1525_, 16, v_version_1503_);
lean_ctor_set(v_reuseFailAlloc_1525_, 17, v_versionTags_1504_);
lean_ctor_set(v_reuseFailAlloc_1525_, 18, v_description_1505_);
lean_ctor_set(v_reuseFailAlloc_1525_, 19, v_keywords_1506_);
lean_ctor_set(v_reuseFailAlloc_1525_, 20, v_homepage_1507_);
lean_ctor_set(v_reuseFailAlloc_1525_, 21, v_license_1508_);
lean_ctor_set(v_reuseFailAlloc_1525_, 22, v_licenseFiles_1509_);
lean_ctor_set(v_reuseFailAlloc_1525_, 23, v_readmeFile_1510_);
lean_ctor_set(v_reuseFailAlloc_1525_, 24, v_enableArtifactCache_x3f_1512_);
lean_ctor_set(v_reuseFailAlloc_1525_, 25, v_restoreAllArtifacts_x3f_1513_);
lean_ctor_set_uint8(v_reuseFailAlloc_1525_, sizeof(void*)*26, v_bootstrap_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1525_, sizeof(void*)*26 + 1, v_precompileModules_1488_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_unbox(v___x_1521_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*26 + 2, v___x_1524_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*26 + 3, v_reservoir_1511_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1514_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*26 + 5, v_allowImportAll_1515_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*26 + 6, v_fixedToolchain_1516_);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1535_, lean_object* v_n_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1538_, lean_object* v_n_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1538_, v_n_1539_);
lean_dec(v_n_1539_);
lean_dec(v_p_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1541_, lean_object* v_n_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1541_, v_n_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1544_, lean_object* v_n_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1544_, v_n_1545_);
lean_dec(v_n_1545_);
lean_dec(v_p_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* v_cfg_1547_){
_start:
{
lean_object* v_testDriver_1548_; 
v_testDriver_1548_ = lean_ctor_get(v_cfg_1547_, 12);
lean_inc_ref(v_testDriver_1548_);
return v_testDriver_1548_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* v_cfg_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lake_PackageConfig_testDriver___proj___lam__0(v_cfg_1549_);
lean_dec_ref(v_cfg_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* v_val_1551_, lean_object* v_cfg_1552_){
_start:
{
lean_object* v_toWorkspaceConfig_1553_; lean_object* v_toLeanConfig_1554_; uint8_t v_bootstrap_1555_; lean_object* v_extraDepTargets_1556_; uint8_t v_precompileModules_1557_; lean_object* v_moreGlobalServerArgs_1558_; lean_object* v_srcDir_1559_; lean_object* v_buildDir_1560_; lean_object* v_leanLibDir_1561_; lean_object* v_nativeLibDir_1562_; lean_object* v_binDir_1563_; lean_object* v_irDir_1564_; lean_object* v_releaseRepo_1565_; lean_object* v_buildArchive_1566_; uint8_t v_preferReleaseBuild_1567_; lean_object* v_testDriverArgs_1568_; lean_object* v_lintDriver_1569_; lean_object* v_lintDriverArgs_1570_; lean_object* v_version_1571_; lean_object* v_versionTags_1572_; lean_object* v_description_1573_; lean_object* v_keywords_1574_; lean_object* v_homepage_1575_; lean_object* v_license_1576_; lean_object* v_licenseFiles_1577_; lean_object* v_readmeFile_1578_; uint8_t v_reservoir_1579_; lean_object* v_enableArtifactCache_x3f_1580_; lean_object* v_restoreAllArtifacts_x3f_1581_; uint8_t v_libPrefixOnWindows_1582_; uint8_t v_allowImportAll_1583_; uint8_t v_fixedToolchain_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_toWorkspaceConfig_1553_ = lean_ctor_get(v_cfg_1552_, 0);
v_toLeanConfig_1554_ = lean_ctor_get(v_cfg_1552_, 1);
v_bootstrap_1555_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26);
v_extraDepTargets_1556_ = lean_ctor_get(v_cfg_1552_, 2);
v_precompileModules_1557_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1558_ = lean_ctor_get(v_cfg_1552_, 3);
v_srcDir_1559_ = lean_ctor_get(v_cfg_1552_, 4);
v_buildDir_1560_ = lean_ctor_get(v_cfg_1552_, 5);
v_leanLibDir_1561_ = lean_ctor_get(v_cfg_1552_, 6);
v_nativeLibDir_1562_ = lean_ctor_get(v_cfg_1552_, 7);
v_binDir_1563_ = lean_ctor_get(v_cfg_1552_, 8);
v_irDir_1564_ = lean_ctor_get(v_cfg_1552_, 9);
v_releaseRepo_1565_ = lean_ctor_get(v_cfg_1552_, 10);
v_buildArchive_1566_ = lean_ctor_get(v_cfg_1552_, 11);
v_preferReleaseBuild_1567_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26 + 2);
v_testDriverArgs_1568_ = lean_ctor_get(v_cfg_1552_, 13);
v_lintDriver_1569_ = lean_ctor_get(v_cfg_1552_, 14);
v_lintDriverArgs_1570_ = lean_ctor_get(v_cfg_1552_, 15);
v_version_1571_ = lean_ctor_get(v_cfg_1552_, 16);
v_versionTags_1572_ = lean_ctor_get(v_cfg_1552_, 17);
v_description_1573_ = lean_ctor_get(v_cfg_1552_, 18);
v_keywords_1574_ = lean_ctor_get(v_cfg_1552_, 19);
v_homepage_1575_ = lean_ctor_get(v_cfg_1552_, 20);
v_license_1576_ = lean_ctor_get(v_cfg_1552_, 21);
v_licenseFiles_1577_ = lean_ctor_get(v_cfg_1552_, 22);
v_readmeFile_1578_ = lean_ctor_get(v_cfg_1552_, 23);
v_reservoir_1579_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1580_ = lean_ctor_get(v_cfg_1552_, 24);
v_restoreAllArtifacts_x3f_1581_ = lean_ctor_get(v_cfg_1552_, 25);
v_libPrefixOnWindows_1582_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26 + 4);
v_allowImportAll_1583_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26 + 5);
v_fixedToolchain_1584_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*26 + 6);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_cfg_1552_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_cfg_1552_, 12);
lean_dec(v_unused_1592_);
v___x_1586_ = v_cfg_1552_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1581_);
lean_inc(v_enableArtifactCache_x3f_1580_);
lean_inc(v_readmeFile_1578_);
lean_inc(v_licenseFiles_1577_);
lean_inc(v_license_1576_);
lean_inc(v_homepage_1575_);
lean_inc(v_keywords_1574_);
lean_inc(v_description_1573_);
lean_inc(v_versionTags_1572_);
lean_inc(v_version_1571_);
lean_inc(v_lintDriverArgs_1570_);
lean_inc(v_lintDriver_1569_);
lean_inc(v_testDriverArgs_1568_);
lean_inc(v_buildArchive_1566_);
lean_inc(v_releaseRepo_1565_);
lean_inc(v_irDir_1564_);
lean_inc(v_binDir_1563_);
lean_inc(v_nativeLibDir_1562_);
lean_inc(v_leanLibDir_1561_);
lean_inc(v_buildDir_1560_);
lean_inc(v_srcDir_1559_);
lean_inc(v_moreGlobalServerArgs_1558_);
lean_inc(v_extraDepTargets_1556_);
lean_inc(v_toLeanConfig_1554_);
lean_inc(v_toWorkspaceConfig_1553_);
lean_dec(v_cfg_1552_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 12, v_val_1551_);
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_toWorkspaceConfig_1553_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_toLeanConfig_1554_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_extraDepTargets_1556_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_moreGlobalServerArgs_1558_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_srcDir_1559_);
lean_ctor_set(v_reuseFailAlloc_1590_, 5, v_buildDir_1560_);
lean_ctor_set(v_reuseFailAlloc_1590_, 6, v_leanLibDir_1561_);
lean_ctor_set(v_reuseFailAlloc_1590_, 7, v_nativeLibDir_1562_);
lean_ctor_set(v_reuseFailAlloc_1590_, 8, v_binDir_1563_);
lean_ctor_set(v_reuseFailAlloc_1590_, 9, v_irDir_1564_);
lean_ctor_set(v_reuseFailAlloc_1590_, 10, v_releaseRepo_1565_);
lean_ctor_set(v_reuseFailAlloc_1590_, 11, v_buildArchive_1566_);
lean_ctor_set(v_reuseFailAlloc_1590_, 12, v_val_1551_);
lean_ctor_set(v_reuseFailAlloc_1590_, 13, v_testDriverArgs_1568_);
lean_ctor_set(v_reuseFailAlloc_1590_, 14, v_lintDriver_1569_);
lean_ctor_set(v_reuseFailAlloc_1590_, 15, v_lintDriverArgs_1570_);
lean_ctor_set(v_reuseFailAlloc_1590_, 16, v_version_1571_);
lean_ctor_set(v_reuseFailAlloc_1590_, 17, v_versionTags_1572_);
lean_ctor_set(v_reuseFailAlloc_1590_, 18, v_description_1573_);
lean_ctor_set(v_reuseFailAlloc_1590_, 19, v_keywords_1574_);
lean_ctor_set(v_reuseFailAlloc_1590_, 20, v_homepage_1575_);
lean_ctor_set(v_reuseFailAlloc_1590_, 21, v_license_1576_);
lean_ctor_set(v_reuseFailAlloc_1590_, 22, v_licenseFiles_1577_);
lean_ctor_set(v_reuseFailAlloc_1590_, 23, v_readmeFile_1578_);
lean_ctor_set(v_reuseFailAlloc_1590_, 24, v_enableArtifactCache_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 25, v_restoreAllArtifacts_x3f_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26, v_bootstrap_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26 + 1, v_precompileModules_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26 + 3, v_reservoir_1579_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26 + 5, v_allowImportAll_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*26 + 6, v_fixedToolchain_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* v_f_1593_, lean_object* v_cfg_1594_){
_start:
{
lean_object* v_toWorkspaceConfig_1595_; lean_object* v_toLeanConfig_1596_; uint8_t v_bootstrap_1597_; lean_object* v_extraDepTargets_1598_; uint8_t v_precompileModules_1599_; lean_object* v_moreGlobalServerArgs_1600_; lean_object* v_srcDir_1601_; lean_object* v_buildDir_1602_; lean_object* v_leanLibDir_1603_; lean_object* v_nativeLibDir_1604_; lean_object* v_binDir_1605_; lean_object* v_irDir_1606_; lean_object* v_releaseRepo_1607_; lean_object* v_buildArchive_1608_; uint8_t v_preferReleaseBuild_1609_; lean_object* v_testDriver_1610_; lean_object* v_testDriverArgs_1611_; lean_object* v_lintDriver_1612_; lean_object* v_lintDriverArgs_1613_; lean_object* v_version_1614_; lean_object* v_versionTags_1615_; lean_object* v_description_1616_; lean_object* v_keywords_1617_; lean_object* v_homepage_1618_; lean_object* v_license_1619_; lean_object* v_licenseFiles_1620_; lean_object* v_readmeFile_1621_; uint8_t v_reservoir_1622_; lean_object* v_enableArtifactCache_x3f_1623_; lean_object* v_restoreAllArtifacts_x3f_1624_; uint8_t v_libPrefixOnWindows_1625_; uint8_t v_allowImportAll_1626_; uint8_t v_fixedToolchain_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1635_; 
v_toWorkspaceConfig_1595_ = lean_ctor_get(v_cfg_1594_, 0);
v_toLeanConfig_1596_ = lean_ctor_get(v_cfg_1594_, 1);
v_bootstrap_1597_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26);
v_extraDepTargets_1598_ = lean_ctor_get(v_cfg_1594_, 2);
v_precompileModules_1599_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1600_ = lean_ctor_get(v_cfg_1594_, 3);
v_srcDir_1601_ = lean_ctor_get(v_cfg_1594_, 4);
v_buildDir_1602_ = lean_ctor_get(v_cfg_1594_, 5);
v_leanLibDir_1603_ = lean_ctor_get(v_cfg_1594_, 6);
v_nativeLibDir_1604_ = lean_ctor_get(v_cfg_1594_, 7);
v_binDir_1605_ = lean_ctor_get(v_cfg_1594_, 8);
v_irDir_1606_ = lean_ctor_get(v_cfg_1594_, 9);
v_releaseRepo_1607_ = lean_ctor_get(v_cfg_1594_, 10);
v_buildArchive_1608_ = lean_ctor_get(v_cfg_1594_, 11);
v_preferReleaseBuild_1609_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26 + 2);
v_testDriver_1610_ = lean_ctor_get(v_cfg_1594_, 12);
v_testDriverArgs_1611_ = lean_ctor_get(v_cfg_1594_, 13);
v_lintDriver_1612_ = lean_ctor_get(v_cfg_1594_, 14);
v_lintDriverArgs_1613_ = lean_ctor_get(v_cfg_1594_, 15);
v_version_1614_ = lean_ctor_get(v_cfg_1594_, 16);
v_versionTags_1615_ = lean_ctor_get(v_cfg_1594_, 17);
v_description_1616_ = lean_ctor_get(v_cfg_1594_, 18);
v_keywords_1617_ = lean_ctor_get(v_cfg_1594_, 19);
v_homepage_1618_ = lean_ctor_get(v_cfg_1594_, 20);
v_license_1619_ = lean_ctor_get(v_cfg_1594_, 21);
v_licenseFiles_1620_ = lean_ctor_get(v_cfg_1594_, 22);
v_readmeFile_1621_ = lean_ctor_get(v_cfg_1594_, 23);
v_reservoir_1622_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1623_ = lean_ctor_get(v_cfg_1594_, 24);
v_restoreAllArtifacts_x3f_1624_ = lean_ctor_get(v_cfg_1594_, 25);
v_libPrefixOnWindows_1625_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26 + 4);
v_allowImportAll_1626_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26 + 5);
v_fixedToolchain_1627_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*26 + 6);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_cfg_1594_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1629_ = v_cfg_1594_;
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1624_);
lean_inc(v_enableArtifactCache_x3f_1623_);
lean_inc(v_readmeFile_1621_);
lean_inc(v_licenseFiles_1620_);
lean_inc(v_license_1619_);
lean_inc(v_homepage_1618_);
lean_inc(v_keywords_1617_);
lean_inc(v_description_1616_);
lean_inc(v_versionTags_1615_);
lean_inc(v_version_1614_);
lean_inc(v_lintDriverArgs_1613_);
lean_inc(v_lintDriver_1612_);
lean_inc(v_testDriverArgs_1611_);
lean_inc(v_testDriver_1610_);
lean_inc(v_buildArchive_1608_);
lean_inc(v_releaseRepo_1607_);
lean_inc(v_irDir_1606_);
lean_inc(v_binDir_1605_);
lean_inc(v_nativeLibDir_1604_);
lean_inc(v_leanLibDir_1603_);
lean_inc(v_buildDir_1602_);
lean_inc(v_srcDir_1601_);
lean_inc(v_moreGlobalServerArgs_1600_);
lean_inc(v_extraDepTargets_1598_);
lean_inc(v_toLeanConfig_1596_);
lean_inc(v_toWorkspaceConfig_1595_);
lean_dec(v_cfg_1594_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_apply_1(v_f_1593_, v_testDriver_1610_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 12, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_toWorkspaceConfig_1595_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_toLeanConfig_1596_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_extraDepTargets_1598_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_moreGlobalServerArgs_1600_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_srcDir_1601_);
lean_ctor_set(v_reuseFailAlloc_1634_, 5, v_buildDir_1602_);
lean_ctor_set(v_reuseFailAlloc_1634_, 6, v_leanLibDir_1603_);
lean_ctor_set(v_reuseFailAlloc_1634_, 7, v_nativeLibDir_1604_);
lean_ctor_set(v_reuseFailAlloc_1634_, 8, v_binDir_1605_);
lean_ctor_set(v_reuseFailAlloc_1634_, 9, v_irDir_1606_);
lean_ctor_set(v_reuseFailAlloc_1634_, 10, v_releaseRepo_1607_);
lean_ctor_set(v_reuseFailAlloc_1634_, 11, v_buildArchive_1608_);
lean_ctor_set(v_reuseFailAlloc_1634_, 12, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1634_, 13, v_testDriverArgs_1611_);
lean_ctor_set(v_reuseFailAlloc_1634_, 14, v_lintDriver_1612_);
lean_ctor_set(v_reuseFailAlloc_1634_, 15, v_lintDriverArgs_1613_);
lean_ctor_set(v_reuseFailAlloc_1634_, 16, v_version_1614_);
lean_ctor_set(v_reuseFailAlloc_1634_, 17, v_versionTags_1615_);
lean_ctor_set(v_reuseFailAlloc_1634_, 18, v_description_1616_);
lean_ctor_set(v_reuseFailAlloc_1634_, 19, v_keywords_1617_);
lean_ctor_set(v_reuseFailAlloc_1634_, 20, v_homepage_1618_);
lean_ctor_set(v_reuseFailAlloc_1634_, 21, v_license_1619_);
lean_ctor_set(v_reuseFailAlloc_1634_, 22, v_licenseFiles_1620_);
lean_ctor_set(v_reuseFailAlloc_1634_, 23, v_readmeFile_1621_);
lean_ctor_set(v_reuseFailAlloc_1634_, 24, v_enableArtifactCache_x3f_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 25, v_restoreAllArtifacts_x3f_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26, v_bootstrap_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26 + 1, v_precompileModules_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26 + 3, v_reservoir_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26 + 5, v_allowImportAll_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*26 + 6, v_fixedToolchain_1627_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* v_x_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lake_PackageConfig_testDriver___proj___lam__3(v_x_1638_);
lean_dec_ref(v_x_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1649_, lean_object* v_n_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1652_, lean_object* v_n_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lake_PackageConfig_testDriver___proj(v_p_1652_, v_n_1653_);
lean_dec(v_n_1653_);
lean_dec(v_p_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1655_, lean_object* v_n_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lake_PackageConfig_testDriver___proj(v_p_1655_, v_n_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1658_, lean_object* v_n_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1658_, v_n_1659_);
lean_dec(v_n_1659_);
lean_dec(v_p_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1661_, lean_object* v_n_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lake_PackageConfig_testDriver___proj(v_p_1661_, v_n_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1664_, lean_object* v_n_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1664_, v_n_1665_);
lean_dec(v_n_1665_);
lean_dec(v_p_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* v_cfg_1667_){
_start:
{
lean_object* v_testDriverArgs_1668_; 
v_testDriverArgs_1668_ = lean_ctor_get(v_cfg_1667_, 13);
lean_inc_ref(v_testDriverArgs_1668_);
return v_testDriverArgs_1668_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(v_cfg_1669_);
lean_dec_ref(v_cfg_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* v_val_1671_, lean_object* v_cfg_1672_){
_start:
{
lean_object* v_toWorkspaceConfig_1673_; lean_object* v_toLeanConfig_1674_; uint8_t v_bootstrap_1675_; lean_object* v_extraDepTargets_1676_; uint8_t v_precompileModules_1677_; lean_object* v_moreGlobalServerArgs_1678_; lean_object* v_srcDir_1679_; lean_object* v_buildDir_1680_; lean_object* v_leanLibDir_1681_; lean_object* v_nativeLibDir_1682_; lean_object* v_binDir_1683_; lean_object* v_irDir_1684_; lean_object* v_releaseRepo_1685_; lean_object* v_buildArchive_1686_; uint8_t v_preferReleaseBuild_1687_; lean_object* v_testDriver_1688_; lean_object* v_lintDriver_1689_; lean_object* v_lintDriverArgs_1690_; lean_object* v_version_1691_; lean_object* v_versionTags_1692_; lean_object* v_description_1693_; lean_object* v_keywords_1694_; lean_object* v_homepage_1695_; lean_object* v_license_1696_; lean_object* v_licenseFiles_1697_; lean_object* v_readmeFile_1698_; uint8_t v_reservoir_1699_; lean_object* v_enableArtifactCache_x3f_1700_; lean_object* v_restoreAllArtifacts_x3f_1701_; uint8_t v_libPrefixOnWindows_1702_; uint8_t v_allowImportAll_1703_; uint8_t v_fixedToolchain_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_toWorkspaceConfig_1673_ = lean_ctor_get(v_cfg_1672_, 0);
v_toLeanConfig_1674_ = lean_ctor_get(v_cfg_1672_, 1);
v_bootstrap_1675_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26);
v_extraDepTargets_1676_ = lean_ctor_get(v_cfg_1672_, 2);
v_precompileModules_1677_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1678_ = lean_ctor_get(v_cfg_1672_, 3);
v_srcDir_1679_ = lean_ctor_get(v_cfg_1672_, 4);
v_buildDir_1680_ = lean_ctor_get(v_cfg_1672_, 5);
v_leanLibDir_1681_ = lean_ctor_get(v_cfg_1672_, 6);
v_nativeLibDir_1682_ = lean_ctor_get(v_cfg_1672_, 7);
v_binDir_1683_ = lean_ctor_get(v_cfg_1672_, 8);
v_irDir_1684_ = lean_ctor_get(v_cfg_1672_, 9);
v_releaseRepo_1685_ = lean_ctor_get(v_cfg_1672_, 10);
v_buildArchive_1686_ = lean_ctor_get(v_cfg_1672_, 11);
v_preferReleaseBuild_1687_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26 + 2);
v_testDriver_1688_ = lean_ctor_get(v_cfg_1672_, 12);
v_lintDriver_1689_ = lean_ctor_get(v_cfg_1672_, 14);
v_lintDriverArgs_1690_ = lean_ctor_get(v_cfg_1672_, 15);
v_version_1691_ = lean_ctor_get(v_cfg_1672_, 16);
v_versionTags_1692_ = lean_ctor_get(v_cfg_1672_, 17);
v_description_1693_ = lean_ctor_get(v_cfg_1672_, 18);
v_keywords_1694_ = lean_ctor_get(v_cfg_1672_, 19);
v_homepage_1695_ = lean_ctor_get(v_cfg_1672_, 20);
v_license_1696_ = lean_ctor_get(v_cfg_1672_, 21);
v_licenseFiles_1697_ = lean_ctor_get(v_cfg_1672_, 22);
v_readmeFile_1698_ = lean_ctor_get(v_cfg_1672_, 23);
v_reservoir_1699_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1700_ = lean_ctor_get(v_cfg_1672_, 24);
v_restoreAllArtifacts_x3f_1701_ = lean_ctor_get(v_cfg_1672_, 25);
v_libPrefixOnWindows_1702_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26 + 4);
v_allowImportAll_1703_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26 + 5);
v_fixedToolchain_1704_ = lean_ctor_get_uint8(v_cfg_1672_, sizeof(void*)*26 + 6);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_cfg_1672_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v_cfg_1672_, 13);
lean_dec(v_unused_1712_);
v___x_1706_ = v_cfg_1672_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1701_);
lean_inc(v_enableArtifactCache_x3f_1700_);
lean_inc(v_readmeFile_1698_);
lean_inc(v_licenseFiles_1697_);
lean_inc(v_license_1696_);
lean_inc(v_homepage_1695_);
lean_inc(v_keywords_1694_);
lean_inc(v_description_1693_);
lean_inc(v_versionTags_1692_);
lean_inc(v_version_1691_);
lean_inc(v_lintDriverArgs_1690_);
lean_inc(v_lintDriver_1689_);
lean_inc(v_testDriver_1688_);
lean_inc(v_buildArchive_1686_);
lean_inc(v_releaseRepo_1685_);
lean_inc(v_irDir_1684_);
lean_inc(v_binDir_1683_);
lean_inc(v_nativeLibDir_1682_);
lean_inc(v_leanLibDir_1681_);
lean_inc(v_buildDir_1680_);
lean_inc(v_srcDir_1679_);
lean_inc(v_moreGlobalServerArgs_1678_);
lean_inc(v_extraDepTargets_1676_);
lean_inc(v_toLeanConfig_1674_);
lean_inc(v_toWorkspaceConfig_1673_);
lean_dec(v_cfg_1672_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 13, v_val_1671_);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_toWorkspaceConfig_1673_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_toLeanConfig_1674_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_extraDepTargets_1676_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_moreGlobalServerArgs_1678_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_srcDir_1679_);
lean_ctor_set(v_reuseFailAlloc_1710_, 5, v_buildDir_1680_);
lean_ctor_set(v_reuseFailAlloc_1710_, 6, v_leanLibDir_1681_);
lean_ctor_set(v_reuseFailAlloc_1710_, 7, v_nativeLibDir_1682_);
lean_ctor_set(v_reuseFailAlloc_1710_, 8, v_binDir_1683_);
lean_ctor_set(v_reuseFailAlloc_1710_, 9, v_irDir_1684_);
lean_ctor_set(v_reuseFailAlloc_1710_, 10, v_releaseRepo_1685_);
lean_ctor_set(v_reuseFailAlloc_1710_, 11, v_buildArchive_1686_);
lean_ctor_set(v_reuseFailAlloc_1710_, 12, v_testDriver_1688_);
lean_ctor_set(v_reuseFailAlloc_1710_, 13, v_val_1671_);
lean_ctor_set(v_reuseFailAlloc_1710_, 14, v_lintDriver_1689_);
lean_ctor_set(v_reuseFailAlloc_1710_, 15, v_lintDriverArgs_1690_);
lean_ctor_set(v_reuseFailAlloc_1710_, 16, v_version_1691_);
lean_ctor_set(v_reuseFailAlloc_1710_, 17, v_versionTags_1692_);
lean_ctor_set(v_reuseFailAlloc_1710_, 18, v_description_1693_);
lean_ctor_set(v_reuseFailAlloc_1710_, 19, v_keywords_1694_);
lean_ctor_set(v_reuseFailAlloc_1710_, 20, v_homepage_1695_);
lean_ctor_set(v_reuseFailAlloc_1710_, 21, v_license_1696_);
lean_ctor_set(v_reuseFailAlloc_1710_, 22, v_licenseFiles_1697_);
lean_ctor_set(v_reuseFailAlloc_1710_, 23, v_readmeFile_1698_);
lean_ctor_set(v_reuseFailAlloc_1710_, 24, v_enableArtifactCache_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1710_, 25, v_restoreAllArtifacts_x3f_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26, v_bootstrap_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26 + 1, v_precompileModules_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26 + 3, v_reservoir_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26 + 5, v_allowImportAll_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*26 + 6, v_fixedToolchain_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* v_f_1713_, lean_object* v_cfg_1714_){
_start:
{
lean_object* v_toWorkspaceConfig_1715_; lean_object* v_toLeanConfig_1716_; uint8_t v_bootstrap_1717_; lean_object* v_extraDepTargets_1718_; uint8_t v_precompileModules_1719_; lean_object* v_moreGlobalServerArgs_1720_; lean_object* v_srcDir_1721_; lean_object* v_buildDir_1722_; lean_object* v_leanLibDir_1723_; lean_object* v_nativeLibDir_1724_; lean_object* v_binDir_1725_; lean_object* v_irDir_1726_; lean_object* v_releaseRepo_1727_; lean_object* v_buildArchive_1728_; uint8_t v_preferReleaseBuild_1729_; lean_object* v_testDriver_1730_; lean_object* v_testDriverArgs_1731_; lean_object* v_lintDriver_1732_; lean_object* v_lintDriverArgs_1733_; lean_object* v_version_1734_; lean_object* v_versionTags_1735_; lean_object* v_description_1736_; lean_object* v_keywords_1737_; lean_object* v_homepage_1738_; lean_object* v_license_1739_; lean_object* v_licenseFiles_1740_; lean_object* v_readmeFile_1741_; uint8_t v_reservoir_1742_; lean_object* v_enableArtifactCache_x3f_1743_; lean_object* v_restoreAllArtifacts_x3f_1744_; uint8_t v_libPrefixOnWindows_1745_; uint8_t v_allowImportAll_1746_; uint8_t v_fixedToolchain_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_toWorkspaceConfig_1715_ = lean_ctor_get(v_cfg_1714_, 0);
v_toLeanConfig_1716_ = lean_ctor_get(v_cfg_1714_, 1);
v_bootstrap_1717_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26);
v_extraDepTargets_1718_ = lean_ctor_get(v_cfg_1714_, 2);
v_precompileModules_1719_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1720_ = lean_ctor_get(v_cfg_1714_, 3);
v_srcDir_1721_ = lean_ctor_get(v_cfg_1714_, 4);
v_buildDir_1722_ = lean_ctor_get(v_cfg_1714_, 5);
v_leanLibDir_1723_ = lean_ctor_get(v_cfg_1714_, 6);
v_nativeLibDir_1724_ = lean_ctor_get(v_cfg_1714_, 7);
v_binDir_1725_ = lean_ctor_get(v_cfg_1714_, 8);
v_irDir_1726_ = lean_ctor_get(v_cfg_1714_, 9);
v_releaseRepo_1727_ = lean_ctor_get(v_cfg_1714_, 10);
v_buildArchive_1728_ = lean_ctor_get(v_cfg_1714_, 11);
v_preferReleaseBuild_1729_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26 + 2);
v_testDriver_1730_ = lean_ctor_get(v_cfg_1714_, 12);
v_testDriverArgs_1731_ = lean_ctor_get(v_cfg_1714_, 13);
v_lintDriver_1732_ = lean_ctor_get(v_cfg_1714_, 14);
v_lintDriverArgs_1733_ = lean_ctor_get(v_cfg_1714_, 15);
v_version_1734_ = lean_ctor_get(v_cfg_1714_, 16);
v_versionTags_1735_ = lean_ctor_get(v_cfg_1714_, 17);
v_description_1736_ = lean_ctor_get(v_cfg_1714_, 18);
v_keywords_1737_ = lean_ctor_get(v_cfg_1714_, 19);
v_homepage_1738_ = lean_ctor_get(v_cfg_1714_, 20);
v_license_1739_ = lean_ctor_get(v_cfg_1714_, 21);
v_licenseFiles_1740_ = lean_ctor_get(v_cfg_1714_, 22);
v_readmeFile_1741_ = lean_ctor_get(v_cfg_1714_, 23);
v_reservoir_1742_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1743_ = lean_ctor_get(v_cfg_1714_, 24);
v_restoreAllArtifacts_x3f_1744_ = lean_ctor_get(v_cfg_1714_, 25);
v_libPrefixOnWindows_1745_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26 + 4);
v_allowImportAll_1746_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26 + 5);
v_fixedToolchain_1747_ = lean_ctor_get_uint8(v_cfg_1714_, sizeof(void*)*26 + 6);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_cfg_1714_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v_cfg_1714_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1744_);
lean_inc(v_enableArtifactCache_x3f_1743_);
lean_inc(v_readmeFile_1741_);
lean_inc(v_licenseFiles_1740_);
lean_inc(v_license_1739_);
lean_inc(v_homepage_1738_);
lean_inc(v_keywords_1737_);
lean_inc(v_description_1736_);
lean_inc(v_versionTags_1735_);
lean_inc(v_version_1734_);
lean_inc(v_lintDriverArgs_1733_);
lean_inc(v_lintDriver_1732_);
lean_inc(v_testDriverArgs_1731_);
lean_inc(v_testDriver_1730_);
lean_inc(v_buildArchive_1728_);
lean_inc(v_releaseRepo_1727_);
lean_inc(v_irDir_1726_);
lean_inc(v_binDir_1725_);
lean_inc(v_nativeLibDir_1724_);
lean_inc(v_leanLibDir_1723_);
lean_inc(v_buildDir_1722_);
lean_inc(v_srcDir_1721_);
lean_inc(v_moreGlobalServerArgs_1720_);
lean_inc(v_extraDepTargets_1718_);
lean_inc(v_toLeanConfig_1716_);
lean_inc(v_toWorkspaceConfig_1715_);
lean_dec(v_cfg_1714_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_apply_1(v_f_1713_, v_testDriverArgs_1731_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 13, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_toWorkspaceConfig_1715_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_toLeanConfig_1716_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_extraDepTargets_1718_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_moreGlobalServerArgs_1720_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_srcDir_1721_);
lean_ctor_set(v_reuseFailAlloc_1754_, 5, v_buildDir_1722_);
lean_ctor_set(v_reuseFailAlloc_1754_, 6, v_leanLibDir_1723_);
lean_ctor_set(v_reuseFailAlloc_1754_, 7, v_nativeLibDir_1724_);
lean_ctor_set(v_reuseFailAlloc_1754_, 8, v_binDir_1725_);
lean_ctor_set(v_reuseFailAlloc_1754_, 9, v_irDir_1726_);
lean_ctor_set(v_reuseFailAlloc_1754_, 10, v_releaseRepo_1727_);
lean_ctor_set(v_reuseFailAlloc_1754_, 11, v_buildArchive_1728_);
lean_ctor_set(v_reuseFailAlloc_1754_, 12, v_testDriver_1730_);
lean_ctor_set(v_reuseFailAlloc_1754_, 13, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1754_, 14, v_lintDriver_1732_);
lean_ctor_set(v_reuseFailAlloc_1754_, 15, v_lintDriverArgs_1733_);
lean_ctor_set(v_reuseFailAlloc_1754_, 16, v_version_1734_);
lean_ctor_set(v_reuseFailAlloc_1754_, 17, v_versionTags_1735_);
lean_ctor_set(v_reuseFailAlloc_1754_, 18, v_description_1736_);
lean_ctor_set(v_reuseFailAlloc_1754_, 19, v_keywords_1737_);
lean_ctor_set(v_reuseFailAlloc_1754_, 20, v_homepage_1738_);
lean_ctor_set(v_reuseFailAlloc_1754_, 21, v_license_1739_);
lean_ctor_set(v_reuseFailAlloc_1754_, 22, v_licenseFiles_1740_);
lean_ctor_set(v_reuseFailAlloc_1754_, 23, v_readmeFile_1741_);
lean_ctor_set(v_reuseFailAlloc_1754_, 24, v_enableArtifactCache_x3f_1743_);
lean_ctor_set(v_reuseFailAlloc_1754_, 25, v_restoreAllArtifacts_x3f_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26, v_bootstrap_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26 + 1, v_precompileModules_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26 + 3, v_reservoir_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26 + 5, v_allowImportAll_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*26 + 6, v_fixedToolchain_1747_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1764_, lean_object* v_n_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1767_, lean_object* v_n_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1767_, v_n_1768_);
lean_dec(v_n_1768_);
lean_dec(v_p_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_1770_, lean_object* v_n_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1770_, v_n_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_1773_, lean_object* v_n_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_1773_, v_n_1774_);
lean_dec(v_n_1774_);
lean_dec(v_p_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* v_cfg_1776_){
_start:
{
lean_object* v_lintDriver_1777_; 
v_lintDriver_1777_ = lean_ctor_get(v_cfg_1776_, 14);
lean_inc_ref(v_lintDriver_1777_);
return v_lintDriver_1777_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* v_cfg_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lake_PackageConfig_lintDriver___proj___lam__0(v_cfg_1778_);
lean_dec_ref(v_cfg_1778_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* v_val_1780_, lean_object* v_cfg_1781_){
_start:
{
lean_object* v_toWorkspaceConfig_1782_; lean_object* v_toLeanConfig_1783_; uint8_t v_bootstrap_1784_; lean_object* v_extraDepTargets_1785_; uint8_t v_precompileModules_1786_; lean_object* v_moreGlobalServerArgs_1787_; lean_object* v_srcDir_1788_; lean_object* v_buildDir_1789_; lean_object* v_leanLibDir_1790_; lean_object* v_nativeLibDir_1791_; lean_object* v_binDir_1792_; lean_object* v_irDir_1793_; lean_object* v_releaseRepo_1794_; lean_object* v_buildArchive_1795_; uint8_t v_preferReleaseBuild_1796_; lean_object* v_testDriver_1797_; lean_object* v_testDriverArgs_1798_; lean_object* v_lintDriverArgs_1799_; lean_object* v_version_1800_; lean_object* v_versionTags_1801_; lean_object* v_description_1802_; lean_object* v_keywords_1803_; lean_object* v_homepage_1804_; lean_object* v_license_1805_; lean_object* v_licenseFiles_1806_; lean_object* v_readmeFile_1807_; uint8_t v_reservoir_1808_; lean_object* v_enableArtifactCache_x3f_1809_; lean_object* v_restoreAllArtifacts_x3f_1810_; uint8_t v_libPrefixOnWindows_1811_; uint8_t v_allowImportAll_1812_; uint8_t v_fixedToolchain_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_toWorkspaceConfig_1782_ = lean_ctor_get(v_cfg_1781_, 0);
v_toLeanConfig_1783_ = lean_ctor_get(v_cfg_1781_, 1);
v_bootstrap_1784_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26);
v_extraDepTargets_1785_ = lean_ctor_get(v_cfg_1781_, 2);
v_precompileModules_1786_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1787_ = lean_ctor_get(v_cfg_1781_, 3);
v_srcDir_1788_ = lean_ctor_get(v_cfg_1781_, 4);
v_buildDir_1789_ = lean_ctor_get(v_cfg_1781_, 5);
v_leanLibDir_1790_ = lean_ctor_get(v_cfg_1781_, 6);
v_nativeLibDir_1791_ = lean_ctor_get(v_cfg_1781_, 7);
v_binDir_1792_ = lean_ctor_get(v_cfg_1781_, 8);
v_irDir_1793_ = lean_ctor_get(v_cfg_1781_, 9);
v_releaseRepo_1794_ = lean_ctor_get(v_cfg_1781_, 10);
v_buildArchive_1795_ = lean_ctor_get(v_cfg_1781_, 11);
v_preferReleaseBuild_1796_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26 + 2);
v_testDriver_1797_ = lean_ctor_get(v_cfg_1781_, 12);
v_testDriverArgs_1798_ = lean_ctor_get(v_cfg_1781_, 13);
v_lintDriverArgs_1799_ = lean_ctor_get(v_cfg_1781_, 15);
v_version_1800_ = lean_ctor_get(v_cfg_1781_, 16);
v_versionTags_1801_ = lean_ctor_get(v_cfg_1781_, 17);
v_description_1802_ = lean_ctor_get(v_cfg_1781_, 18);
v_keywords_1803_ = lean_ctor_get(v_cfg_1781_, 19);
v_homepage_1804_ = lean_ctor_get(v_cfg_1781_, 20);
v_license_1805_ = lean_ctor_get(v_cfg_1781_, 21);
v_licenseFiles_1806_ = lean_ctor_get(v_cfg_1781_, 22);
v_readmeFile_1807_ = lean_ctor_get(v_cfg_1781_, 23);
v_reservoir_1808_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1809_ = lean_ctor_get(v_cfg_1781_, 24);
v_restoreAllArtifacts_x3f_1810_ = lean_ctor_get(v_cfg_1781_, 25);
v_libPrefixOnWindows_1811_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26 + 4);
v_allowImportAll_1812_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26 + 5);
v_fixedToolchain_1813_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*26 + 6);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_cfg_1781_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v_cfg_1781_, 14);
lean_dec(v_unused_1821_);
v___x_1815_ = v_cfg_1781_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1810_);
lean_inc(v_enableArtifactCache_x3f_1809_);
lean_inc(v_readmeFile_1807_);
lean_inc(v_licenseFiles_1806_);
lean_inc(v_license_1805_);
lean_inc(v_homepage_1804_);
lean_inc(v_keywords_1803_);
lean_inc(v_description_1802_);
lean_inc(v_versionTags_1801_);
lean_inc(v_version_1800_);
lean_inc(v_lintDriverArgs_1799_);
lean_inc(v_testDriverArgs_1798_);
lean_inc(v_testDriver_1797_);
lean_inc(v_buildArchive_1795_);
lean_inc(v_releaseRepo_1794_);
lean_inc(v_irDir_1793_);
lean_inc(v_binDir_1792_);
lean_inc(v_nativeLibDir_1791_);
lean_inc(v_leanLibDir_1790_);
lean_inc(v_buildDir_1789_);
lean_inc(v_srcDir_1788_);
lean_inc(v_moreGlobalServerArgs_1787_);
lean_inc(v_extraDepTargets_1785_);
lean_inc(v_toLeanConfig_1783_);
lean_inc(v_toWorkspaceConfig_1782_);
lean_dec(v_cfg_1781_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 14, v_val_1780_);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_toWorkspaceConfig_1782_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_toLeanConfig_1783_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_extraDepTargets_1785_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_moreGlobalServerArgs_1787_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_srcDir_1788_);
lean_ctor_set(v_reuseFailAlloc_1819_, 5, v_buildDir_1789_);
lean_ctor_set(v_reuseFailAlloc_1819_, 6, v_leanLibDir_1790_);
lean_ctor_set(v_reuseFailAlloc_1819_, 7, v_nativeLibDir_1791_);
lean_ctor_set(v_reuseFailAlloc_1819_, 8, v_binDir_1792_);
lean_ctor_set(v_reuseFailAlloc_1819_, 9, v_irDir_1793_);
lean_ctor_set(v_reuseFailAlloc_1819_, 10, v_releaseRepo_1794_);
lean_ctor_set(v_reuseFailAlloc_1819_, 11, v_buildArchive_1795_);
lean_ctor_set(v_reuseFailAlloc_1819_, 12, v_testDriver_1797_);
lean_ctor_set(v_reuseFailAlloc_1819_, 13, v_testDriverArgs_1798_);
lean_ctor_set(v_reuseFailAlloc_1819_, 14, v_val_1780_);
lean_ctor_set(v_reuseFailAlloc_1819_, 15, v_lintDriverArgs_1799_);
lean_ctor_set(v_reuseFailAlloc_1819_, 16, v_version_1800_);
lean_ctor_set(v_reuseFailAlloc_1819_, 17, v_versionTags_1801_);
lean_ctor_set(v_reuseFailAlloc_1819_, 18, v_description_1802_);
lean_ctor_set(v_reuseFailAlloc_1819_, 19, v_keywords_1803_);
lean_ctor_set(v_reuseFailAlloc_1819_, 20, v_homepage_1804_);
lean_ctor_set(v_reuseFailAlloc_1819_, 21, v_license_1805_);
lean_ctor_set(v_reuseFailAlloc_1819_, 22, v_licenseFiles_1806_);
lean_ctor_set(v_reuseFailAlloc_1819_, 23, v_readmeFile_1807_);
lean_ctor_set(v_reuseFailAlloc_1819_, 24, v_enableArtifactCache_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1819_, 25, v_restoreAllArtifacts_x3f_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26, v_bootstrap_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26 + 1, v_precompileModules_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26 + 3, v_reservoir_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26 + 5, v_allowImportAll_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*26 + 6, v_fixedToolchain_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* v_f_1822_, lean_object* v_cfg_1823_){
_start:
{
lean_object* v_toWorkspaceConfig_1824_; lean_object* v_toLeanConfig_1825_; uint8_t v_bootstrap_1826_; lean_object* v_extraDepTargets_1827_; uint8_t v_precompileModules_1828_; lean_object* v_moreGlobalServerArgs_1829_; lean_object* v_srcDir_1830_; lean_object* v_buildDir_1831_; lean_object* v_leanLibDir_1832_; lean_object* v_nativeLibDir_1833_; lean_object* v_binDir_1834_; lean_object* v_irDir_1835_; lean_object* v_releaseRepo_1836_; lean_object* v_buildArchive_1837_; uint8_t v_preferReleaseBuild_1838_; lean_object* v_testDriver_1839_; lean_object* v_testDriverArgs_1840_; lean_object* v_lintDriver_1841_; lean_object* v_lintDriverArgs_1842_; lean_object* v_version_1843_; lean_object* v_versionTags_1844_; lean_object* v_description_1845_; lean_object* v_keywords_1846_; lean_object* v_homepage_1847_; lean_object* v_license_1848_; lean_object* v_licenseFiles_1849_; lean_object* v_readmeFile_1850_; uint8_t v_reservoir_1851_; lean_object* v_enableArtifactCache_x3f_1852_; lean_object* v_restoreAllArtifacts_x3f_1853_; uint8_t v_libPrefixOnWindows_1854_; uint8_t v_allowImportAll_1855_; uint8_t v_fixedToolchain_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
v_toWorkspaceConfig_1824_ = lean_ctor_get(v_cfg_1823_, 0);
v_toLeanConfig_1825_ = lean_ctor_get(v_cfg_1823_, 1);
v_bootstrap_1826_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26);
v_extraDepTargets_1827_ = lean_ctor_get(v_cfg_1823_, 2);
v_precompileModules_1828_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1829_ = lean_ctor_get(v_cfg_1823_, 3);
v_srcDir_1830_ = lean_ctor_get(v_cfg_1823_, 4);
v_buildDir_1831_ = lean_ctor_get(v_cfg_1823_, 5);
v_leanLibDir_1832_ = lean_ctor_get(v_cfg_1823_, 6);
v_nativeLibDir_1833_ = lean_ctor_get(v_cfg_1823_, 7);
v_binDir_1834_ = lean_ctor_get(v_cfg_1823_, 8);
v_irDir_1835_ = lean_ctor_get(v_cfg_1823_, 9);
v_releaseRepo_1836_ = lean_ctor_get(v_cfg_1823_, 10);
v_buildArchive_1837_ = lean_ctor_get(v_cfg_1823_, 11);
v_preferReleaseBuild_1838_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26 + 2);
v_testDriver_1839_ = lean_ctor_get(v_cfg_1823_, 12);
v_testDriverArgs_1840_ = lean_ctor_get(v_cfg_1823_, 13);
v_lintDriver_1841_ = lean_ctor_get(v_cfg_1823_, 14);
v_lintDriverArgs_1842_ = lean_ctor_get(v_cfg_1823_, 15);
v_version_1843_ = lean_ctor_get(v_cfg_1823_, 16);
v_versionTags_1844_ = lean_ctor_get(v_cfg_1823_, 17);
v_description_1845_ = lean_ctor_get(v_cfg_1823_, 18);
v_keywords_1846_ = lean_ctor_get(v_cfg_1823_, 19);
v_homepage_1847_ = lean_ctor_get(v_cfg_1823_, 20);
v_license_1848_ = lean_ctor_get(v_cfg_1823_, 21);
v_licenseFiles_1849_ = lean_ctor_get(v_cfg_1823_, 22);
v_readmeFile_1850_ = lean_ctor_get(v_cfg_1823_, 23);
v_reservoir_1851_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1852_ = lean_ctor_get(v_cfg_1823_, 24);
v_restoreAllArtifacts_x3f_1853_ = lean_ctor_get(v_cfg_1823_, 25);
v_libPrefixOnWindows_1854_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26 + 4);
v_allowImportAll_1855_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26 + 5);
v_fixedToolchain_1856_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*26 + 6);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_cfg_1823_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v_cfg_1823_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1853_);
lean_inc(v_enableArtifactCache_x3f_1852_);
lean_inc(v_readmeFile_1850_);
lean_inc(v_licenseFiles_1849_);
lean_inc(v_license_1848_);
lean_inc(v_homepage_1847_);
lean_inc(v_keywords_1846_);
lean_inc(v_description_1845_);
lean_inc(v_versionTags_1844_);
lean_inc(v_version_1843_);
lean_inc(v_lintDriverArgs_1842_);
lean_inc(v_lintDriver_1841_);
lean_inc(v_testDriverArgs_1840_);
lean_inc(v_testDriver_1839_);
lean_inc(v_buildArchive_1837_);
lean_inc(v_releaseRepo_1836_);
lean_inc(v_irDir_1835_);
lean_inc(v_binDir_1834_);
lean_inc(v_nativeLibDir_1833_);
lean_inc(v_leanLibDir_1832_);
lean_inc(v_buildDir_1831_);
lean_inc(v_srcDir_1830_);
lean_inc(v_moreGlobalServerArgs_1829_);
lean_inc(v_extraDepTargets_1827_);
lean_inc(v_toLeanConfig_1825_);
lean_inc(v_toWorkspaceConfig_1824_);
lean_dec(v_cfg_1823_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1860_ = lean_apply_1(v_f_1822_, v_lintDriver_1841_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 14, v___x_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_toWorkspaceConfig_1824_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_toLeanConfig_1825_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_extraDepTargets_1827_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_moreGlobalServerArgs_1829_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_srcDir_1830_);
lean_ctor_set(v_reuseFailAlloc_1863_, 5, v_buildDir_1831_);
lean_ctor_set(v_reuseFailAlloc_1863_, 6, v_leanLibDir_1832_);
lean_ctor_set(v_reuseFailAlloc_1863_, 7, v_nativeLibDir_1833_);
lean_ctor_set(v_reuseFailAlloc_1863_, 8, v_binDir_1834_);
lean_ctor_set(v_reuseFailAlloc_1863_, 9, v_irDir_1835_);
lean_ctor_set(v_reuseFailAlloc_1863_, 10, v_releaseRepo_1836_);
lean_ctor_set(v_reuseFailAlloc_1863_, 11, v_buildArchive_1837_);
lean_ctor_set(v_reuseFailAlloc_1863_, 12, v_testDriver_1839_);
lean_ctor_set(v_reuseFailAlloc_1863_, 13, v_testDriverArgs_1840_);
lean_ctor_set(v_reuseFailAlloc_1863_, 14, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1863_, 15, v_lintDriverArgs_1842_);
lean_ctor_set(v_reuseFailAlloc_1863_, 16, v_version_1843_);
lean_ctor_set(v_reuseFailAlloc_1863_, 17, v_versionTags_1844_);
lean_ctor_set(v_reuseFailAlloc_1863_, 18, v_description_1845_);
lean_ctor_set(v_reuseFailAlloc_1863_, 19, v_keywords_1846_);
lean_ctor_set(v_reuseFailAlloc_1863_, 20, v_homepage_1847_);
lean_ctor_set(v_reuseFailAlloc_1863_, 21, v_license_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 22, v_licenseFiles_1849_);
lean_ctor_set(v_reuseFailAlloc_1863_, 23, v_readmeFile_1850_);
lean_ctor_set(v_reuseFailAlloc_1863_, 24, v_enableArtifactCache_x3f_1852_);
lean_ctor_set(v_reuseFailAlloc_1863_, 25, v_restoreAllArtifacts_x3f_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26, v_bootstrap_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26 + 1, v_precompileModules_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26 + 3, v_reservoir_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26 + 5, v_allowImportAll_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*26 + 6, v_fixedToolchain_1856_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_1873_, lean_object* v_n_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_1876_, lean_object* v_n_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1876_, v_n_1877_);
lean_dec(v_n_1877_);
lean_dec(v_p_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_1879_, lean_object* v_n_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1879_, v_n_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_1882_, lean_object* v_n_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_1882_, v_n_1883_);
lean_dec(v_n_1883_);
lean_dec(v_p_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* v_cfg_1885_){
_start:
{
lean_object* v_lintDriverArgs_1886_; 
v_lintDriverArgs_1886_ = lean_ctor_get(v_cfg_1885_, 15);
lean_inc_ref(v_lintDriverArgs_1886_);
return v_lintDriverArgs_1886_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(v_cfg_1887_);
lean_dec_ref(v_cfg_1887_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* v_val_1889_, lean_object* v_cfg_1890_){
_start:
{
lean_object* v_toWorkspaceConfig_1891_; lean_object* v_toLeanConfig_1892_; uint8_t v_bootstrap_1893_; lean_object* v_extraDepTargets_1894_; uint8_t v_precompileModules_1895_; lean_object* v_moreGlobalServerArgs_1896_; lean_object* v_srcDir_1897_; lean_object* v_buildDir_1898_; lean_object* v_leanLibDir_1899_; lean_object* v_nativeLibDir_1900_; lean_object* v_binDir_1901_; lean_object* v_irDir_1902_; lean_object* v_releaseRepo_1903_; lean_object* v_buildArchive_1904_; uint8_t v_preferReleaseBuild_1905_; lean_object* v_testDriver_1906_; lean_object* v_testDriverArgs_1907_; lean_object* v_lintDriver_1908_; lean_object* v_version_1909_; lean_object* v_versionTags_1910_; lean_object* v_description_1911_; lean_object* v_keywords_1912_; lean_object* v_homepage_1913_; lean_object* v_license_1914_; lean_object* v_licenseFiles_1915_; lean_object* v_readmeFile_1916_; uint8_t v_reservoir_1917_; lean_object* v_enableArtifactCache_x3f_1918_; lean_object* v_restoreAllArtifacts_x3f_1919_; uint8_t v_libPrefixOnWindows_1920_; uint8_t v_allowImportAll_1921_; uint8_t v_fixedToolchain_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_toWorkspaceConfig_1891_ = lean_ctor_get(v_cfg_1890_, 0);
v_toLeanConfig_1892_ = lean_ctor_get(v_cfg_1890_, 1);
v_bootstrap_1893_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26);
v_extraDepTargets_1894_ = lean_ctor_get(v_cfg_1890_, 2);
v_precompileModules_1895_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1896_ = lean_ctor_get(v_cfg_1890_, 3);
v_srcDir_1897_ = lean_ctor_get(v_cfg_1890_, 4);
v_buildDir_1898_ = lean_ctor_get(v_cfg_1890_, 5);
v_leanLibDir_1899_ = lean_ctor_get(v_cfg_1890_, 6);
v_nativeLibDir_1900_ = lean_ctor_get(v_cfg_1890_, 7);
v_binDir_1901_ = lean_ctor_get(v_cfg_1890_, 8);
v_irDir_1902_ = lean_ctor_get(v_cfg_1890_, 9);
v_releaseRepo_1903_ = lean_ctor_get(v_cfg_1890_, 10);
v_buildArchive_1904_ = lean_ctor_get(v_cfg_1890_, 11);
v_preferReleaseBuild_1905_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26 + 2);
v_testDriver_1906_ = lean_ctor_get(v_cfg_1890_, 12);
v_testDriverArgs_1907_ = lean_ctor_get(v_cfg_1890_, 13);
v_lintDriver_1908_ = lean_ctor_get(v_cfg_1890_, 14);
v_version_1909_ = lean_ctor_get(v_cfg_1890_, 16);
v_versionTags_1910_ = lean_ctor_get(v_cfg_1890_, 17);
v_description_1911_ = lean_ctor_get(v_cfg_1890_, 18);
v_keywords_1912_ = lean_ctor_get(v_cfg_1890_, 19);
v_homepage_1913_ = lean_ctor_get(v_cfg_1890_, 20);
v_license_1914_ = lean_ctor_get(v_cfg_1890_, 21);
v_licenseFiles_1915_ = lean_ctor_get(v_cfg_1890_, 22);
v_readmeFile_1916_ = lean_ctor_get(v_cfg_1890_, 23);
v_reservoir_1917_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1918_ = lean_ctor_get(v_cfg_1890_, 24);
v_restoreAllArtifacts_x3f_1919_ = lean_ctor_get(v_cfg_1890_, 25);
v_libPrefixOnWindows_1920_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26 + 4);
v_allowImportAll_1921_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26 + 5);
v_fixedToolchain_1922_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*26 + 6);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_cfg_1890_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v_cfg_1890_, 15);
lean_dec(v_unused_1930_);
v___x_1924_ = v_cfg_1890_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1919_);
lean_inc(v_enableArtifactCache_x3f_1918_);
lean_inc(v_readmeFile_1916_);
lean_inc(v_licenseFiles_1915_);
lean_inc(v_license_1914_);
lean_inc(v_homepage_1913_);
lean_inc(v_keywords_1912_);
lean_inc(v_description_1911_);
lean_inc(v_versionTags_1910_);
lean_inc(v_version_1909_);
lean_inc(v_lintDriver_1908_);
lean_inc(v_testDriverArgs_1907_);
lean_inc(v_testDriver_1906_);
lean_inc(v_buildArchive_1904_);
lean_inc(v_releaseRepo_1903_);
lean_inc(v_irDir_1902_);
lean_inc(v_binDir_1901_);
lean_inc(v_nativeLibDir_1900_);
lean_inc(v_leanLibDir_1899_);
lean_inc(v_buildDir_1898_);
lean_inc(v_srcDir_1897_);
lean_inc(v_moreGlobalServerArgs_1896_);
lean_inc(v_extraDepTargets_1894_);
lean_inc(v_toLeanConfig_1892_);
lean_inc(v_toWorkspaceConfig_1891_);
lean_dec(v_cfg_1890_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 15, v_val_1889_);
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_toWorkspaceConfig_1891_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_toLeanConfig_1892_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_extraDepTargets_1894_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_moreGlobalServerArgs_1896_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_srcDir_1897_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_buildDir_1898_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_leanLibDir_1899_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_nativeLibDir_1900_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v_binDir_1901_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_irDir_1902_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v_releaseRepo_1903_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_buildArchive_1904_);
lean_ctor_set(v_reuseFailAlloc_1928_, 12, v_testDriver_1906_);
lean_ctor_set(v_reuseFailAlloc_1928_, 13, v_testDriverArgs_1907_);
lean_ctor_set(v_reuseFailAlloc_1928_, 14, v_lintDriver_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 15, v_val_1889_);
lean_ctor_set(v_reuseFailAlloc_1928_, 16, v_version_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 17, v_versionTags_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 18, v_description_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 19, v_keywords_1912_);
lean_ctor_set(v_reuseFailAlloc_1928_, 20, v_homepage_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 21, v_license_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 22, v_licenseFiles_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 23, v_readmeFile_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 24, v_enableArtifactCache_x3f_1918_);
lean_ctor_set(v_reuseFailAlloc_1928_, 25, v_restoreAllArtifacts_x3f_1919_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26, v_bootstrap_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26 + 1, v_precompileModules_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26 + 3, v_reservoir_1917_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26 + 5, v_allowImportAll_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*26 + 6, v_fixedToolchain_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* v_f_1931_, lean_object* v_cfg_1932_){
_start:
{
lean_object* v_toWorkspaceConfig_1933_; lean_object* v_toLeanConfig_1934_; uint8_t v_bootstrap_1935_; lean_object* v_extraDepTargets_1936_; uint8_t v_precompileModules_1937_; lean_object* v_moreGlobalServerArgs_1938_; lean_object* v_srcDir_1939_; lean_object* v_buildDir_1940_; lean_object* v_leanLibDir_1941_; lean_object* v_nativeLibDir_1942_; lean_object* v_binDir_1943_; lean_object* v_irDir_1944_; lean_object* v_releaseRepo_1945_; lean_object* v_buildArchive_1946_; uint8_t v_preferReleaseBuild_1947_; lean_object* v_testDriver_1948_; lean_object* v_testDriverArgs_1949_; lean_object* v_lintDriver_1950_; lean_object* v_lintDriverArgs_1951_; lean_object* v_version_1952_; lean_object* v_versionTags_1953_; lean_object* v_description_1954_; lean_object* v_keywords_1955_; lean_object* v_homepage_1956_; lean_object* v_license_1957_; lean_object* v_licenseFiles_1958_; lean_object* v_readmeFile_1959_; uint8_t v_reservoir_1960_; lean_object* v_enableArtifactCache_x3f_1961_; lean_object* v_restoreAllArtifacts_x3f_1962_; uint8_t v_libPrefixOnWindows_1963_; uint8_t v_allowImportAll_1964_; uint8_t v_fixedToolchain_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_toWorkspaceConfig_1933_ = lean_ctor_get(v_cfg_1932_, 0);
v_toLeanConfig_1934_ = lean_ctor_get(v_cfg_1932_, 1);
v_bootstrap_1935_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26);
v_extraDepTargets_1936_ = lean_ctor_get(v_cfg_1932_, 2);
v_precompileModules_1937_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1938_ = lean_ctor_get(v_cfg_1932_, 3);
v_srcDir_1939_ = lean_ctor_get(v_cfg_1932_, 4);
v_buildDir_1940_ = lean_ctor_get(v_cfg_1932_, 5);
v_leanLibDir_1941_ = lean_ctor_get(v_cfg_1932_, 6);
v_nativeLibDir_1942_ = lean_ctor_get(v_cfg_1932_, 7);
v_binDir_1943_ = lean_ctor_get(v_cfg_1932_, 8);
v_irDir_1944_ = lean_ctor_get(v_cfg_1932_, 9);
v_releaseRepo_1945_ = lean_ctor_get(v_cfg_1932_, 10);
v_buildArchive_1946_ = lean_ctor_get(v_cfg_1932_, 11);
v_preferReleaseBuild_1947_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26 + 2);
v_testDriver_1948_ = lean_ctor_get(v_cfg_1932_, 12);
v_testDriverArgs_1949_ = lean_ctor_get(v_cfg_1932_, 13);
v_lintDriver_1950_ = lean_ctor_get(v_cfg_1932_, 14);
v_lintDriverArgs_1951_ = lean_ctor_get(v_cfg_1932_, 15);
v_version_1952_ = lean_ctor_get(v_cfg_1932_, 16);
v_versionTags_1953_ = lean_ctor_get(v_cfg_1932_, 17);
v_description_1954_ = lean_ctor_get(v_cfg_1932_, 18);
v_keywords_1955_ = lean_ctor_get(v_cfg_1932_, 19);
v_homepage_1956_ = lean_ctor_get(v_cfg_1932_, 20);
v_license_1957_ = lean_ctor_get(v_cfg_1932_, 21);
v_licenseFiles_1958_ = lean_ctor_get(v_cfg_1932_, 22);
v_readmeFile_1959_ = lean_ctor_get(v_cfg_1932_, 23);
v_reservoir_1960_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1961_ = lean_ctor_get(v_cfg_1932_, 24);
v_restoreAllArtifacts_x3f_1962_ = lean_ctor_get(v_cfg_1932_, 25);
v_libPrefixOnWindows_1963_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26 + 4);
v_allowImportAll_1964_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26 + 5);
v_fixedToolchain_1965_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*26 + 6);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_cfg_1932_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v_cfg_1932_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1962_);
lean_inc(v_enableArtifactCache_x3f_1961_);
lean_inc(v_readmeFile_1959_);
lean_inc(v_licenseFiles_1958_);
lean_inc(v_license_1957_);
lean_inc(v_homepage_1956_);
lean_inc(v_keywords_1955_);
lean_inc(v_description_1954_);
lean_inc(v_versionTags_1953_);
lean_inc(v_version_1952_);
lean_inc(v_lintDriverArgs_1951_);
lean_inc(v_lintDriver_1950_);
lean_inc(v_testDriverArgs_1949_);
lean_inc(v_testDriver_1948_);
lean_inc(v_buildArchive_1946_);
lean_inc(v_releaseRepo_1945_);
lean_inc(v_irDir_1944_);
lean_inc(v_binDir_1943_);
lean_inc(v_nativeLibDir_1942_);
lean_inc(v_leanLibDir_1941_);
lean_inc(v_buildDir_1940_);
lean_inc(v_srcDir_1939_);
lean_inc(v_moreGlobalServerArgs_1938_);
lean_inc(v_extraDepTargets_1936_);
lean_inc(v_toLeanConfig_1934_);
lean_inc(v_toWorkspaceConfig_1933_);
lean_dec(v_cfg_1932_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_apply_1(v_f_1931_, v_lintDriverArgs_1951_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 15, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_toWorkspaceConfig_1933_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_toLeanConfig_1934_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_extraDepTargets_1936_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_moreGlobalServerArgs_1938_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_srcDir_1939_);
lean_ctor_set(v_reuseFailAlloc_1972_, 5, v_buildDir_1940_);
lean_ctor_set(v_reuseFailAlloc_1972_, 6, v_leanLibDir_1941_);
lean_ctor_set(v_reuseFailAlloc_1972_, 7, v_nativeLibDir_1942_);
lean_ctor_set(v_reuseFailAlloc_1972_, 8, v_binDir_1943_);
lean_ctor_set(v_reuseFailAlloc_1972_, 9, v_irDir_1944_);
lean_ctor_set(v_reuseFailAlloc_1972_, 10, v_releaseRepo_1945_);
lean_ctor_set(v_reuseFailAlloc_1972_, 11, v_buildArchive_1946_);
lean_ctor_set(v_reuseFailAlloc_1972_, 12, v_testDriver_1948_);
lean_ctor_set(v_reuseFailAlloc_1972_, 13, v_testDriverArgs_1949_);
lean_ctor_set(v_reuseFailAlloc_1972_, 14, v_lintDriver_1950_);
lean_ctor_set(v_reuseFailAlloc_1972_, 15, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1972_, 16, v_version_1952_);
lean_ctor_set(v_reuseFailAlloc_1972_, 17, v_versionTags_1953_);
lean_ctor_set(v_reuseFailAlloc_1972_, 18, v_description_1954_);
lean_ctor_set(v_reuseFailAlloc_1972_, 19, v_keywords_1955_);
lean_ctor_set(v_reuseFailAlloc_1972_, 20, v_homepage_1956_);
lean_ctor_set(v_reuseFailAlloc_1972_, 21, v_license_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 22, v_licenseFiles_1958_);
lean_ctor_set(v_reuseFailAlloc_1972_, 23, v_readmeFile_1959_);
lean_ctor_set(v_reuseFailAlloc_1972_, 24, v_enableArtifactCache_x3f_1961_);
lean_ctor_set(v_reuseFailAlloc_1972_, 25, v_restoreAllArtifacts_x3f_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26, v_bootstrap_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26 + 1, v_precompileModules_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26 + 3, v_reservoir_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26 + 5, v_allowImportAll_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*26 + 6, v_fixedToolchain_1965_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_1982_, lean_object* v_n_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_1985_, lean_object* v_n_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_1985_, v_n_1986_);
lean_dec(v_n_1986_);
lean_dec(v_p_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_1988_, lean_object* v_n_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_1988_, v_n_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_1991_, lean_object* v_n_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_1991_, v_n_1992_);
lean_dec(v_n_1992_);
lean_dec(v_p_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* v_cfg_1994_){
_start:
{
lean_object* v_version_1995_; 
v_version_1995_ = lean_ctor_get(v_cfg_1994_, 16);
lean_inc_ref(v_version_1995_);
return v_version_1995_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* v_cfg_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lake_PackageConfig_version___proj___lam__0(v_cfg_1996_);
lean_dec_ref(v_cfg_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* v_val_1998_, lean_object* v_cfg_1999_){
_start:
{
lean_object* v_toWorkspaceConfig_2000_; lean_object* v_toLeanConfig_2001_; uint8_t v_bootstrap_2002_; lean_object* v_extraDepTargets_2003_; uint8_t v_precompileModules_2004_; lean_object* v_moreGlobalServerArgs_2005_; lean_object* v_srcDir_2006_; lean_object* v_buildDir_2007_; lean_object* v_leanLibDir_2008_; lean_object* v_nativeLibDir_2009_; lean_object* v_binDir_2010_; lean_object* v_irDir_2011_; lean_object* v_releaseRepo_2012_; lean_object* v_buildArchive_2013_; uint8_t v_preferReleaseBuild_2014_; lean_object* v_testDriver_2015_; lean_object* v_testDriverArgs_2016_; lean_object* v_lintDriver_2017_; lean_object* v_lintDriverArgs_2018_; lean_object* v_versionTags_2019_; lean_object* v_description_2020_; lean_object* v_keywords_2021_; lean_object* v_homepage_2022_; lean_object* v_license_2023_; lean_object* v_licenseFiles_2024_; lean_object* v_readmeFile_2025_; uint8_t v_reservoir_2026_; lean_object* v_enableArtifactCache_x3f_2027_; lean_object* v_restoreAllArtifacts_x3f_2028_; uint8_t v_libPrefixOnWindows_2029_; uint8_t v_allowImportAll_2030_; uint8_t v_fixedToolchain_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_toWorkspaceConfig_2000_ = lean_ctor_get(v_cfg_1999_, 0);
v_toLeanConfig_2001_ = lean_ctor_get(v_cfg_1999_, 1);
v_bootstrap_2002_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26);
v_extraDepTargets_2003_ = lean_ctor_get(v_cfg_1999_, 2);
v_precompileModules_2004_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2005_ = lean_ctor_get(v_cfg_1999_, 3);
v_srcDir_2006_ = lean_ctor_get(v_cfg_1999_, 4);
v_buildDir_2007_ = lean_ctor_get(v_cfg_1999_, 5);
v_leanLibDir_2008_ = lean_ctor_get(v_cfg_1999_, 6);
v_nativeLibDir_2009_ = lean_ctor_get(v_cfg_1999_, 7);
v_binDir_2010_ = lean_ctor_get(v_cfg_1999_, 8);
v_irDir_2011_ = lean_ctor_get(v_cfg_1999_, 9);
v_releaseRepo_2012_ = lean_ctor_get(v_cfg_1999_, 10);
v_buildArchive_2013_ = lean_ctor_get(v_cfg_1999_, 11);
v_preferReleaseBuild_2014_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26 + 2);
v_testDriver_2015_ = lean_ctor_get(v_cfg_1999_, 12);
v_testDriverArgs_2016_ = lean_ctor_get(v_cfg_1999_, 13);
v_lintDriver_2017_ = lean_ctor_get(v_cfg_1999_, 14);
v_lintDriverArgs_2018_ = lean_ctor_get(v_cfg_1999_, 15);
v_versionTags_2019_ = lean_ctor_get(v_cfg_1999_, 17);
v_description_2020_ = lean_ctor_get(v_cfg_1999_, 18);
v_keywords_2021_ = lean_ctor_get(v_cfg_1999_, 19);
v_homepage_2022_ = lean_ctor_get(v_cfg_1999_, 20);
v_license_2023_ = lean_ctor_get(v_cfg_1999_, 21);
v_licenseFiles_2024_ = lean_ctor_get(v_cfg_1999_, 22);
v_readmeFile_2025_ = lean_ctor_get(v_cfg_1999_, 23);
v_reservoir_2026_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2027_ = lean_ctor_get(v_cfg_1999_, 24);
v_restoreAllArtifacts_x3f_2028_ = lean_ctor_get(v_cfg_1999_, 25);
v_libPrefixOnWindows_2029_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26 + 4);
v_allowImportAll_2030_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26 + 5);
v_fixedToolchain_2031_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*26 + 6);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_cfg_1999_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v_cfg_1999_, 16);
lean_dec(v_unused_2039_);
v___x_2033_ = v_cfg_1999_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2028_);
lean_inc(v_enableArtifactCache_x3f_2027_);
lean_inc(v_readmeFile_2025_);
lean_inc(v_licenseFiles_2024_);
lean_inc(v_license_2023_);
lean_inc(v_homepage_2022_);
lean_inc(v_keywords_2021_);
lean_inc(v_description_2020_);
lean_inc(v_versionTags_2019_);
lean_inc(v_lintDriverArgs_2018_);
lean_inc(v_lintDriver_2017_);
lean_inc(v_testDriverArgs_2016_);
lean_inc(v_testDriver_2015_);
lean_inc(v_buildArchive_2013_);
lean_inc(v_releaseRepo_2012_);
lean_inc(v_irDir_2011_);
lean_inc(v_binDir_2010_);
lean_inc(v_nativeLibDir_2009_);
lean_inc(v_leanLibDir_2008_);
lean_inc(v_buildDir_2007_);
lean_inc(v_srcDir_2006_);
lean_inc(v_moreGlobalServerArgs_2005_);
lean_inc(v_extraDepTargets_2003_);
lean_inc(v_toLeanConfig_2001_);
lean_inc(v_toWorkspaceConfig_2000_);
lean_dec(v_cfg_1999_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 16, v_val_1998_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_toWorkspaceConfig_2000_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_toLeanConfig_2001_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_extraDepTargets_2003_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v_moreGlobalServerArgs_2005_);
lean_ctor_set(v_reuseFailAlloc_2037_, 4, v_srcDir_2006_);
lean_ctor_set(v_reuseFailAlloc_2037_, 5, v_buildDir_2007_);
lean_ctor_set(v_reuseFailAlloc_2037_, 6, v_leanLibDir_2008_);
lean_ctor_set(v_reuseFailAlloc_2037_, 7, v_nativeLibDir_2009_);
lean_ctor_set(v_reuseFailAlloc_2037_, 8, v_binDir_2010_);
lean_ctor_set(v_reuseFailAlloc_2037_, 9, v_irDir_2011_);
lean_ctor_set(v_reuseFailAlloc_2037_, 10, v_releaseRepo_2012_);
lean_ctor_set(v_reuseFailAlloc_2037_, 11, v_buildArchive_2013_);
lean_ctor_set(v_reuseFailAlloc_2037_, 12, v_testDriver_2015_);
lean_ctor_set(v_reuseFailAlloc_2037_, 13, v_testDriverArgs_2016_);
lean_ctor_set(v_reuseFailAlloc_2037_, 14, v_lintDriver_2017_);
lean_ctor_set(v_reuseFailAlloc_2037_, 15, v_lintDriverArgs_2018_);
lean_ctor_set(v_reuseFailAlloc_2037_, 16, v_val_1998_);
lean_ctor_set(v_reuseFailAlloc_2037_, 17, v_versionTags_2019_);
lean_ctor_set(v_reuseFailAlloc_2037_, 18, v_description_2020_);
lean_ctor_set(v_reuseFailAlloc_2037_, 19, v_keywords_2021_);
lean_ctor_set(v_reuseFailAlloc_2037_, 20, v_homepage_2022_);
lean_ctor_set(v_reuseFailAlloc_2037_, 21, v_license_2023_);
lean_ctor_set(v_reuseFailAlloc_2037_, 22, v_licenseFiles_2024_);
lean_ctor_set(v_reuseFailAlloc_2037_, 23, v_readmeFile_2025_);
lean_ctor_set(v_reuseFailAlloc_2037_, 24, v_enableArtifactCache_x3f_2027_);
lean_ctor_set(v_reuseFailAlloc_2037_, 25, v_restoreAllArtifacts_x3f_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26, v_bootstrap_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26 + 1, v_precompileModules_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26 + 3, v_reservoir_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26 + 5, v_allowImportAll_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*26 + 6, v_fixedToolchain_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* v_f_2040_, lean_object* v_cfg_2041_){
_start:
{
lean_object* v_toWorkspaceConfig_2042_; lean_object* v_toLeanConfig_2043_; uint8_t v_bootstrap_2044_; lean_object* v_extraDepTargets_2045_; uint8_t v_precompileModules_2046_; lean_object* v_moreGlobalServerArgs_2047_; lean_object* v_srcDir_2048_; lean_object* v_buildDir_2049_; lean_object* v_leanLibDir_2050_; lean_object* v_nativeLibDir_2051_; lean_object* v_binDir_2052_; lean_object* v_irDir_2053_; lean_object* v_releaseRepo_2054_; lean_object* v_buildArchive_2055_; uint8_t v_preferReleaseBuild_2056_; lean_object* v_testDriver_2057_; lean_object* v_testDriverArgs_2058_; lean_object* v_lintDriver_2059_; lean_object* v_lintDriverArgs_2060_; lean_object* v_version_2061_; lean_object* v_versionTags_2062_; lean_object* v_description_2063_; lean_object* v_keywords_2064_; lean_object* v_homepage_2065_; lean_object* v_license_2066_; lean_object* v_licenseFiles_2067_; lean_object* v_readmeFile_2068_; uint8_t v_reservoir_2069_; lean_object* v_enableArtifactCache_x3f_2070_; lean_object* v_restoreAllArtifacts_x3f_2071_; uint8_t v_libPrefixOnWindows_2072_; uint8_t v_allowImportAll_2073_; uint8_t v_fixedToolchain_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_toWorkspaceConfig_2042_ = lean_ctor_get(v_cfg_2041_, 0);
v_toLeanConfig_2043_ = lean_ctor_get(v_cfg_2041_, 1);
v_bootstrap_2044_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26);
v_extraDepTargets_2045_ = lean_ctor_get(v_cfg_2041_, 2);
v_precompileModules_2046_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2047_ = lean_ctor_get(v_cfg_2041_, 3);
v_srcDir_2048_ = lean_ctor_get(v_cfg_2041_, 4);
v_buildDir_2049_ = lean_ctor_get(v_cfg_2041_, 5);
v_leanLibDir_2050_ = lean_ctor_get(v_cfg_2041_, 6);
v_nativeLibDir_2051_ = lean_ctor_get(v_cfg_2041_, 7);
v_binDir_2052_ = lean_ctor_get(v_cfg_2041_, 8);
v_irDir_2053_ = lean_ctor_get(v_cfg_2041_, 9);
v_releaseRepo_2054_ = lean_ctor_get(v_cfg_2041_, 10);
v_buildArchive_2055_ = lean_ctor_get(v_cfg_2041_, 11);
v_preferReleaseBuild_2056_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26 + 2);
v_testDriver_2057_ = lean_ctor_get(v_cfg_2041_, 12);
v_testDriverArgs_2058_ = lean_ctor_get(v_cfg_2041_, 13);
v_lintDriver_2059_ = lean_ctor_get(v_cfg_2041_, 14);
v_lintDriverArgs_2060_ = lean_ctor_get(v_cfg_2041_, 15);
v_version_2061_ = lean_ctor_get(v_cfg_2041_, 16);
v_versionTags_2062_ = lean_ctor_get(v_cfg_2041_, 17);
v_description_2063_ = lean_ctor_get(v_cfg_2041_, 18);
v_keywords_2064_ = lean_ctor_get(v_cfg_2041_, 19);
v_homepage_2065_ = lean_ctor_get(v_cfg_2041_, 20);
v_license_2066_ = lean_ctor_get(v_cfg_2041_, 21);
v_licenseFiles_2067_ = lean_ctor_get(v_cfg_2041_, 22);
v_readmeFile_2068_ = lean_ctor_get(v_cfg_2041_, 23);
v_reservoir_2069_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2070_ = lean_ctor_get(v_cfg_2041_, 24);
v_restoreAllArtifacts_x3f_2071_ = lean_ctor_get(v_cfg_2041_, 25);
v_libPrefixOnWindows_2072_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26 + 4);
v_allowImportAll_2073_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26 + 5);
v_fixedToolchain_2074_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*26 + 6);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_cfg_2041_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v_cfg_2041_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2071_);
lean_inc(v_enableArtifactCache_x3f_2070_);
lean_inc(v_readmeFile_2068_);
lean_inc(v_licenseFiles_2067_);
lean_inc(v_license_2066_);
lean_inc(v_homepage_2065_);
lean_inc(v_keywords_2064_);
lean_inc(v_description_2063_);
lean_inc(v_versionTags_2062_);
lean_inc(v_version_2061_);
lean_inc(v_lintDriverArgs_2060_);
lean_inc(v_lintDriver_2059_);
lean_inc(v_testDriverArgs_2058_);
lean_inc(v_testDriver_2057_);
lean_inc(v_buildArchive_2055_);
lean_inc(v_releaseRepo_2054_);
lean_inc(v_irDir_2053_);
lean_inc(v_binDir_2052_);
lean_inc(v_nativeLibDir_2051_);
lean_inc(v_leanLibDir_2050_);
lean_inc(v_buildDir_2049_);
lean_inc(v_srcDir_2048_);
lean_inc(v_moreGlobalServerArgs_2047_);
lean_inc(v_extraDepTargets_2045_);
lean_inc(v_toLeanConfig_2043_);
lean_inc(v_toWorkspaceConfig_2042_);
lean_dec(v_cfg_2041_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_apply_1(v_f_2040_, v_version_2061_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 16, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_toWorkspaceConfig_2042_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_toLeanConfig_2043_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_extraDepTargets_2045_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_moreGlobalServerArgs_2047_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_srcDir_2048_);
lean_ctor_set(v_reuseFailAlloc_2081_, 5, v_buildDir_2049_);
lean_ctor_set(v_reuseFailAlloc_2081_, 6, v_leanLibDir_2050_);
lean_ctor_set(v_reuseFailAlloc_2081_, 7, v_nativeLibDir_2051_);
lean_ctor_set(v_reuseFailAlloc_2081_, 8, v_binDir_2052_);
lean_ctor_set(v_reuseFailAlloc_2081_, 9, v_irDir_2053_);
lean_ctor_set(v_reuseFailAlloc_2081_, 10, v_releaseRepo_2054_);
lean_ctor_set(v_reuseFailAlloc_2081_, 11, v_buildArchive_2055_);
lean_ctor_set(v_reuseFailAlloc_2081_, 12, v_testDriver_2057_);
lean_ctor_set(v_reuseFailAlloc_2081_, 13, v_testDriverArgs_2058_);
lean_ctor_set(v_reuseFailAlloc_2081_, 14, v_lintDriver_2059_);
lean_ctor_set(v_reuseFailAlloc_2081_, 15, v_lintDriverArgs_2060_);
lean_ctor_set(v_reuseFailAlloc_2081_, 16, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2081_, 17, v_versionTags_2062_);
lean_ctor_set(v_reuseFailAlloc_2081_, 18, v_description_2063_);
lean_ctor_set(v_reuseFailAlloc_2081_, 19, v_keywords_2064_);
lean_ctor_set(v_reuseFailAlloc_2081_, 20, v_homepage_2065_);
lean_ctor_set(v_reuseFailAlloc_2081_, 21, v_license_2066_);
lean_ctor_set(v_reuseFailAlloc_2081_, 22, v_licenseFiles_2067_);
lean_ctor_set(v_reuseFailAlloc_2081_, 23, v_readmeFile_2068_);
lean_ctor_set(v_reuseFailAlloc_2081_, 24, v_enableArtifactCache_x3f_2070_);
lean_ctor_set(v_reuseFailAlloc_2081_, 25, v_restoreAllArtifacts_x3f_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26, v_bootstrap_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26 + 1, v_precompileModules_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2056_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26 + 3, v_reservoir_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26 + 5, v_allowImportAll_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*26 + 6, v_fixedToolchain_2074_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* v_x_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___lam__3___closed__1));
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* v_x_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lake_PackageConfig_version___proj___lam__3(v_x_2090_);
lean_dec_ref(v_x_2090_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2101_, lean_object* v_n_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2104_, lean_object* v_n_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lake_PackageConfig_version___proj(v_p_2104_, v_n_2105_);
lean_dec(v_n_2105_);
lean_dec(v_p_2104_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2107_, lean_object* v_n_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lake_PackageConfig_version___proj(v_p_2107_, v_n_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2110_, lean_object* v_n_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lake_PackageConfig_version_instConfigField(v_p_2110_, v_n_2111_);
lean_dec(v_n_2111_);
lean_dec(v_p_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* v_cfg_2113_){
_start:
{
lean_object* v_versionTags_2114_; 
v_versionTags_2114_ = lean_ctor_get(v_cfg_2113_, 17);
lean_inc_ref(v_versionTags_2114_);
return v_versionTags_2114_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* v_cfg_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lake_PackageConfig_versionTags___proj___lam__0(v_cfg_2115_);
lean_dec_ref(v_cfg_2115_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* v_val_2117_, lean_object* v_cfg_2118_){
_start:
{
lean_object* v_toWorkspaceConfig_2119_; lean_object* v_toLeanConfig_2120_; uint8_t v_bootstrap_2121_; lean_object* v_extraDepTargets_2122_; uint8_t v_precompileModules_2123_; lean_object* v_moreGlobalServerArgs_2124_; lean_object* v_srcDir_2125_; lean_object* v_buildDir_2126_; lean_object* v_leanLibDir_2127_; lean_object* v_nativeLibDir_2128_; lean_object* v_binDir_2129_; lean_object* v_irDir_2130_; lean_object* v_releaseRepo_2131_; lean_object* v_buildArchive_2132_; uint8_t v_preferReleaseBuild_2133_; lean_object* v_testDriver_2134_; lean_object* v_testDriverArgs_2135_; lean_object* v_lintDriver_2136_; lean_object* v_lintDriverArgs_2137_; lean_object* v_version_2138_; lean_object* v_description_2139_; lean_object* v_keywords_2140_; lean_object* v_homepage_2141_; lean_object* v_license_2142_; lean_object* v_licenseFiles_2143_; lean_object* v_readmeFile_2144_; uint8_t v_reservoir_2145_; lean_object* v_enableArtifactCache_x3f_2146_; lean_object* v_restoreAllArtifacts_x3f_2147_; uint8_t v_libPrefixOnWindows_2148_; uint8_t v_allowImportAll_2149_; uint8_t v_fixedToolchain_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_toWorkspaceConfig_2119_ = lean_ctor_get(v_cfg_2118_, 0);
v_toLeanConfig_2120_ = lean_ctor_get(v_cfg_2118_, 1);
v_bootstrap_2121_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26);
v_extraDepTargets_2122_ = lean_ctor_get(v_cfg_2118_, 2);
v_precompileModules_2123_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2124_ = lean_ctor_get(v_cfg_2118_, 3);
v_srcDir_2125_ = lean_ctor_get(v_cfg_2118_, 4);
v_buildDir_2126_ = lean_ctor_get(v_cfg_2118_, 5);
v_leanLibDir_2127_ = lean_ctor_get(v_cfg_2118_, 6);
v_nativeLibDir_2128_ = lean_ctor_get(v_cfg_2118_, 7);
v_binDir_2129_ = lean_ctor_get(v_cfg_2118_, 8);
v_irDir_2130_ = lean_ctor_get(v_cfg_2118_, 9);
v_releaseRepo_2131_ = lean_ctor_get(v_cfg_2118_, 10);
v_buildArchive_2132_ = lean_ctor_get(v_cfg_2118_, 11);
v_preferReleaseBuild_2133_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26 + 2);
v_testDriver_2134_ = lean_ctor_get(v_cfg_2118_, 12);
v_testDriverArgs_2135_ = lean_ctor_get(v_cfg_2118_, 13);
v_lintDriver_2136_ = lean_ctor_get(v_cfg_2118_, 14);
v_lintDriverArgs_2137_ = lean_ctor_get(v_cfg_2118_, 15);
v_version_2138_ = lean_ctor_get(v_cfg_2118_, 16);
v_description_2139_ = lean_ctor_get(v_cfg_2118_, 18);
v_keywords_2140_ = lean_ctor_get(v_cfg_2118_, 19);
v_homepage_2141_ = lean_ctor_get(v_cfg_2118_, 20);
v_license_2142_ = lean_ctor_get(v_cfg_2118_, 21);
v_licenseFiles_2143_ = lean_ctor_get(v_cfg_2118_, 22);
v_readmeFile_2144_ = lean_ctor_get(v_cfg_2118_, 23);
v_reservoir_2145_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2146_ = lean_ctor_get(v_cfg_2118_, 24);
v_restoreAllArtifacts_x3f_2147_ = lean_ctor_get(v_cfg_2118_, 25);
v_libPrefixOnWindows_2148_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26 + 4);
v_allowImportAll_2149_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26 + 5);
v_fixedToolchain_2150_ = lean_ctor_get_uint8(v_cfg_2118_, sizeof(void*)*26 + 6);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_cfg_2118_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_cfg_2118_, 17);
lean_dec(v_unused_2158_);
v___x_2152_ = v_cfg_2118_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2147_);
lean_inc(v_enableArtifactCache_x3f_2146_);
lean_inc(v_readmeFile_2144_);
lean_inc(v_licenseFiles_2143_);
lean_inc(v_license_2142_);
lean_inc(v_homepage_2141_);
lean_inc(v_keywords_2140_);
lean_inc(v_description_2139_);
lean_inc(v_version_2138_);
lean_inc(v_lintDriverArgs_2137_);
lean_inc(v_lintDriver_2136_);
lean_inc(v_testDriverArgs_2135_);
lean_inc(v_testDriver_2134_);
lean_inc(v_buildArchive_2132_);
lean_inc(v_releaseRepo_2131_);
lean_inc(v_irDir_2130_);
lean_inc(v_binDir_2129_);
lean_inc(v_nativeLibDir_2128_);
lean_inc(v_leanLibDir_2127_);
lean_inc(v_buildDir_2126_);
lean_inc(v_srcDir_2125_);
lean_inc(v_moreGlobalServerArgs_2124_);
lean_inc(v_extraDepTargets_2122_);
lean_inc(v_toLeanConfig_2120_);
lean_inc(v_toWorkspaceConfig_2119_);
lean_dec(v_cfg_2118_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 17, v_val_2117_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_toWorkspaceConfig_2119_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_toLeanConfig_2120_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_extraDepTargets_2122_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_moreGlobalServerArgs_2124_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_srcDir_2125_);
lean_ctor_set(v_reuseFailAlloc_2156_, 5, v_buildDir_2126_);
lean_ctor_set(v_reuseFailAlloc_2156_, 6, v_leanLibDir_2127_);
lean_ctor_set(v_reuseFailAlloc_2156_, 7, v_nativeLibDir_2128_);
lean_ctor_set(v_reuseFailAlloc_2156_, 8, v_binDir_2129_);
lean_ctor_set(v_reuseFailAlloc_2156_, 9, v_irDir_2130_);
lean_ctor_set(v_reuseFailAlloc_2156_, 10, v_releaseRepo_2131_);
lean_ctor_set(v_reuseFailAlloc_2156_, 11, v_buildArchive_2132_);
lean_ctor_set(v_reuseFailAlloc_2156_, 12, v_testDriver_2134_);
lean_ctor_set(v_reuseFailAlloc_2156_, 13, v_testDriverArgs_2135_);
lean_ctor_set(v_reuseFailAlloc_2156_, 14, v_lintDriver_2136_);
lean_ctor_set(v_reuseFailAlloc_2156_, 15, v_lintDriverArgs_2137_);
lean_ctor_set(v_reuseFailAlloc_2156_, 16, v_version_2138_);
lean_ctor_set(v_reuseFailAlloc_2156_, 17, v_val_2117_);
lean_ctor_set(v_reuseFailAlloc_2156_, 18, v_description_2139_);
lean_ctor_set(v_reuseFailAlloc_2156_, 19, v_keywords_2140_);
lean_ctor_set(v_reuseFailAlloc_2156_, 20, v_homepage_2141_);
lean_ctor_set(v_reuseFailAlloc_2156_, 21, v_license_2142_);
lean_ctor_set(v_reuseFailAlloc_2156_, 22, v_licenseFiles_2143_);
lean_ctor_set(v_reuseFailAlloc_2156_, 23, v_readmeFile_2144_);
lean_ctor_set(v_reuseFailAlloc_2156_, 24, v_enableArtifactCache_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2156_, 25, v_restoreAllArtifacts_x3f_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26, v_bootstrap_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26 + 1, v_precompileModules_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26 + 3, v_reservoir_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26 + 5, v_allowImportAll_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*26 + 6, v_fixedToolchain_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* v_f_2159_, lean_object* v_cfg_2160_){
_start:
{
lean_object* v_toWorkspaceConfig_2161_; lean_object* v_toLeanConfig_2162_; uint8_t v_bootstrap_2163_; lean_object* v_extraDepTargets_2164_; uint8_t v_precompileModules_2165_; lean_object* v_moreGlobalServerArgs_2166_; lean_object* v_srcDir_2167_; lean_object* v_buildDir_2168_; lean_object* v_leanLibDir_2169_; lean_object* v_nativeLibDir_2170_; lean_object* v_binDir_2171_; lean_object* v_irDir_2172_; lean_object* v_releaseRepo_2173_; lean_object* v_buildArchive_2174_; uint8_t v_preferReleaseBuild_2175_; lean_object* v_testDriver_2176_; lean_object* v_testDriverArgs_2177_; lean_object* v_lintDriver_2178_; lean_object* v_lintDriverArgs_2179_; lean_object* v_version_2180_; lean_object* v_versionTags_2181_; lean_object* v_description_2182_; lean_object* v_keywords_2183_; lean_object* v_homepage_2184_; lean_object* v_license_2185_; lean_object* v_licenseFiles_2186_; lean_object* v_readmeFile_2187_; uint8_t v_reservoir_2188_; lean_object* v_enableArtifactCache_x3f_2189_; lean_object* v_restoreAllArtifacts_x3f_2190_; uint8_t v_libPrefixOnWindows_2191_; uint8_t v_allowImportAll_2192_; uint8_t v_fixedToolchain_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2201_; 
v_toWorkspaceConfig_2161_ = lean_ctor_get(v_cfg_2160_, 0);
v_toLeanConfig_2162_ = lean_ctor_get(v_cfg_2160_, 1);
v_bootstrap_2163_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26);
v_extraDepTargets_2164_ = lean_ctor_get(v_cfg_2160_, 2);
v_precompileModules_2165_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2166_ = lean_ctor_get(v_cfg_2160_, 3);
v_srcDir_2167_ = lean_ctor_get(v_cfg_2160_, 4);
v_buildDir_2168_ = lean_ctor_get(v_cfg_2160_, 5);
v_leanLibDir_2169_ = lean_ctor_get(v_cfg_2160_, 6);
v_nativeLibDir_2170_ = lean_ctor_get(v_cfg_2160_, 7);
v_binDir_2171_ = lean_ctor_get(v_cfg_2160_, 8);
v_irDir_2172_ = lean_ctor_get(v_cfg_2160_, 9);
v_releaseRepo_2173_ = lean_ctor_get(v_cfg_2160_, 10);
v_buildArchive_2174_ = lean_ctor_get(v_cfg_2160_, 11);
v_preferReleaseBuild_2175_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26 + 2);
v_testDriver_2176_ = lean_ctor_get(v_cfg_2160_, 12);
v_testDriverArgs_2177_ = lean_ctor_get(v_cfg_2160_, 13);
v_lintDriver_2178_ = lean_ctor_get(v_cfg_2160_, 14);
v_lintDriverArgs_2179_ = lean_ctor_get(v_cfg_2160_, 15);
v_version_2180_ = lean_ctor_get(v_cfg_2160_, 16);
v_versionTags_2181_ = lean_ctor_get(v_cfg_2160_, 17);
v_description_2182_ = lean_ctor_get(v_cfg_2160_, 18);
v_keywords_2183_ = lean_ctor_get(v_cfg_2160_, 19);
v_homepage_2184_ = lean_ctor_get(v_cfg_2160_, 20);
v_license_2185_ = lean_ctor_get(v_cfg_2160_, 21);
v_licenseFiles_2186_ = lean_ctor_get(v_cfg_2160_, 22);
v_readmeFile_2187_ = lean_ctor_get(v_cfg_2160_, 23);
v_reservoir_2188_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2189_ = lean_ctor_get(v_cfg_2160_, 24);
v_restoreAllArtifacts_x3f_2190_ = lean_ctor_get(v_cfg_2160_, 25);
v_libPrefixOnWindows_2191_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26 + 4);
v_allowImportAll_2192_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26 + 5);
v_fixedToolchain_2193_ = lean_ctor_get_uint8(v_cfg_2160_, sizeof(void*)*26 + 6);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_cfg_2160_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2195_ = v_cfg_2160_;
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2190_);
lean_inc(v_enableArtifactCache_x3f_2189_);
lean_inc(v_readmeFile_2187_);
lean_inc(v_licenseFiles_2186_);
lean_inc(v_license_2185_);
lean_inc(v_homepage_2184_);
lean_inc(v_keywords_2183_);
lean_inc(v_description_2182_);
lean_inc(v_versionTags_2181_);
lean_inc(v_version_2180_);
lean_inc(v_lintDriverArgs_2179_);
lean_inc(v_lintDriver_2178_);
lean_inc(v_testDriverArgs_2177_);
lean_inc(v_testDriver_2176_);
lean_inc(v_buildArchive_2174_);
lean_inc(v_releaseRepo_2173_);
lean_inc(v_irDir_2172_);
lean_inc(v_binDir_2171_);
lean_inc(v_nativeLibDir_2170_);
lean_inc(v_leanLibDir_2169_);
lean_inc(v_buildDir_2168_);
lean_inc(v_srcDir_2167_);
lean_inc(v_moreGlobalServerArgs_2166_);
lean_inc(v_extraDepTargets_2164_);
lean_inc(v_toLeanConfig_2162_);
lean_inc(v_toWorkspaceConfig_2161_);
lean_dec(v_cfg_2160_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_apply_1(v_f_2159_, v_versionTags_2181_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 17, v___x_2197_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_toWorkspaceConfig_2161_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_toLeanConfig_2162_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_extraDepTargets_2164_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_moreGlobalServerArgs_2166_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_srcDir_2167_);
lean_ctor_set(v_reuseFailAlloc_2200_, 5, v_buildDir_2168_);
lean_ctor_set(v_reuseFailAlloc_2200_, 6, v_leanLibDir_2169_);
lean_ctor_set(v_reuseFailAlloc_2200_, 7, v_nativeLibDir_2170_);
lean_ctor_set(v_reuseFailAlloc_2200_, 8, v_binDir_2171_);
lean_ctor_set(v_reuseFailAlloc_2200_, 9, v_irDir_2172_);
lean_ctor_set(v_reuseFailAlloc_2200_, 10, v_releaseRepo_2173_);
lean_ctor_set(v_reuseFailAlloc_2200_, 11, v_buildArchive_2174_);
lean_ctor_set(v_reuseFailAlloc_2200_, 12, v_testDriver_2176_);
lean_ctor_set(v_reuseFailAlloc_2200_, 13, v_testDriverArgs_2177_);
lean_ctor_set(v_reuseFailAlloc_2200_, 14, v_lintDriver_2178_);
lean_ctor_set(v_reuseFailAlloc_2200_, 15, v_lintDriverArgs_2179_);
lean_ctor_set(v_reuseFailAlloc_2200_, 16, v_version_2180_);
lean_ctor_set(v_reuseFailAlloc_2200_, 17, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 18, v_description_2182_);
lean_ctor_set(v_reuseFailAlloc_2200_, 19, v_keywords_2183_);
lean_ctor_set(v_reuseFailAlloc_2200_, 20, v_homepage_2184_);
lean_ctor_set(v_reuseFailAlloc_2200_, 21, v_license_2185_);
lean_ctor_set(v_reuseFailAlloc_2200_, 22, v_licenseFiles_2186_);
lean_ctor_set(v_reuseFailAlloc_2200_, 23, v_readmeFile_2187_);
lean_ctor_set(v_reuseFailAlloc_2200_, 24, v_enableArtifactCache_x3f_2189_);
lean_ctor_set(v_reuseFailAlloc_2200_, 25, v_restoreAllArtifacts_x3f_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26, v_bootstrap_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26 + 1, v_precompileModules_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26 + 3, v_reservoir_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26 + 5, v_allowImportAll_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*26 + 6, v_fixedToolchain_2193_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* v_x_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lake_defaultVersionTags;
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* v_x_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lake_PackageConfig_versionTags___proj___lam__3(v_x_2204_);
lean_dec_ref(v_x_2204_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2215_, lean_object* v_n_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2218_, lean_object* v_n_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lake_PackageConfig_versionTags___proj(v_p_2218_, v_n_2219_);
lean_dec(v_n_2219_);
lean_dec(v_p_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2221_, lean_object* v_n_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lake_PackageConfig_versionTags___proj(v_p_2221_, v_n_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2224_, lean_object* v_n_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2224_, v_n_2225_);
lean_dec(v_n_2225_);
lean_dec(v_p_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* v_cfg_2227_){
_start:
{
lean_object* v_description_2228_; 
v_description_2228_ = lean_ctor_get(v_cfg_2227_, 18);
lean_inc_ref(v_description_2228_);
return v_description_2228_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* v_cfg_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lake_PackageConfig_description___proj___lam__0(v_cfg_2229_);
lean_dec_ref(v_cfg_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* v_val_2231_, lean_object* v_cfg_2232_){
_start:
{
lean_object* v_toWorkspaceConfig_2233_; lean_object* v_toLeanConfig_2234_; uint8_t v_bootstrap_2235_; lean_object* v_extraDepTargets_2236_; uint8_t v_precompileModules_2237_; lean_object* v_moreGlobalServerArgs_2238_; lean_object* v_srcDir_2239_; lean_object* v_buildDir_2240_; lean_object* v_leanLibDir_2241_; lean_object* v_nativeLibDir_2242_; lean_object* v_binDir_2243_; lean_object* v_irDir_2244_; lean_object* v_releaseRepo_2245_; lean_object* v_buildArchive_2246_; uint8_t v_preferReleaseBuild_2247_; lean_object* v_testDriver_2248_; lean_object* v_testDriverArgs_2249_; lean_object* v_lintDriver_2250_; lean_object* v_lintDriverArgs_2251_; lean_object* v_version_2252_; lean_object* v_versionTags_2253_; lean_object* v_keywords_2254_; lean_object* v_homepage_2255_; lean_object* v_license_2256_; lean_object* v_licenseFiles_2257_; lean_object* v_readmeFile_2258_; uint8_t v_reservoir_2259_; lean_object* v_enableArtifactCache_x3f_2260_; lean_object* v_restoreAllArtifacts_x3f_2261_; uint8_t v_libPrefixOnWindows_2262_; uint8_t v_allowImportAll_2263_; uint8_t v_fixedToolchain_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
v_toWorkspaceConfig_2233_ = lean_ctor_get(v_cfg_2232_, 0);
v_toLeanConfig_2234_ = lean_ctor_get(v_cfg_2232_, 1);
v_bootstrap_2235_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26);
v_extraDepTargets_2236_ = lean_ctor_get(v_cfg_2232_, 2);
v_precompileModules_2237_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2238_ = lean_ctor_get(v_cfg_2232_, 3);
v_srcDir_2239_ = lean_ctor_get(v_cfg_2232_, 4);
v_buildDir_2240_ = lean_ctor_get(v_cfg_2232_, 5);
v_leanLibDir_2241_ = lean_ctor_get(v_cfg_2232_, 6);
v_nativeLibDir_2242_ = lean_ctor_get(v_cfg_2232_, 7);
v_binDir_2243_ = lean_ctor_get(v_cfg_2232_, 8);
v_irDir_2244_ = lean_ctor_get(v_cfg_2232_, 9);
v_releaseRepo_2245_ = lean_ctor_get(v_cfg_2232_, 10);
v_buildArchive_2246_ = lean_ctor_get(v_cfg_2232_, 11);
v_preferReleaseBuild_2247_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26 + 2);
v_testDriver_2248_ = lean_ctor_get(v_cfg_2232_, 12);
v_testDriverArgs_2249_ = lean_ctor_get(v_cfg_2232_, 13);
v_lintDriver_2250_ = lean_ctor_get(v_cfg_2232_, 14);
v_lintDriverArgs_2251_ = lean_ctor_get(v_cfg_2232_, 15);
v_version_2252_ = lean_ctor_get(v_cfg_2232_, 16);
v_versionTags_2253_ = lean_ctor_get(v_cfg_2232_, 17);
v_keywords_2254_ = lean_ctor_get(v_cfg_2232_, 19);
v_homepage_2255_ = lean_ctor_get(v_cfg_2232_, 20);
v_license_2256_ = lean_ctor_get(v_cfg_2232_, 21);
v_licenseFiles_2257_ = lean_ctor_get(v_cfg_2232_, 22);
v_readmeFile_2258_ = lean_ctor_get(v_cfg_2232_, 23);
v_reservoir_2259_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2260_ = lean_ctor_get(v_cfg_2232_, 24);
v_restoreAllArtifacts_x3f_2261_ = lean_ctor_get(v_cfg_2232_, 25);
v_libPrefixOnWindows_2262_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26 + 4);
v_allowImportAll_2263_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26 + 5);
v_fixedToolchain_2264_ = lean_ctor_get_uint8(v_cfg_2232_, sizeof(void*)*26 + 6);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_cfg_2232_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v_cfg_2232_, 18);
lean_dec(v_unused_2272_);
v___x_2266_ = v_cfg_2232_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2261_);
lean_inc(v_enableArtifactCache_x3f_2260_);
lean_inc(v_readmeFile_2258_);
lean_inc(v_licenseFiles_2257_);
lean_inc(v_license_2256_);
lean_inc(v_homepage_2255_);
lean_inc(v_keywords_2254_);
lean_inc(v_versionTags_2253_);
lean_inc(v_version_2252_);
lean_inc(v_lintDriverArgs_2251_);
lean_inc(v_lintDriver_2250_);
lean_inc(v_testDriverArgs_2249_);
lean_inc(v_testDriver_2248_);
lean_inc(v_buildArchive_2246_);
lean_inc(v_releaseRepo_2245_);
lean_inc(v_irDir_2244_);
lean_inc(v_binDir_2243_);
lean_inc(v_nativeLibDir_2242_);
lean_inc(v_leanLibDir_2241_);
lean_inc(v_buildDir_2240_);
lean_inc(v_srcDir_2239_);
lean_inc(v_moreGlobalServerArgs_2238_);
lean_inc(v_extraDepTargets_2236_);
lean_inc(v_toLeanConfig_2234_);
lean_inc(v_toWorkspaceConfig_2233_);
lean_dec(v_cfg_2232_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 18, v_val_2231_);
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_toWorkspaceConfig_2233_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_toLeanConfig_2234_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_extraDepTargets_2236_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_moreGlobalServerArgs_2238_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v_srcDir_2239_);
lean_ctor_set(v_reuseFailAlloc_2270_, 5, v_buildDir_2240_);
lean_ctor_set(v_reuseFailAlloc_2270_, 6, v_leanLibDir_2241_);
lean_ctor_set(v_reuseFailAlloc_2270_, 7, v_nativeLibDir_2242_);
lean_ctor_set(v_reuseFailAlloc_2270_, 8, v_binDir_2243_);
lean_ctor_set(v_reuseFailAlloc_2270_, 9, v_irDir_2244_);
lean_ctor_set(v_reuseFailAlloc_2270_, 10, v_releaseRepo_2245_);
lean_ctor_set(v_reuseFailAlloc_2270_, 11, v_buildArchive_2246_);
lean_ctor_set(v_reuseFailAlloc_2270_, 12, v_testDriver_2248_);
lean_ctor_set(v_reuseFailAlloc_2270_, 13, v_testDriverArgs_2249_);
lean_ctor_set(v_reuseFailAlloc_2270_, 14, v_lintDriver_2250_);
lean_ctor_set(v_reuseFailAlloc_2270_, 15, v_lintDriverArgs_2251_);
lean_ctor_set(v_reuseFailAlloc_2270_, 16, v_version_2252_);
lean_ctor_set(v_reuseFailAlloc_2270_, 17, v_versionTags_2253_);
lean_ctor_set(v_reuseFailAlloc_2270_, 18, v_val_2231_);
lean_ctor_set(v_reuseFailAlloc_2270_, 19, v_keywords_2254_);
lean_ctor_set(v_reuseFailAlloc_2270_, 20, v_homepage_2255_);
lean_ctor_set(v_reuseFailAlloc_2270_, 21, v_license_2256_);
lean_ctor_set(v_reuseFailAlloc_2270_, 22, v_licenseFiles_2257_);
lean_ctor_set(v_reuseFailAlloc_2270_, 23, v_readmeFile_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 24, v_enableArtifactCache_x3f_2260_);
lean_ctor_set(v_reuseFailAlloc_2270_, 25, v_restoreAllArtifacts_x3f_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26, v_bootstrap_2235_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26 + 1, v_precompileModules_2237_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26 + 3, v_reservoir_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26 + 5, v_allowImportAll_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*26 + 6, v_fixedToolchain_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* v_f_2273_, lean_object* v_cfg_2274_){
_start:
{
lean_object* v_toWorkspaceConfig_2275_; lean_object* v_toLeanConfig_2276_; uint8_t v_bootstrap_2277_; lean_object* v_extraDepTargets_2278_; uint8_t v_precompileModules_2279_; lean_object* v_moreGlobalServerArgs_2280_; lean_object* v_srcDir_2281_; lean_object* v_buildDir_2282_; lean_object* v_leanLibDir_2283_; lean_object* v_nativeLibDir_2284_; lean_object* v_binDir_2285_; lean_object* v_irDir_2286_; lean_object* v_releaseRepo_2287_; lean_object* v_buildArchive_2288_; uint8_t v_preferReleaseBuild_2289_; lean_object* v_testDriver_2290_; lean_object* v_testDriverArgs_2291_; lean_object* v_lintDriver_2292_; lean_object* v_lintDriverArgs_2293_; lean_object* v_version_2294_; lean_object* v_versionTags_2295_; lean_object* v_description_2296_; lean_object* v_keywords_2297_; lean_object* v_homepage_2298_; lean_object* v_license_2299_; lean_object* v_licenseFiles_2300_; lean_object* v_readmeFile_2301_; uint8_t v_reservoir_2302_; lean_object* v_enableArtifactCache_x3f_2303_; lean_object* v_restoreAllArtifacts_x3f_2304_; uint8_t v_libPrefixOnWindows_2305_; uint8_t v_allowImportAll_2306_; uint8_t v_fixedToolchain_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_toWorkspaceConfig_2275_ = lean_ctor_get(v_cfg_2274_, 0);
v_toLeanConfig_2276_ = lean_ctor_get(v_cfg_2274_, 1);
v_bootstrap_2277_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26);
v_extraDepTargets_2278_ = lean_ctor_get(v_cfg_2274_, 2);
v_precompileModules_2279_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2280_ = lean_ctor_get(v_cfg_2274_, 3);
v_srcDir_2281_ = lean_ctor_get(v_cfg_2274_, 4);
v_buildDir_2282_ = lean_ctor_get(v_cfg_2274_, 5);
v_leanLibDir_2283_ = lean_ctor_get(v_cfg_2274_, 6);
v_nativeLibDir_2284_ = lean_ctor_get(v_cfg_2274_, 7);
v_binDir_2285_ = lean_ctor_get(v_cfg_2274_, 8);
v_irDir_2286_ = lean_ctor_get(v_cfg_2274_, 9);
v_releaseRepo_2287_ = lean_ctor_get(v_cfg_2274_, 10);
v_buildArchive_2288_ = lean_ctor_get(v_cfg_2274_, 11);
v_preferReleaseBuild_2289_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26 + 2);
v_testDriver_2290_ = lean_ctor_get(v_cfg_2274_, 12);
v_testDriverArgs_2291_ = lean_ctor_get(v_cfg_2274_, 13);
v_lintDriver_2292_ = lean_ctor_get(v_cfg_2274_, 14);
v_lintDriverArgs_2293_ = lean_ctor_get(v_cfg_2274_, 15);
v_version_2294_ = lean_ctor_get(v_cfg_2274_, 16);
v_versionTags_2295_ = lean_ctor_get(v_cfg_2274_, 17);
v_description_2296_ = lean_ctor_get(v_cfg_2274_, 18);
v_keywords_2297_ = lean_ctor_get(v_cfg_2274_, 19);
v_homepage_2298_ = lean_ctor_get(v_cfg_2274_, 20);
v_license_2299_ = lean_ctor_get(v_cfg_2274_, 21);
v_licenseFiles_2300_ = lean_ctor_get(v_cfg_2274_, 22);
v_readmeFile_2301_ = lean_ctor_get(v_cfg_2274_, 23);
v_reservoir_2302_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2303_ = lean_ctor_get(v_cfg_2274_, 24);
v_restoreAllArtifacts_x3f_2304_ = lean_ctor_get(v_cfg_2274_, 25);
v_libPrefixOnWindows_2305_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26 + 4);
v_allowImportAll_2306_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26 + 5);
v_fixedToolchain_2307_ = lean_ctor_get_uint8(v_cfg_2274_, sizeof(void*)*26 + 6);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_cfg_2274_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v_cfg_2274_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2304_);
lean_inc(v_enableArtifactCache_x3f_2303_);
lean_inc(v_readmeFile_2301_);
lean_inc(v_licenseFiles_2300_);
lean_inc(v_license_2299_);
lean_inc(v_homepage_2298_);
lean_inc(v_keywords_2297_);
lean_inc(v_description_2296_);
lean_inc(v_versionTags_2295_);
lean_inc(v_version_2294_);
lean_inc(v_lintDriverArgs_2293_);
lean_inc(v_lintDriver_2292_);
lean_inc(v_testDriverArgs_2291_);
lean_inc(v_testDriver_2290_);
lean_inc(v_buildArchive_2288_);
lean_inc(v_releaseRepo_2287_);
lean_inc(v_irDir_2286_);
lean_inc(v_binDir_2285_);
lean_inc(v_nativeLibDir_2284_);
lean_inc(v_leanLibDir_2283_);
lean_inc(v_buildDir_2282_);
lean_inc(v_srcDir_2281_);
lean_inc(v_moreGlobalServerArgs_2280_);
lean_inc(v_extraDepTargets_2278_);
lean_inc(v_toLeanConfig_2276_);
lean_inc(v_toWorkspaceConfig_2275_);
lean_dec(v_cfg_2274_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_apply_1(v_f_2273_, v_description_2296_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 18, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_toWorkspaceConfig_2275_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_toLeanConfig_2276_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_extraDepTargets_2278_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_moreGlobalServerArgs_2280_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_srcDir_2281_);
lean_ctor_set(v_reuseFailAlloc_2314_, 5, v_buildDir_2282_);
lean_ctor_set(v_reuseFailAlloc_2314_, 6, v_leanLibDir_2283_);
lean_ctor_set(v_reuseFailAlloc_2314_, 7, v_nativeLibDir_2284_);
lean_ctor_set(v_reuseFailAlloc_2314_, 8, v_binDir_2285_);
lean_ctor_set(v_reuseFailAlloc_2314_, 9, v_irDir_2286_);
lean_ctor_set(v_reuseFailAlloc_2314_, 10, v_releaseRepo_2287_);
lean_ctor_set(v_reuseFailAlloc_2314_, 11, v_buildArchive_2288_);
lean_ctor_set(v_reuseFailAlloc_2314_, 12, v_testDriver_2290_);
lean_ctor_set(v_reuseFailAlloc_2314_, 13, v_testDriverArgs_2291_);
lean_ctor_set(v_reuseFailAlloc_2314_, 14, v_lintDriver_2292_);
lean_ctor_set(v_reuseFailAlloc_2314_, 15, v_lintDriverArgs_2293_);
lean_ctor_set(v_reuseFailAlloc_2314_, 16, v_version_2294_);
lean_ctor_set(v_reuseFailAlloc_2314_, 17, v_versionTags_2295_);
lean_ctor_set(v_reuseFailAlloc_2314_, 18, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2314_, 19, v_keywords_2297_);
lean_ctor_set(v_reuseFailAlloc_2314_, 20, v_homepage_2298_);
lean_ctor_set(v_reuseFailAlloc_2314_, 21, v_license_2299_);
lean_ctor_set(v_reuseFailAlloc_2314_, 22, v_licenseFiles_2300_);
lean_ctor_set(v_reuseFailAlloc_2314_, 23, v_readmeFile_2301_);
lean_ctor_set(v_reuseFailAlloc_2314_, 24, v_enableArtifactCache_x3f_2303_);
lean_ctor_set(v_reuseFailAlloc_2314_, 25, v_restoreAllArtifacts_x3f_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26, v_bootstrap_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26 + 1, v_precompileModules_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26 + 3, v_reservoir_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26 + 5, v_allowImportAll_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*26 + 6, v_fixedToolchain_2307_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2324_, lean_object* v_n_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2327_, lean_object* v_n_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lake_PackageConfig_description___proj(v_p_2327_, v_n_2328_);
lean_dec(v_n_2328_);
lean_dec(v_p_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2330_, lean_object* v_n_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lake_PackageConfig_description___proj(v_p_2330_, v_n_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2333_, lean_object* v_n_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lake_PackageConfig_description_instConfigField(v_p_2333_, v_n_2334_);
lean_dec(v_n_2334_);
lean_dec(v_p_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* v_cfg_2336_){
_start:
{
lean_object* v_keywords_2337_; 
v_keywords_2337_ = lean_ctor_get(v_cfg_2336_, 19);
lean_inc_ref(v_keywords_2337_);
return v_keywords_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* v_cfg_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lake_PackageConfig_keywords___proj___lam__0(v_cfg_2338_);
lean_dec_ref(v_cfg_2338_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* v_val_2340_, lean_object* v_cfg_2341_){
_start:
{
lean_object* v_toWorkspaceConfig_2342_; lean_object* v_toLeanConfig_2343_; uint8_t v_bootstrap_2344_; lean_object* v_extraDepTargets_2345_; uint8_t v_precompileModules_2346_; lean_object* v_moreGlobalServerArgs_2347_; lean_object* v_srcDir_2348_; lean_object* v_buildDir_2349_; lean_object* v_leanLibDir_2350_; lean_object* v_nativeLibDir_2351_; lean_object* v_binDir_2352_; lean_object* v_irDir_2353_; lean_object* v_releaseRepo_2354_; lean_object* v_buildArchive_2355_; uint8_t v_preferReleaseBuild_2356_; lean_object* v_testDriver_2357_; lean_object* v_testDriverArgs_2358_; lean_object* v_lintDriver_2359_; lean_object* v_lintDriverArgs_2360_; lean_object* v_version_2361_; lean_object* v_versionTags_2362_; lean_object* v_description_2363_; lean_object* v_homepage_2364_; lean_object* v_license_2365_; lean_object* v_licenseFiles_2366_; lean_object* v_readmeFile_2367_; uint8_t v_reservoir_2368_; lean_object* v_enableArtifactCache_x3f_2369_; lean_object* v_restoreAllArtifacts_x3f_2370_; uint8_t v_libPrefixOnWindows_2371_; uint8_t v_allowImportAll_2372_; uint8_t v_fixedToolchain_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_toWorkspaceConfig_2342_ = lean_ctor_get(v_cfg_2341_, 0);
v_toLeanConfig_2343_ = lean_ctor_get(v_cfg_2341_, 1);
v_bootstrap_2344_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26);
v_extraDepTargets_2345_ = lean_ctor_get(v_cfg_2341_, 2);
v_precompileModules_2346_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2347_ = lean_ctor_get(v_cfg_2341_, 3);
v_srcDir_2348_ = lean_ctor_get(v_cfg_2341_, 4);
v_buildDir_2349_ = lean_ctor_get(v_cfg_2341_, 5);
v_leanLibDir_2350_ = lean_ctor_get(v_cfg_2341_, 6);
v_nativeLibDir_2351_ = lean_ctor_get(v_cfg_2341_, 7);
v_binDir_2352_ = lean_ctor_get(v_cfg_2341_, 8);
v_irDir_2353_ = lean_ctor_get(v_cfg_2341_, 9);
v_releaseRepo_2354_ = lean_ctor_get(v_cfg_2341_, 10);
v_buildArchive_2355_ = lean_ctor_get(v_cfg_2341_, 11);
v_preferReleaseBuild_2356_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26 + 2);
v_testDriver_2357_ = lean_ctor_get(v_cfg_2341_, 12);
v_testDriverArgs_2358_ = lean_ctor_get(v_cfg_2341_, 13);
v_lintDriver_2359_ = lean_ctor_get(v_cfg_2341_, 14);
v_lintDriverArgs_2360_ = lean_ctor_get(v_cfg_2341_, 15);
v_version_2361_ = lean_ctor_get(v_cfg_2341_, 16);
v_versionTags_2362_ = lean_ctor_get(v_cfg_2341_, 17);
v_description_2363_ = lean_ctor_get(v_cfg_2341_, 18);
v_homepage_2364_ = lean_ctor_get(v_cfg_2341_, 20);
v_license_2365_ = lean_ctor_get(v_cfg_2341_, 21);
v_licenseFiles_2366_ = lean_ctor_get(v_cfg_2341_, 22);
v_readmeFile_2367_ = lean_ctor_get(v_cfg_2341_, 23);
v_reservoir_2368_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2369_ = lean_ctor_get(v_cfg_2341_, 24);
v_restoreAllArtifacts_x3f_2370_ = lean_ctor_get(v_cfg_2341_, 25);
v_libPrefixOnWindows_2371_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26 + 4);
v_allowImportAll_2372_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26 + 5);
v_fixedToolchain_2373_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*26 + 6);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_cfg_2341_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v_cfg_2341_, 19);
lean_dec(v_unused_2381_);
v___x_2375_ = v_cfg_2341_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2370_);
lean_inc(v_enableArtifactCache_x3f_2369_);
lean_inc(v_readmeFile_2367_);
lean_inc(v_licenseFiles_2366_);
lean_inc(v_license_2365_);
lean_inc(v_homepage_2364_);
lean_inc(v_description_2363_);
lean_inc(v_versionTags_2362_);
lean_inc(v_version_2361_);
lean_inc(v_lintDriverArgs_2360_);
lean_inc(v_lintDriver_2359_);
lean_inc(v_testDriverArgs_2358_);
lean_inc(v_testDriver_2357_);
lean_inc(v_buildArchive_2355_);
lean_inc(v_releaseRepo_2354_);
lean_inc(v_irDir_2353_);
lean_inc(v_binDir_2352_);
lean_inc(v_nativeLibDir_2351_);
lean_inc(v_leanLibDir_2350_);
lean_inc(v_buildDir_2349_);
lean_inc(v_srcDir_2348_);
lean_inc(v_moreGlobalServerArgs_2347_);
lean_inc(v_extraDepTargets_2345_);
lean_inc(v_toLeanConfig_2343_);
lean_inc(v_toWorkspaceConfig_2342_);
lean_dec(v_cfg_2341_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 19, v_val_2340_);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_toWorkspaceConfig_2342_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_toLeanConfig_2343_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_extraDepTargets_2345_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_moreGlobalServerArgs_2347_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v_srcDir_2348_);
lean_ctor_set(v_reuseFailAlloc_2379_, 5, v_buildDir_2349_);
lean_ctor_set(v_reuseFailAlloc_2379_, 6, v_leanLibDir_2350_);
lean_ctor_set(v_reuseFailAlloc_2379_, 7, v_nativeLibDir_2351_);
lean_ctor_set(v_reuseFailAlloc_2379_, 8, v_binDir_2352_);
lean_ctor_set(v_reuseFailAlloc_2379_, 9, v_irDir_2353_);
lean_ctor_set(v_reuseFailAlloc_2379_, 10, v_releaseRepo_2354_);
lean_ctor_set(v_reuseFailAlloc_2379_, 11, v_buildArchive_2355_);
lean_ctor_set(v_reuseFailAlloc_2379_, 12, v_testDriver_2357_);
lean_ctor_set(v_reuseFailAlloc_2379_, 13, v_testDriverArgs_2358_);
lean_ctor_set(v_reuseFailAlloc_2379_, 14, v_lintDriver_2359_);
lean_ctor_set(v_reuseFailAlloc_2379_, 15, v_lintDriverArgs_2360_);
lean_ctor_set(v_reuseFailAlloc_2379_, 16, v_version_2361_);
lean_ctor_set(v_reuseFailAlloc_2379_, 17, v_versionTags_2362_);
lean_ctor_set(v_reuseFailAlloc_2379_, 18, v_description_2363_);
lean_ctor_set(v_reuseFailAlloc_2379_, 19, v_val_2340_);
lean_ctor_set(v_reuseFailAlloc_2379_, 20, v_homepage_2364_);
lean_ctor_set(v_reuseFailAlloc_2379_, 21, v_license_2365_);
lean_ctor_set(v_reuseFailAlloc_2379_, 22, v_licenseFiles_2366_);
lean_ctor_set(v_reuseFailAlloc_2379_, 23, v_readmeFile_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 24, v_enableArtifactCache_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2379_, 25, v_restoreAllArtifacts_x3f_2370_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26, v_bootstrap_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26 + 1, v_precompileModules_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26 + 3, v_reservoir_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26 + 5, v_allowImportAll_2372_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*26 + 6, v_fixedToolchain_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* v_f_2382_, lean_object* v_cfg_2383_){
_start:
{
lean_object* v_toWorkspaceConfig_2384_; lean_object* v_toLeanConfig_2385_; uint8_t v_bootstrap_2386_; lean_object* v_extraDepTargets_2387_; uint8_t v_precompileModules_2388_; lean_object* v_moreGlobalServerArgs_2389_; lean_object* v_srcDir_2390_; lean_object* v_buildDir_2391_; lean_object* v_leanLibDir_2392_; lean_object* v_nativeLibDir_2393_; lean_object* v_binDir_2394_; lean_object* v_irDir_2395_; lean_object* v_releaseRepo_2396_; lean_object* v_buildArchive_2397_; uint8_t v_preferReleaseBuild_2398_; lean_object* v_testDriver_2399_; lean_object* v_testDriverArgs_2400_; lean_object* v_lintDriver_2401_; lean_object* v_lintDriverArgs_2402_; lean_object* v_version_2403_; lean_object* v_versionTags_2404_; lean_object* v_description_2405_; lean_object* v_keywords_2406_; lean_object* v_homepage_2407_; lean_object* v_license_2408_; lean_object* v_licenseFiles_2409_; lean_object* v_readmeFile_2410_; uint8_t v_reservoir_2411_; lean_object* v_enableArtifactCache_x3f_2412_; lean_object* v_restoreAllArtifacts_x3f_2413_; uint8_t v_libPrefixOnWindows_2414_; uint8_t v_allowImportAll_2415_; uint8_t v_fixedToolchain_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_toWorkspaceConfig_2384_ = lean_ctor_get(v_cfg_2383_, 0);
v_toLeanConfig_2385_ = lean_ctor_get(v_cfg_2383_, 1);
v_bootstrap_2386_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26);
v_extraDepTargets_2387_ = lean_ctor_get(v_cfg_2383_, 2);
v_precompileModules_2388_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2389_ = lean_ctor_get(v_cfg_2383_, 3);
v_srcDir_2390_ = lean_ctor_get(v_cfg_2383_, 4);
v_buildDir_2391_ = lean_ctor_get(v_cfg_2383_, 5);
v_leanLibDir_2392_ = lean_ctor_get(v_cfg_2383_, 6);
v_nativeLibDir_2393_ = lean_ctor_get(v_cfg_2383_, 7);
v_binDir_2394_ = lean_ctor_get(v_cfg_2383_, 8);
v_irDir_2395_ = lean_ctor_get(v_cfg_2383_, 9);
v_releaseRepo_2396_ = lean_ctor_get(v_cfg_2383_, 10);
v_buildArchive_2397_ = lean_ctor_get(v_cfg_2383_, 11);
v_preferReleaseBuild_2398_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26 + 2);
v_testDriver_2399_ = lean_ctor_get(v_cfg_2383_, 12);
v_testDriverArgs_2400_ = lean_ctor_get(v_cfg_2383_, 13);
v_lintDriver_2401_ = lean_ctor_get(v_cfg_2383_, 14);
v_lintDriverArgs_2402_ = lean_ctor_get(v_cfg_2383_, 15);
v_version_2403_ = lean_ctor_get(v_cfg_2383_, 16);
v_versionTags_2404_ = lean_ctor_get(v_cfg_2383_, 17);
v_description_2405_ = lean_ctor_get(v_cfg_2383_, 18);
v_keywords_2406_ = lean_ctor_get(v_cfg_2383_, 19);
v_homepage_2407_ = lean_ctor_get(v_cfg_2383_, 20);
v_license_2408_ = lean_ctor_get(v_cfg_2383_, 21);
v_licenseFiles_2409_ = lean_ctor_get(v_cfg_2383_, 22);
v_readmeFile_2410_ = lean_ctor_get(v_cfg_2383_, 23);
v_reservoir_2411_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2412_ = lean_ctor_get(v_cfg_2383_, 24);
v_restoreAllArtifacts_x3f_2413_ = lean_ctor_get(v_cfg_2383_, 25);
v_libPrefixOnWindows_2414_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26 + 4);
v_allowImportAll_2415_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26 + 5);
v_fixedToolchain_2416_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*26 + 6);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_cfg_2383_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v_cfg_2383_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2413_);
lean_inc(v_enableArtifactCache_x3f_2412_);
lean_inc(v_readmeFile_2410_);
lean_inc(v_licenseFiles_2409_);
lean_inc(v_license_2408_);
lean_inc(v_homepage_2407_);
lean_inc(v_keywords_2406_);
lean_inc(v_description_2405_);
lean_inc(v_versionTags_2404_);
lean_inc(v_version_2403_);
lean_inc(v_lintDriverArgs_2402_);
lean_inc(v_lintDriver_2401_);
lean_inc(v_testDriverArgs_2400_);
lean_inc(v_testDriver_2399_);
lean_inc(v_buildArchive_2397_);
lean_inc(v_releaseRepo_2396_);
lean_inc(v_irDir_2395_);
lean_inc(v_binDir_2394_);
lean_inc(v_nativeLibDir_2393_);
lean_inc(v_leanLibDir_2392_);
lean_inc(v_buildDir_2391_);
lean_inc(v_srcDir_2390_);
lean_inc(v_moreGlobalServerArgs_2389_);
lean_inc(v_extraDepTargets_2387_);
lean_inc(v_toLeanConfig_2385_);
lean_inc(v_toWorkspaceConfig_2384_);
lean_dec(v_cfg_2383_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_apply_1(v_f_2382_, v_keywords_2406_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 19, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_toWorkspaceConfig_2384_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_toLeanConfig_2385_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_extraDepTargets_2387_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_moreGlobalServerArgs_2389_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_srcDir_2390_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_buildDir_2391_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_leanLibDir_2392_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_nativeLibDir_2393_);
lean_ctor_set(v_reuseFailAlloc_2423_, 8, v_binDir_2394_);
lean_ctor_set(v_reuseFailAlloc_2423_, 9, v_irDir_2395_);
lean_ctor_set(v_reuseFailAlloc_2423_, 10, v_releaseRepo_2396_);
lean_ctor_set(v_reuseFailAlloc_2423_, 11, v_buildArchive_2397_);
lean_ctor_set(v_reuseFailAlloc_2423_, 12, v_testDriver_2399_);
lean_ctor_set(v_reuseFailAlloc_2423_, 13, v_testDriverArgs_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 14, v_lintDriver_2401_);
lean_ctor_set(v_reuseFailAlloc_2423_, 15, v_lintDriverArgs_2402_);
lean_ctor_set(v_reuseFailAlloc_2423_, 16, v_version_2403_);
lean_ctor_set(v_reuseFailAlloc_2423_, 17, v_versionTags_2404_);
lean_ctor_set(v_reuseFailAlloc_2423_, 18, v_description_2405_);
lean_ctor_set(v_reuseFailAlloc_2423_, 19, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2423_, 20, v_homepage_2407_);
lean_ctor_set(v_reuseFailAlloc_2423_, 21, v_license_2408_);
lean_ctor_set(v_reuseFailAlloc_2423_, 22, v_licenseFiles_2409_);
lean_ctor_set(v_reuseFailAlloc_2423_, 23, v_readmeFile_2410_);
lean_ctor_set(v_reuseFailAlloc_2423_, 24, v_enableArtifactCache_x3f_2412_);
lean_ctor_set(v_reuseFailAlloc_2423_, 25, v_restoreAllArtifacts_x3f_2413_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26, v_bootstrap_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26 + 1, v_precompileModules_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26 + 3, v_reservoir_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2414_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26 + 5, v_allowImportAll_2415_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*26 + 6, v_fixedToolchain_2416_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2433_, lean_object* v_n_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2436_, lean_object* v_n_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lake_PackageConfig_keywords___proj(v_p_2436_, v_n_2437_);
lean_dec(v_n_2437_);
lean_dec(v_p_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2439_, lean_object* v_n_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lake_PackageConfig_keywords___proj(v_p_2439_, v_n_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2442_, lean_object* v_n_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2442_, v_n_2443_);
lean_dec(v_n_2443_);
lean_dec(v_p_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* v_cfg_2445_){
_start:
{
lean_object* v_homepage_2446_; 
v_homepage_2446_ = lean_ctor_get(v_cfg_2445_, 20);
lean_inc_ref(v_homepage_2446_);
return v_homepage_2446_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* v_cfg_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lake_PackageConfig_homepage___proj___lam__0(v_cfg_2447_);
lean_dec_ref(v_cfg_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* v_val_2449_, lean_object* v_cfg_2450_){
_start:
{
lean_object* v_toWorkspaceConfig_2451_; lean_object* v_toLeanConfig_2452_; uint8_t v_bootstrap_2453_; lean_object* v_extraDepTargets_2454_; uint8_t v_precompileModules_2455_; lean_object* v_moreGlobalServerArgs_2456_; lean_object* v_srcDir_2457_; lean_object* v_buildDir_2458_; lean_object* v_leanLibDir_2459_; lean_object* v_nativeLibDir_2460_; lean_object* v_binDir_2461_; lean_object* v_irDir_2462_; lean_object* v_releaseRepo_2463_; lean_object* v_buildArchive_2464_; uint8_t v_preferReleaseBuild_2465_; lean_object* v_testDriver_2466_; lean_object* v_testDriverArgs_2467_; lean_object* v_lintDriver_2468_; lean_object* v_lintDriverArgs_2469_; lean_object* v_version_2470_; lean_object* v_versionTags_2471_; lean_object* v_description_2472_; lean_object* v_keywords_2473_; lean_object* v_license_2474_; lean_object* v_licenseFiles_2475_; lean_object* v_readmeFile_2476_; uint8_t v_reservoir_2477_; lean_object* v_enableArtifactCache_x3f_2478_; lean_object* v_restoreAllArtifacts_x3f_2479_; uint8_t v_libPrefixOnWindows_2480_; uint8_t v_allowImportAll_2481_; uint8_t v_fixedToolchain_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_toWorkspaceConfig_2451_ = lean_ctor_get(v_cfg_2450_, 0);
v_toLeanConfig_2452_ = lean_ctor_get(v_cfg_2450_, 1);
v_bootstrap_2453_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26);
v_extraDepTargets_2454_ = lean_ctor_get(v_cfg_2450_, 2);
v_precompileModules_2455_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2456_ = lean_ctor_get(v_cfg_2450_, 3);
v_srcDir_2457_ = lean_ctor_get(v_cfg_2450_, 4);
v_buildDir_2458_ = lean_ctor_get(v_cfg_2450_, 5);
v_leanLibDir_2459_ = lean_ctor_get(v_cfg_2450_, 6);
v_nativeLibDir_2460_ = lean_ctor_get(v_cfg_2450_, 7);
v_binDir_2461_ = lean_ctor_get(v_cfg_2450_, 8);
v_irDir_2462_ = lean_ctor_get(v_cfg_2450_, 9);
v_releaseRepo_2463_ = lean_ctor_get(v_cfg_2450_, 10);
v_buildArchive_2464_ = lean_ctor_get(v_cfg_2450_, 11);
v_preferReleaseBuild_2465_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26 + 2);
v_testDriver_2466_ = lean_ctor_get(v_cfg_2450_, 12);
v_testDriverArgs_2467_ = lean_ctor_get(v_cfg_2450_, 13);
v_lintDriver_2468_ = lean_ctor_get(v_cfg_2450_, 14);
v_lintDriverArgs_2469_ = lean_ctor_get(v_cfg_2450_, 15);
v_version_2470_ = lean_ctor_get(v_cfg_2450_, 16);
v_versionTags_2471_ = lean_ctor_get(v_cfg_2450_, 17);
v_description_2472_ = lean_ctor_get(v_cfg_2450_, 18);
v_keywords_2473_ = lean_ctor_get(v_cfg_2450_, 19);
v_license_2474_ = lean_ctor_get(v_cfg_2450_, 21);
v_licenseFiles_2475_ = lean_ctor_get(v_cfg_2450_, 22);
v_readmeFile_2476_ = lean_ctor_get(v_cfg_2450_, 23);
v_reservoir_2477_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2478_ = lean_ctor_get(v_cfg_2450_, 24);
v_restoreAllArtifacts_x3f_2479_ = lean_ctor_get(v_cfg_2450_, 25);
v_libPrefixOnWindows_2480_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26 + 4);
v_allowImportAll_2481_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26 + 5);
v_fixedToolchain_2482_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*26 + 6);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_cfg_2450_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v_cfg_2450_, 20);
lean_dec(v_unused_2490_);
v___x_2484_ = v_cfg_2450_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2479_);
lean_inc(v_enableArtifactCache_x3f_2478_);
lean_inc(v_readmeFile_2476_);
lean_inc(v_licenseFiles_2475_);
lean_inc(v_license_2474_);
lean_inc(v_keywords_2473_);
lean_inc(v_description_2472_);
lean_inc(v_versionTags_2471_);
lean_inc(v_version_2470_);
lean_inc(v_lintDriverArgs_2469_);
lean_inc(v_lintDriver_2468_);
lean_inc(v_testDriverArgs_2467_);
lean_inc(v_testDriver_2466_);
lean_inc(v_buildArchive_2464_);
lean_inc(v_releaseRepo_2463_);
lean_inc(v_irDir_2462_);
lean_inc(v_binDir_2461_);
lean_inc(v_nativeLibDir_2460_);
lean_inc(v_leanLibDir_2459_);
lean_inc(v_buildDir_2458_);
lean_inc(v_srcDir_2457_);
lean_inc(v_moreGlobalServerArgs_2456_);
lean_inc(v_extraDepTargets_2454_);
lean_inc(v_toLeanConfig_2452_);
lean_inc(v_toWorkspaceConfig_2451_);
lean_dec(v_cfg_2450_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 20, v_val_2449_);
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_toWorkspaceConfig_2451_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_toLeanConfig_2452_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_extraDepTargets_2454_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_moreGlobalServerArgs_2456_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_srcDir_2457_);
lean_ctor_set(v_reuseFailAlloc_2488_, 5, v_buildDir_2458_);
lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_leanLibDir_2459_);
lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_nativeLibDir_2460_);
lean_ctor_set(v_reuseFailAlloc_2488_, 8, v_binDir_2461_);
lean_ctor_set(v_reuseFailAlloc_2488_, 9, v_irDir_2462_);
lean_ctor_set(v_reuseFailAlloc_2488_, 10, v_releaseRepo_2463_);
lean_ctor_set(v_reuseFailAlloc_2488_, 11, v_buildArchive_2464_);
lean_ctor_set(v_reuseFailAlloc_2488_, 12, v_testDriver_2466_);
lean_ctor_set(v_reuseFailAlloc_2488_, 13, v_testDriverArgs_2467_);
lean_ctor_set(v_reuseFailAlloc_2488_, 14, v_lintDriver_2468_);
lean_ctor_set(v_reuseFailAlloc_2488_, 15, v_lintDriverArgs_2469_);
lean_ctor_set(v_reuseFailAlloc_2488_, 16, v_version_2470_);
lean_ctor_set(v_reuseFailAlloc_2488_, 17, v_versionTags_2471_);
lean_ctor_set(v_reuseFailAlloc_2488_, 18, v_description_2472_);
lean_ctor_set(v_reuseFailAlloc_2488_, 19, v_keywords_2473_);
lean_ctor_set(v_reuseFailAlloc_2488_, 20, v_val_2449_);
lean_ctor_set(v_reuseFailAlloc_2488_, 21, v_license_2474_);
lean_ctor_set(v_reuseFailAlloc_2488_, 22, v_licenseFiles_2475_);
lean_ctor_set(v_reuseFailAlloc_2488_, 23, v_readmeFile_2476_);
lean_ctor_set(v_reuseFailAlloc_2488_, 24, v_enableArtifactCache_x3f_2478_);
lean_ctor_set(v_reuseFailAlloc_2488_, 25, v_restoreAllArtifacts_x3f_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26, v_bootstrap_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26 + 1, v_precompileModules_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26 + 3, v_reservoir_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26 + 5, v_allowImportAll_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*26 + 6, v_fixedToolchain_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* v_f_2491_, lean_object* v_cfg_2492_){
_start:
{
lean_object* v_toWorkspaceConfig_2493_; lean_object* v_toLeanConfig_2494_; uint8_t v_bootstrap_2495_; lean_object* v_extraDepTargets_2496_; uint8_t v_precompileModules_2497_; lean_object* v_moreGlobalServerArgs_2498_; lean_object* v_srcDir_2499_; lean_object* v_buildDir_2500_; lean_object* v_leanLibDir_2501_; lean_object* v_nativeLibDir_2502_; lean_object* v_binDir_2503_; lean_object* v_irDir_2504_; lean_object* v_releaseRepo_2505_; lean_object* v_buildArchive_2506_; uint8_t v_preferReleaseBuild_2507_; lean_object* v_testDriver_2508_; lean_object* v_testDriverArgs_2509_; lean_object* v_lintDriver_2510_; lean_object* v_lintDriverArgs_2511_; lean_object* v_version_2512_; lean_object* v_versionTags_2513_; lean_object* v_description_2514_; lean_object* v_keywords_2515_; lean_object* v_homepage_2516_; lean_object* v_license_2517_; lean_object* v_licenseFiles_2518_; lean_object* v_readmeFile_2519_; uint8_t v_reservoir_2520_; lean_object* v_enableArtifactCache_x3f_2521_; lean_object* v_restoreAllArtifacts_x3f_2522_; uint8_t v_libPrefixOnWindows_2523_; uint8_t v_allowImportAll_2524_; uint8_t v_fixedToolchain_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2533_; 
v_toWorkspaceConfig_2493_ = lean_ctor_get(v_cfg_2492_, 0);
v_toLeanConfig_2494_ = lean_ctor_get(v_cfg_2492_, 1);
v_bootstrap_2495_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26);
v_extraDepTargets_2496_ = lean_ctor_get(v_cfg_2492_, 2);
v_precompileModules_2497_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2498_ = lean_ctor_get(v_cfg_2492_, 3);
v_srcDir_2499_ = lean_ctor_get(v_cfg_2492_, 4);
v_buildDir_2500_ = lean_ctor_get(v_cfg_2492_, 5);
v_leanLibDir_2501_ = lean_ctor_get(v_cfg_2492_, 6);
v_nativeLibDir_2502_ = lean_ctor_get(v_cfg_2492_, 7);
v_binDir_2503_ = lean_ctor_get(v_cfg_2492_, 8);
v_irDir_2504_ = lean_ctor_get(v_cfg_2492_, 9);
v_releaseRepo_2505_ = lean_ctor_get(v_cfg_2492_, 10);
v_buildArchive_2506_ = lean_ctor_get(v_cfg_2492_, 11);
v_preferReleaseBuild_2507_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26 + 2);
v_testDriver_2508_ = lean_ctor_get(v_cfg_2492_, 12);
v_testDriverArgs_2509_ = lean_ctor_get(v_cfg_2492_, 13);
v_lintDriver_2510_ = lean_ctor_get(v_cfg_2492_, 14);
v_lintDriverArgs_2511_ = lean_ctor_get(v_cfg_2492_, 15);
v_version_2512_ = lean_ctor_get(v_cfg_2492_, 16);
v_versionTags_2513_ = lean_ctor_get(v_cfg_2492_, 17);
v_description_2514_ = lean_ctor_get(v_cfg_2492_, 18);
v_keywords_2515_ = lean_ctor_get(v_cfg_2492_, 19);
v_homepage_2516_ = lean_ctor_get(v_cfg_2492_, 20);
v_license_2517_ = lean_ctor_get(v_cfg_2492_, 21);
v_licenseFiles_2518_ = lean_ctor_get(v_cfg_2492_, 22);
v_readmeFile_2519_ = lean_ctor_get(v_cfg_2492_, 23);
v_reservoir_2520_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2521_ = lean_ctor_get(v_cfg_2492_, 24);
v_restoreAllArtifacts_x3f_2522_ = lean_ctor_get(v_cfg_2492_, 25);
v_libPrefixOnWindows_2523_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26 + 4);
v_allowImportAll_2524_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26 + 5);
v_fixedToolchain_2525_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*26 + 6);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_cfg_2492_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2527_ = v_cfg_2492_;
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2522_);
lean_inc(v_enableArtifactCache_x3f_2521_);
lean_inc(v_readmeFile_2519_);
lean_inc(v_licenseFiles_2518_);
lean_inc(v_license_2517_);
lean_inc(v_homepage_2516_);
lean_inc(v_keywords_2515_);
lean_inc(v_description_2514_);
lean_inc(v_versionTags_2513_);
lean_inc(v_version_2512_);
lean_inc(v_lintDriverArgs_2511_);
lean_inc(v_lintDriver_2510_);
lean_inc(v_testDriverArgs_2509_);
lean_inc(v_testDriver_2508_);
lean_inc(v_buildArchive_2506_);
lean_inc(v_releaseRepo_2505_);
lean_inc(v_irDir_2504_);
lean_inc(v_binDir_2503_);
lean_inc(v_nativeLibDir_2502_);
lean_inc(v_leanLibDir_2501_);
lean_inc(v_buildDir_2500_);
lean_inc(v_srcDir_2499_);
lean_inc(v_moreGlobalServerArgs_2498_);
lean_inc(v_extraDepTargets_2496_);
lean_inc(v_toLeanConfig_2494_);
lean_inc(v_toWorkspaceConfig_2493_);
lean_dec(v_cfg_2492_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_apply_1(v_f_2491_, v_homepage_2516_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 20, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_toWorkspaceConfig_2493_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_toLeanConfig_2494_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_extraDepTargets_2496_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_moreGlobalServerArgs_2498_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_srcDir_2499_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v_buildDir_2500_);
lean_ctor_set(v_reuseFailAlloc_2532_, 6, v_leanLibDir_2501_);
lean_ctor_set(v_reuseFailAlloc_2532_, 7, v_nativeLibDir_2502_);
lean_ctor_set(v_reuseFailAlloc_2532_, 8, v_binDir_2503_);
lean_ctor_set(v_reuseFailAlloc_2532_, 9, v_irDir_2504_);
lean_ctor_set(v_reuseFailAlloc_2532_, 10, v_releaseRepo_2505_);
lean_ctor_set(v_reuseFailAlloc_2532_, 11, v_buildArchive_2506_);
lean_ctor_set(v_reuseFailAlloc_2532_, 12, v_testDriver_2508_);
lean_ctor_set(v_reuseFailAlloc_2532_, 13, v_testDriverArgs_2509_);
lean_ctor_set(v_reuseFailAlloc_2532_, 14, v_lintDriver_2510_);
lean_ctor_set(v_reuseFailAlloc_2532_, 15, v_lintDriverArgs_2511_);
lean_ctor_set(v_reuseFailAlloc_2532_, 16, v_version_2512_);
lean_ctor_set(v_reuseFailAlloc_2532_, 17, v_versionTags_2513_);
lean_ctor_set(v_reuseFailAlloc_2532_, 18, v_description_2514_);
lean_ctor_set(v_reuseFailAlloc_2532_, 19, v_keywords_2515_);
lean_ctor_set(v_reuseFailAlloc_2532_, 20, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2532_, 21, v_license_2517_);
lean_ctor_set(v_reuseFailAlloc_2532_, 22, v_licenseFiles_2518_);
lean_ctor_set(v_reuseFailAlloc_2532_, 23, v_readmeFile_2519_);
lean_ctor_set(v_reuseFailAlloc_2532_, 24, v_enableArtifactCache_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2532_, 25, v_restoreAllArtifacts_x3f_2522_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26, v_bootstrap_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26 + 1, v_precompileModules_2497_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26 + 3, v_reservoir_2520_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2523_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26 + 5, v_allowImportAll_2524_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*26 + 6, v_fixedToolchain_2525_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2542_, lean_object* v_n_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2545_, lean_object* v_n_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lake_PackageConfig_homepage___proj(v_p_2545_, v_n_2546_);
lean_dec(v_n_2546_);
lean_dec(v_p_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2548_, lean_object* v_n_2549_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lake_PackageConfig_homepage___proj(v_p_2548_, v_n_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2551_, lean_object* v_n_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2551_, v_n_2552_);
lean_dec(v_n_2552_);
lean_dec(v_p_2551_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* v_cfg_2554_){
_start:
{
lean_object* v_license_2555_; 
v_license_2555_ = lean_ctor_get(v_cfg_2554_, 21);
lean_inc_ref(v_license_2555_);
return v_license_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* v_cfg_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lake_PackageConfig_license___proj___lam__0(v_cfg_2556_);
lean_dec_ref(v_cfg_2556_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* v_val_2558_, lean_object* v_cfg_2559_){
_start:
{
lean_object* v_toWorkspaceConfig_2560_; lean_object* v_toLeanConfig_2561_; uint8_t v_bootstrap_2562_; lean_object* v_extraDepTargets_2563_; uint8_t v_precompileModules_2564_; lean_object* v_moreGlobalServerArgs_2565_; lean_object* v_srcDir_2566_; lean_object* v_buildDir_2567_; lean_object* v_leanLibDir_2568_; lean_object* v_nativeLibDir_2569_; lean_object* v_binDir_2570_; lean_object* v_irDir_2571_; lean_object* v_releaseRepo_2572_; lean_object* v_buildArchive_2573_; uint8_t v_preferReleaseBuild_2574_; lean_object* v_testDriver_2575_; lean_object* v_testDriverArgs_2576_; lean_object* v_lintDriver_2577_; lean_object* v_lintDriverArgs_2578_; lean_object* v_version_2579_; lean_object* v_versionTags_2580_; lean_object* v_description_2581_; lean_object* v_keywords_2582_; lean_object* v_homepage_2583_; lean_object* v_licenseFiles_2584_; lean_object* v_readmeFile_2585_; uint8_t v_reservoir_2586_; lean_object* v_enableArtifactCache_x3f_2587_; lean_object* v_restoreAllArtifacts_x3f_2588_; uint8_t v_libPrefixOnWindows_2589_; uint8_t v_allowImportAll_2590_; uint8_t v_fixedToolchain_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_toWorkspaceConfig_2560_ = lean_ctor_get(v_cfg_2559_, 0);
v_toLeanConfig_2561_ = lean_ctor_get(v_cfg_2559_, 1);
v_bootstrap_2562_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26);
v_extraDepTargets_2563_ = lean_ctor_get(v_cfg_2559_, 2);
v_precompileModules_2564_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2565_ = lean_ctor_get(v_cfg_2559_, 3);
v_srcDir_2566_ = lean_ctor_get(v_cfg_2559_, 4);
v_buildDir_2567_ = lean_ctor_get(v_cfg_2559_, 5);
v_leanLibDir_2568_ = lean_ctor_get(v_cfg_2559_, 6);
v_nativeLibDir_2569_ = lean_ctor_get(v_cfg_2559_, 7);
v_binDir_2570_ = lean_ctor_get(v_cfg_2559_, 8);
v_irDir_2571_ = lean_ctor_get(v_cfg_2559_, 9);
v_releaseRepo_2572_ = lean_ctor_get(v_cfg_2559_, 10);
v_buildArchive_2573_ = lean_ctor_get(v_cfg_2559_, 11);
v_preferReleaseBuild_2574_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26 + 2);
v_testDriver_2575_ = lean_ctor_get(v_cfg_2559_, 12);
v_testDriverArgs_2576_ = lean_ctor_get(v_cfg_2559_, 13);
v_lintDriver_2577_ = lean_ctor_get(v_cfg_2559_, 14);
v_lintDriverArgs_2578_ = lean_ctor_get(v_cfg_2559_, 15);
v_version_2579_ = lean_ctor_get(v_cfg_2559_, 16);
v_versionTags_2580_ = lean_ctor_get(v_cfg_2559_, 17);
v_description_2581_ = lean_ctor_get(v_cfg_2559_, 18);
v_keywords_2582_ = lean_ctor_get(v_cfg_2559_, 19);
v_homepage_2583_ = lean_ctor_get(v_cfg_2559_, 20);
v_licenseFiles_2584_ = lean_ctor_get(v_cfg_2559_, 22);
v_readmeFile_2585_ = lean_ctor_get(v_cfg_2559_, 23);
v_reservoir_2586_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2587_ = lean_ctor_get(v_cfg_2559_, 24);
v_restoreAllArtifacts_x3f_2588_ = lean_ctor_get(v_cfg_2559_, 25);
v_libPrefixOnWindows_2589_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26 + 4);
v_allowImportAll_2590_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26 + 5);
v_fixedToolchain_2591_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*26 + 6);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_cfg_2559_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v_cfg_2559_, 21);
lean_dec(v_unused_2599_);
v___x_2593_ = v_cfg_2559_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2588_);
lean_inc(v_enableArtifactCache_x3f_2587_);
lean_inc(v_readmeFile_2585_);
lean_inc(v_licenseFiles_2584_);
lean_inc(v_homepage_2583_);
lean_inc(v_keywords_2582_);
lean_inc(v_description_2581_);
lean_inc(v_versionTags_2580_);
lean_inc(v_version_2579_);
lean_inc(v_lintDriverArgs_2578_);
lean_inc(v_lintDriver_2577_);
lean_inc(v_testDriverArgs_2576_);
lean_inc(v_testDriver_2575_);
lean_inc(v_buildArchive_2573_);
lean_inc(v_releaseRepo_2572_);
lean_inc(v_irDir_2571_);
lean_inc(v_binDir_2570_);
lean_inc(v_nativeLibDir_2569_);
lean_inc(v_leanLibDir_2568_);
lean_inc(v_buildDir_2567_);
lean_inc(v_srcDir_2566_);
lean_inc(v_moreGlobalServerArgs_2565_);
lean_inc(v_extraDepTargets_2563_);
lean_inc(v_toLeanConfig_2561_);
lean_inc(v_toWorkspaceConfig_2560_);
lean_dec(v_cfg_2559_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 21, v_val_2558_);
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_toWorkspaceConfig_2560_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_toLeanConfig_2561_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_extraDepTargets_2563_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_moreGlobalServerArgs_2565_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_srcDir_2566_);
lean_ctor_set(v_reuseFailAlloc_2597_, 5, v_buildDir_2567_);
lean_ctor_set(v_reuseFailAlloc_2597_, 6, v_leanLibDir_2568_);
lean_ctor_set(v_reuseFailAlloc_2597_, 7, v_nativeLibDir_2569_);
lean_ctor_set(v_reuseFailAlloc_2597_, 8, v_binDir_2570_);
lean_ctor_set(v_reuseFailAlloc_2597_, 9, v_irDir_2571_);
lean_ctor_set(v_reuseFailAlloc_2597_, 10, v_releaseRepo_2572_);
lean_ctor_set(v_reuseFailAlloc_2597_, 11, v_buildArchive_2573_);
lean_ctor_set(v_reuseFailAlloc_2597_, 12, v_testDriver_2575_);
lean_ctor_set(v_reuseFailAlloc_2597_, 13, v_testDriverArgs_2576_);
lean_ctor_set(v_reuseFailAlloc_2597_, 14, v_lintDriver_2577_);
lean_ctor_set(v_reuseFailAlloc_2597_, 15, v_lintDriverArgs_2578_);
lean_ctor_set(v_reuseFailAlloc_2597_, 16, v_version_2579_);
lean_ctor_set(v_reuseFailAlloc_2597_, 17, v_versionTags_2580_);
lean_ctor_set(v_reuseFailAlloc_2597_, 18, v_description_2581_);
lean_ctor_set(v_reuseFailAlloc_2597_, 19, v_keywords_2582_);
lean_ctor_set(v_reuseFailAlloc_2597_, 20, v_homepage_2583_);
lean_ctor_set(v_reuseFailAlloc_2597_, 21, v_val_2558_);
lean_ctor_set(v_reuseFailAlloc_2597_, 22, v_licenseFiles_2584_);
lean_ctor_set(v_reuseFailAlloc_2597_, 23, v_readmeFile_2585_);
lean_ctor_set(v_reuseFailAlloc_2597_, 24, v_enableArtifactCache_x3f_2587_);
lean_ctor_set(v_reuseFailAlloc_2597_, 25, v_restoreAllArtifacts_x3f_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26, v_bootstrap_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26 + 1, v_precompileModules_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26 + 3, v_reservoir_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26 + 5, v_allowImportAll_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*26 + 6, v_fixedToolchain_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* v_f_2600_, lean_object* v_cfg_2601_){
_start:
{
lean_object* v_toWorkspaceConfig_2602_; lean_object* v_toLeanConfig_2603_; uint8_t v_bootstrap_2604_; lean_object* v_extraDepTargets_2605_; uint8_t v_precompileModules_2606_; lean_object* v_moreGlobalServerArgs_2607_; lean_object* v_srcDir_2608_; lean_object* v_buildDir_2609_; lean_object* v_leanLibDir_2610_; lean_object* v_nativeLibDir_2611_; lean_object* v_binDir_2612_; lean_object* v_irDir_2613_; lean_object* v_releaseRepo_2614_; lean_object* v_buildArchive_2615_; uint8_t v_preferReleaseBuild_2616_; lean_object* v_testDriver_2617_; lean_object* v_testDriverArgs_2618_; lean_object* v_lintDriver_2619_; lean_object* v_lintDriverArgs_2620_; lean_object* v_version_2621_; lean_object* v_versionTags_2622_; lean_object* v_description_2623_; lean_object* v_keywords_2624_; lean_object* v_homepage_2625_; lean_object* v_license_2626_; lean_object* v_licenseFiles_2627_; lean_object* v_readmeFile_2628_; uint8_t v_reservoir_2629_; lean_object* v_enableArtifactCache_x3f_2630_; lean_object* v_restoreAllArtifacts_x3f_2631_; uint8_t v_libPrefixOnWindows_2632_; uint8_t v_allowImportAll_2633_; uint8_t v_fixedToolchain_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v_toWorkspaceConfig_2602_ = lean_ctor_get(v_cfg_2601_, 0);
v_toLeanConfig_2603_ = lean_ctor_get(v_cfg_2601_, 1);
v_bootstrap_2604_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26);
v_extraDepTargets_2605_ = lean_ctor_get(v_cfg_2601_, 2);
v_precompileModules_2606_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2607_ = lean_ctor_get(v_cfg_2601_, 3);
v_srcDir_2608_ = lean_ctor_get(v_cfg_2601_, 4);
v_buildDir_2609_ = lean_ctor_get(v_cfg_2601_, 5);
v_leanLibDir_2610_ = lean_ctor_get(v_cfg_2601_, 6);
v_nativeLibDir_2611_ = lean_ctor_get(v_cfg_2601_, 7);
v_binDir_2612_ = lean_ctor_get(v_cfg_2601_, 8);
v_irDir_2613_ = lean_ctor_get(v_cfg_2601_, 9);
v_releaseRepo_2614_ = lean_ctor_get(v_cfg_2601_, 10);
v_buildArchive_2615_ = lean_ctor_get(v_cfg_2601_, 11);
v_preferReleaseBuild_2616_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26 + 2);
v_testDriver_2617_ = lean_ctor_get(v_cfg_2601_, 12);
v_testDriverArgs_2618_ = lean_ctor_get(v_cfg_2601_, 13);
v_lintDriver_2619_ = lean_ctor_get(v_cfg_2601_, 14);
v_lintDriverArgs_2620_ = lean_ctor_get(v_cfg_2601_, 15);
v_version_2621_ = lean_ctor_get(v_cfg_2601_, 16);
v_versionTags_2622_ = lean_ctor_get(v_cfg_2601_, 17);
v_description_2623_ = lean_ctor_get(v_cfg_2601_, 18);
v_keywords_2624_ = lean_ctor_get(v_cfg_2601_, 19);
v_homepage_2625_ = lean_ctor_get(v_cfg_2601_, 20);
v_license_2626_ = lean_ctor_get(v_cfg_2601_, 21);
v_licenseFiles_2627_ = lean_ctor_get(v_cfg_2601_, 22);
v_readmeFile_2628_ = lean_ctor_get(v_cfg_2601_, 23);
v_reservoir_2629_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2630_ = lean_ctor_get(v_cfg_2601_, 24);
v_restoreAllArtifacts_x3f_2631_ = lean_ctor_get(v_cfg_2601_, 25);
v_libPrefixOnWindows_2632_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26 + 4);
v_allowImportAll_2633_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26 + 5);
v_fixedToolchain_2634_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*26 + 6);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_cfg_2601_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2636_ = v_cfg_2601_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2631_);
lean_inc(v_enableArtifactCache_x3f_2630_);
lean_inc(v_readmeFile_2628_);
lean_inc(v_licenseFiles_2627_);
lean_inc(v_license_2626_);
lean_inc(v_homepage_2625_);
lean_inc(v_keywords_2624_);
lean_inc(v_description_2623_);
lean_inc(v_versionTags_2622_);
lean_inc(v_version_2621_);
lean_inc(v_lintDriverArgs_2620_);
lean_inc(v_lintDriver_2619_);
lean_inc(v_testDriverArgs_2618_);
lean_inc(v_testDriver_2617_);
lean_inc(v_buildArchive_2615_);
lean_inc(v_releaseRepo_2614_);
lean_inc(v_irDir_2613_);
lean_inc(v_binDir_2612_);
lean_inc(v_nativeLibDir_2611_);
lean_inc(v_leanLibDir_2610_);
lean_inc(v_buildDir_2609_);
lean_inc(v_srcDir_2608_);
lean_inc(v_moreGlobalServerArgs_2607_);
lean_inc(v_extraDepTargets_2605_);
lean_inc(v_toLeanConfig_2603_);
lean_inc(v_toWorkspaceConfig_2602_);
lean_dec(v_cfg_2601_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_apply_1(v_f_2600_, v_license_2626_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 21, v___x_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_toWorkspaceConfig_2602_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_toLeanConfig_2603_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_extraDepTargets_2605_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_moreGlobalServerArgs_2607_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_srcDir_2608_);
lean_ctor_set(v_reuseFailAlloc_2641_, 5, v_buildDir_2609_);
lean_ctor_set(v_reuseFailAlloc_2641_, 6, v_leanLibDir_2610_);
lean_ctor_set(v_reuseFailAlloc_2641_, 7, v_nativeLibDir_2611_);
lean_ctor_set(v_reuseFailAlloc_2641_, 8, v_binDir_2612_);
lean_ctor_set(v_reuseFailAlloc_2641_, 9, v_irDir_2613_);
lean_ctor_set(v_reuseFailAlloc_2641_, 10, v_releaseRepo_2614_);
lean_ctor_set(v_reuseFailAlloc_2641_, 11, v_buildArchive_2615_);
lean_ctor_set(v_reuseFailAlloc_2641_, 12, v_testDriver_2617_);
lean_ctor_set(v_reuseFailAlloc_2641_, 13, v_testDriverArgs_2618_);
lean_ctor_set(v_reuseFailAlloc_2641_, 14, v_lintDriver_2619_);
lean_ctor_set(v_reuseFailAlloc_2641_, 15, v_lintDriverArgs_2620_);
lean_ctor_set(v_reuseFailAlloc_2641_, 16, v_version_2621_);
lean_ctor_set(v_reuseFailAlloc_2641_, 17, v_versionTags_2622_);
lean_ctor_set(v_reuseFailAlloc_2641_, 18, v_description_2623_);
lean_ctor_set(v_reuseFailAlloc_2641_, 19, v_keywords_2624_);
lean_ctor_set(v_reuseFailAlloc_2641_, 20, v_homepage_2625_);
lean_ctor_set(v_reuseFailAlloc_2641_, 21, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2641_, 22, v_licenseFiles_2627_);
lean_ctor_set(v_reuseFailAlloc_2641_, 23, v_readmeFile_2628_);
lean_ctor_set(v_reuseFailAlloc_2641_, 24, v_enableArtifactCache_x3f_2630_);
lean_ctor_set(v_reuseFailAlloc_2641_, 25, v_restoreAllArtifacts_x3f_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26, v_bootstrap_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26 + 1, v_precompileModules_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26 + 3, v_reservoir_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26 + 5, v_allowImportAll_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*26 + 6, v_fixedToolchain_2634_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2651_, lean_object* v_n_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2654_, lean_object* v_n_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lake_PackageConfig_license___proj(v_p_2654_, v_n_2655_);
lean_dec(v_n_2655_);
lean_dec(v_p_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2657_, lean_object* v_n_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lake_PackageConfig_license___proj(v_p_2657_, v_n_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2660_, lean_object* v_n_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lake_PackageConfig_license_instConfigField(v_p_2660_, v_n_2661_);
lean_dec(v_n_2661_);
lean_dec(v_p_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* v_cfg_2663_){
_start:
{
lean_object* v_licenseFiles_2664_; 
v_licenseFiles_2664_ = lean_ctor_get(v_cfg_2663_, 22);
lean_inc_ref(v_licenseFiles_2664_);
return v_licenseFiles_2664_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* v_cfg_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lake_PackageConfig_licenseFiles___proj___lam__0(v_cfg_2665_);
lean_dec_ref(v_cfg_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* v_val_2667_, lean_object* v_cfg_2668_){
_start:
{
lean_object* v_toWorkspaceConfig_2669_; lean_object* v_toLeanConfig_2670_; uint8_t v_bootstrap_2671_; lean_object* v_extraDepTargets_2672_; uint8_t v_precompileModules_2673_; lean_object* v_moreGlobalServerArgs_2674_; lean_object* v_srcDir_2675_; lean_object* v_buildDir_2676_; lean_object* v_leanLibDir_2677_; lean_object* v_nativeLibDir_2678_; lean_object* v_binDir_2679_; lean_object* v_irDir_2680_; lean_object* v_releaseRepo_2681_; lean_object* v_buildArchive_2682_; uint8_t v_preferReleaseBuild_2683_; lean_object* v_testDriver_2684_; lean_object* v_testDriverArgs_2685_; lean_object* v_lintDriver_2686_; lean_object* v_lintDriverArgs_2687_; lean_object* v_version_2688_; lean_object* v_versionTags_2689_; lean_object* v_description_2690_; lean_object* v_keywords_2691_; lean_object* v_homepage_2692_; lean_object* v_license_2693_; lean_object* v_readmeFile_2694_; uint8_t v_reservoir_2695_; lean_object* v_enableArtifactCache_x3f_2696_; lean_object* v_restoreAllArtifacts_x3f_2697_; uint8_t v_libPrefixOnWindows_2698_; uint8_t v_allowImportAll_2699_; uint8_t v_fixedToolchain_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_toWorkspaceConfig_2669_ = lean_ctor_get(v_cfg_2668_, 0);
v_toLeanConfig_2670_ = lean_ctor_get(v_cfg_2668_, 1);
v_bootstrap_2671_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26);
v_extraDepTargets_2672_ = lean_ctor_get(v_cfg_2668_, 2);
v_precompileModules_2673_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2674_ = lean_ctor_get(v_cfg_2668_, 3);
v_srcDir_2675_ = lean_ctor_get(v_cfg_2668_, 4);
v_buildDir_2676_ = lean_ctor_get(v_cfg_2668_, 5);
v_leanLibDir_2677_ = lean_ctor_get(v_cfg_2668_, 6);
v_nativeLibDir_2678_ = lean_ctor_get(v_cfg_2668_, 7);
v_binDir_2679_ = lean_ctor_get(v_cfg_2668_, 8);
v_irDir_2680_ = lean_ctor_get(v_cfg_2668_, 9);
v_releaseRepo_2681_ = lean_ctor_get(v_cfg_2668_, 10);
v_buildArchive_2682_ = lean_ctor_get(v_cfg_2668_, 11);
v_preferReleaseBuild_2683_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26 + 2);
v_testDriver_2684_ = lean_ctor_get(v_cfg_2668_, 12);
v_testDriverArgs_2685_ = lean_ctor_get(v_cfg_2668_, 13);
v_lintDriver_2686_ = lean_ctor_get(v_cfg_2668_, 14);
v_lintDriverArgs_2687_ = lean_ctor_get(v_cfg_2668_, 15);
v_version_2688_ = lean_ctor_get(v_cfg_2668_, 16);
v_versionTags_2689_ = lean_ctor_get(v_cfg_2668_, 17);
v_description_2690_ = lean_ctor_get(v_cfg_2668_, 18);
v_keywords_2691_ = lean_ctor_get(v_cfg_2668_, 19);
v_homepage_2692_ = lean_ctor_get(v_cfg_2668_, 20);
v_license_2693_ = lean_ctor_get(v_cfg_2668_, 21);
v_readmeFile_2694_ = lean_ctor_get(v_cfg_2668_, 23);
v_reservoir_2695_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2696_ = lean_ctor_get(v_cfg_2668_, 24);
v_restoreAllArtifacts_x3f_2697_ = lean_ctor_get(v_cfg_2668_, 25);
v_libPrefixOnWindows_2698_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26 + 4);
v_allowImportAll_2699_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26 + 5);
v_fixedToolchain_2700_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*26 + 6);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_cfg_2668_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v_cfg_2668_, 22);
lean_dec(v_unused_2708_);
v___x_2702_ = v_cfg_2668_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2697_);
lean_inc(v_enableArtifactCache_x3f_2696_);
lean_inc(v_readmeFile_2694_);
lean_inc(v_license_2693_);
lean_inc(v_homepage_2692_);
lean_inc(v_keywords_2691_);
lean_inc(v_description_2690_);
lean_inc(v_versionTags_2689_);
lean_inc(v_version_2688_);
lean_inc(v_lintDriverArgs_2687_);
lean_inc(v_lintDriver_2686_);
lean_inc(v_testDriverArgs_2685_);
lean_inc(v_testDriver_2684_);
lean_inc(v_buildArchive_2682_);
lean_inc(v_releaseRepo_2681_);
lean_inc(v_irDir_2680_);
lean_inc(v_binDir_2679_);
lean_inc(v_nativeLibDir_2678_);
lean_inc(v_leanLibDir_2677_);
lean_inc(v_buildDir_2676_);
lean_inc(v_srcDir_2675_);
lean_inc(v_moreGlobalServerArgs_2674_);
lean_inc(v_extraDepTargets_2672_);
lean_inc(v_toLeanConfig_2670_);
lean_inc(v_toWorkspaceConfig_2669_);
lean_dec(v_cfg_2668_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 22, v_val_2667_);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_toWorkspaceConfig_2669_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_toLeanConfig_2670_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_extraDepTargets_2672_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_moreGlobalServerArgs_2674_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_srcDir_2675_);
lean_ctor_set(v_reuseFailAlloc_2706_, 5, v_buildDir_2676_);
lean_ctor_set(v_reuseFailAlloc_2706_, 6, v_leanLibDir_2677_);
lean_ctor_set(v_reuseFailAlloc_2706_, 7, v_nativeLibDir_2678_);
lean_ctor_set(v_reuseFailAlloc_2706_, 8, v_binDir_2679_);
lean_ctor_set(v_reuseFailAlloc_2706_, 9, v_irDir_2680_);
lean_ctor_set(v_reuseFailAlloc_2706_, 10, v_releaseRepo_2681_);
lean_ctor_set(v_reuseFailAlloc_2706_, 11, v_buildArchive_2682_);
lean_ctor_set(v_reuseFailAlloc_2706_, 12, v_testDriver_2684_);
lean_ctor_set(v_reuseFailAlloc_2706_, 13, v_testDriverArgs_2685_);
lean_ctor_set(v_reuseFailAlloc_2706_, 14, v_lintDriver_2686_);
lean_ctor_set(v_reuseFailAlloc_2706_, 15, v_lintDriverArgs_2687_);
lean_ctor_set(v_reuseFailAlloc_2706_, 16, v_version_2688_);
lean_ctor_set(v_reuseFailAlloc_2706_, 17, v_versionTags_2689_);
lean_ctor_set(v_reuseFailAlloc_2706_, 18, v_description_2690_);
lean_ctor_set(v_reuseFailAlloc_2706_, 19, v_keywords_2691_);
lean_ctor_set(v_reuseFailAlloc_2706_, 20, v_homepage_2692_);
lean_ctor_set(v_reuseFailAlloc_2706_, 21, v_license_2693_);
lean_ctor_set(v_reuseFailAlloc_2706_, 22, v_val_2667_);
lean_ctor_set(v_reuseFailAlloc_2706_, 23, v_readmeFile_2694_);
lean_ctor_set(v_reuseFailAlloc_2706_, 24, v_enableArtifactCache_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2706_, 25, v_restoreAllArtifacts_x3f_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26, v_bootstrap_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26 + 1, v_precompileModules_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2683_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26 + 3, v_reservoir_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26 + 5, v_allowImportAll_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*26 + 6, v_fixedToolchain_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* v_f_2709_, lean_object* v_cfg_2710_){
_start:
{
lean_object* v_toWorkspaceConfig_2711_; lean_object* v_toLeanConfig_2712_; uint8_t v_bootstrap_2713_; lean_object* v_extraDepTargets_2714_; uint8_t v_precompileModules_2715_; lean_object* v_moreGlobalServerArgs_2716_; lean_object* v_srcDir_2717_; lean_object* v_buildDir_2718_; lean_object* v_leanLibDir_2719_; lean_object* v_nativeLibDir_2720_; lean_object* v_binDir_2721_; lean_object* v_irDir_2722_; lean_object* v_releaseRepo_2723_; lean_object* v_buildArchive_2724_; uint8_t v_preferReleaseBuild_2725_; lean_object* v_testDriver_2726_; lean_object* v_testDriverArgs_2727_; lean_object* v_lintDriver_2728_; lean_object* v_lintDriverArgs_2729_; lean_object* v_version_2730_; lean_object* v_versionTags_2731_; lean_object* v_description_2732_; lean_object* v_keywords_2733_; lean_object* v_homepage_2734_; lean_object* v_license_2735_; lean_object* v_licenseFiles_2736_; lean_object* v_readmeFile_2737_; uint8_t v_reservoir_2738_; lean_object* v_enableArtifactCache_x3f_2739_; lean_object* v_restoreAllArtifacts_x3f_2740_; uint8_t v_libPrefixOnWindows_2741_; uint8_t v_allowImportAll_2742_; uint8_t v_fixedToolchain_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v_toWorkspaceConfig_2711_ = lean_ctor_get(v_cfg_2710_, 0);
v_toLeanConfig_2712_ = lean_ctor_get(v_cfg_2710_, 1);
v_bootstrap_2713_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26);
v_extraDepTargets_2714_ = lean_ctor_get(v_cfg_2710_, 2);
v_precompileModules_2715_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2716_ = lean_ctor_get(v_cfg_2710_, 3);
v_srcDir_2717_ = lean_ctor_get(v_cfg_2710_, 4);
v_buildDir_2718_ = lean_ctor_get(v_cfg_2710_, 5);
v_leanLibDir_2719_ = lean_ctor_get(v_cfg_2710_, 6);
v_nativeLibDir_2720_ = lean_ctor_get(v_cfg_2710_, 7);
v_binDir_2721_ = lean_ctor_get(v_cfg_2710_, 8);
v_irDir_2722_ = lean_ctor_get(v_cfg_2710_, 9);
v_releaseRepo_2723_ = lean_ctor_get(v_cfg_2710_, 10);
v_buildArchive_2724_ = lean_ctor_get(v_cfg_2710_, 11);
v_preferReleaseBuild_2725_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26 + 2);
v_testDriver_2726_ = lean_ctor_get(v_cfg_2710_, 12);
v_testDriverArgs_2727_ = lean_ctor_get(v_cfg_2710_, 13);
v_lintDriver_2728_ = lean_ctor_get(v_cfg_2710_, 14);
v_lintDriverArgs_2729_ = lean_ctor_get(v_cfg_2710_, 15);
v_version_2730_ = lean_ctor_get(v_cfg_2710_, 16);
v_versionTags_2731_ = lean_ctor_get(v_cfg_2710_, 17);
v_description_2732_ = lean_ctor_get(v_cfg_2710_, 18);
v_keywords_2733_ = lean_ctor_get(v_cfg_2710_, 19);
v_homepage_2734_ = lean_ctor_get(v_cfg_2710_, 20);
v_license_2735_ = lean_ctor_get(v_cfg_2710_, 21);
v_licenseFiles_2736_ = lean_ctor_get(v_cfg_2710_, 22);
v_readmeFile_2737_ = lean_ctor_get(v_cfg_2710_, 23);
v_reservoir_2738_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2739_ = lean_ctor_get(v_cfg_2710_, 24);
v_restoreAllArtifacts_x3f_2740_ = lean_ctor_get(v_cfg_2710_, 25);
v_libPrefixOnWindows_2741_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26 + 4);
v_allowImportAll_2742_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26 + 5);
v_fixedToolchain_2743_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*26 + 6);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_cfg_2710_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2745_ = v_cfg_2710_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2740_);
lean_inc(v_enableArtifactCache_x3f_2739_);
lean_inc(v_readmeFile_2737_);
lean_inc(v_licenseFiles_2736_);
lean_inc(v_license_2735_);
lean_inc(v_homepage_2734_);
lean_inc(v_keywords_2733_);
lean_inc(v_description_2732_);
lean_inc(v_versionTags_2731_);
lean_inc(v_version_2730_);
lean_inc(v_lintDriverArgs_2729_);
lean_inc(v_lintDriver_2728_);
lean_inc(v_testDriverArgs_2727_);
lean_inc(v_testDriver_2726_);
lean_inc(v_buildArchive_2724_);
lean_inc(v_releaseRepo_2723_);
lean_inc(v_irDir_2722_);
lean_inc(v_binDir_2721_);
lean_inc(v_nativeLibDir_2720_);
lean_inc(v_leanLibDir_2719_);
lean_inc(v_buildDir_2718_);
lean_inc(v_srcDir_2717_);
lean_inc(v_moreGlobalServerArgs_2716_);
lean_inc(v_extraDepTargets_2714_);
lean_inc(v_toLeanConfig_2712_);
lean_inc(v_toWorkspaceConfig_2711_);
lean_dec(v_cfg_2710_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_apply_1(v_f_2709_, v_licenseFiles_2736_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 22, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_toWorkspaceConfig_2711_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_toLeanConfig_2712_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_extraDepTargets_2714_);
lean_ctor_set(v_reuseFailAlloc_2750_, 3, v_moreGlobalServerArgs_2716_);
lean_ctor_set(v_reuseFailAlloc_2750_, 4, v_srcDir_2717_);
lean_ctor_set(v_reuseFailAlloc_2750_, 5, v_buildDir_2718_);
lean_ctor_set(v_reuseFailAlloc_2750_, 6, v_leanLibDir_2719_);
lean_ctor_set(v_reuseFailAlloc_2750_, 7, v_nativeLibDir_2720_);
lean_ctor_set(v_reuseFailAlloc_2750_, 8, v_binDir_2721_);
lean_ctor_set(v_reuseFailAlloc_2750_, 9, v_irDir_2722_);
lean_ctor_set(v_reuseFailAlloc_2750_, 10, v_releaseRepo_2723_);
lean_ctor_set(v_reuseFailAlloc_2750_, 11, v_buildArchive_2724_);
lean_ctor_set(v_reuseFailAlloc_2750_, 12, v_testDriver_2726_);
lean_ctor_set(v_reuseFailAlloc_2750_, 13, v_testDriverArgs_2727_);
lean_ctor_set(v_reuseFailAlloc_2750_, 14, v_lintDriver_2728_);
lean_ctor_set(v_reuseFailAlloc_2750_, 15, v_lintDriverArgs_2729_);
lean_ctor_set(v_reuseFailAlloc_2750_, 16, v_version_2730_);
lean_ctor_set(v_reuseFailAlloc_2750_, 17, v_versionTags_2731_);
lean_ctor_set(v_reuseFailAlloc_2750_, 18, v_description_2732_);
lean_ctor_set(v_reuseFailAlloc_2750_, 19, v_keywords_2733_);
lean_ctor_set(v_reuseFailAlloc_2750_, 20, v_homepage_2734_);
lean_ctor_set(v_reuseFailAlloc_2750_, 21, v_license_2735_);
lean_ctor_set(v_reuseFailAlloc_2750_, 22, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2750_, 23, v_readmeFile_2737_);
lean_ctor_set(v_reuseFailAlloc_2750_, 24, v_enableArtifactCache_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2750_, 25, v_restoreAllArtifacts_x3f_2740_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26, v_bootstrap_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26 + 1, v_precompileModules_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2725_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26 + 3, v_reservoir_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26 + 5, v_allowImportAll_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*26 + 6, v_fixedToolchain_2743_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* v_x_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1));
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* v_x_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lake_PackageConfig_licenseFiles___proj___lam__3(v_x_2759_);
lean_dec_ref(v_x_2759_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_2770_, lean_object* v_n_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_2773_, lean_object* v_n_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2773_, v_n_2774_);
lean_dec(v_n_2774_);
lean_dec(v_p_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_2776_, lean_object* v_n_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2776_, v_n_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_2779_, lean_object* v_n_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_2779_, v_n_2780_);
lean_dec(v_n_2780_);
lean_dec(v_p_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* v_cfg_2782_){
_start:
{
lean_object* v_readmeFile_2783_; 
v_readmeFile_2783_ = lean_ctor_get(v_cfg_2782_, 23);
lean_inc_ref(v_readmeFile_2783_);
return v_readmeFile_2783_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* v_cfg_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lake_PackageConfig_readmeFile___proj___lam__0(v_cfg_2784_);
lean_dec_ref(v_cfg_2784_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* v_val_2786_, lean_object* v_cfg_2787_){
_start:
{
lean_object* v_toWorkspaceConfig_2788_; lean_object* v_toLeanConfig_2789_; uint8_t v_bootstrap_2790_; lean_object* v_extraDepTargets_2791_; uint8_t v_precompileModules_2792_; lean_object* v_moreGlobalServerArgs_2793_; lean_object* v_srcDir_2794_; lean_object* v_buildDir_2795_; lean_object* v_leanLibDir_2796_; lean_object* v_nativeLibDir_2797_; lean_object* v_binDir_2798_; lean_object* v_irDir_2799_; lean_object* v_releaseRepo_2800_; lean_object* v_buildArchive_2801_; uint8_t v_preferReleaseBuild_2802_; lean_object* v_testDriver_2803_; lean_object* v_testDriverArgs_2804_; lean_object* v_lintDriver_2805_; lean_object* v_lintDriverArgs_2806_; lean_object* v_version_2807_; lean_object* v_versionTags_2808_; lean_object* v_description_2809_; lean_object* v_keywords_2810_; lean_object* v_homepage_2811_; lean_object* v_license_2812_; lean_object* v_licenseFiles_2813_; uint8_t v_reservoir_2814_; lean_object* v_enableArtifactCache_x3f_2815_; lean_object* v_restoreAllArtifacts_x3f_2816_; uint8_t v_libPrefixOnWindows_2817_; uint8_t v_allowImportAll_2818_; uint8_t v_fixedToolchain_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_toWorkspaceConfig_2788_ = lean_ctor_get(v_cfg_2787_, 0);
v_toLeanConfig_2789_ = lean_ctor_get(v_cfg_2787_, 1);
v_bootstrap_2790_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26);
v_extraDepTargets_2791_ = lean_ctor_get(v_cfg_2787_, 2);
v_precompileModules_2792_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2793_ = lean_ctor_get(v_cfg_2787_, 3);
v_srcDir_2794_ = lean_ctor_get(v_cfg_2787_, 4);
v_buildDir_2795_ = lean_ctor_get(v_cfg_2787_, 5);
v_leanLibDir_2796_ = lean_ctor_get(v_cfg_2787_, 6);
v_nativeLibDir_2797_ = lean_ctor_get(v_cfg_2787_, 7);
v_binDir_2798_ = lean_ctor_get(v_cfg_2787_, 8);
v_irDir_2799_ = lean_ctor_get(v_cfg_2787_, 9);
v_releaseRepo_2800_ = lean_ctor_get(v_cfg_2787_, 10);
v_buildArchive_2801_ = lean_ctor_get(v_cfg_2787_, 11);
v_preferReleaseBuild_2802_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26 + 2);
v_testDriver_2803_ = lean_ctor_get(v_cfg_2787_, 12);
v_testDriverArgs_2804_ = lean_ctor_get(v_cfg_2787_, 13);
v_lintDriver_2805_ = lean_ctor_get(v_cfg_2787_, 14);
v_lintDriverArgs_2806_ = lean_ctor_get(v_cfg_2787_, 15);
v_version_2807_ = lean_ctor_get(v_cfg_2787_, 16);
v_versionTags_2808_ = lean_ctor_get(v_cfg_2787_, 17);
v_description_2809_ = lean_ctor_get(v_cfg_2787_, 18);
v_keywords_2810_ = lean_ctor_get(v_cfg_2787_, 19);
v_homepage_2811_ = lean_ctor_get(v_cfg_2787_, 20);
v_license_2812_ = lean_ctor_get(v_cfg_2787_, 21);
v_licenseFiles_2813_ = lean_ctor_get(v_cfg_2787_, 22);
v_reservoir_2814_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2815_ = lean_ctor_get(v_cfg_2787_, 24);
v_restoreAllArtifacts_x3f_2816_ = lean_ctor_get(v_cfg_2787_, 25);
v_libPrefixOnWindows_2817_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26 + 4);
v_allowImportAll_2818_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26 + 5);
v_fixedToolchain_2819_ = lean_ctor_get_uint8(v_cfg_2787_, sizeof(void*)*26 + 6);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_cfg_2787_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v_cfg_2787_, 23);
lean_dec(v_unused_2827_);
v___x_2821_ = v_cfg_2787_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2816_);
lean_inc(v_enableArtifactCache_x3f_2815_);
lean_inc(v_licenseFiles_2813_);
lean_inc(v_license_2812_);
lean_inc(v_homepage_2811_);
lean_inc(v_keywords_2810_);
lean_inc(v_description_2809_);
lean_inc(v_versionTags_2808_);
lean_inc(v_version_2807_);
lean_inc(v_lintDriverArgs_2806_);
lean_inc(v_lintDriver_2805_);
lean_inc(v_testDriverArgs_2804_);
lean_inc(v_testDriver_2803_);
lean_inc(v_buildArchive_2801_);
lean_inc(v_releaseRepo_2800_);
lean_inc(v_irDir_2799_);
lean_inc(v_binDir_2798_);
lean_inc(v_nativeLibDir_2797_);
lean_inc(v_leanLibDir_2796_);
lean_inc(v_buildDir_2795_);
lean_inc(v_srcDir_2794_);
lean_inc(v_moreGlobalServerArgs_2793_);
lean_inc(v_extraDepTargets_2791_);
lean_inc(v_toLeanConfig_2789_);
lean_inc(v_toWorkspaceConfig_2788_);
lean_dec(v_cfg_2787_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 23, v_val_2786_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_toWorkspaceConfig_2788_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_toLeanConfig_2789_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_extraDepTargets_2791_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_moreGlobalServerArgs_2793_);
lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_srcDir_2794_);
lean_ctor_set(v_reuseFailAlloc_2825_, 5, v_buildDir_2795_);
lean_ctor_set(v_reuseFailAlloc_2825_, 6, v_leanLibDir_2796_);
lean_ctor_set(v_reuseFailAlloc_2825_, 7, v_nativeLibDir_2797_);
lean_ctor_set(v_reuseFailAlloc_2825_, 8, v_binDir_2798_);
lean_ctor_set(v_reuseFailAlloc_2825_, 9, v_irDir_2799_);
lean_ctor_set(v_reuseFailAlloc_2825_, 10, v_releaseRepo_2800_);
lean_ctor_set(v_reuseFailAlloc_2825_, 11, v_buildArchive_2801_);
lean_ctor_set(v_reuseFailAlloc_2825_, 12, v_testDriver_2803_);
lean_ctor_set(v_reuseFailAlloc_2825_, 13, v_testDriverArgs_2804_);
lean_ctor_set(v_reuseFailAlloc_2825_, 14, v_lintDriver_2805_);
lean_ctor_set(v_reuseFailAlloc_2825_, 15, v_lintDriverArgs_2806_);
lean_ctor_set(v_reuseFailAlloc_2825_, 16, v_version_2807_);
lean_ctor_set(v_reuseFailAlloc_2825_, 17, v_versionTags_2808_);
lean_ctor_set(v_reuseFailAlloc_2825_, 18, v_description_2809_);
lean_ctor_set(v_reuseFailAlloc_2825_, 19, v_keywords_2810_);
lean_ctor_set(v_reuseFailAlloc_2825_, 20, v_homepage_2811_);
lean_ctor_set(v_reuseFailAlloc_2825_, 21, v_license_2812_);
lean_ctor_set(v_reuseFailAlloc_2825_, 22, v_licenseFiles_2813_);
lean_ctor_set(v_reuseFailAlloc_2825_, 23, v_val_2786_);
lean_ctor_set(v_reuseFailAlloc_2825_, 24, v_enableArtifactCache_x3f_2815_);
lean_ctor_set(v_reuseFailAlloc_2825_, 25, v_restoreAllArtifacts_x3f_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26, v_bootstrap_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26 + 1, v_precompileModules_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26 + 3, v_reservoir_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26 + 5, v_allowImportAll_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*26 + 6, v_fixedToolchain_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* v_f_2828_, lean_object* v_cfg_2829_){
_start:
{
lean_object* v_toWorkspaceConfig_2830_; lean_object* v_toLeanConfig_2831_; uint8_t v_bootstrap_2832_; lean_object* v_extraDepTargets_2833_; uint8_t v_precompileModules_2834_; lean_object* v_moreGlobalServerArgs_2835_; lean_object* v_srcDir_2836_; lean_object* v_buildDir_2837_; lean_object* v_leanLibDir_2838_; lean_object* v_nativeLibDir_2839_; lean_object* v_binDir_2840_; lean_object* v_irDir_2841_; lean_object* v_releaseRepo_2842_; lean_object* v_buildArchive_2843_; uint8_t v_preferReleaseBuild_2844_; lean_object* v_testDriver_2845_; lean_object* v_testDriverArgs_2846_; lean_object* v_lintDriver_2847_; lean_object* v_lintDriverArgs_2848_; lean_object* v_version_2849_; lean_object* v_versionTags_2850_; lean_object* v_description_2851_; lean_object* v_keywords_2852_; lean_object* v_homepage_2853_; lean_object* v_license_2854_; lean_object* v_licenseFiles_2855_; lean_object* v_readmeFile_2856_; uint8_t v_reservoir_2857_; lean_object* v_enableArtifactCache_x3f_2858_; lean_object* v_restoreAllArtifacts_x3f_2859_; uint8_t v_libPrefixOnWindows_2860_; uint8_t v_allowImportAll_2861_; uint8_t v_fixedToolchain_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2870_; 
v_toWorkspaceConfig_2830_ = lean_ctor_get(v_cfg_2829_, 0);
v_toLeanConfig_2831_ = lean_ctor_get(v_cfg_2829_, 1);
v_bootstrap_2832_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26);
v_extraDepTargets_2833_ = lean_ctor_get(v_cfg_2829_, 2);
v_precompileModules_2834_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2835_ = lean_ctor_get(v_cfg_2829_, 3);
v_srcDir_2836_ = lean_ctor_get(v_cfg_2829_, 4);
v_buildDir_2837_ = lean_ctor_get(v_cfg_2829_, 5);
v_leanLibDir_2838_ = lean_ctor_get(v_cfg_2829_, 6);
v_nativeLibDir_2839_ = lean_ctor_get(v_cfg_2829_, 7);
v_binDir_2840_ = lean_ctor_get(v_cfg_2829_, 8);
v_irDir_2841_ = lean_ctor_get(v_cfg_2829_, 9);
v_releaseRepo_2842_ = lean_ctor_get(v_cfg_2829_, 10);
v_buildArchive_2843_ = lean_ctor_get(v_cfg_2829_, 11);
v_preferReleaseBuild_2844_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26 + 2);
v_testDriver_2845_ = lean_ctor_get(v_cfg_2829_, 12);
v_testDriverArgs_2846_ = lean_ctor_get(v_cfg_2829_, 13);
v_lintDriver_2847_ = lean_ctor_get(v_cfg_2829_, 14);
v_lintDriverArgs_2848_ = lean_ctor_get(v_cfg_2829_, 15);
v_version_2849_ = lean_ctor_get(v_cfg_2829_, 16);
v_versionTags_2850_ = lean_ctor_get(v_cfg_2829_, 17);
v_description_2851_ = lean_ctor_get(v_cfg_2829_, 18);
v_keywords_2852_ = lean_ctor_get(v_cfg_2829_, 19);
v_homepage_2853_ = lean_ctor_get(v_cfg_2829_, 20);
v_license_2854_ = lean_ctor_get(v_cfg_2829_, 21);
v_licenseFiles_2855_ = lean_ctor_get(v_cfg_2829_, 22);
v_readmeFile_2856_ = lean_ctor_get(v_cfg_2829_, 23);
v_reservoir_2857_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2858_ = lean_ctor_get(v_cfg_2829_, 24);
v_restoreAllArtifacts_x3f_2859_ = lean_ctor_get(v_cfg_2829_, 25);
v_libPrefixOnWindows_2860_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26 + 4);
v_allowImportAll_2861_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26 + 5);
v_fixedToolchain_2862_ = lean_ctor_get_uint8(v_cfg_2829_, sizeof(void*)*26 + 6);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_cfg_2829_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2864_ = v_cfg_2829_;
v_isShared_2865_ = v_isSharedCheck_2870_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2859_);
lean_inc(v_enableArtifactCache_x3f_2858_);
lean_inc(v_readmeFile_2856_);
lean_inc(v_licenseFiles_2855_);
lean_inc(v_license_2854_);
lean_inc(v_homepage_2853_);
lean_inc(v_keywords_2852_);
lean_inc(v_description_2851_);
lean_inc(v_versionTags_2850_);
lean_inc(v_version_2849_);
lean_inc(v_lintDriverArgs_2848_);
lean_inc(v_lintDriver_2847_);
lean_inc(v_testDriverArgs_2846_);
lean_inc(v_testDriver_2845_);
lean_inc(v_buildArchive_2843_);
lean_inc(v_releaseRepo_2842_);
lean_inc(v_irDir_2841_);
lean_inc(v_binDir_2840_);
lean_inc(v_nativeLibDir_2839_);
lean_inc(v_leanLibDir_2838_);
lean_inc(v_buildDir_2837_);
lean_inc(v_srcDir_2836_);
lean_inc(v_moreGlobalServerArgs_2835_);
lean_inc(v_extraDepTargets_2833_);
lean_inc(v_toLeanConfig_2831_);
lean_inc(v_toWorkspaceConfig_2830_);
lean_dec(v_cfg_2829_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2870_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2866_ = lean_apply_1(v_f_2828_, v_readmeFile_2856_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 23, v___x_2866_);
v___x_2868_ = v___x_2864_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_toWorkspaceConfig_2830_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_toLeanConfig_2831_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_extraDepTargets_2833_);
lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_moreGlobalServerArgs_2835_);
lean_ctor_set(v_reuseFailAlloc_2869_, 4, v_srcDir_2836_);
lean_ctor_set(v_reuseFailAlloc_2869_, 5, v_buildDir_2837_);
lean_ctor_set(v_reuseFailAlloc_2869_, 6, v_leanLibDir_2838_);
lean_ctor_set(v_reuseFailAlloc_2869_, 7, v_nativeLibDir_2839_);
lean_ctor_set(v_reuseFailAlloc_2869_, 8, v_binDir_2840_);
lean_ctor_set(v_reuseFailAlloc_2869_, 9, v_irDir_2841_);
lean_ctor_set(v_reuseFailAlloc_2869_, 10, v_releaseRepo_2842_);
lean_ctor_set(v_reuseFailAlloc_2869_, 11, v_buildArchive_2843_);
lean_ctor_set(v_reuseFailAlloc_2869_, 12, v_testDriver_2845_);
lean_ctor_set(v_reuseFailAlloc_2869_, 13, v_testDriverArgs_2846_);
lean_ctor_set(v_reuseFailAlloc_2869_, 14, v_lintDriver_2847_);
lean_ctor_set(v_reuseFailAlloc_2869_, 15, v_lintDriverArgs_2848_);
lean_ctor_set(v_reuseFailAlloc_2869_, 16, v_version_2849_);
lean_ctor_set(v_reuseFailAlloc_2869_, 17, v_versionTags_2850_);
lean_ctor_set(v_reuseFailAlloc_2869_, 18, v_description_2851_);
lean_ctor_set(v_reuseFailAlloc_2869_, 19, v_keywords_2852_);
lean_ctor_set(v_reuseFailAlloc_2869_, 20, v_homepage_2853_);
lean_ctor_set(v_reuseFailAlloc_2869_, 21, v_license_2854_);
lean_ctor_set(v_reuseFailAlloc_2869_, 22, v_licenseFiles_2855_);
lean_ctor_set(v_reuseFailAlloc_2869_, 23, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2869_, 24, v_enableArtifactCache_x3f_2858_);
lean_ctor_set(v_reuseFailAlloc_2869_, 25, v_restoreAllArtifacts_x3f_2859_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26, v_bootstrap_2832_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26 + 1, v_precompileModules_2834_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26 + 3, v_reservoir_2857_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2860_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26 + 5, v_allowImportAll_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*26 + 6, v_fixedToolchain_2862_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* v_x_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0));
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* v_x_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lake_PackageConfig_readmeFile___proj___lam__3(v_x_2874_);
lean_dec_ref(v_x_2874_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_2885_, lean_object* v_n_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_2888_, lean_object* v_n_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2888_, v_n_2889_);
lean_dec(v_n_2889_);
lean_dec(v_p_2888_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_2891_, lean_object* v_n_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2891_, v_n_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_2894_, lean_object* v_n_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_2894_, v_n_2895_);
lean_dec(v_n_2895_);
lean_dec(v_p_2894_);
return v_res_2896_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* v_cfg_2897_){
_start:
{
uint8_t v_reservoir_2898_; 
v_reservoir_2898_ = lean_ctor_get_uint8(v_cfg_2897_, sizeof(void*)*26 + 3);
return v_reservoir_2898_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* v_cfg_2899_){
_start:
{
uint8_t v_res_2900_; lean_object* v_r_2901_; 
v_res_2900_ = l_Lake_PackageConfig_reservoir___proj___lam__0(v_cfg_2899_);
lean_dec_ref(v_cfg_2899_);
v_r_2901_ = lean_box(v_res_2900_);
return v_r_2901_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t v_val_2902_, lean_object* v_cfg_2903_){
_start:
{
lean_object* v_toWorkspaceConfig_2904_; lean_object* v_toLeanConfig_2905_; uint8_t v_bootstrap_2906_; lean_object* v_extraDepTargets_2907_; uint8_t v_precompileModules_2908_; lean_object* v_moreGlobalServerArgs_2909_; lean_object* v_srcDir_2910_; lean_object* v_buildDir_2911_; lean_object* v_leanLibDir_2912_; lean_object* v_nativeLibDir_2913_; lean_object* v_binDir_2914_; lean_object* v_irDir_2915_; lean_object* v_releaseRepo_2916_; lean_object* v_buildArchive_2917_; uint8_t v_preferReleaseBuild_2918_; lean_object* v_testDriver_2919_; lean_object* v_testDriverArgs_2920_; lean_object* v_lintDriver_2921_; lean_object* v_lintDriverArgs_2922_; lean_object* v_version_2923_; lean_object* v_versionTags_2924_; lean_object* v_description_2925_; lean_object* v_keywords_2926_; lean_object* v_homepage_2927_; lean_object* v_license_2928_; lean_object* v_licenseFiles_2929_; lean_object* v_readmeFile_2930_; lean_object* v_enableArtifactCache_x3f_2931_; lean_object* v_restoreAllArtifacts_x3f_2932_; uint8_t v_libPrefixOnWindows_2933_; uint8_t v_allowImportAll_2934_; uint8_t v_fixedToolchain_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
v_toWorkspaceConfig_2904_ = lean_ctor_get(v_cfg_2903_, 0);
v_toLeanConfig_2905_ = lean_ctor_get(v_cfg_2903_, 1);
v_bootstrap_2906_ = lean_ctor_get_uint8(v_cfg_2903_, sizeof(void*)*26);
v_extraDepTargets_2907_ = lean_ctor_get(v_cfg_2903_, 2);
v_precompileModules_2908_ = lean_ctor_get_uint8(v_cfg_2903_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2909_ = lean_ctor_get(v_cfg_2903_, 3);
v_srcDir_2910_ = lean_ctor_get(v_cfg_2903_, 4);
v_buildDir_2911_ = lean_ctor_get(v_cfg_2903_, 5);
v_leanLibDir_2912_ = lean_ctor_get(v_cfg_2903_, 6);
v_nativeLibDir_2913_ = lean_ctor_get(v_cfg_2903_, 7);
v_binDir_2914_ = lean_ctor_get(v_cfg_2903_, 8);
v_irDir_2915_ = lean_ctor_get(v_cfg_2903_, 9);
v_releaseRepo_2916_ = lean_ctor_get(v_cfg_2903_, 10);
v_buildArchive_2917_ = lean_ctor_get(v_cfg_2903_, 11);
v_preferReleaseBuild_2918_ = lean_ctor_get_uint8(v_cfg_2903_, sizeof(void*)*26 + 2);
v_testDriver_2919_ = lean_ctor_get(v_cfg_2903_, 12);
v_testDriverArgs_2920_ = lean_ctor_get(v_cfg_2903_, 13);
v_lintDriver_2921_ = lean_ctor_get(v_cfg_2903_, 14);
v_lintDriverArgs_2922_ = lean_ctor_get(v_cfg_2903_, 15);
v_version_2923_ = lean_ctor_get(v_cfg_2903_, 16);
v_versionTags_2924_ = lean_ctor_get(v_cfg_2903_, 17);
v_description_2925_ = lean_ctor_get(v_cfg_2903_, 18);
v_keywords_2926_ = lean_ctor_get(v_cfg_2903_, 19);
v_homepage_2927_ = lean_ctor_get(v_cfg_2903_, 20);
v_license_2928_ = lean_ctor_get(v_cfg_2903_, 21);
v_licenseFiles_2929_ = lean_ctor_get(v_cfg_2903_, 22);
v_readmeFile_2930_ = lean_ctor_get(v_cfg_2903_, 23);
v_enableArtifactCache_x3f_2931_ = lean_ctor_get(v_cfg_2903_, 24);
v_restoreAllArtifacts_x3f_2932_ = lean_ctor_get(v_cfg_2903_, 25);
v_libPrefixOnWindows_2933_ = lean_ctor_get_uint8(v_cfg_2903_, sizeof(void*)*26 + 4);
v_allowImportAll_2934_ = lean_ctor_get_uint8(v_cfg_2903_, sizeof(void*)*26 + 5);
v_fixedToolchain_2935_ = lean_ctor_get_uint8(v_cfg_2903_, sizeof(void*)*26 + 6);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_cfg_2903_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v_cfg_2903_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2932_);
lean_inc(v_enableArtifactCache_x3f_2931_);
lean_inc(v_readmeFile_2930_);
lean_inc(v_licenseFiles_2929_);
lean_inc(v_license_2928_);
lean_inc(v_homepage_2927_);
lean_inc(v_keywords_2926_);
lean_inc(v_description_2925_);
lean_inc(v_versionTags_2924_);
lean_inc(v_version_2923_);
lean_inc(v_lintDriverArgs_2922_);
lean_inc(v_lintDriver_2921_);
lean_inc(v_testDriverArgs_2920_);
lean_inc(v_testDriver_2919_);
lean_inc(v_buildArchive_2917_);
lean_inc(v_releaseRepo_2916_);
lean_inc(v_irDir_2915_);
lean_inc(v_binDir_2914_);
lean_inc(v_nativeLibDir_2913_);
lean_inc(v_leanLibDir_2912_);
lean_inc(v_buildDir_2911_);
lean_inc(v_srcDir_2910_);
lean_inc(v_moreGlobalServerArgs_2909_);
lean_inc(v_extraDepTargets_2907_);
lean_inc(v_toLeanConfig_2905_);
lean_inc(v_toWorkspaceConfig_2904_);
lean_dec(v_cfg_2903_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_toWorkspaceConfig_2904_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_toLeanConfig_2905_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v_extraDepTargets_2907_);
lean_ctor_set(v_reuseFailAlloc_2941_, 3, v_moreGlobalServerArgs_2909_);
lean_ctor_set(v_reuseFailAlloc_2941_, 4, v_srcDir_2910_);
lean_ctor_set(v_reuseFailAlloc_2941_, 5, v_buildDir_2911_);
lean_ctor_set(v_reuseFailAlloc_2941_, 6, v_leanLibDir_2912_);
lean_ctor_set(v_reuseFailAlloc_2941_, 7, v_nativeLibDir_2913_);
lean_ctor_set(v_reuseFailAlloc_2941_, 8, v_binDir_2914_);
lean_ctor_set(v_reuseFailAlloc_2941_, 9, v_irDir_2915_);
lean_ctor_set(v_reuseFailAlloc_2941_, 10, v_releaseRepo_2916_);
lean_ctor_set(v_reuseFailAlloc_2941_, 11, v_buildArchive_2917_);
lean_ctor_set(v_reuseFailAlloc_2941_, 12, v_testDriver_2919_);
lean_ctor_set(v_reuseFailAlloc_2941_, 13, v_testDriverArgs_2920_);
lean_ctor_set(v_reuseFailAlloc_2941_, 14, v_lintDriver_2921_);
lean_ctor_set(v_reuseFailAlloc_2941_, 15, v_lintDriverArgs_2922_);
lean_ctor_set(v_reuseFailAlloc_2941_, 16, v_version_2923_);
lean_ctor_set(v_reuseFailAlloc_2941_, 17, v_versionTags_2924_);
lean_ctor_set(v_reuseFailAlloc_2941_, 18, v_description_2925_);
lean_ctor_set(v_reuseFailAlloc_2941_, 19, v_keywords_2926_);
lean_ctor_set(v_reuseFailAlloc_2941_, 20, v_homepage_2927_);
lean_ctor_set(v_reuseFailAlloc_2941_, 21, v_license_2928_);
lean_ctor_set(v_reuseFailAlloc_2941_, 22, v_licenseFiles_2929_);
lean_ctor_set(v_reuseFailAlloc_2941_, 23, v_readmeFile_2930_);
lean_ctor_set(v_reuseFailAlloc_2941_, 24, v_enableArtifactCache_x3f_2931_);
lean_ctor_set(v_reuseFailAlloc_2941_, 25, v_restoreAllArtifacts_x3f_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*26, v_bootstrap_2906_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*26 + 1, v_precompileModules_2908_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*26 + 5, v_allowImportAll_2934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*26 + 6, v_fixedToolchain_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_ctor_set_uint8(v___x_2940_, sizeof(void*)*26 + 3, v_val_2902_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* v_val_2943_, lean_object* v_cfg_2944_){
_start:
{
uint8_t v_val_134__boxed_2945_; lean_object* v_res_2946_; 
v_val_134__boxed_2945_ = lean_unbox(v_val_2943_);
v_res_2946_ = l_Lake_PackageConfig_reservoir___proj___lam__1(v_val_134__boxed_2945_, v_cfg_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* v_f_2947_, lean_object* v_cfg_2948_){
_start:
{
lean_object* v_toWorkspaceConfig_2949_; lean_object* v_toLeanConfig_2950_; uint8_t v_bootstrap_2951_; lean_object* v_extraDepTargets_2952_; uint8_t v_precompileModules_2953_; lean_object* v_moreGlobalServerArgs_2954_; lean_object* v_srcDir_2955_; lean_object* v_buildDir_2956_; lean_object* v_leanLibDir_2957_; lean_object* v_nativeLibDir_2958_; lean_object* v_binDir_2959_; lean_object* v_irDir_2960_; lean_object* v_releaseRepo_2961_; lean_object* v_buildArchive_2962_; uint8_t v_preferReleaseBuild_2963_; lean_object* v_testDriver_2964_; lean_object* v_testDriverArgs_2965_; lean_object* v_lintDriver_2966_; lean_object* v_lintDriverArgs_2967_; lean_object* v_version_2968_; lean_object* v_versionTags_2969_; lean_object* v_description_2970_; lean_object* v_keywords_2971_; lean_object* v_homepage_2972_; lean_object* v_license_2973_; lean_object* v_licenseFiles_2974_; lean_object* v_readmeFile_2975_; uint8_t v_reservoir_2976_; lean_object* v_enableArtifactCache_x3f_2977_; lean_object* v_restoreAllArtifacts_x3f_2978_; uint8_t v_libPrefixOnWindows_2979_; uint8_t v_allowImportAll_2980_; uint8_t v_fixedToolchain_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2991_; 
v_toWorkspaceConfig_2949_ = lean_ctor_get(v_cfg_2948_, 0);
v_toLeanConfig_2950_ = lean_ctor_get(v_cfg_2948_, 1);
v_bootstrap_2951_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26);
v_extraDepTargets_2952_ = lean_ctor_get(v_cfg_2948_, 2);
v_precompileModules_2953_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2954_ = lean_ctor_get(v_cfg_2948_, 3);
v_srcDir_2955_ = lean_ctor_get(v_cfg_2948_, 4);
v_buildDir_2956_ = lean_ctor_get(v_cfg_2948_, 5);
v_leanLibDir_2957_ = lean_ctor_get(v_cfg_2948_, 6);
v_nativeLibDir_2958_ = lean_ctor_get(v_cfg_2948_, 7);
v_binDir_2959_ = lean_ctor_get(v_cfg_2948_, 8);
v_irDir_2960_ = lean_ctor_get(v_cfg_2948_, 9);
v_releaseRepo_2961_ = lean_ctor_get(v_cfg_2948_, 10);
v_buildArchive_2962_ = lean_ctor_get(v_cfg_2948_, 11);
v_preferReleaseBuild_2963_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26 + 2);
v_testDriver_2964_ = lean_ctor_get(v_cfg_2948_, 12);
v_testDriverArgs_2965_ = lean_ctor_get(v_cfg_2948_, 13);
v_lintDriver_2966_ = lean_ctor_get(v_cfg_2948_, 14);
v_lintDriverArgs_2967_ = lean_ctor_get(v_cfg_2948_, 15);
v_version_2968_ = lean_ctor_get(v_cfg_2948_, 16);
v_versionTags_2969_ = lean_ctor_get(v_cfg_2948_, 17);
v_description_2970_ = lean_ctor_get(v_cfg_2948_, 18);
v_keywords_2971_ = lean_ctor_get(v_cfg_2948_, 19);
v_homepage_2972_ = lean_ctor_get(v_cfg_2948_, 20);
v_license_2973_ = lean_ctor_get(v_cfg_2948_, 21);
v_licenseFiles_2974_ = lean_ctor_get(v_cfg_2948_, 22);
v_readmeFile_2975_ = lean_ctor_get(v_cfg_2948_, 23);
v_reservoir_2976_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2977_ = lean_ctor_get(v_cfg_2948_, 24);
v_restoreAllArtifacts_x3f_2978_ = lean_ctor_get(v_cfg_2948_, 25);
v_libPrefixOnWindows_2979_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26 + 4);
v_allowImportAll_2980_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26 + 5);
v_fixedToolchain_2981_ = lean_ctor_get_uint8(v_cfg_2948_, sizeof(void*)*26 + 6);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_cfg_2948_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2983_ = v_cfg_2948_;
v_isShared_2984_ = v_isSharedCheck_2991_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2978_);
lean_inc(v_enableArtifactCache_x3f_2977_);
lean_inc(v_readmeFile_2975_);
lean_inc(v_licenseFiles_2974_);
lean_inc(v_license_2973_);
lean_inc(v_homepage_2972_);
lean_inc(v_keywords_2971_);
lean_inc(v_description_2970_);
lean_inc(v_versionTags_2969_);
lean_inc(v_version_2968_);
lean_inc(v_lintDriverArgs_2967_);
lean_inc(v_lintDriver_2966_);
lean_inc(v_testDriverArgs_2965_);
lean_inc(v_testDriver_2964_);
lean_inc(v_buildArchive_2962_);
lean_inc(v_releaseRepo_2961_);
lean_inc(v_irDir_2960_);
lean_inc(v_binDir_2959_);
lean_inc(v_nativeLibDir_2958_);
lean_inc(v_leanLibDir_2957_);
lean_inc(v_buildDir_2956_);
lean_inc(v_srcDir_2955_);
lean_inc(v_moreGlobalServerArgs_2954_);
lean_inc(v_extraDepTargets_2952_);
lean_inc(v_toLeanConfig_2950_);
lean_inc(v_toWorkspaceConfig_2949_);
lean_dec(v_cfg_2948_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2991_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2985_ = lean_box(v_reservoir_2976_);
v___x_2986_ = lean_apply_1(v_f_2947_, v___x_2985_);
if (v_isShared_2984_ == 0)
{
v___x_2988_ = v___x_2983_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_toWorkspaceConfig_2949_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_toLeanConfig_2950_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_extraDepTargets_2952_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_moreGlobalServerArgs_2954_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_srcDir_2955_);
lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_buildDir_2956_);
lean_ctor_set(v_reuseFailAlloc_2990_, 6, v_leanLibDir_2957_);
lean_ctor_set(v_reuseFailAlloc_2990_, 7, v_nativeLibDir_2958_);
lean_ctor_set(v_reuseFailAlloc_2990_, 8, v_binDir_2959_);
lean_ctor_set(v_reuseFailAlloc_2990_, 9, v_irDir_2960_);
lean_ctor_set(v_reuseFailAlloc_2990_, 10, v_releaseRepo_2961_);
lean_ctor_set(v_reuseFailAlloc_2990_, 11, v_buildArchive_2962_);
lean_ctor_set(v_reuseFailAlloc_2990_, 12, v_testDriver_2964_);
lean_ctor_set(v_reuseFailAlloc_2990_, 13, v_testDriverArgs_2965_);
lean_ctor_set(v_reuseFailAlloc_2990_, 14, v_lintDriver_2966_);
lean_ctor_set(v_reuseFailAlloc_2990_, 15, v_lintDriverArgs_2967_);
lean_ctor_set(v_reuseFailAlloc_2990_, 16, v_version_2968_);
lean_ctor_set(v_reuseFailAlloc_2990_, 17, v_versionTags_2969_);
lean_ctor_set(v_reuseFailAlloc_2990_, 18, v_description_2970_);
lean_ctor_set(v_reuseFailAlloc_2990_, 19, v_keywords_2971_);
lean_ctor_set(v_reuseFailAlloc_2990_, 20, v_homepage_2972_);
lean_ctor_set(v_reuseFailAlloc_2990_, 21, v_license_2973_);
lean_ctor_set(v_reuseFailAlloc_2990_, 22, v_licenseFiles_2974_);
lean_ctor_set(v_reuseFailAlloc_2990_, 23, v_readmeFile_2975_);
lean_ctor_set(v_reuseFailAlloc_2990_, 24, v_enableArtifactCache_x3f_2977_);
lean_ctor_set(v_reuseFailAlloc_2990_, 25, v_restoreAllArtifacts_x3f_2978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*26, v_bootstrap_2951_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*26 + 1, v_precompileModules_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2963_);
v___x_2988_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_unbox(v___x_2986_);
lean_ctor_set_uint8(v___x_2988_, sizeof(void*)*26 + 3, v___x_2989_);
lean_ctor_set_uint8(v___x_2988_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2979_);
lean_ctor_set_uint8(v___x_2988_, sizeof(void*)*26 + 5, v_allowImportAll_2980_);
lean_ctor_set_uint8(v___x_2988_, sizeof(void*)*26 + 6, v_fixedToolchain_2981_);
return v___x_2988_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* v_x_2992_){
_start:
{
uint8_t v___x_2993_; 
v___x_2993_ = 1;
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* v_x_2994_){
_start:
{
uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_res_2995_ = l_Lake_PackageConfig_reservoir___proj___lam__3(v_x_2994_);
lean_dec_ref(v_x_2994_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3006_, lean_object* v_n_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3009_, lean_object* v_n_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lake_PackageConfig_reservoir___proj(v_p_3009_, v_n_3010_);
lean_dec(v_n_3010_);
lean_dec(v_p_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3012_, lean_object* v_n_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lake_PackageConfig_reservoir___proj(v_p_3012_, v_n_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3015_, lean_object* v_n_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3015_, v_n_3016_);
lean_dec(v_n_3016_);
lean_dec(v_p_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* v_cfg_3018_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3019_; 
v_enableArtifactCache_x3f_3019_ = lean_ctor_get(v_cfg_3018_, 24);
lean_inc(v_enableArtifactCache_x3f_3019_);
return v_enableArtifactCache_x3f_3019_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* v_cfg_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(v_cfg_3020_);
lean_dec_ref(v_cfg_3020_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* v_val_3022_, lean_object* v_cfg_3023_){
_start:
{
lean_object* v_toWorkspaceConfig_3024_; lean_object* v_toLeanConfig_3025_; uint8_t v_bootstrap_3026_; lean_object* v_extraDepTargets_3027_; uint8_t v_precompileModules_3028_; lean_object* v_moreGlobalServerArgs_3029_; lean_object* v_srcDir_3030_; lean_object* v_buildDir_3031_; lean_object* v_leanLibDir_3032_; lean_object* v_nativeLibDir_3033_; lean_object* v_binDir_3034_; lean_object* v_irDir_3035_; lean_object* v_releaseRepo_3036_; lean_object* v_buildArchive_3037_; uint8_t v_preferReleaseBuild_3038_; lean_object* v_testDriver_3039_; lean_object* v_testDriverArgs_3040_; lean_object* v_lintDriver_3041_; lean_object* v_lintDriverArgs_3042_; lean_object* v_version_3043_; lean_object* v_versionTags_3044_; lean_object* v_description_3045_; lean_object* v_keywords_3046_; lean_object* v_homepage_3047_; lean_object* v_license_3048_; lean_object* v_licenseFiles_3049_; lean_object* v_readmeFile_3050_; uint8_t v_reservoir_3051_; lean_object* v_restoreAllArtifacts_x3f_3052_; uint8_t v_libPrefixOnWindows_3053_; uint8_t v_allowImportAll_3054_; uint8_t v_fixedToolchain_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_toWorkspaceConfig_3024_ = lean_ctor_get(v_cfg_3023_, 0);
v_toLeanConfig_3025_ = lean_ctor_get(v_cfg_3023_, 1);
v_bootstrap_3026_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26);
v_extraDepTargets_3027_ = lean_ctor_get(v_cfg_3023_, 2);
v_precompileModules_3028_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3029_ = lean_ctor_get(v_cfg_3023_, 3);
v_srcDir_3030_ = lean_ctor_get(v_cfg_3023_, 4);
v_buildDir_3031_ = lean_ctor_get(v_cfg_3023_, 5);
v_leanLibDir_3032_ = lean_ctor_get(v_cfg_3023_, 6);
v_nativeLibDir_3033_ = lean_ctor_get(v_cfg_3023_, 7);
v_binDir_3034_ = lean_ctor_get(v_cfg_3023_, 8);
v_irDir_3035_ = lean_ctor_get(v_cfg_3023_, 9);
v_releaseRepo_3036_ = lean_ctor_get(v_cfg_3023_, 10);
v_buildArchive_3037_ = lean_ctor_get(v_cfg_3023_, 11);
v_preferReleaseBuild_3038_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26 + 2);
v_testDriver_3039_ = lean_ctor_get(v_cfg_3023_, 12);
v_testDriverArgs_3040_ = lean_ctor_get(v_cfg_3023_, 13);
v_lintDriver_3041_ = lean_ctor_get(v_cfg_3023_, 14);
v_lintDriverArgs_3042_ = lean_ctor_get(v_cfg_3023_, 15);
v_version_3043_ = lean_ctor_get(v_cfg_3023_, 16);
v_versionTags_3044_ = lean_ctor_get(v_cfg_3023_, 17);
v_description_3045_ = lean_ctor_get(v_cfg_3023_, 18);
v_keywords_3046_ = lean_ctor_get(v_cfg_3023_, 19);
v_homepage_3047_ = lean_ctor_get(v_cfg_3023_, 20);
v_license_3048_ = lean_ctor_get(v_cfg_3023_, 21);
v_licenseFiles_3049_ = lean_ctor_get(v_cfg_3023_, 22);
v_readmeFile_3050_ = lean_ctor_get(v_cfg_3023_, 23);
v_reservoir_3051_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26 + 3);
v_restoreAllArtifacts_x3f_3052_ = lean_ctor_get(v_cfg_3023_, 25);
v_libPrefixOnWindows_3053_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26 + 4);
v_allowImportAll_3054_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26 + 5);
v_fixedToolchain_3055_ = lean_ctor_get_uint8(v_cfg_3023_, sizeof(void*)*26 + 6);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_cfg_3023_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_cfg_3023_, 24);
lean_dec(v_unused_3063_);
v___x_3057_ = v_cfg_3023_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3052_);
lean_inc(v_readmeFile_3050_);
lean_inc(v_licenseFiles_3049_);
lean_inc(v_license_3048_);
lean_inc(v_homepage_3047_);
lean_inc(v_keywords_3046_);
lean_inc(v_description_3045_);
lean_inc(v_versionTags_3044_);
lean_inc(v_version_3043_);
lean_inc(v_lintDriverArgs_3042_);
lean_inc(v_lintDriver_3041_);
lean_inc(v_testDriverArgs_3040_);
lean_inc(v_testDriver_3039_);
lean_inc(v_buildArchive_3037_);
lean_inc(v_releaseRepo_3036_);
lean_inc(v_irDir_3035_);
lean_inc(v_binDir_3034_);
lean_inc(v_nativeLibDir_3033_);
lean_inc(v_leanLibDir_3032_);
lean_inc(v_buildDir_3031_);
lean_inc(v_srcDir_3030_);
lean_inc(v_moreGlobalServerArgs_3029_);
lean_inc(v_extraDepTargets_3027_);
lean_inc(v_toLeanConfig_3025_);
lean_inc(v_toWorkspaceConfig_3024_);
lean_dec(v_cfg_3023_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 24, v_val_3022_);
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_toWorkspaceConfig_3024_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_toLeanConfig_3025_);
lean_ctor_set(v_reuseFailAlloc_3061_, 2, v_extraDepTargets_3027_);
lean_ctor_set(v_reuseFailAlloc_3061_, 3, v_moreGlobalServerArgs_3029_);
lean_ctor_set(v_reuseFailAlloc_3061_, 4, v_srcDir_3030_);
lean_ctor_set(v_reuseFailAlloc_3061_, 5, v_buildDir_3031_);
lean_ctor_set(v_reuseFailAlloc_3061_, 6, v_leanLibDir_3032_);
lean_ctor_set(v_reuseFailAlloc_3061_, 7, v_nativeLibDir_3033_);
lean_ctor_set(v_reuseFailAlloc_3061_, 8, v_binDir_3034_);
lean_ctor_set(v_reuseFailAlloc_3061_, 9, v_irDir_3035_);
lean_ctor_set(v_reuseFailAlloc_3061_, 10, v_releaseRepo_3036_);
lean_ctor_set(v_reuseFailAlloc_3061_, 11, v_buildArchive_3037_);
lean_ctor_set(v_reuseFailAlloc_3061_, 12, v_testDriver_3039_);
lean_ctor_set(v_reuseFailAlloc_3061_, 13, v_testDriverArgs_3040_);
lean_ctor_set(v_reuseFailAlloc_3061_, 14, v_lintDriver_3041_);
lean_ctor_set(v_reuseFailAlloc_3061_, 15, v_lintDriverArgs_3042_);
lean_ctor_set(v_reuseFailAlloc_3061_, 16, v_version_3043_);
lean_ctor_set(v_reuseFailAlloc_3061_, 17, v_versionTags_3044_);
lean_ctor_set(v_reuseFailAlloc_3061_, 18, v_description_3045_);
lean_ctor_set(v_reuseFailAlloc_3061_, 19, v_keywords_3046_);
lean_ctor_set(v_reuseFailAlloc_3061_, 20, v_homepage_3047_);
lean_ctor_set(v_reuseFailAlloc_3061_, 21, v_license_3048_);
lean_ctor_set(v_reuseFailAlloc_3061_, 22, v_licenseFiles_3049_);
lean_ctor_set(v_reuseFailAlloc_3061_, 23, v_readmeFile_3050_);
lean_ctor_set(v_reuseFailAlloc_3061_, 24, v_val_3022_);
lean_ctor_set(v_reuseFailAlloc_3061_, 25, v_restoreAllArtifacts_x3f_3052_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26, v_bootstrap_3026_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26 + 1, v_precompileModules_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3038_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26 + 3, v_reservoir_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3053_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26 + 5, v_allowImportAll_3054_);
lean_ctor_set_uint8(v_reuseFailAlloc_3061_, sizeof(void*)*26 + 6, v_fixedToolchain_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* v_f_3064_, lean_object* v_cfg_3065_){
_start:
{
lean_object* v_toWorkspaceConfig_3066_; lean_object* v_toLeanConfig_3067_; uint8_t v_bootstrap_3068_; lean_object* v_extraDepTargets_3069_; uint8_t v_precompileModules_3070_; lean_object* v_moreGlobalServerArgs_3071_; lean_object* v_srcDir_3072_; lean_object* v_buildDir_3073_; lean_object* v_leanLibDir_3074_; lean_object* v_nativeLibDir_3075_; lean_object* v_binDir_3076_; lean_object* v_irDir_3077_; lean_object* v_releaseRepo_3078_; lean_object* v_buildArchive_3079_; uint8_t v_preferReleaseBuild_3080_; lean_object* v_testDriver_3081_; lean_object* v_testDriverArgs_3082_; lean_object* v_lintDriver_3083_; lean_object* v_lintDriverArgs_3084_; lean_object* v_version_3085_; lean_object* v_versionTags_3086_; lean_object* v_description_3087_; lean_object* v_keywords_3088_; lean_object* v_homepage_3089_; lean_object* v_license_3090_; lean_object* v_licenseFiles_3091_; lean_object* v_readmeFile_3092_; uint8_t v_reservoir_3093_; lean_object* v_enableArtifactCache_x3f_3094_; lean_object* v_restoreAllArtifacts_x3f_3095_; uint8_t v_libPrefixOnWindows_3096_; uint8_t v_allowImportAll_3097_; uint8_t v_fixedToolchain_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3106_; 
v_toWorkspaceConfig_3066_ = lean_ctor_get(v_cfg_3065_, 0);
v_toLeanConfig_3067_ = lean_ctor_get(v_cfg_3065_, 1);
v_bootstrap_3068_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26);
v_extraDepTargets_3069_ = lean_ctor_get(v_cfg_3065_, 2);
v_precompileModules_3070_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3071_ = lean_ctor_get(v_cfg_3065_, 3);
v_srcDir_3072_ = lean_ctor_get(v_cfg_3065_, 4);
v_buildDir_3073_ = lean_ctor_get(v_cfg_3065_, 5);
v_leanLibDir_3074_ = lean_ctor_get(v_cfg_3065_, 6);
v_nativeLibDir_3075_ = lean_ctor_get(v_cfg_3065_, 7);
v_binDir_3076_ = lean_ctor_get(v_cfg_3065_, 8);
v_irDir_3077_ = lean_ctor_get(v_cfg_3065_, 9);
v_releaseRepo_3078_ = lean_ctor_get(v_cfg_3065_, 10);
v_buildArchive_3079_ = lean_ctor_get(v_cfg_3065_, 11);
v_preferReleaseBuild_3080_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26 + 2);
v_testDriver_3081_ = lean_ctor_get(v_cfg_3065_, 12);
v_testDriverArgs_3082_ = lean_ctor_get(v_cfg_3065_, 13);
v_lintDriver_3083_ = lean_ctor_get(v_cfg_3065_, 14);
v_lintDriverArgs_3084_ = lean_ctor_get(v_cfg_3065_, 15);
v_version_3085_ = lean_ctor_get(v_cfg_3065_, 16);
v_versionTags_3086_ = lean_ctor_get(v_cfg_3065_, 17);
v_description_3087_ = lean_ctor_get(v_cfg_3065_, 18);
v_keywords_3088_ = lean_ctor_get(v_cfg_3065_, 19);
v_homepage_3089_ = lean_ctor_get(v_cfg_3065_, 20);
v_license_3090_ = lean_ctor_get(v_cfg_3065_, 21);
v_licenseFiles_3091_ = lean_ctor_get(v_cfg_3065_, 22);
v_readmeFile_3092_ = lean_ctor_get(v_cfg_3065_, 23);
v_reservoir_3093_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3094_ = lean_ctor_get(v_cfg_3065_, 24);
v_restoreAllArtifacts_x3f_3095_ = lean_ctor_get(v_cfg_3065_, 25);
v_libPrefixOnWindows_3096_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26 + 4);
v_allowImportAll_3097_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26 + 5);
v_fixedToolchain_3098_ = lean_ctor_get_uint8(v_cfg_3065_, sizeof(void*)*26 + 6);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_cfg_3065_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3100_ = v_cfg_3065_;
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3095_);
lean_inc(v_enableArtifactCache_x3f_3094_);
lean_inc(v_readmeFile_3092_);
lean_inc(v_licenseFiles_3091_);
lean_inc(v_license_3090_);
lean_inc(v_homepage_3089_);
lean_inc(v_keywords_3088_);
lean_inc(v_description_3087_);
lean_inc(v_versionTags_3086_);
lean_inc(v_version_3085_);
lean_inc(v_lintDriverArgs_3084_);
lean_inc(v_lintDriver_3083_);
lean_inc(v_testDriverArgs_3082_);
lean_inc(v_testDriver_3081_);
lean_inc(v_buildArchive_3079_);
lean_inc(v_releaseRepo_3078_);
lean_inc(v_irDir_3077_);
lean_inc(v_binDir_3076_);
lean_inc(v_nativeLibDir_3075_);
lean_inc(v_leanLibDir_3074_);
lean_inc(v_buildDir_3073_);
lean_inc(v_srcDir_3072_);
lean_inc(v_moreGlobalServerArgs_3071_);
lean_inc(v_extraDepTargets_3069_);
lean_inc(v_toLeanConfig_3067_);
lean_inc(v_toWorkspaceConfig_3066_);
lean_dec(v_cfg_3065_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_apply_1(v_f_3064_, v_enableArtifactCache_x3f_3094_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 24, v___x_3102_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_toWorkspaceConfig_3066_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_toLeanConfig_3067_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_extraDepTargets_3069_);
lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_moreGlobalServerArgs_3071_);
lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_srcDir_3072_);
lean_ctor_set(v_reuseFailAlloc_3105_, 5, v_buildDir_3073_);
lean_ctor_set(v_reuseFailAlloc_3105_, 6, v_leanLibDir_3074_);
lean_ctor_set(v_reuseFailAlloc_3105_, 7, v_nativeLibDir_3075_);
lean_ctor_set(v_reuseFailAlloc_3105_, 8, v_binDir_3076_);
lean_ctor_set(v_reuseFailAlloc_3105_, 9, v_irDir_3077_);
lean_ctor_set(v_reuseFailAlloc_3105_, 10, v_releaseRepo_3078_);
lean_ctor_set(v_reuseFailAlloc_3105_, 11, v_buildArchive_3079_);
lean_ctor_set(v_reuseFailAlloc_3105_, 12, v_testDriver_3081_);
lean_ctor_set(v_reuseFailAlloc_3105_, 13, v_testDriverArgs_3082_);
lean_ctor_set(v_reuseFailAlloc_3105_, 14, v_lintDriver_3083_);
lean_ctor_set(v_reuseFailAlloc_3105_, 15, v_lintDriverArgs_3084_);
lean_ctor_set(v_reuseFailAlloc_3105_, 16, v_version_3085_);
lean_ctor_set(v_reuseFailAlloc_3105_, 17, v_versionTags_3086_);
lean_ctor_set(v_reuseFailAlloc_3105_, 18, v_description_3087_);
lean_ctor_set(v_reuseFailAlloc_3105_, 19, v_keywords_3088_);
lean_ctor_set(v_reuseFailAlloc_3105_, 20, v_homepage_3089_);
lean_ctor_set(v_reuseFailAlloc_3105_, 21, v_license_3090_);
lean_ctor_set(v_reuseFailAlloc_3105_, 22, v_licenseFiles_3091_);
lean_ctor_set(v_reuseFailAlloc_3105_, 23, v_readmeFile_3092_);
lean_ctor_set(v_reuseFailAlloc_3105_, 24, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3105_, 25, v_restoreAllArtifacts_x3f_3095_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26, v_bootstrap_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26 + 1, v_precompileModules_3070_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3080_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26 + 3, v_reservoir_3093_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3096_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26 + 5, v_allowImportAll_3097_);
lean_ctor_set_uint8(v_reuseFailAlloc_3105_, sizeof(void*)*26 + 6, v_fixedToolchain_3098_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* v_x_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_box(0);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* v_x_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(v_x_3109_);
lean_dec_ref(v_x_3109_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3120_, lean_object* v_n_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3123_, lean_object* v_n_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3123_, v_n_3124_);
lean_dec(v_n_3124_);
lean_dec(v_p_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3126_, lean_object* v_n_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3126_, v_n_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3129_, lean_object* v_n_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3129_, v_n_3130_);
lean_dec(v_n_3130_);
lean_dec(v_p_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3132_, lean_object* v_n_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3132_, v_n_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3135_, lean_object* v_n_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3135_, v_n_3136_);
lean_dec(v_n_3136_);
lean_dec(v_p_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object* v_cfg_3138_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3139_; 
v_restoreAllArtifacts_x3f_3139_ = lean_ctor_get(v_cfg_3138_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3139_);
return v_restoreAllArtifacts_x3f_3139_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object* v_cfg_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(v_cfg_3140_);
lean_dec_ref(v_cfg_3140_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object* v_val_3142_, lean_object* v_cfg_3143_){
_start:
{
lean_object* v_toWorkspaceConfig_3144_; lean_object* v_toLeanConfig_3145_; uint8_t v_bootstrap_3146_; lean_object* v_extraDepTargets_3147_; uint8_t v_precompileModules_3148_; lean_object* v_moreGlobalServerArgs_3149_; lean_object* v_srcDir_3150_; lean_object* v_buildDir_3151_; lean_object* v_leanLibDir_3152_; lean_object* v_nativeLibDir_3153_; lean_object* v_binDir_3154_; lean_object* v_irDir_3155_; lean_object* v_releaseRepo_3156_; lean_object* v_buildArchive_3157_; uint8_t v_preferReleaseBuild_3158_; lean_object* v_testDriver_3159_; lean_object* v_testDriverArgs_3160_; lean_object* v_lintDriver_3161_; lean_object* v_lintDriverArgs_3162_; lean_object* v_version_3163_; lean_object* v_versionTags_3164_; lean_object* v_description_3165_; lean_object* v_keywords_3166_; lean_object* v_homepage_3167_; lean_object* v_license_3168_; lean_object* v_licenseFiles_3169_; lean_object* v_readmeFile_3170_; uint8_t v_reservoir_3171_; lean_object* v_enableArtifactCache_x3f_3172_; uint8_t v_libPrefixOnWindows_3173_; uint8_t v_allowImportAll_3174_; uint8_t v_fixedToolchain_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
v_toWorkspaceConfig_3144_ = lean_ctor_get(v_cfg_3143_, 0);
v_toLeanConfig_3145_ = lean_ctor_get(v_cfg_3143_, 1);
v_bootstrap_3146_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26);
v_extraDepTargets_3147_ = lean_ctor_get(v_cfg_3143_, 2);
v_precompileModules_3148_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3149_ = lean_ctor_get(v_cfg_3143_, 3);
v_srcDir_3150_ = lean_ctor_get(v_cfg_3143_, 4);
v_buildDir_3151_ = lean_ctor_get(v_cfg_3143_, 5);
v_leanLibDir_3152_ = lean_ctor_get(v_cfg_3143_, 6);
v_nativeLibDir_3153_ = lean_ctor_get(v_cfg_3143_, 7);
v_binDir_3154_ = lean_ctor_get(v_cfg_3143_, 8);
v_irDir_3155_ = lean_ctor_get(v_cfg_3143_, 9);
v_releaseRepo_3156_ = lean_ctor_get(v_cfg_3143_, 10);
v_buildArchive_3157_ = lean_ctor_get(v_cfg_3143_, 11);
v_preferReleaseBuild_3158_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26 + 2);
v_testDriver_3159_ = lean_ctor_get(v_cfg_3143_, 12);
v_testDriverArgs_3160_ = lean_ctor_get(v_cfg_3143_, 13);
v_lintDriver_3161_ = lean_ctor_get(v_cfg_3143_, 14);
v_lintDriverArgs_3162_ = lean_ctor_get(v_cfg_3143_, 15);
v_version_3163_ = lean_ctor_get(v_cfg_3143_, 16);
v_versionTags_3164_ = lean_ctor_get(v_cfg_3143_, 17);
v_description_3165_ = lean_ctor_get(v_cfg_3143_, 18);
v_keywords_3166_ = lean_ctor_get(v_cfg_3143_, 19);
v_homepage_3167_ = lean_ctor_get(v_cfg_3143_, 20);
v_license_3168_ = lean_ctor_get(v_cfg_3143_, 21);
v_licenseFiles_3169_ = lean_ctor_get(v_cfg_3143_, 22);
v_readmeFile_3170_ = lean_ctor_get(v_cfg_3143_, 23);
v_reservoir_3171_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3172_ = lean_ctor_get(v_cfg_3143_, 24);
v_libPrefixOnWindows_3173_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26 + 4);
v_allowImportAll_3174_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26 + 5);
v_fixedToolchain_3175_ = lean_ctor_get_uint8(v_cfg_3143_, sizeof(void*)*26 + 6);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_cfg_3143_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v_cfg_3143_, 25);
lean_dec(v_unused_3183_);
v___x_3177_ = v_cfg_3143_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_enableArtifactCache_x3f_3172_);
lean_inc(v_readmeFile_3170_);
lean_inc(v_licenseFiles_3169_);
lean_inc(v_license_3168_);
lean_inc(v_homepage_3167_);
lean_inc(v_keywords_3166_);
lean_inc(v_description_3165_);
lean_inc(v_versionTags_3164_);
lean_inc(v_version_3163_);
lean_inc(v_lintDriverArgs_3162_);
lean_inc(v_lintDriver_3161_);
lean_inc(v_testDriverArgs_3160_);
lean_inc(v_testDriver_3159_);
lean_inc(v_buildArchive_3157_);
lean_inc(v_releaseRepo_3156_);
lean_inc(v_irDir_3155_);
lean_inc(v_binDir_3154_);
lean_inc(v_nativeLibDir_3153_);
lean_inc(v_leanLibDir_3152_);
lean_inc(v_buildDir_3151_);
lean_inc(v_srcDir_3150_);
lean_inc(v_moreGlobalServerArgs_3149_);
lean_inc(v_extraDepTargets_3147_);
lean_inc(v_toLeanConfig_3145_);
lean_inc(v_toWorkspaceConfig_3144_);
lean_dec(v_cfg_3143_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 25, v_val_3142_);
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_toWorkspaceConfig_3144_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_toLeanConfig_3145_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_extraDepTargets_3147_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v_moreGlobalServerArgs_3149_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_srcDir_3150_);
lean_ctor_set(v_reuseFailAlloc_3181_, 5, v_buildDir_3151_);
lean_ctor_set(v_reuseFailAlloc_3181_, 6, v_leanLibDir_3152_);
lean_ctor_set(v_reuseFailAlloc_3181_, 7, v_nativeLibDir_3153_);
lean_ctor_set(v_reuseFailAlloc_3181_, 8, v_binDir_3154_);
lean_ctor_set(v_reuseFailAlloc_3181_, 9, v_irDir_3155_);
lean_ctor_set(v_reuseFailAlloc_3181_, 10, v_releaseRepo_3156_);
lean_ctor_set(v_reuseFailAlloc_3181_, 11, v_buildArchive_3157_);
lean_ctor_set(v_reuseFailAlloc_3181_, 12, v_testDriver_3159_);
lean_ctor_set(v_reuseFailAlloc_3181_, 13, v_testDriverArgs_3160_);
lean_ctor_set(v_reuseFailAlloc_3181_, 14, v_lintDriver_3161_);
lean_ctor_set(v_reuseFailAlloc_3181_, 15, v_lintDriverArgs_3162_);
lean_ctor_set(v_reuseFailAlloc_3181_, 16, v_version_3163_);
lean_ctor_set(v_reuseFailAlloc_3181_, 17, v_versionTags_3164_);
lean_ctor_set(v_reuseFailAlloc_3181_, 18, v_description_3165_);
lean_ctor_set(v_reuseFailAlloc_3181_, 19, v_keywords_3166_);
lean_ctor_set(v_reuseFailAlloc_3181_, 20, v_homepage_3167_);
lean_ctor_set(v_reuseFailAlloc_3181_, 21, v_license_3168_);
lean_ctor_set(v_reuseFailAlloc_3181_, 22, v_licenseFiles_3169_);
lean_ctor_set(v_reuseFailAlloc_3181_, 23, v_readmeFile_3170_);
lean_ctor_set(v_reuseFailAlloc_3181_, 24, v_enableArtifactCache_x3f_3172_);
lean_ctor_set(v_reuseFailAlloc_3181_, 25, v_val_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26, v_bootstrap_3146_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26 + 1, v_precompileModules_3148_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3158_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26 + 3, v_reservoir_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26 + 5, v_allowImportAll_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3181_, sizeof(void*)*26 + 6, v_fixedToolchain_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object* v_f_3184_, lean_object* v_cfg_3185_){
_start:
{
lean_object* v_toWorkspaceConfig_3186_; lean_object* v_toLeanConfig_3187_; uint8_t v_bootstrap_3188_; lean_object* v_extraDepTargets_3189_; uint8_t v_precompileModules_3190_; lean_object* v_moreGlobalServerArgs_3191_; lean_object* v_srcDir_3192_; lean_object* v_buildDir_3193_; lean_object* v_leanLibDir_3194_; lean_object* v_nativeLibDir_3195_; lean_object* v_binDir_3196_; lean_object* v_irDir_3197_; lean_object* v_releaseRepo_3198_; lean_object* v_buildArchive_3199_; uint8_t v_preferReleaseBuild_3200_; lean_object* v_testDriver_3201_; lean_object* v_testDriverArgs_3202_; lean_object* v_lintDriver_3203_; lean_object* v_lintDriverArgs_3204_; lean_object* v_version_3205_; lean_object* v_versionTags_3206_; lean_object* v_description_3207_; lean_object* v_keywords_3208_; lean_object* v_homepage_3209_; lean_object* v_license_3210_; lean_object* v_licenseFiles_3211_; lean_object* v_readmeFile_3212_; uint8_t v_reservoir_3213_; lean_object* v_enableArtifactCache_x3f_3214_; lean_object* v_restoreAllArtifacts_x3f_3215_; uint8_t v_libPrefixOnWindows_3216_; uint8_t v_allowImportAll_3217_; uint8_t v_fixedToolchain_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3226_; 
v_toWorkspaceConfig_3186_ = lean_ctor_get(v_cfg_3185_, 0);
v_toLeanConfig_3187_ = lean_ctor_get(v_cfg_3185_, 1);
v_bootstrap_3188_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26);
v_extraDepTargets_3189_ = lean_ctor_get(v_cfg_3185_, 2);
v_precompileModules_3190_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3191_ = lean_ctor_get(v_cfg_3185_, 3);
v_srcDir_3192_ = lean_ctor_get(v_cfg_3185_, 4);
v_buildDir_3193_ = lean_ctor_get(v_cfg_3185_, 5);
v_leanLibDir_3194_ = lean_ctor_get(v_cfg_3185_, 6);
v_nativeLibDir_3195_ = lean_ctor_get(v_cfg_3185_, 7);
v_binDir_3196_ = lean_ctor_get(v_cfg_3185_, 8);
v_irDir_3197_ = lean_ctor_get(v_cfg_3185_, 9);
v_releaseRepo_3198_ = lean_ctor_get(v_cfg_3185_, 10);
v_buildArchive_3199_ = lean_ctor_get(v_cfg_3185_, 11);
v_preferReleaseBuild_3200_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26 + 2);
v_testDriver_3201_ = lean_ctor_get(v_cfg_3185_, 12);
v_testDriverArgs_3202_ = lean_ctor_get(v_cfg_3185_, 13);
v_lintDriver_3203_ = lean_ctor_get(v_cfg_3185_, 14);
v_lintDriverArgs_3204_ = lean_ctor_get(v_cfg_3185_, 15);
v_version_3205_ = lean_ctor_get(v_cfg_3185_, 16);
v_versionTags_3206_ = lean_ctor_get(v_cfg_3185_, 17);
v_description_3207_ = lean_ctor_get(v_cfg_3185_, 18);
v_keywords_3208_ = lean_ctor_get(v_cfg_3185_, 19);
v_homepage_3209_ = lean_ctor_get(v_cfg_3185_, 20);
v_license_3210_ = lean_ctor_get(v_cfg_3185_, 21);
v_licenseFiles_3211_ = lean_ctor_get(v_cfg_3185_, 22);
v_readmeFile_3212_ = lean_ctor_get(v_cfg_3185_, 23);
v_reservoir_3213_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3214_ = lean_ctor_get(v_cfg_3185_, 24);
v_restoreAllArtifacts_x3f_3215_ = lean_ctor_get(v_cfg_3185_, 25);
v_libPrefixOnWindows_3216_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26 + 4);
v_allowImportAll_3217_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26 + 5);
v_fixedToolchain_3218_ = lean_ctor_get_uint8(v_cfg_3185_, sizeof(void*)*26 + 6);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_cfg_3185_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3220_ = v_cfg_3185_;
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3215_);
lean_inc(v_enableArtifactCache_x3f_3214_);
lean_inc(v_readmeFile_3212_);
lean_inc(v_licenseFiles_3211_);
lean_inc(v_license_3210_);
lean_inc(v_homepage_3209_);
lean_inc(v_keywords_3208_);
lean_inc(v_description_3207_);
lean_inc(v_versionTags_3206_);
lean_inc(v_version_3205_);
lean_inc(v_lintDriverArgs_3204_);
lean_inc(v_lintDriver_3203_);
lean_inc(v_testDriverArgs_3202_);
lean_inc(v_testDriver_3201_);
lean_inc(v_buildArchive_3199_);
lean_inc(v_releaseRepo_3198_);
lean_inc(v_irDir_3197_);
lean_inc(v_binDir_3196_);
lean_inc(v_nativeLibDir_3195_);
lean_inc(v_leanLibDir_3194_);
lean_inc(v_buildDir_3193_);
lean_inc(v_srcDir_3192_);
lean_inc(v_moreGlobalServerArgs_3191_);
lean_inc(v_extraDepTargets_3189_);
lean_inc(v_toLeanConfig_3187_);
lean_inc(v_toWorkspaceConfig_3186_);
lean_dec(v_cfg_3185_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_apply_1(v_f_3184_, v_restoreAllArtifacts_x3f_3215_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 25, v___x_3222_);
v___x_3224_ = v___x_3220_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_toWorkspaceConfig_3186_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_toLeanConfig_3187_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_extraDepTargets_3189_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_moreGlobalServerArgs_3191_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_srcDir_3192_);
lean_ctor_set(v_reuseFailAlloc_3225_, 5, v_buildDir_3193_);
lean_ctor_set(v_reuseFailAlloc_3225_, 6, v_leanLibDir_3194_);
lean_ctor_set(v_reuseFailAlloc_3225_, 7, v_nativeLibDir_3195_);
lean_ctor_set(v_reuseFailAlloc_3225_, 8, v_binDir_3196_);
lean_ctor_set(v_reuseFailAlloc_3225_, 9, v_irDir_3197_);
lean_ctor_set(v_reuseFailAlloc_3225_, 10, v_releaseRepo_3198_);
lean_ctor_set(v_reuseFailAlloc_3225_, 11, v_buildArchive_3199_);
lean_ctor_set(v_reuseFailAlloc_3225_, 12, v_testDriver_3201_);
lean_ctor_set(v_reuseFailAlloc_3225_, 13, v_testDriverArgs_3202_);
lean_ctor_set(v_reuseFailAlloc_3225_, 14, v_lintDriver_3203_);
lean_ctor_set(v_reuseFailAlloc_3225_, 15, v_lintDriverArgs_3204_);
lean_ctor_set(v_reuseFailAlloc_3225_, 16, v_version_3205_);
lean_ctor_set(v_reuseFailAlloc_3225_, 17, v_versionTags_3206_);
lean_ctor_set(v_reuseFailAlloc_3225_, 18, v_description_3207_);
lean_ctor_set(v_reuseFailAlloc_3225_, 19, v_keywords_3208_);
lean_ctor_set(v_reuseFailAlloc_3225_, 20, v_homepage_3209_);
lean_ctor_set(v_reuseFailAlloc_3225_, 21, v_license_3210_);
lean_ctor_set(v_reuseFailAlloc_3225_, 22, v_licenseFiles_3211_);
lean_ctor_set(v_reuseFailAlloc_3225_, 23, v_readmeFile_3212_);
lean_ctor_set(v_reuseFailAlloc_3225_, 24, v_enableArtifactCache_x3f_3214_);
lean_ctor_set(v_reuseFailAlloc_3225_, 25, v___x_3222_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26, v_bootstrap_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26 + 1, v_precompileModules_3190_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3200_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26 + 3, v_reservoir_3213_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3216_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26 + 5, v_allowImportAll_3217_);
lean_ctor_set_uint8(v_reuseFailAlloc_3225_, sizeof(void*)*26 + 6, v_fixedToolchain_3218_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3235_, lean_object* v_n_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3));
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3238_, lean_object* v_n_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3238_, v_n_3239_);
lean_dec(v_n_3239_);
lean_dec(v_p_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3241_, lean_object* v_n_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3241_, v_n_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3244_, lean_object* v_n_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3244_, v_n_3245_);
lean_dec(v_n_3245_);
lean_dec(v_p_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3247_, lean_object* v_n_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3247_, v_n_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3250_, lean_object* v_n_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3250_, v_n_3251_);
lean_dec(v_n_3251_);
lean_dec(v_p_3250_);
return v_res_3252_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_3253_){
_start:
{
uint8_t v_libPrefixOnWindows_3254_; 
v_libPrefixOnWindows_3254_ = lean_ctor_get_uint8(v_cfg_3253_, sizeof(void*)*26 + 4);
return v_libPrefixOnWindows_3254_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_3255_){
_start:
{
uint8_t v_res_3256_; lean_object* v_r_3257_; 
v_res_3256_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(v_cfg_3255_);
lean_dec_ref(v_cfg_3255_);
v_r_3257_ = lean_box(v_res_3256_);
return v_r_3257_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_3258_, lean_object* v_cfg_3259_){
_start:
{
lean_object* v_toWorkspaceConfig_3260_; lean_object* v_toLeanConfig_3261_; uint8_t v_bootstrap_3262_; lean_object* v_extraDepTargets_3263_; uint8_t v_precompileModules_3264_; lean_object* v_moreGlobalServerArgs_3265_; lean_object* v_srcDir_3266_; lean_object* v_buildDir_3267_; lean_object* v_leanLibDir_3268_; lean_object* v_nativeLibDir_3269_; lean_object* v_binDir_3270_; lean_object* v_irDir_3271_; lean_object* v_releaseRepo_3272_; lean_object* v_buildArchive_3273_; uint8_t v_preferReleaseBuild_3274_; lean_object* v_testDriver_3275_; lean_object* v_testDriverArgs_3276_; lean_object* v_lintDriver_3277_; lean_object* v_lintDriverArgs_3278_; lean_object* v_version_3279_; lean_object* v_versionTags_3280_; lean_object* v_description_3281_; lean_object* v_keywords_3282_; lean_object* v_homepage_3283_; lean_object* v_license_3284_; lean_object* v_licenseFiles_3285_; lean_object* v_readmeFile_3286_; uint8_t v_reservoir_3287_; lean_object* v_enableArtifactCache_x3f_3288_; lean_object* v_restoreAllArtifacts_x3f_3289_; uint8_t v_allowImportAll_3290_; uint8_t v_fixedToolchain_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
v_toWorkspaceConfig_3260_ = lean_ctor_get(v_cfg_3259_, 0);
v_toLeanConfig_3261_ = lean_ctor_get(v_cfg_3259_, 1);
v_bootstrap_3262_ = lean_ctor_get_uint8(v_cfg_3259_, sizeof(void*)*26);
v_extraDepTargets_3263_ = lean_ctor_get(v_cfg_3259_, 2);
v_precompileModules_3264_ = lean_ctor_get_uint8(v_cfg_3259_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3265_ = lean_ctor_get(v_cfg_3259_, 3);
v_srcDir_3266_ = lean_ctor_get(v_cfg_3259_, 4);
v_buildDir_3267_ = lean_ctor_get(v_cfg_3259_, 5);
v_leanLibDir_3268_ = lean_ctor_get(v_cfg_3259_, 6);
v_nativeLibDir_3269_ = lean_ctor_get(v_cfg_3259_, 7);
v_binDir_3270_ = lean_ctor_get(v_cfg_3259_, 8);
v_irDir_3271_ = lean_ctor_get(v_cfg_3259_, 9);
v_releaseRepo_3272_ = lean_ctor_get(v_cfg_3259_, 10);
v_buildArchive_3273_ = lean_ctor_get(v_cfg_3259_, 11);
v_preferReleaseBuild_3274_ = lean_ctor_get_uint8(v_cfg_3259_, sizeof(void*)*26 + 2);
v_testDriver_3275_ = lean_ctor_get(v_cfg_3259_, 12);
v_testDriverArgs_3276_ = lean_ctor_get(v_cfg_3259_, 13);
v_lintDriver_3277_ = lean_ctor_get(v_cfg_3259_, 14);
v_lintDriverArgs_3278_ = lean_ctor_get(v_cfg_3259_, 15);
v_version_3279_ = lean_ctor_get(v_cfg_3259_, 16);
v_versionTags_3280_ = lean_ctor_get(v_cfg_3259_, 17);
v_description_3281_ = lean_ctor_get(v_cfg_3259_, 18);
v_keywords_3282_ = lean_ctor_get(v_cfg_3259_, 19);
v_homepage_3283_ = lean_ctor_get(v_cfg_3259_, 20);
v_license_3284_ = lean_ctor_get(v_cfg_3259_, 21);
v_licenseFiles_3285_ = lean_ctor_get(v_cfg_3259_, 22);
v_readmeFile_3286_ = lean_ctor_get(v_cfg_3259_, 23);
v_reservoir_3287_ = lean_ctor_get_uint8(v_cfg_3259_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3288_ = lean_ctor_get(v_cfg_3259_, 24);
v_restoreAllArtifacts_x3f_3289_ = lean_ctor_get(v_cfg_3259_, 25);
v_allowImportAll_3290_ = lean_ctor_get_uint8(v_cfg_3259_, sizeof(void*)*26 + 5);
v_fixedToolchain_3291_ = lean_ctor_get_uint8(v_cfg_3259_, sizeof(void*)*26 + 6);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_cfg_3259_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v_cfg_3259_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3289_);
lean_inc(v_enableArtifactCache_x3f_3288_);
lean_inc(v_readmeFile_3286_);
lean_inc(v_licenseFiles_3285_);
lean_inc(v_license_3284_);
lean_inc(v_homepage_3283_);
lean_inc(v_keywords_3282_);
lean_inc(v_description_3281_);
lean_inc(v_versionTags_3280_);
lean_inc(v_version_3279_);
lean_inc(v_lintDriverArgs_3278_);
lean_inc(v_lintDriver_3277_);
lean_inc(v_testDriverArgs_3276_);
lean_inc(v_testDriver_3275_);
lean_inc(v_buildArchive_3273_);
lean_inc(v_releaseRepo_3272_);
lean_inc(v_irDir_3271_);
lean_inc(v_binDir_3270_);
lean_inc(v_nativeLibDir_3269_);
lean_inc(v_leanLibDir_3268_);
lean_inc(v_buildDir_3267_);
lean_inc(v_srcDir_3266_);
lean_inc(v_moreGlobalServerArgs_3265_);
lean_inc(v_extraDepTargets_3263_);
lean_inc(v_toLeanConfig_3261_);
lean_inc(v_toWorkspaceConfig_3260_);
lean_dec(v_cfg_3259_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_toWorkspaceConfig_3260_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_toLeanConfig_3261_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_extraDepTargets_3263_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_moreGlobalServerArgs_3265_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_srcDir_3266_);
lean_ctor_set(v_reuseFailAlloc_3297_, 5, v_buildDir_3267_);
lean_ctor_set(v_reuseFailAlloc_3297_, 6, v_leanLibDir_3268_);
lean_ctor_set(v_reuseFailAlloc_3297_, 7, v_nativeLibDir_3269_);
lean_ctor_set(v_reuseFailAlloc_3297_, 8, v_binDir_3270_);
lean_ctor_set(v_reuseFailAlloc_3297_, 9, v_irDir_3271_);
lean_ctor_set(v_reuseFailAlloc_3297_, 10, v_releaseRepo_3272_);
lean_ctor_set(v_reuseFailAlloc_3297_, 11, v_buildArchive_3273_);
lean_ctor_set(v_reuseFailAlloc_3297_, 12, v_testDriver_3275_);
lean_ctor_set(v_reuseFailAlloc_3297_, 13, v_testDriverArgs_3276_);
lean_ctor_set(v_reuseFailAlloc_3297_, 14, v_lintDriver_3277_);
lean_ctor_set(v_reuseFailAlloc_3297_, 15, v_lintDriverArgs_3278_);
lean_ctor_set(v_reuseFailAlloc_3297_, 16, v_version_3279_);
lean_ctor_set(v_reuseFailAlloc_3297_, 17, v_versionTags_3280_);
lean_ctor_set(v_reuseFailAlloc_3297_, 18, v_description_3281_);
lean_ctor_set(v_reuseFailAlloc_3297_, 19, v_keywords_3282_);
lean_ctor_set(v_reuseFailAlloc_3297_, 20, v_homepage_3283_);
lean_ctor_set(v_reuseFailAlloc_3297_, 21, v_license_3284_);
lean_ctor_set(v_reuseFailAlloc_3297_, 22, v_licenseFiles_3285_);
lean_ctor_set(v_reuseFailAlloc_3297_, 23, v_readmeFile_3286_);
lean_ctor_set(v_reuseFailAlloc_3297_, 24, v_enableArtifactCache_x3f_3288_);
lean_ctor_set(v_reuseFailAlloc_3297_, 25, v_restoreAllArtifacts_x3f_3289_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*26, v_bootstrap_3262_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*26 + 1, v_precompileModules_3264_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3274_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*26 + 3, v_reservoir_3287_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*26 + 5, v_allowImportAll_3290_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*26 + 6, v_fixedToolchain_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*26 + 4, v_val_3258_);
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_3299_, lean_object* v_cfg_3300_){
_start:
{
uint8_t v_val_134__boxed_3301_; lean_object* v_res_3302_; 
v_val_134__boxed_3301_ = lean_unbox(v_val_3299_);
v_res_3302_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(v_val_134__boxed_3301_, v_cfg_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_3303_, lean_object* v_cfg_3304_){
_start:
{
lean_object* v_toWorkspaceConfig_3305_; lean_object* v_toLeanConfig_3306_; uint8_t v_bootstrap_3307_; lean_object* v_extraDepTargets_3308_; uint8_t v_precompileModules_3309_; lean_object* v_moreGlobalServerArgs_3310_; lean_object* v_srcDir_3311_; lean_object* v_buildDir_3312_; lean_object* v_leanLibDir_3313_; lean_object* v_nativeLibDir_3314_; lean_object* v_binDir_3315_; lean_object* v_irDir_3316_; lean_object* v_releaseRepo_3317_; lean_object* v_buildArchive_3318_; uint8_t v_preferReleaseBuild_3319_; lean_object* v_testDriver_3320_; lean_object* v_testDriverArgs_3321_; lean_object* v_lintDriver_3322_; lean_object* v_lintDriverArgs_3323_; lean_object* v_version_3324_; lean_object* v_versionTags_3325_; lean_object* v_description_3326_; lean_object* v_keywords_3327_; lean_object* v_homepage_3328_; lean_object* v_license_3329_; lean_object* v_licenseFiles_3330_; lean_object* v_readmeFile_3331_; uint8_t v_reservoir_3332_; lean_object* v_enableArtifactCache_x3f_3333_; lean_object* v_restoreAllArtifacts_x3f_3334_; uint8_t v_libPrefixOnWindows_3335_; uint8_t v_allowImportAll_3336_; uint8_t v_fixedToolchain_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3347_; 
v_toWorkspaceConfig_3305_ = lean_ctor_get(v_cfg_3304_, 0);
v_toLeanConfig_3306_ = lean_ctor_get(v_cfg_3304_, 1);
v_bootstrap_3307_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26);
v_extraDepTargets_3308_ = lean_ctor_get(v_cfg_3304_, 2);
v_precompileModules_3309_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3310_ = lean_ctor_get(v_cfg_3304_, 3);
v_srcDir_3311_ = lean_ctor_get(v_cfg_3304_, 4);
v_buildDir_3312_ = lean_ctor_get(v_cfg_3304_, 5);
v_leanLibDir_3313_ = lean_ctor_get(v_cfg_3304_, 6);
v_nativeLibDir_3314_ = lean_ctor_get(v_cfg_3304_, 7);
v_binDir_3315_ = lean_ctor_get(v_cfg_3304_, 8);
v_irDir_3316_ = lean_ctor_get(v_cfg_3304_, 9);
v_releaseRepo_3317_ = lean_ctor_get(v_cfg_3304_, 10);
v_buildArchive_3318_ = lean_ctor_get(v_cfg_3304_, 11);
v_preferReleaseBuild_3319_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26 + 2);
v_testDriver_3320_ = lean_ctor_get(v_cfg_3304_, 12);
v_testDriverArgs_3321_ = lean_ctor_get(v_cfg_3304_, 13);
v_lintDriver_3322_ = lean_ctor_get(v_cfg_3304_, 14);
v_lintDriverArgs_3323_ = lean_ctor_get(v_cfg_3304_, 15);
v_version_3324_ = lean_ctor_get(v_cfg_3304_, 16);
v_versionTags_3325_ = lean_ctor_get(v_cfg_3304_, 17);
v_description_3326_ = lean_ctor_get(v_cfg_3304_, 18);
v_keywords_3327_ = lean_ctor_get(v_cfg_3304_, 19);
v_homepage_3328_ = lean_ctor_get(v_cfg_3304_, 20);
v_license_3329_ = lean_ctor_get(v_cfg_3304_, 21);
v_licenseFiles_3330_ = lean_ctor_get(v_cfg_3304_, 22);
v_readmeFile_3331_ = lean_ctor_get(v_cfg_3304_, 23);
v_reservoir_3332_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3333_ = lean_ctor_get(v_cfg_3304_, 24);
v_restoreAllArtifacts_x3f_3334_ = lean_ctor_get(v_cfg_3304_, 25);
v_libPrefixOnWindows_3335_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26 + 4);
v_allowImportAll_3336_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26 + 5);
v_fixedToolchain_3337_ = lean_ctor_get_uint8(v_cfg_3304_, sizeof(void*)*26 + 6);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_cfg_3304_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3339_ = v_cfg_3304_;
v_isShared_3340_ = v_isSharedCheck_3347_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3334_);
lean_inc(v_enableArtifactCache_x3f_3333_);
lean_inc(v_readmeFile_3331_);
lean_inc(v_licenseFiles_3330_);
lean_inc(v_license_3329_);
lean_inc(v_homepage_3328_);
lean_inc(v_keywords_3327_);
lean_inc(v_description_3326_);
lean_inc(v_versionTags_3325_);
lean_inc(v_version_3324_);
lean_inc(v_lintDriverArgs_3323_);
lean_inc(v_lintDriver_3322_);
lean_inc(v_testDriverArgs_3321_);
lean_inc(v_testDriver_3320_);
lean_inc(v_buildArchive_3318_);
lean_inc(v_releaseRepo_3317_);
lean_inc(v_irDir_3316_);
lean_inc(v_binDir_3315_);
lean_inc(v_nativeLibDir_3314_);
lean_inc(v_leanLibDir_3313_);
lean_inc(v_buildDir_3312_);
lean_inc(v_srcDir_3311_);
lean_inc(v_moreGlobalServerArgs_3310_);
lean_inc(v_extraDepTargets_3308_);
lean_inc(v_toLeanConfig_3306_);
lean_inc(v_toWorkspaceConfig_3305_);
lean_dec(v_cfg_3304_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3347_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = lean_box(v_libPrefixOnWindows_3335_);
v___x_3342_ = lean_apply_1(v_f_3303_, v___x_3341_);
if (v_isShared_3340_ == 0)
{
v___x_3344_ = v___x_3339_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_toWorkspaceConfig_3305_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_toLeanConfig_3306_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_extraDepTargets_3308_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_moreGlobalServerArgs_3310_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_srcDir_3311_);
lean_ctor_set(v_reuseFailAlloc_3346_, 5, v_buildDir_3312_);
lean_ctor_set(v_reuseFailAlloc_3346_, 6, v_leanLibDir_3313_);
lean_ctor_set(v_reuseFailAlloc_3346_, 7, v_nativeLibDir_3314_);
lean_ctor_set(v_reuseFailAlloc_3346_, 8, v_binDir_3315_);
lean_ctor_set(v_reuseFailAlloc_3346_, 9, v_irDir_3316_);
lean_ctor_set(v_reuseFailAlloc_3346_, 10, v_releaseRepo_3317_);
lean_ctor_set(v_reuseFailAlloc_3346_, 11, v_buildArchive_3318_);
lean_ctor_set(v_reuseFailAlloc_3346_, 12, v_testDriver_3320_);
lean_ctor_set(v_reuseFailAlloc_3346_, 13, v_testDriverArgs_3321_);
lean_ctor_set(v_reuseFailAlloc_3346_, 14, v_lintDriver_3322_);
lean_ctor_set(v_reuseFailAlloc_3346_, 15, v_lintDriverArgs_3323_);
lean_ctor_set(v_reuseFailAlloc_3346_, 16, v_version_3324_);
lean_ctor_set(v_reuseFailAlloc_3346_, 17, v_versionTags_3325_);
lean_ctor_set(v_reuseFailAlloc_3346_, 18, v_description_3326_);
lean_ctor_set(v_reuseFailAlloc_3346_, 19, v_keywords_3327_);
lean_ctor_set(v_reuseFailAlloc_3346_, 20, v_homepage_3328_);
lean_ctor_set(v_reuseFailAlloc_3346_, 21, v_license_3329_);
lean_ctor_set(v_reuseFailAlloc_3346_, 22, v_licenseFiles_3330_);
lean_ctor_set(v_reuseFailAlloc_3346_, 23, v_readmeFile_3331_);
lean_ctor_set(v_reuseFailAlloc_3346_, 24, v_enableArtifactCache_x3f_3333_);
lean_ctor_set(v_reuseFailAlloc_3346_, 25, v_restoreAllArtifacts_x3f_3334_);
lean_ctor_set_uint8(v_reuseFailAlloc_3346_, sizeof(void*)*26, v_bootstrap_3307_);
lean_ctor_set_uint8(v_reuseFailAlloc_3346_, sizeof(void*)*26 + 1, v_precompileModules_3309_);
lean_ctor_set_uint8(v_reuseFailAlloc_3346_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3319_);
lean_ctor_set_uint8(v_reuseFailAlloc_3346_, sizeof(void*)*26 + 3, v_reservoir_3332_);
v___x_3344_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_unbox(v___x_3342_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*26 + 4, v___x_3345_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*26 + 5, v_allowImportAll_3336_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*26 + 6, v_fixedToolchain_3337_);
return v___x_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3356_, lean_object* v_n_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3359_, lean_object* v_n_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3359_, v_n_3360_);
lean_dec(v_n_3360_);
lean_dec(v_p_3359_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3362_, lean_object* v_n_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3362_, v_n_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3365_, lean_object* v_n_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3365_, v_n_3366_);
lean_dec(v_n_3366_);
lean_dec(v_p_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_3368_){
_start:
{
uint8_t v_allowImportAll_3369_; 
v_allowImportAll_3369_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*26 + 5);
return v_allowImportAll_3369_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_3370_){
_start:
{
uint8_t v_res_3371_; lean_object* v_r_3372_; 
v_res_3371_ = l_Lake_PackageConfig_allowImportAll___proj___lam__0(v_cfg_3370_);
lean_dec_ref(v_cfg_3370_);
v_r_3372_ = lean_box(v_res_3371_);
return v_r_3372_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t v_val_3373_, lean_object* v_cfg_3374_){
_start:
{
lean_object* v_toWorkspaceConfig_3375_; lean_object* v_toLeanConfig_3376_; uint8_t v_bootstrap_3377_; lean_object* v_extraDepTargets_3378_; uint8_t v_precompileModules_3379_; lean_object* v_moreGlobalServerArgs_3380_; lean_object* v_srcDir_3381_; lean_object* v_buildDir_3382_; lean_object* v_leanLibDir_3383_; lean_object* v_nativeLibDir_3384_; lean_object* v_binDir_3385_; lean_object* v_irDir_3386_; lean_object* v_releaseRepo_3387_; lean_object* v_buildArchive_3388_; uint8_t v_preferReleaseBuild_3389_; lean_object* v_testDriver_3390_; lean_object* v_testDriverArgs_3391_; lean_object* v_lintDriver_3392_; lean_object* v_lintDriverArgs_3393_; lean_object* v_version_3394_; lean_object* v_versionTags_3395_; lean_object* v_description_3396_; lean_object* v_keywords_3397_; lean_object* v_homepage_3398_; lean_object* v_license_3399_; lean_object* v_licenseFiles_3400_; lean_object* v_readmeFile_3401_; uint8_t v_reservoir_3402_; lean_object* v_enableArtifactCache_x3f_3403_; lean_object* v_restoreAllArtifacts_x3f_3404_; uint8_t v_libPrefixOnWindows_3405_; uint8_t v_fixedToolchain_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
v_toWorkspaceConfig_3375_ = lean_ctor_get(v_cfg_3374_, 0);
v_toLeanConfig_3376_ = lean_ctor_get(v_cfg_3374_, 1);
v_bootstrap_3377_ = lean_ctor_get_uint8(v_cfg_3374_, sizeof(void*)*26);
v_extraDepTargets_3378_ = lean_ctor_get(v_cfg_3374_, 2);
v_precompileModules_3379_ = lean_ctor_get_uint8(v_cfg_3374_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3380_ = lean_ctor_get(v_cfg_3374_, 3);
v_srcDir_3381_ = lean_ctor_get(v_cfg_3374_, 4);
v_buildDir_3382_ = lean_ctor_get(v_cfg_3374_, 5);
v_leanLibDir_3383_ = lean_ctor_get(v_cfg_3374_, 6);
v_nativeLibDir_3384_ = lean_ctor_get(v_cfg_3374_, 7);
v_binDir_3385_ = lean_ctor_get(v_cfg_3374_, 8);
v_irDir_3386_ = lean_ctor_get(v_cfg_3374_, 9);
v_releaseRepo_3387_ = lean_ctor_get(v_cfg_3374_, 10);
v_buildArchive_3388_ = lean_ctor_get(v_cfg_3374_, 11);
v_preferReleaseBuild_3389_ = lean_ctor_get_uint8(v_cfg_3374_, sizeof(void*)*26 + 2);
v_testDriver_3390_ = lean_ctor_get(v_cfg_3374_, 12);
v_testDriverArgs_3391_ = lean_ctor_get(v_cfg_3374_, 13);
v_lintDriver_3392_ = lean_ctor_get(v_cfg_3374_, 14);
v_lintDriverArgs_3393_ = lean_ctor_get(v_cfg_3374_, 15);
v_version_3394_ = lean_ctor_get(v_cfg_3374_, 16);
v_versionTags_3395_ = lean_ctor_get(v_cfg_3374_, 17);
v_description_3396_ = lean_ctor_get(v_cfg_3374_, 18);
v_keywords_3397_ = lean_ctor_get(v_cfg_3374_, 19);
v_homepage_3398_ = lean_ctor_get(v_cfg_3374_, 20);
v_license_3399_ = lean_ctor_get(v_cfg_3374_, 21);
v_licenseFiles_3400_ = lean_ctor_get(v_cfg_3374_, 22);
v_readmeFile_3401_ = lean_ctor_get(v_cfg_3374_, 23);
v_reservoir_3402_ = lean_ctor_get_uint8(v_cfg_3374_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3403_ = lean_ctor_get(v_cfg_3374_, 24);
v_restoreAllArtifacts_x3f_3404_ = lean_ctor_get(v_cfg_3374_, 25);
v_libPrefixOnWindows_3405_ = lean_ctor_get_uint8(v_cfg_3374_, sizeof(void*)*26 + 4);
v_fixedToolchain_3406_ = lean_ctor_get_uint8(v_cfg_3374_, sizeof(void*)*26 + 6);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_cfg_3374_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v_cfg_3374_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3404_);
lean_inc(v_enableArtifactCache_x3f_3403_);
lean_inc(v_readmeFile_3401_);
lean_inc(v_licenseFiles_3400_);
lean_inc(v_license_3399_);
lean_inc(v_homepage_3398_);
lean_inc(v_keywords_3397_);
lean_inc(v_description_3396_);
lean_inc(v_versionTags_3395_);
lean_inc(v_version_3394_);
lean_inc(v_lintDriverArgs_3393_);
lean_inc(v_lintDriver_3392_);
lean_inc(v_testDriverArgs_3391_);
lean_inc(v_testDriver_3390_);
lean_inc(v_buildArchive_3388_);
lean_inc(v_releaseRepo_3387_);
lean_inc(v_irDir_3386_);
lean_inc(v_binDir_3385_);
lean_inc(v_nativeLibDir_3384_);
lean_inc(v_leanLibDir_3383_);
lean_inc(v_buildDir_3382_);
lean_inc(v_srcDir_3381_);
lean_inc(v_moreGlobalServerArgs_3380_);
lean_inc(v_extraDepTargets_3378_);
lean_inc(v_toLeanConfig_3376_);
lean_inc(v_toWorkspaceConfig_3375_);
lean_dec(v_cfg_3374_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_toWorkspaceConfig_3375_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_toLeanConfig_3376_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_extraDepTargets_3378_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_moreGlobalServerArgs_3380_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_srcDir_3381_);
lean_ctor_set(v_reuseFailAlloc_3412_, 5, v_buildDir_3382_);
lean_ctor_set(v_reuseFailAlloc_3412_, 6, v_leanLibDir_3383_);
lean_ctor_set(v_reuseFailAlloc_3412_, 7, v_nativeLibDir_3384_);
lean_ctor_set(v_reuseFailAlloc_3412_, 8, v_binDir_3385_);
lean_ctor_set(v_reuseFailAlloc_3412_, 9, v_irDir_3386_);
lean_ctor_set(v_reuseFailAlloc_3412_, 10, v_releaseRepo_3387_);
lean_ctor_set(v_reuseFailAlloc_3412_, 11, v_buildArchive_3388_);
lean_ctor_set(v_reuseFailAlloc_3412_, 12, v_testDriver_3390_);
lean_ctor_set(v_reuseFailAlloc_3412_, 13, v_testDriverArgs_3391_);
lean_ctor_set(v_reuseFailAlloc_3412_, 14, v_lintDriver_3392_);
lean_ctor_set(v_reuseFailAlloc_3412_, 15, v_lintDriverArgs_3393_);
lean_ctor_set(v_reuseFailAlloc_3412_, 16, v_version_3394_);
lean_ctor_set(v_reuseFailAlloc_3412_, 17, v_versionTags_3395_);
lean_ctor_set(v_reuseFailAlloc_3412_, 18, v_description_3396_);
lean_ctor_set(v_reuseFailAlloc_3412_, 19, v_keywords_3397_);
lean_ctor_set(v_reuseFailAlloc_3412_, 20, v_homepage_3398_);
lean_ctor_set(v_reuseFailAlloc_3412_, 21, v_license_3399_);
lean_ctor_set(v_reuseFailAlloc_3412_, 22, v_licenseFiles_3400_);
lean_ctor_set(v_reuseFailAlloc_3412_, 23, v_readmeFile_3401_);
lean_ctor_set(v_reuseFailAlloc_3412_, 24, v_enableArtifactCache_x3f_3403_);
lean_ctor_set(v_reuseFailAlloc_3412_, 25, v_restoreAllArtifacts_x3f_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*26, v_bootstrap_3377_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*26 + 1, v_precompileModules_3379_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3389_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*26 + 3, v_reservoir_3402_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*26 + 6, v_fixedToolchain_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*26 + 5, v_val_3373_);
return v___x_3411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_3414_, lean_object* v_cfg_3415_){
_start:
{
uint8_t v_val_134__boxed_3416_; lean_object* v_res_3417_; 
v_val_134__boxed_3416_ = lean_unbox(v_val_3414_);
v_res_3417_ = l_Lake_PackageConfig_allowImportAll___proj___lam__1(v_val_134__boxed_3416_, v_cfg_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* v_f_3418_, lean_object* v_cfg_3419_){
_start:
{
lean_object* v_toWorkspaceConfig_3420_; lean_object* v_toLeanConfig_3421_; uint8_t v_bootstrap_3422_; lean_object* v_extraDepTargets_3423_; uint8_t v_precompileModules_3424_; lean_object* v_moreGlobalServerArgs_3425_; lean_object* v_srcDir_3426_; lean_object* v_buildDir_3427_; lean_object* v_leanLibDir_3428_; lean_object* v_nativeLibDir_3429_; lean_object* v_binDir_3430_; lean_object* v_irDir_3431_; lean_object* v_releaseRepo_3432_; lean_object* v_buildArchive_3433_; uint8_t v_preferReleaseBuild_3434_; lean_object* v_testDriver_3435_; lean_object* v_testDriverArgs_3436_; lean_object* v_lintDriver_3437_; lean_object* v_lintDriverArgs_3438_; lean_object* v_version_3439_; lean_object* v_versionTags_3440_; lean_object* v_description_3441_; lean_object* v_keywords_3442_; lean_object* v_homepage_3443_; lean_object* v_license_3444_; lean_object* v_licenseFiles_3445_; lean_object* v_readmeFile_3446_; uint8_t v_reservoir_3447_; lean_object* v_enableArtifactCache_x3f_3448_; lean_object* v_restoreAllArtifacts_x3f_3449_; uint8_t v_libPrefixOnWindows_3450_; uint8_t v_allowImportAll_3451_; uint8_t v_fixedToolchain_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3462_; 
v_toWorkspaceConfig_3420_ = lean_ctor_get(v_cfg_3419_, 0);
v_toLeanConfig_3421_ = lean_ctor_get(v_cfg_3419_, 1);
v_bootstrap_3422_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26);
v_extraDepTargets_3423_ = lean_ctor_get(v_cfg_3419_, 2);
v_precompileModules_3424_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3425_ = lean_ctor_get(v_cfg_3419_, 3);
v_srcDir_3426_ = lean_ctor_get(v_cfg_3419_, 4);
v_buildDir_3427_ = lean_ctor_get(v_cfg_3419_, 5);
v_leanLibDir_3428_ = lean_ctor_get(v_cfg_3419_, 6);
v_nativeLibDir_3429_ = lean_ctor_get(v_cfg_3419_, 7);
v_binDir_3430_ = lean_ctor_get(v_cfg_3419_, 8);
v_irDir_3431_ = lean_ctor_get(v_cfg_3419_, 9);
v_releaseRepo_3432_ = lean_ctor_get(v_cfg_3419_, 10);
v_buildArchive_3433_ = lean_ctor_get(v_cfg_3419_, 11);
v_preferReleaseBuild_3434_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26 + 2);
v_testDriver_3435_ = lean_ctor_get(v_cfg_3419_, 12);
v_testDriverArgs_3436_ = lean_ctor_get(v_cfg_3419_, 13);
v_lintDriver_3437_ = lean_ctor_get(v_cfg_3419_, 14);
v_lintDriverArgs_3438_ = lean_ctor_get(v_cfg_3419_, 15);
v_version_3439_ = lean_ctor_get(v_cfg_3419_, 16);
v_versionTags_3440_ = lean_ctor_get(v_cfg_3419_, 17);
v_description_3441_ = lean_ctor_get(v_cfg_3419_, 18);
v_keywords_3442_ = lean_ctor_get(v_cfg_3419_, 19);
v_homepage_3443_ = lean_ctor_get(v_cfg_3419_, 20);
v_license_3444_ = lean_ctor_get(v_cfg_3419_, 21);
v_licenseFiles_3445_ = lean_ctor_get(v_cfg_3419_, 22);
v_readmeFile_3446_ = lean_ctor_get(v_cfg_3419_, 23);
v_reservoir_3447_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3448_ = lean_ctor_get(v_cfg_3419_, 24);
v_restoreAllArtifacts_x3f_3449_ = lean_ctor_get(v_cfg_3419_, 25);
v_libPrefixOnWindows_3450_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26 + 4);
v_allowImportAll_3451_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26 + 5);
v_fixedToolchain_3452_ = lean_ctor_get_uint8(v_cfg_3419_, sizeof(void*)*26 + 6);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_cfg_3419_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3454_ = v_cfg_3419_;
v_isShared_3455_ = v_isSharedCheck_3462_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3449_);
lean_inc(v_enableArtifactCache_x3f_3448_);
lean_inc(v_readmeFile_3446_);
lean_inc(v_licenseFiles_3445_);
lean_inc(v_license_3444_);
lean_inc(v_homepage_3443_);
lean_inc(v_keywords_3442_);
lean_inc(v_description_3441_);
lean_inc(v_versionTags_3440_);
lean_inc(v_version_3439_);
lean_inc(v_lintDriverArgs_3438_);
lean_inc(v_lintDriver_3437_);
lean_inc(v_testDriverArgs_3436_);
lean_inc(v_testDriver_3435_);
lean_inc(v_buildArchive_3433_);
lean_inc(v_releaseRepo_3432_);
lean_inc(v_irDir_3431_);
lean_inc(v_binDir_3430_);
lean_inc(v_nativeLibDir_3429_);
lean_inc(v_leanLibDir_3428_);
lean_inc(v_buildDir_3427_);
lean_inc(v_srcDir_3426_);
lean_inc(v_moreGlobalServerArgs_3425_);
lean_inc(v_extraDepTargets_3423_);
lean_inc(v_toLeanConfig_3421_);
lean_inc(v_toWorkspaceConfig_3420_);
lean_dec(v_cfg_3419_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3462_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3456_ = lean_box(v_allowImportAll_3451_);
v___x_3457_ = lean_apply_1(v_f_3418_, v___x_3456_);
if (v_isShared_3455_ == 0)
{
v___x_3459_ = v___x_3454_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_toWorkspaceConfig_3420_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_toLeanConfig_3421_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_extraDepTargets_3423_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_moreGlobalServerArgs_3425_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_srcDir_3426_);
lean_ctor_set(v_reuseFailAlloc_3461_, 5, v_buildDir_3427_);
lean_ctor_set(v_reuseFailAlloc_3461_, 6, v_leanLibDir_3428_);
lean_ctor_set(v_reuseFailAlloc_3461_, 7, v_nativeLibDir_3429_);
lean_ctor_set(v_reuseFailAlloc_3461_, 8, v_binDir_3430_);
lean_ctor_set(v_reuseFailAlloc_3461_, 9, v_irDir_3431_);
lean_ctor_set(v_reuseFailAlloc_3461_, 10, v_releaseRepo_3432_);
lean_ctor_set(v_reuseFailAlloc_3461_, 11, v_buildArchive_3433_);
lean_ctor_set(v_reuseFailAlloc_3461_, 12, v_testDriver_3435_);
lean_ctor_set(v_reuseFailAlloc_3461_, 13, v_testDriverArgs_3436_);
lean_ctor_set(v_reuseFailAlloc_3461_, 14, v_lintDriver_3437_);
lean_ctor_set(v_reuseFailAlloc_3461_, 15, v_lintDriverArgs_3438_);
lean_ctor_set(v_reuseFailAlloc_3461_, 16, v_version_3439_);
lean_ctor_set(v_reuseFailAlloc_3461_, 17, v_versionTags_3440_);
lean_ctor_set(v_reuseFailAlloc_3461_, 18, v_description_3441_);
lean_ctor_set(v_reuseFailAlloc_3461_, 19, v_keywords_3442_);
lean_ctor_set(v_reuseFailAlloc_3461_, 20, v_homepage_3443_);
lean_ctor_set(v_reuseFailAlloc_3461_, 21, v_license_3444_);
lean_ctor_set(v_reuseFailAlloc_3461_, 22, v_licenseFiles_3445_);
lean_ctor_set(v_reuseFailAlloc_3461_, 23, v_readmeFile_3446_);
lean_ctor_set(v_reuseFailAlloc_3461_, 24, v_enableArtifactCache_x3f_3448_);
lean_ctor_set(v_reuseFailAlloc_3461_, 25, v_restoreAllArtifacts_x3f_3449_);
lean_ctor_set_uint8(v_reuseFailAlloc_3461_, sizeof(void*)*26, v_bootstrap_3422_);
lean_ctor_set_uint8(v_reuseFailAlloc_3461_, sizeof(void*)*26 + 1, v_precompileModules_3424_);
lean_ctor_set_uint8(v_reuseFailAlloc_3461_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3434_);
lean_ctor_set_uint8(v_reuseFailAlloc_3461_, sizeof(void*)*26 + 3, v_reservoir_3447_);
lean_ctor_set_uint8(v_reuseFailAlloc_3461_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3450_);
v___x_3459_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_unbox(v___x_3457_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*26 + 5, v___x_3460_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*26 + 6, v_fixedToolchain_3452_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3471_, lean_object* v_n_3472_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3474_, lean_object* v_n_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3474_, v_n_3475_);
lean_dec(v_n_3475_);
lean_dec(v_p_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3477_, lean_object* v_n_3478_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3477_, v_n_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3480_, lean_object* v_n_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3480_, v_n_3481_);
lean_dec(v_n_3481_);
lean_dec(v_p_3480_);
return v_res_3482_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___lam__0(lean_object* v_cfg_3483_){
_start:
{
uint8_t v_fixedToolchain_3484_; 
v_fixedToolchain_3484_ = lean_ctor_get_uint8(v_cfg_3483_, sizeof(void*)*26 + 6);
return v_fixedToolchain_3484_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed(lean_object* v_cfg_3485_){
_start:
{
uint8_t v_res_3486_; lean_object* v_r_3487_; 
v_res_3486_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__0(v_cfg_3485_);
lean_dec_ref(v_cfg_3485_);
v_r_3487_ = lean_box(v_res_3486_);
return v_r_3487_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1(uint8_t v_val_3488_, lean_object* v_cfg_3489_){
_start:
{
lean_object* v_toWorkspaceConfig_3490_; lean_object* v_toLeanConfig_3491_; uint8_t v_bootstrap_3492_; lean_object* v_extraDepTargets_3493_; uint8_t v_precompileModules_3494_; lean_object* v_moreGlobalServerArgs_3495_; lean_object* v_srcDir_3496_; lean_object* v_buildDir_3497_; lean_object* v_leanLibDir_3498_; lean_object* v_nativeLibDir_3499_; lean_object* v_binDir_3500_; lean_object* v_irDir_3501_; lean_object* v_releaseRepo_3502_; lean_object* v_buildArchive_3503_; uint8_t v_preferReleaseBuild_3504_; lean_object* v_testDriver_3505_; lean_object* v_testDriverArgs_3506_; lean_object* v_lintDriver_3507_; lean_object* v_lintDriverArgs_3508_; lean_object* v_version_3509_; lean_object* v_versionTags_3510_; lean_object* v_description_3511_; lean_object* v_keywords_3512_; lean_object* v_homepage_3513_; lean_object* v_license_3514_; lean_object* v_licenseFiles_3515_; lean_object* v_readmeFile_3516_; uint8_t v_reservoir_3517_; lean_object* v_enableArtifactCache_x3f_3518_; lean_object* v_restoreAllArtifacts_x3f_3519_; uint8_t v_libPrefixOnWindows_3520_; uint8_t v_allowImportAll_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
v_toWorkspaceConfig_3490_ = lean_ctor_get(v_cfg_3489_, 0);
v_toLeanConfig_3491_ = lean_ctor_get(v_cfg_3489_, 1);
v_bootstrap_3492_ = lean_ctor_get_uint8(v_cfg_3489_, sizeof(void*)*26);
v_extraDepTargets_3493_ = lean_ctor_get(v_cfg_3489_, 2);
v_precompileModules_3494_ = lean_ctor_get_uint8(v_cfg_3489_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3495_ = lean_ctor_get(v_cfg_3489_, 3);
v_srcDir_3496_ = lean_ctor_get(v_cfg_3489_, 4);
v_buildDir_3497_ = lean_ctor_get(v_cfg_3489_, 5);
v_leanLibDir_3498_ = lean_ctor_get(v_cfg_3489_, 6);
v_nativeLibDir_3499_ = lean_ctor_get(v_cfg_3489_, 7);
v_binDir_3500_ = lean_ctor_get(v_cfg_3489_, 8);
v_irDir_3501_ = lean_ctor_get(v_cfg_3489_, 9);
v_releaseRepo_3502_ = lean_ctor_get(v_cfg_3489_, 10);
v_buildArchive_3503_ = lean_ctor_get(v_cfg_3489_, 11);
v_preferReleaseBuild_3504_ = lean_ctor_get_uint8(v_cfg_3489_, sizeof(void*)*26 + 2);
v_testDriver_3505_ = lean_ctor_get(v_cfg_3489_, 12);
v_testDriverArgs_3506_ = lean_ctor_get(v_cfg_3489_, 13);
v_lintDriver_3507_ = lean_ctor_get(v_cfg_3489_, 14);
v_lintDriverArgs_3508_ = lean_ctor_get(v_cfg_3489_, 15);
v_version_3509_ = lean_ctor_get(v_cfg_3489_, 16);
v_versionTags_3510_ = lean_ctor_get(v_cfg_3489_, 17);
v_description_3511_ = lean_ctor_get(v_cfg_3489_, 18);
v_keywords_3512_ = lean_ctor_get(v_cfg_3489_, 19);
v_homepage_3513_ = lean_ctor_get(v_cfg_3489_, 20);
v_license_3514_ = lean_ctor_get(v_cfg_3489_, 21);
v_licenseFiles_3515_ = lean_ctor_get(v_cfg_3489_, 22);
v_readmeFile_3516_ = lean_ctor_get(v_cfg_3489_, 23);
v_reservoir_3517_ = lean_ctor_get_uint8(v_cfg_3489_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3518_ = lean_ctor_get(v_cfg_3489_, 24);
v_restoreAllArtifacts_x3f_3519_ = lean_ctor_get(v_cfg_3489_, 25);
v_libPrefixOnWindows_3520_ = lean_ctor_get_uint8(v_cfg_3489_, sizeof(void*)*26 + 4);
v_allowImportAll_3521_ = lean_ctor_get_uint8(v_cfg_3489_, sizeof(void*)*26 + 5);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_cfg_3489_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v_cfg_3489_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3519_);
lean_inc(v_enableArtifactCache_x3f_3518_);
lean_inc(v_readmeFile_3516_);
lean_inc(v_licenseFiles_3515_);
lean_inc(v_license_3514_);
lean_inc(v_homepage_3513_);
lean_inc(v_keywords_3512_);
lean_inc(v_description_3511_);
lean_inc(v_versionTags_3510_);
lean_inc(v_version_3509_);
lean_inc(v_lintDriverArgs_3508_);
lean_inc(v_lintDriver_3507_);
lean_inc(v_testDriverArgs_3506_);
lean_inc(v_testDriver_3505_);
lean_inc(v_buildArchive_3503_);
lean_inc(v_releaseRepo_3502_);
lean_inc(v_irDir_3501_);
lean_inc(v_binDir_3500_);
lean_inc(v_nativeLibDir_3499_);
lean_inc(v_leanLibDir_3498_);
lean_inc(v_buildDir_3497_);
lean_inc(v_srcDir_3496_);
lean_inc(v_moreGlobalServerArgs_3495_);
lean_inc(v_extraDepTargets_3493_);
lean_inc(v_toLeanConfig_3491_);
lean_inc(v_toWorkspaceConfig_3490_);
lean_dec(v_cfg_3489_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_toWorkspaceConfig_3490_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_toLeanConfig_3491_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_extraDepTargets_3493_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_moreGlobalServerArgs_3495_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_srcDir_3496_);
lean_ctor_set(v_reuseFailAlloc_3527_, 5, v_buildDir_3497_);
lean_ctor_set(v_reuseFailAlloc_3527_, 6, v_leanLibDir_3498_);
lean_ctor_set(v_reuseFailAlloc_3527_, 7, v_nativeLibDir_3499_);
lean_ctor_set(v_reuseFailAlloc_3527_, 8, v_binDir_3500_);
lean_ctor_set(v_reuseFailAlloc_3527_, 9, v_irDir_3501_);
lean_ctor_set(v_reuseFailAlloc_3527_, 10, v_releaseRepo_3502_);
lean_ctor_set(v_reuseFailAlloc_3527_, 11, v_buildArchive_3503_);
lean_ctor_set(v_reuseFailAlloc_3527_, 12, v_testDriver_3505_);
lean_ctor_set(v_reuseFailAlloc_3527_, 13, v_testDriverArgs_3506_);
lean_ctor_set(v_reuseFailAlloc_3527_, 14, v_lintDriver_3507_);
lean_ctor_set(v_reuseFailAlloc_3527_, 15, v_lintDriverArgs_3508_);
lean_ctor_set(v_reuseFailAlloc_3527_, 16, v_version_3509_);
lean_ctor_set(v_reuseFailAlloc_3527_, 17, v_versionTags_3510_);
lean_ctor_set(v_reuseFailAlloc_3527_, 18, v_description_3511_);
lean_ctor_set(v_reuseFailAlloc_3527_, 19, v_keywords_3512_);
lean_ctor_set(v_reuseFailAlloc_3527_, 20, v_homepage_3513_);
lean_ctor_set(v_reuseFailAlloc_3527_, 21, v_license_3514_);
lean_ctor_set(v_reuseFailAlloc_3527_, 22, v_licenseFiles_3515_);
lean_ctor_set(v_reuseFailAlloc_3527_, 23, v_readmeFile_3516_);
lean_ctor_set(v_reuseFailAlloc_3527_, 24, v_enableArtifactCache_x3f_3518_);
lean_ctor_set(v_reuseFailAlloc_3527_, 25, v_restoreAllArtifacts_x3f_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*26, v_bootstrap_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*26 + 1, v_precompileModules_3494_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3504_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*26 + 3, v_reservoir_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*26 + 5, v_allowImportAll_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*26 + 6, v_val_3488_);
return v___x_3526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed(lean_object* v_val_3529_, lean_object* v_cfg_3530_){
_start:
{
uint8_t v_val_134__boxed_3531_; lean_object* v_res_3532_; 
v_val_134__boxed_3531_ = lean_unbox(v_val_3529_);
v_res_3532_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__1(v_val_134__boxed_3531_, v_cfg_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__2(lean_object* v_f_3533_, lean_object* v_cfg_3534_){
_start:
{
lean_object* v_toWorkspaceConfig_3535_; lean_object* v_toLeanConfig_3536_; uint8_t v_bootstrap_3537_; lean_object* v_extraDepTargets_3538_; uint8_t v_precompileModules_3539_; lean_object* v_moreGlobalServerArgs_3540_; lean_object* v_srcDir_3541_; lean_object* v_buildDir_3542_; lean_object* v_leanLibDir_3543_; lean_object* v_nativeLibDir_3544_; lean_object* v_binDir_3545_; lean_object* v_irDir_3546_; lean_object* v_releaseRepo_3547_; lean_object* v_buildArchive_3548_; uint8_t v_preferReleaseBuild_3549_; lean_object* v_testDriver_3550_; lean_object* v_testDriverArgs_3551_; lean_object* v_lintDriver_3552_; lean_object* v_lintDriverArgs_3553_; lean_object* v_version_3554_; lean_object* v_versionTags_3555_; lean_object* v_description_3556_; lean_object* v_keywords_3557_; lean_object* v_homepage_3558_; lean_object* v_license_3559_; lean_object* v_licenseFiles_3560_; lean_object* v_readmeFile_3561_; uint8_t v_reservoir_3562_; lean_object* v_enableArtifactCache_x3f_3563_; lean_object* v_restoreAllArtifacts_x3f_3564_; uint8_t v_libPrefixOnWindows_3565_; uint8_t v_allowImportAll_3566_; uint8_t v_fixedToolchain_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
v_toWorkspaceConfig_3535_ = lean_ctor_get(v_cfg_3534_, 0);
v_toLeanConfig_3536_ = lean_ctor_get(v_cfg_3534_, 1);
v_bootstrap_3537_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26);
v_extraDepTargets_3538_ = lean_ctor_get(v_cfg_3534_, 2);
v_precompileModules_3539_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3540_ = lean_ctor_get(v_cfg_3534_, 3);
v_srcDir_3541_ = lean_ctor_get(v_cfg_3534_, 4);
v_buildDir_3542_ = lean_ctor_get(v_cfg_3534_, 5);
v_leanLibDir_3543_ = lean_ctor_get(v_cfg_3534_, 6);
v_nativeLibDir_3544_ = lean_ctor_get(v_cfg_3534_, 7);
v_binDir_3545_ = lean_ctor_get(v_cfg_3534_, 8);
v_irDir_3546_ = lean_ctor_get(v_cfg_3534_, 9);
v_releaseRepo_3547_ = lean_ctor_get(v_cfg_3534_, 10);
v_buildArchive_3548_ = lean_ctor_get(v_cfg_3534_, 11);
v_preferReleaseBuild_3549_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26 + 2);
v_testDriver_3550_ = lean_ctor_get(v_cfg_3534_, 12);
v_testDriverArgs_3551_ = lean_ctor_get(v_cfg_3534_, 13);
v_lintDriver_3552_ = lean_ctor_get(v_cfg_3534_, 14);
v_lintDriverArgs_3553_ = lean_ctor_get(v_cfg_3534_, 15);
v_version_3554_ = lean_ctor_get(v_cfg_3534_, 16);
v_versionTags_3555_ = lean_ctor_get(v_cfg_3534_, 17);
v_description_3556_ = lean_ctor_get(v_cfg_3534_, 18);
v_keywords_3557_ = lean_ctor_get(v_cfg_3534_, 19);
v_homepage_3558_ = lean_ctor_get(v_cfg_3534_, 20);
v_license_3559_ = lean_ctor_get(v_cfg_3534_, 21);
v_licenseFiles_3560_ = lean_ctor_get(v_cfg_3534_, 22);
v_readmeFile_3561_ = lean_ctor_get(v_cfg_3534_, 23);
v_reservoir_3562_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3563_ = lean_ctor_get(v_cfg_3534_, 24);
v_restoreAllArtifacts_x3f_3564_ = lean_ctor_get(v_cfg_3534_, 25);
v_libPrefixOnWindows_3565_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26 + 4);
v_allowImportAll_3566_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26 + 5);
v_fixedToolchain_3567_ = lean_ctor_get_uint8(v_cfg_3534_, sizeof(void*)*26 + 6);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_cfg_3534_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3569_ = v_cfg_3534_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3564_);
lean_inc(v_enableArtifactCache_x3f_3563_);
lean_inc(v_readmeFile_3561_);
lean_inc(v_licenseFiles_3560_);
lean_inc(v_license_3559_);
lean_inc(v_homepage_3558_);
lean_inc(v_keywords_3557_);
lean_inc(v_description_3556_);
lean_inc(v_versionTags_3555_);
lean_inc(v_version_3554_);
lean_inc(v_lintDriverArgs_3553_);
lean_inc(v_lintDriver_3552_);
lean_inc(v_testDriverArgs_3551_);
lean_inc(v_testDriver_3550_);
lean_inc(v_buildArchive_3548_);
lean_inc(v_releaseRepo_3547_);
lean_inc(v_irDir_3546_);
lean_inc(v_binDir_3545_);
lean_inc(v_nativeLibDir_3544_);
lean_inc(v_leanLibDir_3543_);
lean_inc(v_buildDir_3542_);
lean_inc(v_srcDir_3541_);
lean_inc(v_moreGlobalServerArgs_3540_);
lean_inc(v_extraDepTargets_3538_);
lean_inc(v_toLeanConfig_3536_);
lean_inc(v_toWorkspaceConfig_3535_);
lean_dec(v_cfg_3534_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3571_ = lean_box(v_fixedToolchain_3567_);
v___x_3572_ = lean_apply_1(v_f_3533_, v___x_3571_);
if (v_isShared_3570_ == 0)
{
v___x_3574_ = v___x_3569_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_toWorkspaceConfig_3535_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_toLeanConfig_3536_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_extraDepTargets_3538_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_moreGlobalServerArgs_3540_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_srcDir_3541_);
lean_ctor_set(v_reuseFailAlloc_3576_, 5, v_buildDir_3542_);
lean_ctor_set(v_reuseFailAlloc_3576_, 6, v_leanLibDir_3543_);
lean_ctor_set(v_reuseFailAlloc_3576_, 7, v_nativeLibDir_3544_);
lean_ctor_set(v_reuseFailAlloc_3576_, 8, v_binDir_3545_);
lean_ctor_set(v_reuseFailAlloc_3576_, 9, v_irDir_3546_);
lean_ctor_set(v_reuseFailAlloc_3576_, 10, v_releaseRepo_3547_);
lean_ctor_set(v_reuseFailAlloc_3576_, 11, v_buildArchive_3548_);
lean_ctor_set(v_reuseFailAlloc_3576_, 12, v_testDriver_3550_);
lean_ctor_set(v_reuseFailAlloc_3576_, 13, v_testDriverArgs_3551_);
lean_ctor_set(v_reuseFailAlloc_3576_, 14, v_lintDriver_3552_);
lean_ctor_set(v_reuseFailAlloc_3576_, 15, v_lintDriverArgs_3553_);
lean_ctor_set(v_reuseFailAlloc_3576_, 16, v_version_3554_);
lean_ctor_set(v_reuseFailAlloc_3576_, 17, v_versionTags_3555_);
lean_ctor_set(v_reuseFailAlloc_3576_, 18, v_description_3556_);
lean_ctor_set(v_reuseFailAlloc_3576_, 19, v_keywords_3557_);
lean_ctor_set(v_reuseFailAlloc_3576_, 20, v_homepage_3558_);
lean_ctor_set(v_reuseFailAlloc_3576_, 21, v_license_3559_);
lean_ctor_set(v_reuseFailAlloc_3576_, 22, v_licenseFiles_3560_);
lean_ctor_set(v_reuseFailAlloc_3576_, 23, v_readmeFile_3561_);
lean_ctor_set(v_reuseFailAlloc_3576_, 24, v_enableArtifactCache_x3f_3563_);
lean_ctor_set(v_reuseFailAlloc_3576_, 25, v_restoreAllArtifacts_x3f_3564_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*26, v_bootstrap_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*26 + 1, v_precompileModules_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3549_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*26 + 3, v_reservoir_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3565_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*26 + 5, v_allowImportAll_3566_);
v___x_3574_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_unbox(v___x_3572_);
lean_ctor_set_uint8(v___x_3574_, sizeof(void*)*26 + 6, v___x_3575_);
return v___x_3574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_3586_, lean_object* v_n_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___closed__3));
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_3589_, lean_object* v_n_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3589_, v_n_3590_);
lean_dec(v_n_3590_);
lean_dec(v_p_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_3592_, lean_object* v_n_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3592_, v_n_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_3595_, lean_object* v_n_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_3595_, v_n_3596_);
lean_dec(v_n_3596_);
lean_dec(v_p_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* v_cfg_3598_){
_start:
{
lean_object* v_toWorkspaceConfig_3599_; 
v_toWorkspaceConfig_3599_ = lean_ctor_get(v_cfg_3598_, 0);
lean_inc_ref(v_toWorkspaceConfig_3599_);
return v_toWorkspaceConfig_3599_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* v_cfg_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(v_cfg_3600_);
lean_dec_ref(v_cfg_3600_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* v_val_3602_, lean_object* v_cfg_3603_){
_start:
{
lean_object* v_toLeanConfig_3604_; uint8_t v_bootstrap_3605_; lean_object* v_extraDepTargets_3606_; uint8_t v_precompileModules_3607_; lean_object* v_moreGlobalServerArgs_3608_; lean_object* v_srcDir_3609_; lean_object* v_buildDir_3610_; lean_object* v_leanLibDir_3611_; lean_object* v_nativeLibDir_3612_; lean_object* v_binDir_3613_; lean_object* v_irDir_3614_; lean_object* v_releaseRepo_3615_; lean_object* v_buildArchive_3616_; uint8_t v_preferReleaseBuild_3617_; lean_object* v_testDriver_3618_; lean_object* v_testDriverArgs_3619_; lean_object* v_lintDriver_3620_; lean_object* v_lintDriverArgs_3621_; lean_object* v_version_3622_; lean_object* v_versionTags_3623_; lean_object* v_description_3624_; lean_object* v_keywords_3625_; lean_object* v_homepage_3626_; lean_object* v_license_3627_; lean_object* v_licenseFiles_3628_; lean_object* v_readmeFile_3629_; uint8_t v_reservoir_3630_; lean_object* v_enableArtifactCache_x3f_3631_; lean_object* v_restoreAllArtifacts_x3f_3632_; uint8_t v_libPrefixOnWindows_3633_; uint8_t v_allowImportAll_3634_; uint8_t v_fixedToolchain_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_toLeanConfig_3604_ = lean_ctor_get(v_cfg_3603_, 1);
v_bootstrap_3605_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26);
v_extraDepTargets_3606_ = lean_ctor_get(v_cfg_3603_, 2);
v_precompileModules_3607_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3608_ = lean_ctor_get(v_cfg_3603_, 3);
v_srcDir_3609_ = lean_ctor_get(v_cfg_3603_, 4);
v_buildDir_3610_ = lean_ctor_get(v_cfg_3603_, 5);
v_leanLibDir_3611_ = lean_ctor_get(v_cfg_3603_, 6);
v_nativeLibDir_3612_ = lean_ctor_get(v_cfg_3603_, 7);
v_binDir_3613_ = lean_ctor_get(v_cfg_3603_, 8);
v_irDir_3614_ = lean_ctor_get(v_cfg_3603_, 9);
v_releaseRepo_3615_ = lean_ctor_get(v_cfg_3603_, 10);
v_buildArchive_3616_ = lean_ctor_get(v_cfg_3603_, 11);
v_preferReleaseBuild_3617_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26 + 2);
v_testDriver_3618_ = lean_ctor_get(v_cfg_3603_, 12);
v_testDriverArgs_3619_ = lean_ctor_get(v_cfg_3603_, 13);
v_lintDriver_3620_ = lean_ctor_get(v_cfg_3603_, 14);
v_lintDriverArgs_3621_ = lean_ctor_get(v_cfg_3603_, 15);
v_version_3622_ = lean_ctor_get(v_cfg_3603_, 16);
v_versionTags_3623_ = lean_ctor_get(v_cfg_3603_, 17);
v_description_3624_ = lean_ctor_get(v_cfg_3603_, 18);
v_keywords_3625_ = lean_ctor_get(v_cfg_3603_, 19);
v_homepage_3626_ = lean_ctor_get(v_cfg_3603_, 20);
v_license_3627_ = lean_ctor_get(v_cfg_3603_, 21);
v_licenseFiles_3628_ = lean_ctor_get(v_cfg_3603_, 22);
v_readmeFile_3629_ = lean_ctor_get(v_cfg_3603_, 23);
v_reservoir_3630_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3631_ = lean_ctor_get(v_cfg_3603_, 24);
v_restoreAllArtifacts_x3f_3632_ = lean_ctor_get(v_cfg_3603_, 25);
v_libPrefixOnWindows_3633_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26 + 4);
v_allowImportAll_3634_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26 + 5);
v_fixedToolchain_3635_ = lean_ctor_get_uint8(v_cfg_3603_, sizeof(void*)*26 + 6);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_cfg_3603_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v_cfg_3603_, 0);
lean_dec(v_unused_3643_);
v___x_3637_ = v_cfg_3603_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3632_);
lean_inc(v_enableArtifactCache_x3f_3631_);
lean_inc(v_readmeFile_3629_);
lean_inc(v_licenseFiles_3628_);
lean_inc(v_license_3627_);
lean_inc(v_homepage_3626_);
lean_inc(v_keywords_3625_);
lean_inc(v_description_3624_);
lean_inc(v_versionTags_3623_);
lean_inc(v_version_3622_);
lean_inc(v_lintDriverArgs_3621_);
lean_inc(v_lintDriver_3620_);
lean_inc(v_testDriverArgs_3619_);
lean_inc(v_testDriver_3618_);
lean_inc(v_buildArchive_3616_);
lean_inc(v_releaseRepo_3615_);
lean_inc(v_irDir_3614_);
lean_inc(v_binDir_3613_);
lean_inc(v_nativeLibDir_3612_);
lean_inc(v_leanLibDir_3611_);
lean_inc(v_buildDir_3610_);
lean_inc(v_srcDir_3609_);
lean_inc(v_moreGlobalServerArgs_3608_);
lean_inc(v_extraDepTargets_3606_);
lean_inc(v_toLeanConfig_3604_);
lean_dec(v_cfg_3603_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v_val_3602_);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_val_3602_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_toLeanConfig_3604_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_extraDepTargets_3606_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_moreGlobalServerArgs_3608_);
lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_srcDir_3609_);
lean_ctor_set(v_reuseFailAlloc_3641_, 5, v_buildDir_3610_);
lean_ctor_set(v_reuseFailAlloc_3641_, 6, v_leanLibDir_3611_);
lean_ctor_set(v_reuseFailAlloc_3641_, 7, v_nativeLibDir_3612_);
lean_ctor_set(v_reuseFailAlloc_3641_, 8, v_binDir_3613_);
lean_ctor_set(v_reuseFailAlloc_3641_, 9, v_irDir_3614_);
lean_ctor_set(v_reuseFailAlloc_3641_, 10, v_releaseRepo_3615_);
lean_ctor_set(v_reuseFailAlloc_3641_, 11, v_buildArchive_3616_);
lean_ctor_set(v_reuseFailAlloc_3641_, 12, v_testDriver_3618_);
lean_ctor_set(v_reuseFailAlloc_3641_, 13, v_testDriverArgs_3619_);
lean_ctor_set(v_reuseFailAlloc_3641_, 14, v_lintDriver_3620_);
lean_ctor_set(v_reuseFailAlloc_3641_, 15, v_lintDriverArgs_3621_);
lean_ctor_set(v_reuseFailAlloc_3641_, 16, v_version_3622_);
lean_ctor_set(v_reuseFailAlloc_3641_, 17, v_versionTags_3623_);
lean_ctor_set(v_reuseFailAlloc_3641_, 18, v_description_3624_);
lean_ctor_set(v_reuseFailAlloc_3641_, 19, v_keywords_3625_);
lean_ctor_set(v_reuseFailAlloc_3641_, 20, v_homepage_3626_);
lean_ctor_set(v_reuseFailAlloc_3641_, 21, v_license_3627_);
lean_ctor_set(v_reuseFailAlloc_3641_, 22, v_licenseFiles_3628_);
lean_ctor_set(v_reuseFailAlloc_3641_, 23, v_readmeFile_3629_);
lean_ctor_set(v_reuseFailAlloc_3641_, 24, v_enableArtifactCache_x3f_3631_);
lean_ctor_set(v_reuseFailAlloc_3641_, 25, v_restoreAllArtifacts_x3f_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26, v_bootstrap_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26 + 1, v_precompileModules_3607_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3617_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26 + 3, v_reservoir_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26 + 5, v_allowImportAll_3634_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, sizeof(void*)*26 + 6, v_fixedToolchain_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* v_f_3644_, lean_object* v_cfg_3645_){
_start:
{
lean_object* v_toWorkspaceConfig_3646_; lean_object* v_toLeanConfig_3647_; uint8_t v_bootstrap_3648_; lean_object* v_extraDepTargets_3649_; uint8_t v_precompileModules_3650_; lean_object* v_moreGlobalServerArgs_3651_; lean_object* v_srcDir_3652_; lean_object* v_buildDir_3653_; lean_object* v_leanLibDir_3654_; lean_object* v_nativeLibDir_3655_; lean_object* v_binDir_3656_; lean_object* v_irDir_3657_; lean_object* v_releaseRepo_3658_; lean_object* v_buildArchive_3659_; uint8_t v_preferReleaseBuild_3660_; lean_object* v_testDriver_3661_; lean_object* v_testDriverArgs_3662_; lean_object* v_lintDriver_3663_; lean_object* v_lintDriverArgs_3664_; lean_object* v_version_3665_; lean_object* v_versionTags_3666_; lean_object* v_description_3667_; lean_object* v_keywords_3668_; lean_object* v_homepage_3669_; lean_object* v_license_3670_; lean_object* v_licenseFiles_3671_; lean_object* v_readmeFile_3672_; uint8_t v_reservoir_3673_; lean_object* v_enableArtifactCache_x3f_3674_; lean_object* v_restoreAllArtifacts_x3f_3675_; uint8_t v_libPrefixOnWindows_3676_; uint8_t v_allowImportAll_3677_; uint8_t v_fixedToolchain_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3686_; 
v_toWorkspaceConfig_3646_ = lean_ctor_get(v_cfg_3645_, 0);
v_toLeanConfig_3647_ = lean_ctor_get(v_cfg_3645_, 1);
v_bootstrap_3648_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26);
v_extraDepTargets_3649_ = lean_ctor_get(v_cfg_3645_, 2);
v_precompileModules_3650_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3651_ = lean_ctor_get(v_cfg_3645_, 3);
v_srcDir_3652_ = lean_ctor_get(v_cfg_3645_, 4);
v_buildDir_3653_ = lean_ctor_get(v_cfg_3645_, 5);
v_leanLibDir_3654_ = lean_ctor_get(v_cfg_3645_, 6);
v_nativeLibDir_3655_ = lean_ctor_get(v_cfg_3645_, 7);
v_binDir_3656_ = lean_ctor_get(v_cfg_3645_, 8);
v_irDir_3657_ = lean_ctor_get(v_cfg_3645_, 9);
v_releaseRepo_3658_ = lean_ctor_get(v_cfg_3645_, 10);
v_buildArchive_3659_ = lean_ctor_get(v_cfg_3645_, 11);
v_preferReleaseBuild_3660_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26 + 2);
v_testDriver_3661_ = lean_ctor_get(v_cfg_3645_, 12);
v_testDriverArgs_3662_ = lean_ctor_get(v_cfg_3645_, 13);
v_lintDriver_3663_ = lean_ctor_get(v_cfg_3645_, 14);
v_lintDriverArgs_3664_ = lean_ctor_get(v_cfg_3645_, 15);
v_version_3665_ = lean_ctor_get(v_cfg_3645_, 16);
v_versionTags_3666_ = lean_ctor_get(v_cfg_3645_, 17);
v_description_3667_ = lean_ctor_get(v_cfg_3645_, 18);
v_keywords_3668_ = lean_ctor_get(v_cfg_3645_, 19);
v_homepage_3669_ = lean_ctor_get(v_cfg_3645_, 20);
v_license_3670_ = lean_ctor_get(v_cfg_3645_, 21);
v_licenseFiles_3671_ = lean_ctor_get(v_cfg_3645_, 22);
v_readmeFile_3672_ = lean_ctor_get(v_cfg_3645_, 23);
v_reservoir_3673_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3674_ = lean_ctor_get(v_cfg_3645_, 24);
v_restoreAllArtifacts_x3f_3675_ = lean_ctor_get(v_cfg_3645_, 25);
v_libPrefixOnWindows_3676_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26 + 4);
v_allowImportAll_3677_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26 + 5);
v_fixedToolchain_3678_ = lean_ctor_get_uint8(v_cfg_3645_, sizeof(void*)*26 + 6);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_cfg_3645_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3680_ = v_cfg_3645_;
v_isShared_3681_ = v_isSharedCheck_3686_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3675_);
lean_inc(v_enableArtifactCache_x3f_3674_);
lean_inc(v_readmeFile_3672_);
lean_inc(v_licenseFiles_3671_);
lean_inc(v_license_3670_);
lean_inc(v_homepage_3669_);
lean_inc(v_keywords_3668_);
lean_inc(v_description_3667_);
lean_inc(v_versionTags_3666_);
lean_inc(v_version_3665_);
lean_inc(v_lintDriverArgs_3664_);
lean_inc(v_lintDriver_3663_);
lean_inc(v_testDriverArgs_3662_);
lean_inc(v_testDriver_3661_);
lean_inc(v_buildArchive_3659_);
lean_inc(v_releaseRepo_3658_);
lean_inc(v_irDir_3657_);
lean_inc(v_binDir_3656_);
lean_inc(v_nativeLibDir_3655_);
lean_inc(v_leanLibDir_3654_);
lean_inc(v_buildDir_3653_);
lean_inc(v_srcDir_3652_);
lean_inc(v_moreGlobalServerArgs_3651_);
lean_inc(v_extraDepTargets_3649_);
lean_inc(v_toLeanConfig_3647_);
lean_inc(v_toWorkspaceConfig_3646_);
lean_dec(v_cfg_3645_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3686_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = lean_apply_1(v_f_3644_, v_toWorkspaceConfig_3646_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3682_);
v___x_3684_ = v___x_3680_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_toLeanConfig_3647_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v_extraDepTargets_3649_);
lean_ctor_set(v_reuseFailAlloc_3685_, 3, v_moreGlobalServerArgs_3651_);
lean_ctor_set(v_reuseFailAlloc_3685_, 4, v_srcDir_3652_);
lean_ctor_set(v_reuseFailAlloc_3685_, 5, v_buildDir_3653_);
lean_ctor_set(v_reuseFailAlloc_3685_, 6, v_leanLibDir_3654_);
lean_ctor_set(v_reuseFailAlloc_3685_, 7, v_nativeLibDir_3655_);
lean_ctor_set(v_reuseFailAlloc_3685_, 8, v_binDir_3656_);
lean_ctor_set(v_reuseFailAlloc_3685_, 9, v_irDir_3657_);
lean_ctor_set(v_reuseFailAlloc_3685_, 10, v_releaseRepo_3658_);
lean_ctor_set(v_reuseFailAlloc_3685_, 11, v_buildArchive_3659_);
lean_ctor_set(v_reuseFailAlloc_3685_, 12, v_testDriver_3661_);
lean_ctor_set(v_reuseFailAlloc_3685_, 13, v_testDriverArgs_3662_);
lean_ctor_set(v_reuseFailAlloc_3685_, 14, v_lintDriver_3663_);
lean_ctor_set(v_reuseFailAlloc_3685_, 15, v_lintDriverArgs_3664_);
lean_ctor_set(v_reuseFailAlloc_3685_, 16, v_version_3665_);
lean_ctor_set(v_reuseFailAlloc_3685_, 17, v_versionTags_3666_);
lean_ctor_set(v_reuseFailAlloc_3685_, 18, v_description_3667_);
lean_ctor_set(v_reuseFailAlloc_3685_, 19, v_keywords_3668_);
lean_ctor_set(v_reuseFailAlloc_3685_, 20, v_homepage_3669_);
lean_ctor_set(v_reuseFailAlloc_3685_, 21, v_license_3670_);
lean_ctor_set(v_reuseFailAlloc_3685_, 22, v_licenseFiles_3671_);
lean_ctor_set(v_reuseFailAlloc_3685_, 23, v_readmeFile_3672_);
lean_ctor_set(v_reuseFailAlloc_3685_, 24, v_enableArtifactCache_x3f_3674_);
lean_ctor_set(v_reuseFailAlloc_3685_, 25, v_restoreAllArtifacts_x3f_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26, v_bootstrap_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26 + 1, v_precompileModules_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26 + 3, v_reservoir_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26 + 5, v_allowImportAll_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3685_, sizeof(void*)*26 + 6, v_fixedToolchain_3678_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* v_x_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lake_defaultPackagesDir;
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* v_x_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(v_x_3689_);
lean_dec_ref(v_x_3689_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_3700_, lean_object* v_n_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_3703_, lean_object* v_n_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3703_, v_n_3704_);
lean_dec(v_n_3704_);
lean_dec(v_p_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_3706_, lean_object* v_n_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3706_, v_n_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_3709_, lean_object* v_n_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_3709_, v_n_3710_);
lean_dec(v_n_3710_);
lean_dec(v_p_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_3712_){
_start:
{
lean_object* v_toLeanConfig_3713_; 
v_toLeanConfig_3713_ = lean_ctor_get(v_cfg_3712_, 1);
lean_inc_ref(v_toLeanConfig_3713_);
return v_toLeanConfig_3713_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(v_cfg_3714_);
lean_dec_ref(v_cfg_3714_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* v_val_3716_, lean_object* v_cfg_3717_){
_start:
{
lean_object* v_toWorkspaceConfig_3718_; uint8_t v_bootstrap_3719_; lean_object* v_extraDepTargets_3720_; uint8_t v_precompileModules_3721_; lean_object* v_moreGlobalServerArgs_3722_; lean_object* v_srcDir_3723_; lean_object* v_buildDir_3724_; lean_object* v_leanLibDir_3725_; lean_object* v_nativeLibDir_3726_; lean_object* v_binDir_3727_; lean_object* v_irDir_3728_; lean_object* v_releaseRepo_3729_; lean_object* v_buildArchive_3730_; uint8_t v_preferReleaseBuild_3731_; lean_object* v_testDriver_3732_; lean_object* v_testDriverArgs_3733_; lean_object* v_lintDriver_3734_; lean_object* v_lintDriverArgs_3735_; lean_object* v_version_3736_; lean_object* v_versionTags_3737_; lean_object* v_description_3738_; lean_object* v_keywords_3739_; lean_object* v_homepage_3740_; lean_object* v_license_3741_; lean_object* v_licenseFiles_3742_; lean_object* v_readmeFile_3743_; uint8_t v_reservoir_3744_; lean_object* v_enableArtifactCache_x3f_3745_; lean_object* v_restoreAllArtifacts_x3f_3746_; uint8_t v_libPrefixOnWindows_3747_; uint8_t v_allowImportAll_3748_; uint8_t v_fixedToolchain_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
v_toWorkspaceConfig_3718_ = lean_ctor_get(v_cfg_3717_, 0);
v_bootstrap_3719_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26);
v_extraDepTargets_3720_ = lean_ctor_get(v_cfg_3717_, 2);
v_precompileModules_3721_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3722_ = lean_ctor_get(v_cfg_3717_, 3);
v_srcDir_3723_ = lean_ctor_get(v_cfg_3717_, 4);
v_buildDir_3724_ = lean_ctor_get(v_cfg_3717_, 5);
v_leanLibDir_3725_ = lean_ctor_get(v_cfg_3717_, 6);
v_nativeLibDir_3726_ = lean_ctor_get(v_cfg_3717_, 7);
v_binDir_3727_ = lean_ctor_get(v_cfg_3717_, 8);
v_irDir_3728_ = lean_ctor_get(v_cfg_3717_, 9);
v_releaseRepo_3729_ = lean_ctor_get(v_cfg_3717_, 10);
v_buildArchive_3730_ = lean_ctor_get(v_cfg_3717_, 11);
v_preferReleaseBuild_3731_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26 + 2);
v_testDriver_3732_ = lean_ctor_get(v_cfg_3717_, 12);
v_testDriverArgs_3733_ = lean_ctor_get(v_cfg_3717_, 13);
v_lintDriver_3734_ = lean_ctor_get(v_cfg_3717_, 14);
v_lintDriverArgs_3735_ = lean_ctor_get(v_cfg_3717_, 15);
v_version_3736_ = lean_ctor_get(v_cfg_3717_, 16);
v_versionTags_3737_ = lean_ctor_get(v_cfg_3717_, 17);
v_description_3738_ = lean_ctor_get(v_cfg_3717_, 18);
v_keywords_3739_ = lean_ctor_get(v_cfg_3717_, 19);
v_homepage_3740_ = lean_ctor_get(v_cfg_3717_, 20);
v_license_3741_ = lean_ctor_get(v_cfg_3717_, 21);
v_licenseFiles_3742_ = lean_ctor_get(v_cfg_3717_, 22);
v_readmeFile_3743_ = lean_ctor_get(v_cfg_3717_, 23);
v_reservoir_3744_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3745_ = lean_ctor_get(v_cfg_3717_, 24);
v_restoreAllArtifacts_x3f_3746_ = lean_ctor_get(v_cfg_3717_, 25);
v_libPrefixOnWindows_3747_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26 + 4);
v_allowImportAll_3748_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26 + 5);
v_fixedToolchain_3749_ = lean_ctor_get_uint8(v_cfg_3717_, sizeof(void*)*26 + 6);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_cfg_3717_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; 
v_unused_3757_ = lean_ctor_get(v_cfg_3717_, 1);
lean_dec(v_unused_3757_);
v___x_3751_ = v_cfg_3717_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3746_);
lean_inc(v_enableArtifactCache_x3f_3745_);
lean_inc(v_readmeFile_3743_);
lean_inc(v_licenseFiles_3742_);
lean_inc(v_license_3741_);
lean_inc(v_homepage_3740_);
lean_inc(v_keywords_3739_);
lean_inc(v_description_3738_);
lean_inc(v_versionTags_3737_);
lean_inc(v_version_3736_);
lean_inc(v_lintDriverArgs_3735_);
lean_inc(v_lintDriver_3734_);
lean_inc(v_testDriverArgs_3733_);
lean_inc(v_testDriver_3732_);
lean_inc(v_buildArchive_3730_);
lean_inc(v_releaseRepo_3729_);
lean_inc(v_irDir_3728_);
lean_inc(v_binDir_3727_);
lean_inc(v_nativeLibDir_3726_);
lean_inc(v_leanLibDir_3725_);
lean_inc(v_buildDir_3724_);
lean_inc(v_srcDir_3723_);
lean_inc(v_moreGlobalServerArgs_3722_);
lean_inc(v_extraDepTargets_3720_);
lean_inc(v_toWorkspaceConfig_3718_);
lean_dec(v_cfg_3717_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 1, v_val_3716_);
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_toWorkspaceConfig_3718_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_val_3716_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_extraDepTargets_3720_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_moreGlobalServerArgs_3722_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_srcDir_3723_);
lean_ctor_set(v_reuseFailAlloc_3755_, 5, v_buildDir_3724_);
lean_ctor_set(v_reuseFailAlloc_3755_, 6, v_leanLibDir_3725_);
lean_ctor_set(v_reuseFailAlloc_3755_, 7, v_nativeLibDir_3726_);
lean_ctor_set(v_reuseFailAlloc_3755_, 8, v_binDir_3727_);
lean_ctor_set(v_reuseFailAlloc_3755_, 9, v_irDir_3728_);
lean_ctor_set(v_reuseFailAlloc_3755_, 10, v_releaseRepo_3729_);
lean_ctor_set(v_reuseFailAlloc_3755_, 11, v_buildArchive_3730_);
lean_ctor_set(v_reuseFailAlloc_3755_, 12, v_testDriver_3732_);
lean_ctor_set(v_reuseFailAlloc_3755_, 13, v_testDriverArgs_3733_);
lean_ctor_set(v_reuseFailAlloc_3755_, 14, v_lintDriver_3734_);
lean_ctor_set(v_reuseFailAlloc_3755_, 15, v_lintDriverArgs_3735_);
lean_ctor_set(v_reuseFailAlloc_3755_, 16, v_version_3736_);
lean_ctor_set(v_reuseFailAlloc_3755_, 17, v_versionTags_3737_);
lean_ctor_set(v_reuseFailAlloc_3755_, 18, v_description_3738_);
lean_ctor_set(v_reuseFailAlloc_3755_, 19, v_keywords_3739_);
lean_ctor_set(v_reuseFailAlloc_3755_, 20, v_homepage_3740_);
lean_ctor_set(v_reuseFailAlloc_3755_, 21, v_license_3741_);
lean_ctor_set(v_reuseFailAlloc_3755_, 22, v_licenseFiles_3742_);
lean_ctor_set(v_reuseFailAlloc_3755_, 23, v_readmeFile_3743_);
lean_ctor_set(v_reuseFailAlloc_3755_, 24, v_enableArtifactCache_x3f_3745_);
lean_ctor_set(v_reuseFailAlloc_3755_, 25, v_restoreAllArtifacts_x3f_3746_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26, v_bootstrap_3719_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26 + 1, v_precompileModules_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3731_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26 + 3, v_reservoir_3744_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3747_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26 + 5, v_allowImportAll_3748_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, sizeof(void*)*26 + 6, v_fixedToolchain_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* v_f_3758_, lean_object* v_cfg_3759_){
_start:
{
lean_object* v_toWorkspaceConfig_3760_; lean_object* v_toLeanConfig_3761_; uint8_t v_bootstrap_3762_; lean_object* v_extraDepTargets_3763_; uint8_t v_precompileModules_3764_; lean_object* v_moreGlobalServerArgs_3765_; lean_object* v_srcDir_3766_; lean_object* v_buildDir_3767_; lean_object* v_leanLibDir_3768_; lean_object* v_nativeLibDir_3769_; lean_object* v_binDir_3770_; lean_object* v_irDir_3771_; lean_object* v_releaseRepo_3772_; lean_object* v_buildArchive_3773_; uint8_t v_preferReleaseBuild_3774_; lean_object* v_testDriver_3775_; lean_object* v_testDriverArgs_3776_; lean_object* v_lintDriver_3777_; lean_object* v_lintDriverArgs_3778_; lean_object* v_version_3779_; lean_object* v_versionTags_3780_; lean_object* v_description_3781_; lean_object* v_keywords_3782_; lean_object* v_homepage_3783_; lean_object* v_license_3784_; lean_object* v_licenseFiles_3785_; lean_object* v_readmeFile_3786_; uint8_t v_reservoir_3787_; lean_object* v_enableArtifactCache_x3f_3788_; lean_object* v_restoreAllArtifacts_x3f_3789_; uint8_t v_libPrefixOnWindows_3790_; uint8_t v_allowImportAll_3791_; uint8_t v_fixedToolchain_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3800_; 
v_toWorkspaceConfig_3760_ = lean_ctor_get(v_cfg_3759_, 0);
v_toLeanConfig_3761_ = lean_ctor_get(v_cfg_3759_, 1);
v_bootstrap_3762_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26);
v_extraDepTargets_3763_ = lean_ctor_get(v_cfg_3759_, 2);
v_precompileModules_3764_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3765_ = lean_ctor_get(v_cfg_3759_, 3);
v_srcDir_3766_ = lean_ctor_get(v_cfg_3759_, 4);
v_buildDir_3767_ = lean_ctor_get(v_cfg_3759_, 5);
v_leanLibDir_3768_ = lean_ctor_get(v_cfg_3759_, 6);
v_nativeLibDir_3769_ = lean_ctor_get(v_cfg_3759_, 7);
v_binDir_3770_ = lean_ctor_get(v_cfg_3759_, 8);
v_irDir_3771_ = lean_ctor_get(v_cfg_3759_, 9);
v_releaseRepo_3772_ = lean_ctor_get(v_cfg_3759_, 10);
v_buildArchive_3773_ = lean_ctor_get(v_cfg_3759_, 11);
v_preferReleaseBuild_3774_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26 + 2);
v_testDriver_3775_ = lean_ctor_get(v_cfg_3759_, 12);
v_testDriverArgs_3776_ = lean_ctor_get(v_cfg_3759_, 13);
v_lintDriver_3777_ = lean_ctor_get(v_cfg_3759_, 14);
v_lintDriverArgs_3778_ = lean_ctor_get(v_cfg_3759_, 15);
v_version_3779_ = lean_ctor_get(v_cfg_3759_, 16);
v_versionTags_3780_ = lean_ctor_get(v_cfg_3759_, 17);
v_description_3781_ = lean_ctor_get(v_cfg_3759_, 18);
v_keywords_3782_ = lean_ctor_get(v_cfg_3759_, 19);
v_homepage_3783_ = lean_ctor_get(v_cfg_3759_, 20);
v_license_3784_ = lean_ctor_get(v_cfg_3759_, 21);
v_licenseFiles_3785_ = lean_ctor_get(v_cfg_3759_, 22);
v_readmeFile_3786_ = lean_ctor_get(v_cfg_3759_, 23);
v_reservoir_3787_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3788_ = lean_ctor_get(v_cfg_3759_, 24);
v_restoreAllArtifacts_x3f_3789_ = lean_ctor_get(v_cfg_3759_, 25);
v_libPrefixOnWindows_3790_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26 + 4);
v_allowImportAll_3791_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26 + 5);
v_fixedToolchain_3792_ = lean_ctor_get_uint8(v_cfg_3759_, sizeof(void*)*26 + 6);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_cfg_3759_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3794_ = v_cfg_3759_;
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3789_);
lean_inc(v_enableArtifactCache_x3f_3788_);
lean_inc(v_readmeFile_3786_);
lean_inc(v_licenseFiles_3785_);
lean_inc(v_license_3784_);
lean_inc(v_homepage_3783_);
lean_inc(v_keywords_3782_);
lean_inc(v_description_3781_);
lean_inc(v_versionTags_3780_);
lean_inc(v_version_3779_);
lean_inc(v_lintDriverArgs_3778_);
lean_inc(v_lintDriver_3777_);
lean_inc(v_testDriverArgs_3776_);
lean_inc(v_testDriver_3775_);
lean_inc(v_buildArchive_3773_);
lean_inc(v_releaseRepo_3772_);
lean_inc(v_irDir_3771_);
lean_inc(v_binDir_3770_);
lean_inc(v_nativeLibDir_3769_);
lean_inc(v_leanLibDir_3768_);
lean_inc(v_buildDir_3767_);
lean_inc(v_srcDir_3766_);
lean_inc(v_moreGlobalServerArgs_3765_);
lean_inc(v_extraDepTargets_3763_);
lean_inc(v_toLeanConfig_3761_);
lean_inc(v_toWorkspaceConfig_3760_);
lean_dec(v_cfg_3759_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = lean_apply_1(v_f_3758_, v_toLeanConfig_3761_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 1, v___x_3796_);
v___x_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_toWorkspaceConfig_3760_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_extraDepTargets_3763_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_moreGlobalServerArgs_3765_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_srcDir_3766_);
lean_ctor_set(v_reuseFailAlloc_3799_, 5, v_buildDir_3767_);
lean_ctor_set(v_reuseFailAlloc_3799_, 6, v_leanLibDir_3768_);
lean_ctor_set(v_reuseFailAlloc_3799_, 7, v_nativeLibDir_3769_);
lean_ctor_set(v_reuseFailAlloc_3799_, 8, v_binDir_3770_);
lean_ctor_set(v_reuseFailAlloc_3799_, 9, v_irDir_3771_);
lean_ctor_set(v_reuseFailAlloc_3799_, 10, v_releaseRepo_3772_);
lean_ctor_set(v_reuseFailAlloc_3799_, 11, v_buildArchive_3773_);
lean_ctor_set(v_reuseFailAlloc_3799_, 12, v_testDriver_3775_);
lean_ctor_set(v_reuseFailAlloc_3799_, 13, v_testDriverArgs_3776_);
lean_ctor_set(v_reuseFailAlloc_3799_, 14, v_lintDriver_3777_);
lean_ctor_set(v_reuseFailAlloc_3799_, 15, v_lintDriverArgs_3778_);
lean_ctor_set(v_reuseFailAlloc_3799_, 16, v_version_3779_);
lean_ctor_set(v_reuseFailAlloc_3799_, 17, v_versionTags_3780_);
lean_ctor_set(v_reuseFailAlloc_3799_, 18, v_description_3781_);
lean_ctor_set(v_reuseFailAlloc_3799_, 19, v_keywords_3782_);
lean_ctor_set(v_reuseFailAlloc_3799_, 20, v_homepage_3783_);
lean_ctor_set(v_reuseFailAlloc_3799_, 21, v_license_3784_);
lean_ctor_set(v_reuseFailAlloc_3799_, 22, v_licenseFiles_3785_);
lean_ctor_set(v_reuseFailAlloc_3799_, 23, v_readmeFile_3786_);
lean_ctor_set(v_reuseFailAlloc_3799_, 24, v_enableArtifactCache_x3f_3788_);
lean_ctor_set(v_reuseFailAlloc_3799_, 25, v_restoreAllArtifacts_x3f_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26, v_bootstrap_3762_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26 + 1, v_precompileModules_3764_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3774_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26 + 3, v_reservoir_3787_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3790_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26 + 5, v_allowImportAll_3791_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*26 + 6, v_fixedToolchain_3792_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* v_x_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__3(v_x_3810_);
lean_dec_ref(v_x_3810_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_3821_, lean_object* v_n_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___closed__4));
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_3824_, lean_object* v_n_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_3824_, v_n_3825_);
lean_dec(v_n_3825_);
lean_dec(v_p_3824_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_3827_, lean_object* v_n_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_3827_, v_n_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_3830_, lean_object* v_n_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_3830_, v_n_3831_);
lean_dec(v_n_3831_);
lean_dec(v_p_3830_);
return v_res_3832_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_3843_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_3844_ = lean_array_push(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_3853_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_3854_ = lean_array_push(v___x_3853_, v___x_3852_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3862_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_3863_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_3864_ = lean_array_push(v___x_3863_, v___x_3862_);
return v___x_3864_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_3873_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_3874_ = lean_array_push(v___x_3873_, v___x_3872_);
return v___x_3874_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_3883_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_3884_ = lean_array_push(v___x_3883_, v___x_3882_);
return v___x_3884_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3892_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_3893_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_3894_ = lean_array_push(v___x_3893_, v___x_3892_);
return v___x_3894_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3902_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_3903_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_3904_ = lean_array_push(v___x_3903_, v___x_3902_);
return v___x_3904_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3912_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_3913_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_3914_ = lean_array_push(v___x_3913_, v___x_3912_);
return v___x_3914_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_3923_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_3924_ = lean_array_push(v___x_3923_, v___x_3922_);
return v___x_3924_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_3933_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_3934_ = lean_array_push(v___x_3933_, v___x_3932_);
return v___x_3934_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_3943_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_3944_ = lean_array_push(v___x_3943_, v___x_3942_);
return v___x_3944_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_3953_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_3954_ = lean_array_push(v___x_3953_, v___x_3952_);
return v___x_3954_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_3963_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_3964_ = lean_array_push(v___x_3963_, v___x_3962_);
return v___x_3964_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3972_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_3973_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_3974_ = lean_array_push(v___x_3973_, v___x_3972_);
return v___x_3974_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_3983_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_3984_ = lean_array_push(v___x_3983_, v___x_3982_);
return v___x_3984_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_3993_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_3994_ = lean_array_push(v___x_3993_, v___x_3992_);
return v___x_3994_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__67));
v___x_4003_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4004_ = lean_array_push(v___x_4003_, v___x_4002_);
return v___x_4004_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4013_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4014_ = lean_array_push(v___x_4013_, v___x_4012_);
return v___x_4014_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4023_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4024_ = lean_array_push(v___x_4023_, v___x_4022_);
return v___x_4024_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4033_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4034_ = lean_array_push(v___x_4033_, v___x_4032_);
return v___x_4034_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4043_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4044_ = lean_array_push(v___x_4043_, v___x_4042_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4053_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4054_ = lean_array_push(v___x_4053_, v___x_4052_);
return v___x_4054_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4063_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4064_ = lean_array_push(v___x_4063_, v___x_4062_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_4073_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4074_ = lean_array_push(v___x_4073_, v___x_4072_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_4083_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4084_ = lean_array_push(v___x_4083_, v___x_4082_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_4093_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4094_ = lean_array_push(v___x_4093_, v___x_4092_);
return v___x_4094_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_4103_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4104_ = lean_array_push(v___x_4103_, v___x_4102_);
return v___x_4104_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_4113_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4114_ = lean_array_push(v___x_4113_, v___x_4112_);
return v___x_4114_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_4123_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4124_ = lean_array_push(v___x_4123_, v___x_4122_);
return v___x_4124_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4132_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_4133_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4134_ = lean_array_push(v___x_4133_, v___x_4132_);
return v___x_4134_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_4143_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4144_ = lean_array_push(v___x_4143_, v___x_4142_);
return v___x_4144_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_4153_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4154_ = lean_array_push(v___x_4153_, v___x_4152_);
return v___x_4154_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4162_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4163_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4164_ = lean_array_push(v___x_4163_, v___x_4162_);
return v___x_4164_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_4173_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4174_ = lean_array_push(v___x_4173_, v___x_4172_);
return v___x_4174_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4182_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_4183_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_4184_ = lean_array_push(v___x_4183_, v___x_4182_);
return v___x_4184_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_4193_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_4194_ = lean_array_push(v___x_4193_, v___x_4192_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_4203_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4202_);
return v___x_4204_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__149(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = l_Lake_WorkspaceConfig___fields;
v___x_4206_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_4207_ = l_Array_append___redArg(v___x_4206_, v___x_4205_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__153(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__152));
v___x_4216_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__149, &l_Lake_PackageConfig___fields___closed__149_once, _init_l_Lake_PackageConfig___fields___closed__149);
v___x_4217_ = lean_array_push(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__154(void){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = l_Lake_LeanConfig___fields;
v___x_4219_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__153, &l_Lake_PackageConfig___fields___closed__153_once, _init_l_Lake_PackageConfig___fields___closed__153);
v___x_4220_ = l_Array_append___redArg(v___x_4219_, v___x_4218_);
return v___x_4220_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__158(void){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4228_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__157));
v___x_4229_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__154, &l_Lake_PackageConfig___fields___closed__154_once, _init_l_Lake_PackageConfig___fields___closed__154);
v___x_4230_ = lean_array_push(v___x_4229_, v___x_4228_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__158, &l_Lake_PackageConfig___fields___closed__158_once, _init_l_Lake_PackageConfig___fields___closed__158);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_4232_, lean_object* v_n_4233_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lake_PackageConfig___fields;
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_4235_, lean_object* v_n_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lake_PackageConfig_instConfigFields(v_p_4235_, v_n_4236_);
lean_dec(v_n_4236_);
lean_dec(v_p_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_4238_, lean_object* v_x2_4239_){
_start:
{
lean_object* v_name_4240_; lean_object* v___x_4241_; 
v_name_4240_ = lean_ctor_get(v_x2_4239_, 0);
lean_inc(v_name_4240_);
v___x_4241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_4240_, v_x2_4239_, v_x1_4238_);
return v___x_4241_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = l_Lake_PackageConfig___fields;
v___x_4243_ = lean_array_get_size(v___x_4242_);
return v___x_4243_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v___x_4263_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = lean_nat_dec_lt(v___x_4264_, v___x_4263_);
return v___x_4265_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_4267_; uint8_t v___x_4268_; 
v___x_4267_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4268_ = lean_nat_dec_le(v___x_4267_, v___x_4267_);
return v___x_4268_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_4269_; size_t v___x_4270_; 
v___x_4269_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4270_ = lean_usize_of_nat(v___x_4269_);
return v___x_4270_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_4271_; size_t v___x_4272_; size_t v___x_4273_; lean_object* v___x_4274_; lean_object* v___f_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4271_ = lean_box(1);
v___x_4272_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_4273_ = ((size_t)0ULL);
v___x_4274_ = l_Lake_PackageConfig___fields;
v___f_4275_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_4276_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4276_, v___f_4275_, v___x_4274_, v___x_4273_, v___x_4272_, v___x_4271_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_4278_; lean_object* v___y_4280_; lean_object* v___x_4283_; uint8_t v___x_4284_; 
v___x_4278_ = l_Lake_PackageConfig___fields;
v___x_4283_ = lean_box(1);
v___x_4284_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_4284_ == 0)
{
v___y_4280_ = v___x_4283_;
goto v___jp_4279_;
}
else
{
uint8_t v___x_4285_; 
v___x_4285_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_4285_ == 0)
{
if (v___x_4284_ == 0)
{
v___y_4280_ = v___x_4283_;
goto v___jp_4279_;
}
else
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4280_ = v___x_4286_;
goto v___jp_4279_;
}
}
else
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4280_ = v___x_4287_;
goto v___jp_4279_;
}
}
v___jp_4279_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_4280_);
v___x_4282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4278_);
lean_ctor_set(v___x_4282_, 1, v___y_4280_);
lean_ctor_set(v___x_4282_, 2, v___x_4281_);
return v___x_4282_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
uint8_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4288_ = 1;
v___x_4289_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0));
v___x_4290_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1));
v___x_4291_ = l_Lake_defaultVersionTags;
v___x_4292_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___lam__3___closed__1));
v___x_4293_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_4294_ = lean_box(0);
v___x_4295_ = l_Lake_defaultIrDir;
v___x_4296_ = l_Lake_defaultBinDir;
v___x_4297_ = l_Lake_defaultNativeLibDir;
v___x_4298_ = l_Lake_defaultLeanLibDir;
v___x_4299_ = l_Lake_defaultBuildDir;
v___x_4300_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0));
v___x_4301_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_4302_ = 0;
v___x_4303_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_4304_ = l_Lake_defaultPackagesDir;
v___x_4305_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
lean_ctor_set(v___x_4305_, 1, v___x_4303_);
lean_ctor_set(v___x_4305_, 2, v___x_4301_);
lean_ctor_set(v___x_4305_, 3, v___x_4301_);
lean_ctor_set(v___x_4305_, 4, v___x_4300_);
lean_ctor_set(v___x_4305_, 5, v___x_4299_);
lean_ctor_set(v___x_4305_, 6, v___x_4298_);
lean_ctor_set(v___x_4305_, 7, v___x_4297_);
lean_ctor_set(v___x_4305_, 8, v___x_4296_);
lean_ctor_set(v___x_4305_, 9, v___x_4295_);
lean_ctor_set(v___x_4305_, 10, v___x_4294_);
lean_ctor_set(v___x_4305_, 11, v___x_4294_);
lean_ctor_set(v___x_4305_, 12, v___x_4293_);
lean_ctor_set(v___x_4305_, 13, v___x_4301_);
lean_ctor_set(v___x_4305_, 14, v___x_4293_);
lean_ctor_set(v___x_4305_, 15, v___x_4301_);
lean_ctor_set(v___x_4305_, 16, v___x_4292_);
lean_ctor_set(v___x_4305_, 17, v___x_4291_);
lean_ctor_set(v___x_4305_, 18, v___x_4293_);
lean_ctor_set(v___x_4305_, 19, v___x_4301_);
lean_ctor_set(v___x_4305_, 20, v___x_4293_);
lean_ctor_set(v___x_4305_, 21, v___x_4293_);
lean_ctor_set(v___x_4305_, 22, v___x_4290_);
lean_ctor_set(v___x_4305_, 23, v___x_4289_);
lean_ctor_set(v___x_4305_, 24, v___x_4294_);
lean_ctor_set(v___x_4305_, 25, v___x_4294_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26, v___x_4302_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26 + 1, v___x_4302_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26 + 2, v___x_4302_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26 + 3, v___x_4288_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26 + 4, v___x_4302_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26 + 5, v___x_4302_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*26 + 6, v___x_4302_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_4306_, lean_object* v_n_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_4309_, lean_object* v_n_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lake_PackageConfig_instEmptyCollection(v_p_4309_, v_n_4310_);
lean_dec(v_n_4310_);
lean_dec(v_p_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_4312_){
_start:
{
lean_inc(v_n_4312_);
return v_n_4312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lake_PackageConfig_origName___redArg(v_n_4313_);
lean_dec(v_n_4313_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_4315_, lean_object* v_n_4316_, lean_object* v_x_4317_){
_start:
{
lean_inc(v_n_4316_);
return v_n_4316_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_4318_, lean_object* v_n_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Lake_PackageConfig_origName(v_p_4318_, v_n_4319_, v_x_4320_);
lean_dec_ref(v_x_4320_);
lean_dec(v_n_4319_);
lean_dec(v_p_4318_);
return v_res_4321_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_WorkspaceConfig(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_PackageConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_WorkspaceConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_PackageConfig___fields = _init_l_Lake_PackageConfig___fields();
lean_mark_persistent(l_Lake_PackageConfig___fields);
l_Lake_PackageConfig_instConfigInfo = _init_l_Lake_PackageConfig_instConfigInfo();
lean_mark_persistent(l_Lake_PackageConfig_instConfigInfo);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_PackageConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Pattern(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_WorkspaceConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_PackageConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_WorkspaceConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_PackageConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_PackageConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_PackageConfig(builtin);
}
#ifdef __cplusplus
}
#endif
