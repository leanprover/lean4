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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_manifestFile___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_manifestFile___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_manifestFile___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_manifestFile___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_manifestFile___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_manifestFile___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_manifestFile___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_manifestFile___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_manifestFile___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_manifestFile___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_manifestFile___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_manifestFile___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_manifestFile___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_manifestFile___proj___closed__4 = (const lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile_instConfigField___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_releaseRepo___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___closed__3_value;
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
static const lean_ctor_object l_Lake_PackageConfig_buildArchive___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_manifestFile___proj___closed__3_value)}};
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
static lean_once_cell_t l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1;
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
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__3;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__4;
static const lean_string_object l_Lake_PackageConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "manifestFile"};
static const lean_object* l_Lake_PackageConfig___fields___closed__5 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(119, 77, 202, 12, 106, 133, 208, 66)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__6 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__6_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__7;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__8;
static const lean_string_object l_Lake_PackageConfig___fields___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "extraDepTargets"};
static const lean_object* l_Lake_PackageConfig___fields___closed__9 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__9_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__9_value),LEAN_SCALAR_PTR_LITERAL(232, 29, 68, 154, 160, 50, 56, 5)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__10 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__10_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__11;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__12;
static const lean_string_object l_Lake_PackageConfig___fields___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileModules"};
static const lean_object* l_Lake_PackageConfig___fields___closed__13 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__13_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__13_value),LEAN_SCALAR_PTR_LITERAL(210, 72, 98, 56, 225, 29, 247, 45)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__14 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__14_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__15;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__16;
static const lean_string_object l_Lake_PackageConfig___fields___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "moreGlobalServerArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__17 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__17_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__17_value),LEAN_SCALAR_PTR_LITERAL(217, 219, 52, 240, 88, 87, 45, 147)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__18 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__18_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__19;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__20;
static const lean_string_object l_Lake_PackageConfig___fields___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moreServerArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__21 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__21_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 197, 113, 7, 119, 120, 175, 89)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__22 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__22_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__22_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__18_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__23 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__23_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__24;
static const lean_string_object l_Lake_PackageConfig___fields___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__25 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__25_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__25_value),LEAN_SCALAR_PTR_LITERAL(82, 241, 97, 48, 55, 77, 36, 145)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__26 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__26_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__27;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__28;
static const lean_string_object l_Lake_PackageConfig___fields___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "buildDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__29 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__29_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__29_value),LEAN_SCALAR_PTR_LITERAL(249, 192, 208, 78, 51, 18, 78, 228)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__30 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__30_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__31;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__32;
static const lean_string_object l_Lake_PackageConfig___fields___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanLibDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__33 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__33_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__33_value),LEAN_SCALAR_PTR_LITERAL(1, 89, 218, 214, 52, 197, 188, 252)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__34 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__34_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__35;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__36;
static const lean_string_object l_Lake_PackageConfig___fields___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeLibDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__37 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__37_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__37_value),LEAN_SCALAR_PTR_LITERAL(82, 8, 215, 104, 60, 212, 87, 97)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__38 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__38_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__39;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__40;
static const lean_string_object l_Lake_PackageConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__41 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__41_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__41_value),LEAN_SCALAR_PTR_LITERAL(76, 64, 142, 71, 135, 199, 112, 75)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__42 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__42_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__43;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__44;
static const lean_string_object l_Lake_PackageConfig___fields___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "irDir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__45 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__45_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__45_value),LEAN_SCALAR_PTR_LITERAL(103, 157, 139, 154, 172, 117, 115, 135)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__46 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__46_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__47;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__48;
static const lean_string_object l_Lake_PackageConfig___fields___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "releaseRepo"};
static const lean_object* l_Lake_PackageConfig___fields___closed__49 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__49_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__49_value),LEAN_SCALAR_PTR_LITERAL(200, 115, 184, 27, 119, 80, 150, 143)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__50 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__50_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__51;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__52;
static const lean_string_object l_Lake_PackageConfig___fields___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "releaseRepo\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__53 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__53_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__53_value),LEAN_SCALAR_PTR_LITERAL(110, 119, 158, 92, 2, 186, 119, 253)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__54 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__54_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__54_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__50_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__55 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__55_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__56;
static const lean_string_object l_Lake_PackageConfig___fields___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildArchive"};
static const lean_object* l_Lake_PackageConfig___fields___closed__57 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__57_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__57_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 176, 165, 88, 62, 216, 20)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__58 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__58_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__59;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__60;
static const lean_string_object l_Lake_PackageConfig___fields___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "buildArchive\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__61 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__61_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__61_value),LEAN_SCALAR_PTR_LITERAL(206, 154, 251, 129, 245, 231, 210, 109)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__62 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__62_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__62_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__58_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__63 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__63_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__64;
static const lean_string_object l_Lake_PackageConfig___fields___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "preferReleaseBuild"};
static const lean_object* l_Lake_PackageConfig___fields___closed__65 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__65_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__65_value),LEAN_SCALAR_PTR_LITERAL(75, 209, 233, 233, 163, 174, 95, 235)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__66 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__66_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__67;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__68;
static const lean_string_object l_Lake_PackageConfig___fields___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__69 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__69_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__69_value),LEAN_SCALAR_PTR_LITERAL(187, 40, 173, 233, 223, 78, 220, 191)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__70 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__70_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__71;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__72;
static const lean_string_object l_Lake_PackageConfig___fields___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testRunner"};
static const lean_object* l_Lake_PackageConfig___fields___closed__73 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__73_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__73_value),LEAN_SCALAR_PTR_LITERAL(58, 61, 59, 86, 150, 111, 127, 182)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__74 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__74_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__70_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__75 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__75_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__76;
static const lean_string_object l_Lake_PackageConfig___fields___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__77 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__77_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__77_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 168, 214, 71, 6, 72, 93)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__78 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__78_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__79;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__80;
static const lean_string_object l_Lake_PackageConfig___fields___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__81 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__81_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__81_value),LEAN_SCALAR_PTR_LITERAL(164, 80, 113, 139, 118, 238, 67, 240)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__82 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__82_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__83;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__84;
static const lean_string_object l_Lake_PackageConfig___fields___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__85 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__85_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__85_value),LEAN_SCALAR_PTR_LITERAL(102, 206, 227, 73, 236, 117, 156, 150)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__86 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__86_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__87;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__88;
static const lean_string_object l_Lake_PackageConfig___fields___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_PackageConfig___fields___closed__89 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__89_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__89_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__90 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__90_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__91;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__92;
static const lean_string_object l_Lake_PackageConfig___fields___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "versionTags"};
static const lean_object* l_Lake_PackageConfig___fields___closed__93 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__93_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__93_value),LEAN_SCALAR_PTR_LITERAL(76, 44, 235, 102, 59, 70, 79, 98)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__94 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__94_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__95;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__96;
static const lean_string_object l_Lake_PackageConfig___fields___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "description"};
static const lean_object* l_Lake_PackageConfig___fields___closed__97 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__97_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__97_value),LEAN_SCALAR_PTR_LITERAL(85, 116, 204, 74, 85, 134, 17, 161)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__98 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__98_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__99;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__100;
static const lean_string_object l_Lake_PackageConfig___fields___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "keywords"};
static const lean_object* l_Lake_PackageConfig___fields___closed__101 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__101_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__101_value),LEAN_SCALAR_PTR_LITERAL(84, 45, 198, 62, 56, 187, 72, 125)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__102 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__102_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__103;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__104;
static const lean_string_object l_Lake_PackageConfig___fields___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "homepage"};
static const lean_object* l_Lake_PackageConfig___fields___closed__105 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__105_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__105_value),LEAN_SCALAR_PTR_LITERAL(73, 148, 206, 183, 90, 222, 74, 16)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__106 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__106_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__107;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__108;
static const lean_string_object l_Lake_PackageConfig___fields___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "license"};
static const lean_object* l_Lake_PackageConfig___fields___closed__109 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__109_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__109_value),LEAN_SCALAR_PTR_LITERAL(149, 142, 81, 8, 241, 47, 83, 51)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__110 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__110_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__111;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__112;
static const lean_string_object l_Lake_PackageConfig___fields___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "licenseFiles"};
static const lean_object* l_Lake_PackageConfig___fields___closed__113 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__113_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__113_value),LEAN_SCALAR_PTR_LITERAL(115, 188, 70, 201, 62, 96, 76, 55)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__114 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__114_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__115;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__116_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__116;
static const lean_string_object l_Lake_PackageConfig___fields___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "readmeFile"};
static const lean_object* l_Lake_PackageConfig___fields___closed__117 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__117_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__117_value),LEAN_SCALAR_PTR_LITERAL(86, 68, 195, 254, 204, 64, 41, 249)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__118 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__118_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__119;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__120;
static const lean_string_object l_Lake_PackageConfig___fields___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__121 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__121_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__121_value),LEAN_SCALAR_PTR_LITERAL(98, 62, 227, 196, 233, 158, 105, 168)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__122 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__122_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__123;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__124;
static const lean_string_object l_Lake_PackageConfig___fields___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "enableArtifactCache\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__125 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__125_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__125_value),LEAN_SCALAR_PTR_LITERAL(190, 150, 150, 100, 20, 242, 199, 174)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__126 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__126_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__127;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__128;
static const lean_string_object l_Lake_PackageConfig___fields___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "enableArtifactCache"};
static const lean_object* l_Lake_PackageConfig___fields___closed__129 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__129_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__129_value),LEAN_SCALAR_PTR_LITERAL(69, 183, 189, 255, 13, 235, 31, 38)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__130 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__130_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__130_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__126_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__131 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__131_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__132;
static const lean_string_object l_Lake_PackageConfig___fields___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "restoreAllArtifacts\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__133 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__133_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__133_value),LEAN_SCALAR_PTR_LITERAL(2, 1, 41, 192, 97, 8, 217, 82)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__134 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__134_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__135;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__136;
static const lean_string_object l_Lake_PackageConfig___fields___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "restoreAllArtifacts"};
static const lean_object* l_Lake_PackageConfig___fields___closed__137 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__137_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__137_value),LEAN_SCALAR_PTR_LITERAL(172, 122, 225, 122, 213, 189, 222, 165)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__138 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__138_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__138_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__134_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__139 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__139_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__140;
static const lean_string_object l_Lake_PackageConfig___fields___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libPrefixOnWindows"};
static const lean_object* l_Lake_PackageConfig___fields___closed__141 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__141_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__141_value),LEAN_SCALAR_PTR_LITERAL(26, 75, 58, 45, 181, 132, 175, 34)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__142 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__142_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__143;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__144;
static const lean_string_object l_Lake_PackageConfig___fields___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l_Lake_PackageConfig___fields___closed__145 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__145_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__145_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__146 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__146_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__147;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__148;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__149;
static const lean_string_object l_Lake_PackageConfig___fields___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toWorkspaceConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__150 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__150_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__150_value),LEAN_SCALAR_PTR_LITERAL(135, 228, 155, 156, 156, 252, 46, 118)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__151 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__151_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__152_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__152;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__153;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__154_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__154;
static const lean_string_object l_Lake_PackageConfig___fields___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__155 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__155_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__155_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__156 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__156_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__157;
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
v___x_19_ = l_System_instInhabitedFilePath_default;
v___x_20_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
v___x_21_ = lean_box(0);
v___x_22_ = 0;
v___x_23_ = l_Lake_instInhabitedLeanConfig_default;
v___x_24_ = l_Lake_instInhabitedWorkspaceConfig_default;
v___x_25_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_23_);
lean_ctor_set(v___x_25_, 2, v___x_21_);
lean_ctor_set(v___x_25_, 3, v___x_20_);
lean_ctor_set(v___x_25_, 4, v___x_20_);
lean_ctor_set(v___x_25_, 5, v___x_19_);
lean_ctor_set(v___x_25_, 6, v___x_19_);
lean_ctor_set(v___x_25_, 7, v___x_19_);
lean_ctor_set(v___x_25_, 8, v___x_19_);
lean_ctor_set(v___x_25_, 9, v___x_19_);
lean_ctor_set(v___x_25_, 10, v___x_19_);
lean_ctor_set(v___x_25_, 11, v___x_21_);
lean_ctor_set(v___x_25_, 12, v___x_21_);
lean_ctor_set(v___x_25_, 13, v___x_18_);
lean_ctor_set(v___x_25_, 14, v___x_20_);
lean_ctor_set(v___x_25_, 15, v___x_18_);
lean_ctor_set(v___x_25_, 16, v___x_20_);
lean_ctor_set(v___x_25_, 17, v___x_17_);
lean_ctor_set(v___x_25_, 18, v___x_16_);
lean_ctor_set(v___x_25_, 19, v___x_18_);
lean_ctor_set(v___x_25_, 20, v___x_20_);
lean_ctor_set(v___x_25_, 21, v___x_18_);
lean_ctor_set(v___x_25_, 22, v___x_18_);
lean_ctor_set(v___x_25_, 23, v___x_20_);
lean_ctor_set(v___x_25_, 24, v___x_19_);
lean_ctor_set(v___x_25_, 25, v___x_21_);
lean_ctor_set(v___x_25_, 26, v___x_21_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*27, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*27 + 1, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*27 + 2, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*27 + 3, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*27 + 4, v___x_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*27 + 5, v___x_22_);
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
v_bootstrap_39_ = lean_ctor_get_uint8(v_cfg_38_, sizeof(void*)*27);
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
lean_object* v_toWorkspaceConfig_45_; lean_object* v_toLeanConfig_46_; lean_object* v_manifestFile_47_; lean_object* v_extraDepTargets_48_; uint8_t v_precompileModules_49_; lean_object* v_moreGlobalServerArgs_50_; lean_object* v_srcDir_51_; lean_object* v_buildDir_52_; lean_object* v_leanLibDir_53_; lean_object* v_nativeLibDir_54_; lean_object* v_binDir_55_; lean_object* v_irDir_56_; lean_object* v_releaseRepo_57_; lean_object* v_buildArchive_58_; uint8_t v_preferReleaseBuild_59_; lean_object* v_testDriver_60_; lean_object* v_testDriverArgs_61_; lean_object* v_lintDriver_62_; lean_object* v_lintDriverArgs_63_; lean_object* v_version_64_; lean_object* v_versionTags_65_; lean_object* v_description_66_; lean_object* v_keywords_67_; lean_object* v_homepage_68_; lean_object* v_license_69_; lean_object* v_licenseFiles_70_; lean_object* v_readmeFile_71_; uint8_t v_reservoir_72_; lean_object* v_enableArtifactCache_x3f_73_; lean_object* v_restoreAllArtifacts_x3f_74_; uint8_t v_libPrefixOnWindows_75_; uint8_t v_allowImportAll_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v_toWorkspaceConfig_45_ = lean_ctor_get(v_cfg_44_, 0);
v_toLeanConfig_46_ = lean_ctor_get(v_cfg_44_, 1);
v_manifestFile_47_ = lean_ctor_get(v_cfg_44_, 2);
v_extraDepTargets_48_ = lean_ctor_get(v_cfg_44_, 3);
v_precompileModules_49_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_50_ = lean_ctor_get(v_cfg_44_, 4);
v_srcDir_51_ = lean_ctor_get(v_cfg_44_, 5);
v_buildDir_52_ = lean_ctor_get(v_cfg_44_, 6);
v_leanLibDir_53_ = lean_ctor_get(v_cfg_44_, 7);
v_nativeLibDir_54_ = lean_ctor_get(v_cfg_44_, 8);
v_binDir_55_ = lean_ctor_get(v_cfg_44_, 9);
v_irDir_56_ = lean_ctor_get(v_cfg_44_, 10);
v_releaseRepo_57_ = lean_ctor_get(v_cfg_44_, 11);
v_buildArchive_58_ = lean_ctor_get(v_cfg_44_, 12);
v_preferReleaseBuild_59_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*27 + 2);
v_testDriver_60_ = lean_ctor_get(v_cfg_44_, 13);
v_testDriverArgs_61_ = lean_ctor_get(v_cfg_44_, 14);
v_lintDriver_62_ = lean_ctor_get(v_cfg_44_, 15);
v_lintDriverArgs_63_ = lean_ctor_get(v_cfg_44_, 16);
v_version_64_ = lean_ctor_get(v_cfg_44_, 17);
v_versionTags_65_ = lean_ctor_get(v_cfg_44_, 18);
v_description_66_ = lean_ctor_get(v_cfg_44_, 19);
v_keywords_67_ = lean_ctor_get(v_cfg_44_, 20);
v_homepage_68_ = lean_ctor_get(v_cfg_44_, 21);
v_license_69_ = lean_ctor_get(v_cfg_44_, 22);
v_licenseFiles_70_ = lean_ctor_get(v_cfg_44_, 23);
v_readmeFile_71_ = lean_ctor_get(v_cfg_44_, 24);
v_reservoir_72_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_73_ = lean_ctor_get(v_cfg_44_, 25);
v_restoreAllArtifacts_x3f_74_ = lean_ctor_get(v_cfg_44_, 26);
v_libPrefixOnWindows_75_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*27 + 4);
v_allowImportAll_76_ = lean_ctor_get_uint8(v_cfg_44_, sizeof(void*)*27 + 5);
v_isSharedCheck_83_ = !lean_is_exclusive(v_cfg_44_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v_cfg_44_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_74_);
lean_inc(v_enableArtifactCache_x3f_73_);
lean_inc(v_readmeFile_71_);
lean_inc(v_licenseFiles_70_);
lean_inc(v_license_69_);
lean_inc(v_homepage_68_);
lean_inc(v_keywords_67_);
lean_inc(v_description_66_);
lean_inc(v_versionTags_65_);
lean_inc(v_version_64_);
lean_inc(v_lintDriverArgs_63_);
lean_inc(v_lintDriver_62_);
lean_inc(v_testDriverArgs_61_);
lean_inc(v_testDriver_60_);
lean_inc(v_buildArchive_58_);
lean_inc(v_releaseRepo_57_);
lean_inc(v_irDir_56_);
lean_inc(v_binDir_55_);
lean_inc(v_nativeLibDir_54_);
lean_inc(v_leanLibDir_53_);
lean_inc(v_buildDir_52_);
lean_inc(v_srcDir_51_);
lean_inc(v_moreGlobalServerArgs_50_);
lean_inc(v_extraDepTargets_48_);
lean_inc(v_manifestFile_47_);
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
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_toWorkspaceConfig_45_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_toLeanConfig_46_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_manifestFile_47_);
lean_ctor_set(v_reuseFailAlloc_82_, 3, v_extraDepTargets_48_);
lean_ctor_set(v_reuseFailAlloc_82_, 4, v_moreGlobalServerArgs_50_);
lean_ctor_set(v_reuseFailAlloc_82_, 5, v_srcDir_51_);
lean_ctor_set(v_reuseFailAlloc_82_, 6, v_buildDir_52_);
lean_ctor_set(v_reuseFailAlloc_82_, 7, v_leanLibDir_53_);
lean_ctor_set(v_reuseFailAlloc_82_, 8, v_nativeLibDir_54_);
lean_ctor_set(v_reuseFailAlloc_82_, 9, v_binDir_55_);
lean_ctor_set(v_reuseFailAlloc_82_, 10, v_irDir_56_);
lean_ctor_set(v_reuseFailAlloc_82_, 11, v_releaseRepo_57_);
lean_ctor_set(v_reuseFailAlloc_82_, 12, v_buildArchive_58_);
lean_ctor_set(v_reuseFailAlloc_82_, 13, v_testDriver_60_);
lean_ctor_set(v_reuseFailAlloc_82_, 14, v_testDriverArgs_61_);
lean_ctor_set(v_reuseFailAlloc_82_, 15, v_lintDriver_62_);
lean_ctor_set(v_reuseFailAlloc_82_, 16, v_lintDriverArgs_63_);
lean_ctor_set(v_reuseFailAlloc_82_, 17, v_version_64_);
lean_ctor_set(v_reuseFailAlloc_82_, 18, v_versionTags_65_);
lean_ctor_set(v_reuseFailAlloc_82_, 19, v_description_66_);
lean_ctor_set(v_reuseFailAlloc_82_, 20, v_keywords_67_);
lean_ctor_set(v_reuseFailAlloc_82_, 21, v_homepage_68_);
lean_ctor_set(v_reuseFailAlloc_82_, 22, v_license_69_);
lean_ctor_set(v_reuseFailAlloc_82_, 23, v_licenseFiles_70_);
lean_ctor_set(v_reuseFailAlloc_82_, 24, v_readmeFile_71_);
lean_ctor_set(v_reuseFailAlloc_82_, 25, v_enableArtifactCache_x3f_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 26, v_restoreAllArtifacts_x3f_74_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*27 + 1, v_precompileModules_49_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*27 + 2, v_preferReleaseBuild_59_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*27 + 3, v_reservoir_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_75_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*27 + 5, v_allowImportAll_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*27, v_val_43_);
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
lean_object* v_toWorkspaceConfig_90_; lean_object* v_toLeanConfig_91_; uint8_t v_bootstrap_92_; lean_object* v_manifestFile_93_; lean_object* v_extraDepTargets_94_; uint8_t v_precompileModules_95_; lean_object* v_moreGlobalServerArgs_96_; lean_object* v_srcDir_97_; lean_object* v_buildDir_98_; lean_object* v_leanLibDir_99_; lean_object* v_nativeLibDir_100_; lean_object* v_binDir_101_; lean_object* v_irDir_102_; lean_object* v_releaseRepo_103_; lean_object* v_buildArchive_104_; uint8_t v_preferReleaseBuild_105_; lean_object* v_testDriver_106_; lean_object* v_testDriverArgs_107_; lean_object* v_lintDriver_108_; lean_object* v_lintDriverArgs_109_; lean_object* v_version_110_; lean_object* v_versionTags_111_; lean_object* v_description_112_; lean_object* v_keywords_113_; lean_object* v_homepage_114_; lean_object* v_license_115_; lean_object* v_licenseFiles_116_; lean_object* v_readmeFile_117_; uint8_t v_reservoir_118_; lean_object* v_enableArtifactCache_x3f_119_; lean_object* v_restoreAllArtifacts_x3f_120_; uint8_t v_libPrefixOnWindows_121_; uint8_t v_allowImportAll_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_toWorkspaceConfig_90_ = lean_ctor_get(v_cfg_89_, 0);
v_toLeanConfig_91_ = lean_ctor_get(v_cfg_89_, 1);
v_bootstrap_92_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*27);
v_manifestFile_93_ = lean_ctor_get(v_cfg_89_, 2);
v_extraDepTargets_94_ = lean_ctor_get(v_cfg_89_, 3);
v_precompileModules_95_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_96_ = lean_ctor_get(v_cfg_89_, 4);
v_srcDir_97_ = lean_ctor_get(v_cfg_89_, 5);
v_buildDir_98_ = lean_ctor_get(v_cfg_89_, 6);
v_leanLibDir_99_ = lean_ctor_get(v_cfg_89_, 7);
v_nativeLibDir_100_ = lean_ctor_get(v_cfg_89_, 8);
v_binDir_101_ = lean_ctor_get(v_cfg_89_, 9);
v_irDir_102_ = lean_ctor_get(v_cfg_89_, 10);
v_releaseRepo_103_ = lean_ctor_get(v_cfg_89_, 11);
v_buildArchive_104_ = lean_ctor_get(v_cfg_89_, 12);
v_preferReleaseBuild_105_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*27 + 2);
v_testDriver_106_ = lean_ctor_get(v_cfg_89_, 13);
v_testDriverArgs_107_ = lean_ctor_get(v_cfg_89_, 14);
v_lintDriver_108_ = lean_ctor_get(v_cfg_89_, 15);
v_lintDriverArgs_109_ = lean_ctor_get(v_cfg_89_, 16);
v_version_110_ = lean_ctor_get(v_cfg_89_, 17);
v_versionTags_111_ = lean_ctor_get(v_cfg_89_, 18);
v_description_112_ = lean_ctor_get(v_cfg_89_, 19);
v_keywords_113_ = lean_ctor_get(v_cfg_89_, 20);
v_homepage_114_ = lean_ctor_get(v_cfg_89_, 21);
v_license_115_ = lean_ctor_get(v_cfg_89_, 22);
v_licenseFiles_116_ = lean_ctor_get(v_cfg_89_, 23);
v_readmeFile_117_ = lean_ctor_get(v_cfg_89_, 24);
v_reservoir_118_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_119_ = lean_ctor_get(v_cfg_89_, 25);
v_restoreAllArtifacts_x3f_120_ = lean_ctor_get(v_cfg_89_, 26);
v_libPrefixOnWindows_121_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*27 + 4);
v_allowImportAll_122_ = lean_ctor_get_uint8(v_cfg_89_, sizeof(void*)*27 + 5);
v_isSharedCheck_132_ = !lean_is_exclusive(v_cfg_89_);
if (v_isSharedCheck_132_ == 0)
{
v___x_124_ = v_cfg_89_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_120_);
lean_inc(v_enableArtifactCache_x3f_119_);
lean_inc(v_readmeFile_117_);
lean_inc(v_licenseFiles_116_);
lean_inc(v_license_115_);
lean_inc(v_homepage_114_);
lean_inc(v_keywords_113_);
lean_inc(v_description_112_);
lean_inc(v_versionTags_111_);
lean_inc(v_version_110_);
lean_inc(v_lintDriverArgs_109_);
lean_inc(v_lintDriver_108_);
lean_inc(v_testDriverArgs_107_);
lean_inc(v_testDriver_106_);
lean_inc(v_buildArchive_104_);
lean_inc(v_releaseRepo_103_);
lean_inc(v_irDir_102_);
lean_inc(v_binDir_101_);
lean_inc(v_nativeLibDir_100_);
lean_inc(v_leanLibDir_99_);
lean_inc(v_buildDir_98_);
lean_inc(v_srcDir_97_);
lean_inc(v_moreGlobalServerArgs_96_);
lean_inc(v_extraDepTargets_94_);
lean_inc(v_manifestFile_93_);
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
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_toWorkspaceConfig_90_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_toLeanConfig_91_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_manifestFile_93_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_extraDepTargets_94_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_moreGlobalServerArgs_96_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_srcDir_97_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_buildDir_98_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_leanLibDir_99_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_nativeLibDir_100_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_binDir_101_);
lean_ctor_set(v_reuseFailAlloc_131_, 10, v_irDir_102_);
lean_ctor_set(v_reuseFailAlloc_131_, 11, v_releaseRepo_103_);
lean_ctor_set(v_reuseFailAlloc_131_, 12, v_buildArchive_104_);
lean_ctor_set(v_reuseFailAlloc_131_, 13, v_testDriver_106_);
lean_ctor_set(v_reuseFailAlloc_131_, 14, v_testDriverArgs_107_);
lean_ctor_set(v_reuseFailAlloc_131_, 15, v_lintDriver_108_);
lean_ctor_set(v_reuseFailAlloc_131_, 16, v_lintDriverArgs_109_);
lean_ctor_set(v_reuseFailAlloc_131_, 17, v_version_110_);
lean_ctor_set(v_reuseFailAlloc_131_, 18, v_versionTags_111_);
lean_ctor_set(v_reuseFailAlloc_131_, 19, v_description_112_);
lean_ctor_set(v_reuseFailAlloc_131_, 20, v_keywords_113_);
lean_ctor_set(v_reuseFailAlloc_131_, 21, v_homepage_114_);
lean_ctor_set(v_reuseFailAlloc_131_, 22, v_license_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 23, v_licenseFiles_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 24, v_readmeFile_117_);
lean_ctor_set(v_reuseFailAlloc_131_, 25, v_enableArtifactCache_x3f_119_);
lean_ctor_set(v_reuseFailAlloc_131_, 26, v_restoreAllArtifacts_x3f_120_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
uint8_t v___x_130_; 
v___x_130_ = lean_unbox(v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*27, v___x_130_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*27 + 1, v_precompileModules_95_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*27 + 2, v_preferReleaseBuild_105_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*27 + 3, v_reservoir_118_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_121_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*27 + 5, v_allowImportAll_122_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__0(lean_object* v_cfg_159_){
_start:
{
lean_object* v_manifestFile_160_; 
v_manifestFile_160_ = lean_ctor_get(v_cfg_159_, 2);
lean_inc(v_manifestFile_160_);
return v_manifestFile_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__0___boxed(lean_object* v_cfg_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_PackageConfig_manifestFile___proj___lam__0(v_cfg_161_);
lean_dec_ref(v_cfg_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__1(lean_object* v_val_163_, lean_object* v_cfg_164_){
_start:
{
lean_object* v_toWorkspaceConfig_165_; lean_object* v_toLeanConfig_166_; uint8_t v_bootstrap_167_; lean_object* v_extraDepTargets_168_; uint8_t v_precompileModules_169_; lean_object* v_moreGlobalServerArgs_170_; lean_object* v_srcDir_171_; lean_object* v_buildDir_172_; lean_object* v_leanLibDir_173_; lean_object* v_nativeLibDir_174_; lean_object* v_binDir_175_; lean_object* v_irDir_176_; lean_object* v_releaseRepo_177_; lean_object* v_buildArchive_178_; uint8_t v_preferReleaseBuild_179_; lean_object* v_testDriver_180_; lean_object* v_testDriverArgs_181_; lean_object* v_lintDriver_182_; lean_object* v_lintDriverArgs_183_; lean_object* v_version_184_; lean_object* v_versionTags_185_; lean_object* v_description_186_; lean_object* v_keywords_187_; lean_object* v_homepage_188_; lean_object* v_license_189_; lean_object* v_licenseFiles_190_; lean_object* v_readmeFile_191_; uint8_t v_reservoir_192_; lean_object* v_enableArtifactCache_x3f_193_; lean_object* v_restoreAllArtifacts_x3f_194_; uint8_t v_libPrefixOnWindows_195_; uint8_t v_allowImportAll_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_toWorkspaceConfig_165_ = lean_ctor_get(v_cfg_164_, 0);
v_toLeanConfig_166_ = lean_ctor_get(v_cfg_164_, 1);
v_bootstrap_167_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*27);
v_extraDepTargets_168_ = lean_ctor_get(v_cfg_164_, 3);
v_precompileModules_169_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_170_ = lean_ctor_get(v_cfg_164_, 4);
v_srcDir_171_ = lean_ctor_get(v_cfg_164_, 5);
v_buildDir_172_ = lean_ctor_get(v_cfg_164_, 6);
v_leanLibDir_173_ = lean_ctor_get(v_cfg_164_, 7);
v_nativeLibDir_174_ = lean_ctor_get(v_cfg_164_, 8);
v_binDir_175_ = lean_ctor_get(v_cfg_164_, 9);
v_irDir_176_ = lean_ctor_get(v_cfg_164_, 10);
v_releaseRepo_177_ = lean_ctor_get(v_cfg_164_, 11);
v_buildArchive_178_ = lean_ctor_get(v_cfg_164_, 12);
v_preferReleaseBuild_179_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*27 + 2);
v_testDriver_180_ = lean_ctor_get(v_cfg_164_, 13);
v_testDriverArgs_181_ = lean_ctor_get(v_cfg_164_, 14);
v_lintDriver_182_ = lean_ctor_get(v_cfg_164_, 15);
v_lintDriverArgs_183_ = lean_ctor_get(v_cfg_164_, 16);
v_version_184_ = lean_ctor_get(v_cfg_164_, 17);
v_versionTags_185_ = lean_ctor_get(v_cfg_164_, 18);
v_description_186_ = lean_ctor_get(v_cfg_164_, 19);
v_keywords_187_ = lean_ctor_get(v_cfg_164_, 20);
v_homepage_188_ = lean_ctor_get(v_cfg_164_, 21);
v_license_189_ = lean_ctor_get(v_cfg_164_, 22);
v_licenseFiles_190_ = lean_ctor_get(v_cfg_164_, 23);
v_readmeFile_191_ = lean_ctor_get(v_cfg_164_, 24);
v_reservoir_192_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_193_ = lean_ctor_get(v_cfg_164_, 25);
v_restoreAllArtifacts_x3f_194_ = lean_ctor_get(v_cfg_164_, 26);
v_libPrefixOnWindows_195_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*27 + 4);
v_allowImportAll_196_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_194_);
lean_inc(v_enableArtifactCache_x3f_193_);
lean_inc(v_readmeFile_191_);
lean_inc(v_licenseFiles_190_);
lean_inc(v_license_189_);
lean_inc(v_homepage_188_);
lean_inc(v_keywords_187_);
lean_inc(v_description_186_);
lean_inc(v_versionTags_185_);
lean_inc(v_version_184_);
lean_inc(v_lintDriverArgs_183_);
lean_inc(v_lintDriver_182_);
lean_inc(v_testDriverArgs_181_);
lean_inc(v_testDriver_180_);
lean_inc(v_buildArchive_178_);
lean_inc(v_releaseRepo_177_);
lean_inc(v_irDir_176_);
lean_inc(v_binDir_175_);
lean_inc(v_nativeLibDir_174_);
lean_inc(v_leanLibDir_173_);
lean_inc(v_buildDir_172_);
lean_inc(v_srcDir_171_);
lean_inc(v_moreGlobalServerArgs_170_);
lean_inc(v_extraDepTargets_168_);
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
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_toWorkspaceConfig_165_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_toLeanConfig_166_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_val_163_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_extraDepTargets_168_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_moreGlobalServerArgs_170_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_srcDir_171_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_buildDir_172_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_leanLibDir_173_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v_nativeLibDir_174_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_binDir_175_);
lean_ctor_set(v_reuseFailAlloc_202_, 10, v_irDir_176_);
lean_ctor_set(v_reuseFailAlloc_202_, 11, v_releaseRepo_177_);
lean_ctor_set(v_reuseFailAlloc_202_, 12, v_buildArchive_178_);
lean_ctor_set(v_reuseFailAlloc_202_, 13, v_testDriver_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 14, v_testDriverArgs_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 15, v_lintDriver_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 16, v_lintDriverArgs_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 17, v_version_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 18, v_versionTags_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 19, v_description_186_);
lean_ctor_set(v_reuseFailAlloc_202_, 20, v_keywords_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 21, v_homepage_188_);
lean_ctor_set(v_reuseFailAlloc_202_, 22, v_license_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 23, v_licenseFiles_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 24, v_readmeFile_191_);
lean_ctor_set(v_reuseFailAlloc_202_, 25, v_enableArtifactCache_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_202_, 26, v_restoreAllArtifacts_x3f_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*27, v_bootstrap_167_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*27 + 1, v_precompileModules_169_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*27 + 2, v_preferReleaseBuild_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*27 + 3, v_reservoir_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*27 + 5, v_allowImportAll_196_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__2(lean_object* v_f_205_, lean_object* v_cfg_206_){
_start:
{
lean_object* v_toWorkspaceConfig_207_; lean_object* v_toLeanConfig_208_; uint8_t v_bootstrap_209_; lean_object* v_manifestFile_210_; lean_object* v_extraDepTargets_211_; uint8_t v_precompileModules_212_; lean_object* v_moreGlobalServerArgs_213_; lean_object* v_srcDir_214_; lean_object* v_buildDir_215_; lean_object* v_leanLibDir_216_; lean_object* v_nativeLibDir_217_; lean_object* v_binDir_218_; lean_object* v_irDir_219_; lean_object* v_releaseRepo_220_; lean_object* v_buildArchive_221_; uint8_t v_preferReleaseBuild_222_; lean_object* v_testDriver_223_; lean_object* v_testDriverArgs_224_; lean_object* v_lintDriver_225_; lean_object* v_lintDriverArgs_226_; lean_object* v_version_227_; lean_object* v_versionTags_228_; lean_object* v_description_229_; lean_object* v_keywords_230_; lean_object* v_homepage_231_; lean_object* v_license_232_; lean_object* v_licenseFiles_233_; lean_object* v_readmeFile_234_; uint8_t v_reservoir_235_; lean_object* v_enableArtifactCache_x3f_236_; lean_object* v_restoreAllArtifacts_x3f_237_; uint8_t v_libPrefixOnWindows_238_; uint8_t v_allowImportAll_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_toWorkspaceConfig_207_ = lean_ctor_get(v_cfg_206_, 0);
v_toLeanConfig_208_ = lean_ctor_get(v_cfg_206_, 1);
v_bootstrap_209_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*27);
v_manifestFile_210_ = lean_ctor_get(v_cfg_206_, 2);
v_extraDepTargets_211_ = lean_ctor_get(v_cfg_206_, 3);
v_precompileModules_212_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_213_ = lean_ctor_get(v_cfg_206_, 4);
v_srcDir_214_ = lean_ctor_get(v_cfg_206_, 5);
v_buildDir_215_ = lean_ctor_get(v_cfg_206_, 6);
v_leanLibDir_216_ = lean_ctor_get(v_cfg_206_, 7);
v_nativeLibDir_217_ = lean_ctor_get(v_cfg_206_, 8);
v_binDir_218_ = lean_ctor_get(v_cfg_206_, 9);
v_irDir_219_ = lean_ctor_get(v_cfg_206_, 10);
v_releaseRepo_220_ = lean_ctor_get(v_cfg_206_, 11);
v_buildArchive_221_ = lean_ctor_get(v_cfg_206_, 12);
v_preferReleaseBuild_222_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*27 + 2);
v_testDriver_223_ = lean_ctor_get(v_cfg_206_, 13);
v_testDriverArgs_224_ = lean_ctor_get(v_cfg_206_, 14);
v_lintDriver_225_ = lean_ctor_get(v_cfg_206_, 15);
v_lintDriverArgs_226_ = lean_ctor_get(v_cfg_206_, 16);
v_version_227_ = lean_ctor_get(v_cfg_206_, 17);
v_versionTags_228_ = lean_ctor_get(v_cfg_206_, 18);
v_description_229_ = lean_ctor_get(v_cfg_206_, 19);
v_keywords_230_ = lean_ctor_get(v_cfg_206_, 20);
v_homepage_231_ = lean_ctor_get(v_cfg_206_, 21);
v_license_232_ = lean_ctor_get(v_cfg_206_, 22);
v_licenseFiles_233_ = lean_ctor_get(v_cfg_206_, 23);
v_readmeFile_234_ = lean_ctor_get(v_cfg_206_, 24);
v_reservoir_235_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_236_ = lean_ctor_get(v_cfg_206_, 25);
v_restoreAllArtifacts_x3f_237_ = lean_ctor_get(v_cfg_206_, 26);
v_libPrefixOnWindows_238_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*27 + 4);
v_allowImportAll_239_ = lean_ctor_get_uint8(v_cfg_206_, sizeof(void*)*27 + 5);
v_isSharedCheck_247_ = !lean_is_exclusive(v_cfg_206_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v_cfg_206_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_237_);
lean_inc(v_enableArtifactCache_x3f_236_);
lean_inc(v_readmeFile_234_);
lean_inc(v_licenseFiles_233_);
lean_inc(v_license_232_);
lean_inc(v_homepage_231_);
lean_inc(v_keywords_230_);
lean_inc(v_description_229_);
lean_inc(v_versionTags_228_);
lean_inc(v_version_227_);
lean_inc(v_lintDriverArgs_226_);
lean_inc(v_lintDriver_225_);
lean_inc(v_testDriverArgs_224_);
lean_inc(v_testDriver_223_);
lean_inc(v_buildArchive_221_);
lean_inc(v_releaseRepo_220_);
lean_inc(v_irDir_219_);
lean_inc(v_binDir_218_);
lean_inc(v_nativeLibDir_217_);
lean_inc(v_leanLibDir_216_);
lean_inc(v_buildDir_215_);
lean_inc(v_srcDir_214_);
lean_inc(v_moreGlobalServerArgs_213_);
lean_inc(v_extraDepTargets_211_);
lean_inc(v_manifestFile_210_);
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
v___x_243_ = lean_apply_1(v_f_205_, v_manifestFile_210_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_toWorkspaceConfig_207_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_toLeanConfig_208_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_extraDepTargets_211_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_moreGlobalServerArgs_213_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v_srcDir_214_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_buildDir_215_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_leanLibDir_216_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_nativeLibDir_217_);
lean_ctor_set(v_reuseFailAlloc_246_, 9, v_binDir_218_);
lean_ctor_set(v_reuseFailAlloc_246_, 10, v_irDir_219_);
lean_ctor_set(v_reuseFailAlloc_246_, 11, v_releaseRepo_220_);
lean_ctor_set(v_reuseFailAlloc_246_, 12, v_buildArchive_221_);
lean_ctor_set(v_reuseFailAlloc_246_, 13, v_testDriver_223_);
lean_ctor_set(v_reuseFailAlloc_246_, 14, v_testDriverArgs_224_);
lean_ctor_set(v_reuseFailAlloc_246_, 15, v_lintDriver_225_);
lean_ctor_set(v_reuseFailAlloc_246_, 16, v_lintDriverArgs_226_);
lean_ctor_set(v_reuseFailAlloc_246_, 17, v_version_227_);
lean_ctor_set(v_reuseFailAlloc_246_, 18, v_versionTags_228_);
lean_ctor_set(v_reuseFailAlloc_246_, 19, v_description_229_);
lean_ctor_set(v_reuseFailAlloc_246_, 20, v_keywords_230_);
lean_ctor_set(v_reuseFailAlloc_246_, 21, v_homepage_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 22, v_license_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 23, v_licenseFiles_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 24, v_readmeFile_234_);
lean_ctor_set(v_reuseFailAlloc_246_, 25, v_enableArtifactCache_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_246_, 26, v_restoreAllArtifacts_x3f_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*27, v_bootstrap_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*27 + 1, v_precompileModules_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*27 + 2, v_preferReleaseBuild_222_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*27 + 3, v_reservoir_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*27 + 5, v_allowImportAll_239_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__3(lean_object* v_x_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___lam__3___boxed(lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_PackageConfig_manifestFile___proj___lam__3(v_x_250_);
lean_dec_ref(v_x_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj(lean_object* v_p_261_, lean_object* v_n_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l_Lake_PackageConfig_manifestFile___proj___closed__4));
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___proj___boxed(lean_object* v_p_264_, lean_object* v_n_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lake_PackageConfig_manifestFile___proj(v_p_264_, v_n_265_);
lean_dec(v_n_265_);
lean_dec(v_p_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile_instConfigField(lean_object* v_p_267_, lean_object* v_n_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lake_PackageConfig_manifestFile___proj(v_p_267_, v_n_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile_instConfigField___boxed(lean_object* v_p_270_, lean_object* v_n_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lake_PackageConfig_manifestFile_instConfigField(v_p_270_, v_n_271_);
lean_dec(v_n_271_);
lean_dec(v_p_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_273_){
_start:
{
lean_object* v_extraDepTargets_274_; 
v_extraDepTargets_274_ = lean_ctor_get(v_cfg_273_, 3);
lean_inc_ref(v_extraDepTargets_274_);
return v_extraDepTargets_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(v_cfg_275_);
lean_dec_ref(v_cfg_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* v_val_277_, lean_object* v_cfg_278_){
_start:
{
lean_object* v_toWorkspaceConfig_279_; lean_object* v_toLeanConfig_280_; uint8_t v_bootstrap_281_; lean_object* v_manifestFile_282_; uint8_t v_precompileModules_283_; lean_object* v_moreGlobalServerArgs_284_; lean_object* v_srcDir_285_; lean_object* v_buildDir_286_; lean_object* v_leanLibDir_287_; lean_object* v_nativeLibDir_288_; lean_object* v_binDir_289_; lean_object* v_irDir_290_; lean_object* v_releaseRepo_291_; lean_object* v_buildArchive_292_; uint8_t v_preferReleaseBuild_293_; lean_object* v_testDriver_294_; lean_object* v_testDriverArgs_295_; lean_object* v_lintDriver_296_; lean_object* v_lintDriverArgs_297_; lean_object* v_version_298_; lean_object* v_versionTags_299_; lean_object* v_description_300_; lean_object* v_keywords_301_; lean_object* v_homepage_302_; lean_object* v_license_303_; lean_object* v_licenseFiles_304_; lean_object* v_readmeFile_305_; uint8_t v_reservoir_306_; lean_object* v_enableArtifactCache_x3f_307_; lean_object* v_restoreAllArtifacts_x3f_308_; uint8_t v_libPrefixOnWindows_309_; uint8_t v_allowImportAll_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_toWorkspaceConfig_279_ = lean_ctor_get(v_cfg_278_, 0);
v_toLeanConfig_280_ = lean_ctor_get(v_cfg_278_, 1);
v_bootstrap_281_ = lean_ctor_get_uint8(v_cfg_278_, sizeof(void*)*27);
v_manifestFile_282_ = lean_ctor_get(v_cfg_278_, 2);
v_precompileModules_283_ = lean_ctor_get_uint8(v_cfg_278_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_284_ = lean_ctor_get(v_cfg_278_, 4);
v_srcDir_285_ = lean_ctor_get(v_cfg_278_, 5);
v_buildDir_286_ = lean_ctor_get(v_cfg_278_, 6);
v_leanLibDir_287_ = lean_ctor_get(v_cfg_278_, 7);
v_nativeLibDir_288_ = lean_ctor_get(v_cfg_278_, 8);
v_binDir_289_ = lean_ctor_get(v_cfg_278_, 9);
v_irDir_290_ = lean_ctor_get(v_cfg_278_, 10);
v_releaseRepo_291_ = lean_ctor_get(v_cfg_278_, 11);
v_buildArchive_292_ = lean_ctor_get(v_cfg_278_, 12);
v_preferReleaseBuild_293_ = lean_ctor_get_uint8(v_cfg_278_, sizeof(void*)*27 + 2);
v_testDriver_294_ = lean_ctor_get(v_cfg_278_, 13);
v_testDriverArgs_295_ = lean_ctor_get(v_cfg_278_, 14);
v_lintDriver_296_ = lean_ctor_get(v_cfg_278_, 15);
v_lintDriverArgs_297_ = lean_ctor_get(v_cfg_278_, 16);
v_version_298_ = lean_ctor_get(v_cfg_278_, 17);
v_versionTags_299_ = lean_ctor_get(v_cfg_278_, 18);
v_description_300_ = lean_ctor_get(v_cfg_278_, 19);
v_keywords_301_ = lean_ctor_get(v_cfg_278_, 20);
v_homepage_302_ = lean_ctor_get(v_cfg_278_, 21);
v_license_303_ = lean_ctor_get(v_cfg_278_, 22);
v_licenseFiles_304_ = lean_ctor_get(v_cfg_278_, 23);
v_readmeFile_305_ = lean_ctor_get(v_cfg_278_, 24);
v_reservoir_306_ = lean_ctor_get_uint8(v_cfg_278_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_307_ = lean_ctor_get(v_cfg_278_, 25);
v_restoreAllArtifacts_x3f_308_ = lean_ctor_get(v_cfg_278_, 26);
v_libPrefixOnWindows_309_ = lean_ctor_get_uint8(v_cfg_278_, sizeof(void*)*27 + 4);
v_allowImportAll_310_ = lean_ctor_get_uint8(v_cfg_278_, sizeof(void*)*27 + 5);
v_isSharedCheck_317_ = !lean_is_exclusive(v_cfg_278_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_cfg_278_, 3);
lean_dec(v_unused_318_);
v___x_312_ = v_cfg_278_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_308_);
lean_inc(v_enableArtifactCache_x3f_307_);
lean_inc(v_readmeFile_305_);
lean_inc(v_licenseFiles_304_);
lean_inc(v_license_303_);
lean_inc(v_homepage_302_);
lean_inc(v_keywords_301_);
lean_inc(v_description_300_);
lean_inc(v_versionTags_299_);
lean_inc(v_version_298_);
lean_inc(v_lintDriverArgs_297_);
lean_inc(v_lintDriver_296_);
lean_inc(v_testDriverArgs_295_);
lean_inc(v_testDriver_294_);
lean_inc(v_buildArchive_292_);
lean_inc(v_releaseRepo_291_);
lean_inc(v_irDir_290_);
lean_inc(v_binDir_289_);
lean_inc(v_nativeLibDir_288_);
lean_inc(v_leanLibDir_287_);
lean_inc(v_buildDir_286_);
lean_inc(v_srcDir_285_);
lean_inc(v_moreGlobalServerArgs_284_);
lean_inc(v_manifestFile_282_);
lean_inc(v_toLeanConfig_280_);
lean_inc(v_toWorkspaceConfig_279_);
lean_dec(v_cfg_278_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 3, v_val_277_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_toWorkspaceConfig_279_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_toLeanConfig_280_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_manifestFile_282_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_val_277_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_moreGlobalServerArgs_284_);
lean_ctor_set(v_reuseFailAlloc_316_, 5, v_srcDir_285_);
lean_ctor_set(v_reuseFailAlloc_316_, 6, v_buildDir_286_);
lean_ctor_set(v_reuseFailAlloc_316_, 7, v_leanLibDir_287_);
lean_ctor_set(v_reuseFailAlloc_316_, 8, v_nativeLibDir_288_);
lean_ctor_set(v_reuseFailAlloc_316_, 9, v_binDir_289_);
lean_ctor_set(v_reuseFailAlloc_316_, 10, v_irDir_290_);
lean_ctor_set(v_reuseFailAlloc_316_, 11, v_releaseRepo_291_);
lean_ctor_set(v_reuseFailAlloc_316_, 12, v_buildArchive_292_);
lean_ctor_set(v_reuseFailAlloc_316_, 13, v_testDriver_294_);
lean_ctor_set(v_reuseFailAlloc_316_, 14, v_testDriverArgs_295_);
lean_ctor_set(v_reuseFailAlloc_316_, 15, v_lintDriver_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 16, v_lintDriverArgs_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 17, v_version_298_);
lean_ctor_set(v_reuseFailAlloc_316_, 18, v_versionTags_299_);
lean_ctor_set(v_reuseFailAlloc_316_, 19, v_description_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 20, v_keywords_301_);
lean_ctor_set(v_reuseFailAlloc_316_, 21, v_homepage_302_);
lean_ctor_set(v_reuseFailAlloc_316_, 22, v_license_303_);
lean_ctor_set(v_reuseFailAlloc_316_, 23, v_licenseFiles_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 24, v_readmeFile_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 25, v_enableArtifactCache_x3f_307_);
lean_ctor_set(v_reuseFailAlloc_316_, 26, v_restoreAllArtifacts_x3f_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*27, v_bootstrap_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*27 + 1, v_precompileModules_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*27 + 2, v_preferReleaseBuild_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*27 + 3, v_reservoir_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*27 + 5, v_allowImportAll_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* v_f_319_, lean_object* v_cfg_320_){
_start:
{
lean_object* v_toWorkspaceConfig_321_; lean_object* v_toLeanConfig_322_; uint8_t v_bootstrap_323_; lean_object* v_manifestFile_324_; lean_object* v_extraDepTargets_325_; uint8_t v_precompileModules_326_; lean_object* v_moreGlobalServerArgs_327_; lean_object* v_srcDir_328_; lean_object* v_buildDir_329_; lean_object* v_leanLibDir_330_; lean_object* v_nativeLibDir_331_; lean_object* v_binDir_332_; lean_object* v_irDir_333_; lean_object* v_releaseRepo_334_; lean_object* v_buildArchive_335_; uint8_t v_preferReleaseBuild_336_; lean_object* v_testDriver_337_; lean_object* v_testDriverArgs_338_; lean_object* v_lintDriver_339_; lean_object* v_lintDriverArgs_340_; lean_object* v_version_341_; lean_object* v_versionTags_342_; lean_object* v_description_343_; lean_object* v_keywords_344_; lean_object* v_homepage_345_; lean_object* v_license_346_; lean_object* v_licenseFiles_347_; lean_object* v_readmeFile_348_; uint8_t v_reservoir_349_; lean_object* v_enableArtifactCache_x3f_350_; lean_object* v_restoreAllArtifacts_x3f_351_; uint8_t v_libPrefixOnWindows_352_; uint8_t v_allowImportAll_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_361_; 
v_toWorkspaceConfig_321_ = lean_ctor_get(v_cfg_320_, 0);
v_toLeanConfig_322_ = lean_ctor_get(v_cfg_320_, 1);
v_bootstrap_323_ = lean_ctor_get_uint8(v_cfg_320_, sizeof(void*)*27);
v_manifestFile_324_ = lean_ctor_get(v_cfg_320_, 2);
v_extraDepTargets_325_ = lean_ctor_get(v_cfg_320_, 3);
v_precompileModules_326_ = lean_ctor_get_uint8(v_cfg_320_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_327_ = lean_ctor_get(v_cfg_320_, 4);
v_srcDir_328_ = lean_ctor_get(v_cfg_320_, 5);
v_buildDir_329_ = lean_ctor_get(v_cfg_320_, 6);
v_leanLibDir_330_ = lean_ctor_get(v_cfg_320_, 7);
v_nativeLibDir_331_ = lean_ctor_get(v_cfg_320_, 8);
v_binDir_332_ = lean_ctor_get(v_cfg_320_, 9);
v_irDir_333_ = lean_ctor_get(v_cfg_320_, 10);
v_releaseRepo_334_ = lean_ctor_get(v_cfg_320_, 11);
v_buildArchive_335_ = lean_ctor_get(v_cfg_320_, 12);
v_preferReleaseBuild_336_ = lean_ctor_get_uint8(v_cfg_320_, sizeof(void*)*27 + 2);
v_testDriver_337_ = lean_ctor_get(v_cfg_320_, 13);
v_testDriverArgs_338_ = lean_ctor_get(v_cfg_320_, 14);
v_lintDriver_339_ = lean_ctor_get(v_cfg_320_, 15);
v_lintDriverArgs_340_ = lean_ctor_get(v_cfg_320_, 16);
v_version_341_ = lean_ctor_get(v_cfg_320_, 17);
v_versionTags_342_ = lean_ctor_get(v_cfg_320_, 18);
v_description_343_ = lean_ctor_get(v_cfg_320_, 19);
v_keywords_344_ = lean_ctor_get(v_cfg_320_, 20);
v_homepage_345_ = lean_ctor_get(v_cfg_320_, 21);
v_license_346_ = lean_ctor_get(v_cfg_320_, 22);
v_licenseFiles_347_ = lean_ctor_get(v_cfg_320_, 23);
v_readmeFile_348_ = lean_ctor_get(v_cfg_320_, 24);
v_reservoir_349_ = lean_ctor_get_uint8(v_cfg_320_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_350_ = lean_ctor_get(v_cfg_320_, 25);
v_restoreAllArtifacts_x3f_351_ = lean_ctor_get(v_cfg_320_, 26);
v_libPrefixOnWindows_352_ = lean_ctor_get_uint8(v_cfg_320_, sizeof(void*)*27 + 4);
v_allowImportAll_353_ = lean_ctor_get_uint8(v_cfg_320_, sizeof(void*)*27 + 5);
v_isSharedCheck_361_ = !lean_is_exclusive(v_cfg_320_);
if (v_isSharedCheck_361_ == 0)
{
v___x_355_ = v_cfg_320_;
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_351_);
lean_inc(v_enableArtifactCache_x3f_350_);
lean_inc(v_readmeFile_348_);
lean_inc(v_licenseFiles_347_);
lean_inc(v_license_346_);
lean_inc(v_homepage_345_);
lean_inc(v_keywords_344_);
lean_inc(v_description_343_);
lean_inc(v_versionTags_342_);
lean_inc(v_version_341_);
lean_inc(v_lintDriverArgs_340_);
lean_inc(v_lintDriver_339_);
lean_inc(v_testDriverArgs_338_);
lean_inc(v_testDriver_337_);
lean_inc(v_buildArchive_335_);
lean_inc(v_releaseRepo_334_);
lean_inc(v_irDir_333_);
lean_inc(v_binDir_332_);
lean_inc(v_nativeLibDir_331_);
lean_inc(v_leanLibDir_330_);
lean_inc(v_buildDir_329_);
lean_inc(v_srcDir_328_);
lean_inc(v_moreGlobalServerArgs_327_);
lean_inc(v_extraDepTargets_325_);
lean_inc(v_manifestFile_324_);
lean_inc(v_toLeanConfig_322_);
lean_inc(v_toWorkspaceConfig_321_);
lean_dec(v_cfg_320_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_apply_1(v_f_319_, v_extraDepTargets_325_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 3, v___x_357_);
v___x_359_ = v___x_355_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_toWorkspaceConfig_321_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_toLeanConfig_322_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_manifestFile_324_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_moreGlobalServerArgs_327_);
lean_ctor_set(v_reuseFailAlloc_360_, 5, v_srcDir_328_);
lean_ctor_set(v_reuseFailAlloc_360_, 6, v_buildDir_329_);
lean_ctor_set(v_reuseFailAlloc_360_, 7, v_leanLibDir_330_);
lean_ctor_set(v_reuseFailAlloc_360_, 8, v_nativeLibDir_331_);
lean_ctor_set(v_reuseFailAlloc_360_, 9, v_binDir_332_);
lean_ctor_set(v_reuseFailAlloc_360_, 10, v_irDir_333_);
lean_ctor_set(v_reuseFailAlloc_360_, 11, v_releaseRepo_334_);
lean_ctor_set(v_reuseFailAlloc_360_, 12, v_buildArchive_335_);
lean_ctor_set(v_reuseFailAlloc_360_, 13, v_testDriver_337_);
lean_ctor_set(v_reuseFailAlloc_360_, 14, v_testDriverArgs_338_);
lean_ctor_set(v_reuseFailAlloc_360_, 15, v_lintDriver_339_);
lean_ctor_set(v_reuseFailAlloc_360_, 16, v_lintDriverArgs_340_);
lean_ctor_set(v_reuseFailAlloc_360_, 17, v_version_341_);
lean_ctor_set(v_reuseFailAlloc_360_, 18, v_versionTags_342_);
lean_ctor_set(v_reuseFailAlloc_360_, 19, v_description_343_);
lean_ctor_set(v_reuseFailAlloc_360_, 20, v_keywords_344_);
lean_ctor_set(v_reuseFailAlloc_360_, 21, v_homepage_345_);
lean_ctor_set(v_reuseFailAlloc_360_, 22, v_license_346_);
lean_ctor_set(v_reuseFailAlloc_360_, 23, v_licenseFiles_347_);
lean_ctor_set(v_reuseFailAlloc_360_, 24, v_readmeFile_348_);
lean_ctor_set(v_reuseFailAlloc_360_, 25, v_enableArtifactCache_x3f_350_);
lean_ctor_set(v_reuseFailAlloc_360_, 26, v_restoreAllArtifacts_x3f_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*27, v_bootstrap_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*27 + 1, v_precompileModules_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*27 + 2, v_preferReleaseBuild_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*27 + 3, v_reservoir_349_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*27 + 5, v_allowImportAll_353_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___lam__3___closed__0));
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(v_x_366_);
lean_dec_ref(v_x_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_377_, lean_object* v_n_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_380_, lean_object* v_n_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_380_, v_n_381_);
lean_dec(v_n_381_);
lean_dec(v_p_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_383_, lean_object* v_n_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_383_, v_n_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_386_, lean_object* v_n_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_386_, v_n_387_);
lean_dec(v_n_387_);
lean_dec(v_p_386_);
return v_res_388_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* v_cfg_389_){
_start:
{
uint8_t v_precompileModules_390_; 
v_precompileModules_390_ = lean_ctor_get_uint8(v_cfg_389_, sizeof(void*)*27 + 1);
return v_precompileModules_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lake_PackageConfig_precompileModules___proj___lam__0(v_cfg_391_);
lean_dec_ref(v_cfg_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t v_val_394_, lean_object* v_cfg_395_){
_start:
{
lean_object* v_toWorkspaceConfig_396_; lean_object* v_toLeanConfig_397_; uint8_t v_bootstrap_398_; lean_object* v_manifestFile_399_; lean_object* v_extraDepTargets_400_; lean_object* v_moreGlobalServerArgs_401_; lean_object* v_srcDir_402_; lean_object* v_buildDir_403_; lean_object* v_leanLibDir_404_; lean_object* v_nativeLibDir_405_; lean_object* v_binDir_406_; lean_object* v_irDir_407_; lean_object* v_releaseRepo_408_; lean_object* v_buildArchive_409_; uint8_t v_preferReleaseBuild_410_; lean_object* v_testDriver_411_; lean_object* v_testDriverArgs_412_; lean_object* v_lintDriver_413_; lean_object* v_lintDriverArgs_414_; lean_object* v_version_415_; lean_object* v_versionTags_416_; lean_object* v_description_417_; lean_object* v_keywords_418_; lean_object* v_homepage_419_; lean_object* v_license_420_; lean_object* v_licenseFiles_421_; lean_object* v_readmeFile_422_; uint8_t v_reservoir_423_; lean_object* v_enableArtifactCache_x3f_424_; lean_object* v_restoreAllArtifacts_x3f_425_; uint8_t v_libPrefixOnWindows_426_; uint8_t v_allowImportAll_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_toWorkspaceConfig_396_ = lean_ctor_get(v_cfg_395_, 0);
v_toLeanConfig_397_ = lean_ctor_get(v_cfg_395_, 1);
v_bootstrap_398_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*27);
v_manifestFile_399_ = lean_ctor_get(v_cfg_395_, 2);
v_extraDepTargets_400_ = lean_ctor_get(v_cfg_395_, 3);
v_moreGlobalServerArgs_401_ = lean_ctor_get(v_cfg_395_, 4);
v_srcDir_402_ = lean_ctor_get(v_cfg_395_, 5);
v_buildDir_403_ = lean_ctor_get(v_cfg_395_, 6);
v_leanLibDir_404_ = lean_ctor_get(v_cfg_395_, 7);
v_nativeLibDir_405_ = lean_ctor_get(v_cfg_395_, 8);
v_binDir_406_ = lean_ctor_get(v_cfg_395_, 9);
v_irDir_407_ = lean_ctor_get(v_cfg_395_, 10);
v_releaseRepo_408_ = lean_ctor_get(v_cfg_395_, 11);
v_buildArchive_409_ = lean_ctor_get(v_cfg_395_, 12);
v_preferReleaseBuild_410_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*27 + 2);
v_testDriver_411_ = lean_ctor_get(v_cfg_395_, 13);
v_testDriverArgs_412_ = lean_ctor_get(v_cfg_395_, 14);
v_lintDriver_413_ = lean_ctor_get(v_cfg_395_, 15);
v_lintDriverArgs_414_ = lean_ctor_get(v_cfg_395_, 16);
v_version_415_ = lean_ctor_get(v_cfg_395_, 17);
v_versionTags_416_ = lean_ctor_get(v_cfg_395_, 18);
v_description_417_ = lean_ctor_get(v_cfg_395_, 19);
v_keywords_418_ = lean_ctor_get(v_cfg_395_, 20);
v_homepage_419_ = lean_ctor_get(v_cfg_395_, 21);
v_license_420_ = lean_ctor_get(v_cfg_395_, 22);
v_licenseFiles_421_ = lean_ctor_get(v_cfg_395_, 23);
v_readmeFile_422_ = lean_ctor_get(v_cfg_395_, 24);
v_reservoir_423_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_424_ = lean_ctor_get(v_cfg_395_, 25);
v_restoreAllArtifacts_x3f_425_ = lean_ctor_get(v_cfg_395_, 26);
v_libPrefixOnWindows_426_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*27 + 4);
v_allowImportAll_427_ = lean_ctor_get_uint8(v_cfg_395_, sizeof(void*)*27 + 5);
v_isSharedCheck_434_ = !lean_is_exclusive(v_cfg_395_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v_cfg_395_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_425_);
lean_inc(v_enableArtifactCache_x3f_424_);
lean_inc(v_readmeFile_422_);
lean_inc(v_licenseFiles_421_);
lean_inc(v_license_420_);
lean_inc(v_homepage_419_);
lean_inc(v_keywords_418_);
lean_inc(v_description_417_);
lean_inc(v_versionTags_416_);
lean_inc(v_version_415_);
lean_inc(v_lintDriverArgs_414_);
lean_inc(v_lintDriver_413_);
lean_inc(v_testDriverArgs_412_);
lean_inc(v_testDriver_411_);
lean_inc(v_buildArchive_409_);
lean_inc(v_releaseRepo_408_);
lean_inc(v_irDir_407_);
lean_inc(v_binDir_406_);
lean_inc(v_nativeLibDir_405_);
lean_inc(v_leanLibDir_404_);
lean_inc(v_buildDir_403_);
lean_inc(v_srcDir_402_);
lean_inc(v_moreGlobalServerArgs_401_);
lean_inc(v_extraDepTargets_400_);
lean_inc(v_manifestFile_399_);
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
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_toWorkspaceConfig_396_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_toLeanConfig_397_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_manifestFile_399_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_extraDepTargets_400_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_moreGlobalServerArgs_401_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_srcDir_402_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_buildDir_403_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_leanLibDir_404_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_nativeLibDir_405_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_binDir_406_);
lean_ctor_set(v_reuseFailAlloc_433_, 10, v_irDir_407_);
lean_ctor_set(v_reuseFailAlloc_433_, 11, v_releaseRepo_408_);
lean_ctor_set(v_reuseFailAlloc_433_, 12, v_buildArchive_409_);
lean_ctor_set(v_reuseFailAlloc_433_, 13, v_testDriver_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 14, v_testDriverArgs_412_);
lean_ctor_set(v_reuseFailAlloc_433_, 15, v_lintDriver_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 16, v_lintDriverArgs_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 17, v_version_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 18, v_versionTags_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 19, v_description_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 20, v_keywords_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 21, v_homepage_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 22, v_license_420_);
lean_ctor_set(v_reuseFailAlloc_433_, 23, v_licenseFiles_421_);
lean_ctor_set(v_reuseFailAlloc_433_, 24, v_readmeFile_422_);
lean_ctor_set(v_reuseFailAlloc_433_, 25, v_enableArtifactCache_x3f_424_);
lean_ctor_set(v_reuseFailAlloc_433_, 26, v_restoreAllArtifacts_x3f_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*27, v_bootstrap_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*27 + 2, v_preferReleaseBuild_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*27 + 3, v_reservoir_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*27 + 5, v_allowImportAll_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*27 + 1, v_val_394_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_435_, lean_object* v_cfg_436_){
_start:
{
uint8_t v_val_134__boxed_437_; lean_object* v_res_438_; 
v_val_134__boxed_437_ = lean_unbox(v_val_435_);
v_res_438_ = l_Lake_PackageConfig_precompileModules___proj___lam__1(v_val_134__boxed_437_, v_cfg_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* v_f_439_, lean_object* v_cfg_440_){
_start:
{
lean_object* v_toWorkspaceConfig_441_; lean_object* v_toLeanConfig_442_; uint8_t v_bootstrap_443_; lean_object* v_manifestFile_444_; lean_object* v_extraDepTargets_445_; uint8_t v_precompileModules_446_; lean_object* v_moreGlobalServerArgs_447_; lean_object* v_srcDir_448_; lean_object* v_buildDir_449_; lean_object* v_leanLibDir_450_; lean_object* v_nativeLibDir_451_; lean_object* v_binDir_452_; lean_object* v_irDir_453_; lean_object* v_releaseRepo_454_; lean_object* v_buildArchive_455_; uint8_t v_preferReleaseBuild_456_; lean_object* v_testDriver_457_; lean_object* v_testDriverArgs_458_; lean_object* v_lintDriver_459_; lean_object* v_lintDriverArgs_460_; lean_object* v_version_461_; lean_object* v_versionTags_462_; lean_object* v_description_463_; lean_object* v_keywords_464_; lean_object* v_homepage_465_; lean_object* v_license_466_; lean_object* v_licenseFiles_467_; lean_object* v_readmeFile_468_; uint8_t v_reservoir_469_; lean_object* v_enableArtifactCache_x3f_470_; lean_object* v_restoreAllArtifacts_x3f_471_; uint8_t v_libPrefixOnWindows_472_; uint8_t v_allowImportAll_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_483_; 
v_toWorkspaceConfig_441_ = lean_ctor_get(v_cfg_440_, 0);
v_toLeanConfig_442_ = lean_ctor_get(v_cfg_440_, 1);
v_bootstrap_443_ = lean_ctor_get_uint8(v_cfg_440_, sizeof(void*)*27);
v_manifestFile_444_ = lean_ctor_get(v_cfg_440_, 2);
v_extraDepTargets_445_ = lean_ctor_get(v_cfg_440_, 3);
v_precompileModules_446_ = lean_ctor_get_uint8(v_cfg_440_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_447_ = lean_ctor_get(v_cfg_440_, 4);
v_srcDir_448_ = lean_ctor_get(v_cfg_440_, 5);
v_buildDir_449_ = lean_ctor_get(v_cfg_440_, 6);
v_leanLibDir_450_ = lean_ctor_get(v_cfg_440_, 7);
v_nativeLibDir_451_ = lean_ctor_get(v_cfg_440_, 8);
v_binDir_452_ = lean_ctor_get(v_cfg_440_, 9);
v_irDir_453_ = lean_ctor_get(v_cfg_440_, 10);
v_releaseRepo_454_ = lean_ctor_get(v_cfg_440_, 11);
v_buildArchive_455_ = lean_ctor_get(v_cfg_440_, 12);
v_preferReleaseBuild_456_ = lean_ctor_get_uint8(v_cfg_440_, sizeof(void*)*27 + 2);
v_testDriver_457_ = lean_ctor_get(v_cfg_440_, 13);
v_testDriverArgs_458_ = lean_ctor_get(v_cfg_440_, 14);
v_lintDriver_459_ = lean_ctor_get(v_cfg_440_, 15);
v_lintDriverArgs_460_ = lean_ctor_get(v_cfg_440_, 16);
v_version_461_ = lean_ctor_get(v_cfg_440_, 17);
v_versionTags_462_ = lean_ctor_get(v_cfg_440_, 18);
v_description_463_ = lean_ctor_get(v_cfg_440_, 19);
v_keywords_464_ = lean_ctor_get(v_cfg_440_, 20);
v_homepage_465_ = lean_ctor_get(v_cfg_440_, 21);
v_license_466_ = lean_ctor_get(v_cfg_440_, 22);
v_licenseFiles_467_ = lean_ctor_get(v_cfg_440_, 23);
v_readmeFile_468_ = lean_ctor_get(v_cfg_440_, 24);
v_reservoir_469_ = lean_ctor_get_uint8(v_cfg_440_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_470_ = lean_ctor_get(v_cfg_440_, 25);
v_restoreAllArtifacts_x3f_471_ = lean_ctor_get(v_cfg_440_, 26);
v_libPrefixOnWindows_472_ = lean_ctor_get_uint8(v_cfg_440_, sizeof(void*)*27 + 4);
v_allowImportAll_473_ = lean_ctor_get_uint8(v_cfg_440_, sizeof(void*)*27 + 5);
v_isSharedCheck_483_ = !lean_is_exclusive(v_cfg_440_);
if (v_isSharedCheck_483_ == 0)
{
v___x_475_ = v_cfg_440_;
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_471_);
lean_inc(v_enableArtifactCache_x3f_470_);
lean_inc(v_readmeFile_468_);
lean_inc(v_licenseFiles_467_);
lean_inc(v_license_466_);
lean_inc(v_homepage_465_);
lean_inc(v_keywords_464_);
lean_inc(v_description_463_);
lean_inc(v_versionTags_462_);
lean_inc(v_version_461_);
lean_inc(v_lintDriverArgs_460_);
lean_inc(v_lintDriver_459_);
lean_inc(v_testDriverArgs_458_);
lean_inc(v_testDriver_457_);
lean_inc(v_buildArchive_455_);
lean_inc(v_releaseRepo_454_);
lean_inc(v_irDir_453_);
lean_inc(v_binDir_452_);
lean_inc(v_nativeLibDir_451_);
lean_inc(v_leanLibDir_450_);
lean_inc(v_buildDir_449_);
lean_inc(v_srcDir_448_);
lean_inc(v_moreGlobalServerArgs_447_);
lean_inc(v_extraDepTargets_445_);
lean_inc(v_manifestFile_444_);
lean_inc(v_toLeanConfig_442_);
lean_inc(v_toWorkspaceConfig_441_);
lean_dec(v_cfg_440_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_477_ = lean_box(v_precompileModules_446_);
v___x_478_ = lean_apply_1(v_f_439_, v___x_477_);
if (v_isShared_476_ == 0)
{
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_toWorkspaceConfig_441_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_toLeanConfig_442_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_manifestFile_444_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_extraDepTargets_445_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_moreGlobalServerArgs_447_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_srcDir_448_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_buildDir_449_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_leanLibDir_450_);
lean_ctor_set(v_reuseFailAlloc_482_, 8, v_nativeLibDir_451_);
lean_ctor_set(v_reuseFailAlloc_482_, 9, v_binDir_452_);
lean_ctor_set(v_reuseFailAlloc_482_, 10, v_irDir_453_);
lean_ctor_set(v_reuseFailAlloc_482_, 11, v_releaseRepo_454_);
lean_ctor_set(v_reuseFailAlloc_482_, 12, v_buildArchive_455_);
lean_ctor_set(v_reuseFailAlloc_482_, 13, v_testDriver_457_);
lean_ctor_set(v_reuseFailAlloc_482_, 14, v_testDriverArgs_458_);
lean_ctor_set(v_reuseFailAlloc_482_, 15, v_lintDriver_459_);
lean_ctor_set(v_reuseFailAlloc_482_, 16, v_lintDriverArgs_460_);
lean_ctor_set(v_reuseFailAlloc_482_, 17, v_version_461_);
lean_ctor_set(v_reuseFailAlloc_482_, 18, v_versionTags_462_);
lean_ctor_set(v_reuseFailAlloc_482_, 19, v_description_463_);
lean_ctor_set(v_reuseFailAlloc_482_, 20, v_keywords_464_);
lean_ctor_set(v_reuseFailAlloc_482_, 21, v_homepage_465_);
lean_ctor_set(v_reuseFailAlloc_482_, 22, v_license_466_);
lean_ctor_set(v_reuseFailAlloc_482_, 23, v_licenseFiles_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 24, v_readmeFile_468_);
lean_ctor_set(v_reuseFailAlloc_482_, 25, v_enableArtifactCache_x3f_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 26, v_restoreAllArtifacts_x3f_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*27, v_bootstrap_443_);
v___x_480_ = v_reuseFailAlloc_482_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
uint8_t v___x_481_; 
v___x_481_ = lean_unbox(v___x_478_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*27 + 1, v___x_481_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*27 + 2, v_preferReleaseBuild_456_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*27 + 3, v_reservoir_469_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_472_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*27 + 5, v_allowImportAll_473_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_492_, lean_object* v_n_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_495_, lean_object* v_n_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lake_PackageConfig_precompileModules___proj(v_p_495_, v_n_496_);
lean_dec(v_n_496_);
lean_dec(v_p_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_498_, lean_object* v_n_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lake_PackageConfig_precompileModules___proj(v_p_498_, v_n_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_501_, lean_object* v_n_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_501_, v_n_502_);
lean_dec(v_n_502_);
lean_dec(v_p_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* v_cfg_504_){
_start:
{
lean_object* v_moreGlobalServerArgs_505_; 
v_moreGlobalServerArgs_505_ = lean_ctor_get(v_cfg_504_, 4);
lean_inc_ref(v_moreGlobalServerArgs_505_);
return v_moreGlobalServerArgs_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* v_cfg_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(v_cfg_506_);
lean_dec_ref(v_cfg_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* v_val_508_, lean_object* v_cfg_509_){
_start:
{
lean_object* v_toWorkspaceConfig_510_; lean_object* v_toLeanConfig_511_; uint8_t v_bootstrap_512_; lean_object* v_manifestFile_513_; lean_object* v_extraDepTargets_514_; uint8_t v_precompileModules_515_; lean_object* v_srcDir_516_; lean_object* v_buildDir_517_; lean_object* v_leanLibDir_518_; lean_object* v_nativeLibDir_519_; lean_object* v_binDir_520_; lean_object* v_irDir_521_; lean_object* v_releaseRepo_522_; lean_object* v_buildArchive_523_; uint8_t v_preferReleaseBuild_524_; lean_object* v_testDriver_525_; lean_object* v_testDriverArgs_526_; lean_object* v_lintDriver_527_; lean_object* v_lintDriverArgs_528_; lean_object* v_version_529_; lean_object* v_versionTags_530_; lean_object* v_description_531_; lean_object* v_keywords_532_; lean_object* v_homepage_533_; lean_object* v_license_534_; lean_object* v_licenseFiles_535_; lean_object* v_readmeFile_536_; uint8_t v_reservoir_537_; lean_object* v_enableArtifactCache_x3f_538_; lean_object* v_restoreAllArtifacts_x3f_539_; uint8_t v_libPrefixOnWindows_540_; uint8_t v_allowImportAll_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_toWorkspaceConfig_510_ = lean_ctor_get(v_cfg_509_, 0);
v_toLeanConfig_511_ = lean_ctor_get(v_cfg_509_, 1);
v_bootstrap_512_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*27);
v_manifestFile_513_ = lean_ctor_get(v_cfg_509_, 2);
v_extraDepTargets_514_ = lean_ctor_get(v_cfg_509_, 3);
v_precompileModules_515_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*27 + 1);
v_srcDir_516_ = lean_ctor_get(v_cfg_509_, 5);
v_buildDir_517_ = lean_ctor_get(v_cfg_509_, 6);
v_leanLibDir_518_ = lean_ctor_get(v_cfg_509_, 7);
v_nativeLibDir_519_ = lean_ctor_get(v_cfg_509_, 8);
v_binDir_520_ = lean_ctor_get(v_cfg_509_, 9);
v_irDir_521_ = lean_ctor_get(v_cfg_509_, 10);
v_releaseRepo_522_ = lean_ctor_get(v_cfg_509_, 11);
v_buildArchive_523_ = lean_ctor_get(v_cfg_509_, 12);
v_preferReleaseBuild_524_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*27 + 2);
v_testDriver_525_ = lean_ctor_get(v_cfg_509_, 13);
v_testDriverArgs_526_ = lean_ctor_get(v_cfg_509_, 14);
v_lintDriver_527_ = lean_ctor_get(v_cfg_509_, 15);
v_lintDriverArgs_528_ = lean_ctor_get(v_cfg_509_, 16);
v_version_529_ = lean_ctor_get(v_cfg_509_, 17);
v_versionTags_530_ = lean_ctor_get(v_cfg_509_, 18);
v_description_531_ = lean_ctor_get(v_cfg_509_, 19);
v_keywords_532_ = lean_ctor_get(v_cfg_509_, 20);
v_homepage_533_ = lean_ctor_get(v_cfg_509_, 21);
v_license_534_ = lean_ctor_get(v_cfg_509_, 22);
v_licenseFiles_535_ = lean_ctor_get(v_cfg_509_, 23);
v_readmeFile_536_ = lean_ctor_get(v_cfg_509_, 24);
v_reservoir_537_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_538_ = lean_ctor_get(v_cfg_509_, 25);
v_restoreAllArtifacts_x3f_539_ = lean_ctor_get(v_cfg_509_, 26);
v_libPrefixOnWindows_540_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*27 + 4);
v_allowImportAll_541_ = lean_ctor_get_uint8(v_cfg_509_, sizeof(void*)*27 + 5);
v_isSharedCheck_548_ = !lean_is_exclusive(v_cfg_509_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_cfg_509_, 4);
lean_dec(v_unused_549_);
v___x_543_ = v_cfg_509_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_539_);
lean_inc(v_enableArtifactCache_x3f_538_);
lean_inc(v_readmeFile_536_);
lean_inc(v_licenseFiles_535_);
lean_inc(v_license_534_);
lean_inc(v_homepage_533_);
lean_inc(v_keywords_532_);
lean_inc(v_description_531_);
lean_inc(v_versionTags_530_);
lean_inc(v_version_529_);
lean_inc(v_lintDriverArgs_528_);
lean_inc(v_lintDriver_527_);
lean_inc(v_testDriverArgs_526_);
lean_inc(v_testDriver_525_);
lean_inc(v_buildArchive_523_);
lean_inc(v_releaseRepo_522_);
lean_inc(v_irDir_521_);
lean_inc(v_binDir_520_);
lean_inc(v_nativeLibDir_519_);
lean_inc(v_leanLibDir_518_);
lean_inc(v_buildDir_517_);
lean_inc(v_srcDir_516_);
lean_inc(v_extraDepTargets_514_);
lean_inc(v_manifestFile_513_);
lean_inc(v_toLeanConfig_511_);
lean_inc(v_toWorkspaceConfig_510_);
lean_dec(v_cfg_509_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 4, v_val_508_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_toWorkspaceConfig_510_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_toLeanConfig_511_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_manifestFile_513_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_extraDepTargets_514_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_val_508_);
lean_ctor_set(v_reuseFailAlloc_547_, 5, v_srcDir_516_);
lean_ctor_set(v_reuseFailAlloc_547_, 6, v_buildDir_517_);
lean_ctor_set(v_reuseFailAlloc_547_, 7, v_leanLibDir_518_);
lean_ctor_set(v_reuseFailAlloc_547_, 8, v_nativeLibDir_519_);
lean_ctor_set(v_reuseFailAlloc_547_, 9, v_binDir_520_);
lean_ctor_set(v_reuseFailAlloc_547_, 10, v_irDir_521_);
lean_ctor_set(v_reuseFailAlloc_547_, 11, v_releaseRepo_522_);
lean_ctor_set(v_reuseFailAlloc_547_, 12, v_buildArchive_523_);
lean_ctor_set(v_reuseFailAlloc_547_, 13, v_testDriver_525_);
lean_ctor_set(v_reuseFailAlloc_547_, 14, v_testDriverArgs_526_);
lean_ctor_set(v_reuseFailAlloc_547_, 15, v_lintDriver_527_);
lean_ctor_set(v_reuseFailAlloc_547_, 16, v_lintDriverArgs_528_);
lean_ctor_set(v_reuseFailAlloc_547_, 17, v_version_529_);
lean_ctor_set(v_reuseFailAlloc_547_, 18, v_versionTags_530_);
lean_ctor_set(v_reuseFailAlloc_547_, 19, v_description_531_);
lean_ctor_set(v_reuseFailAlloc_547_, 20, v_keywords_532_);
lean_ctor_set(v_reuseFailAlloc_547_, 21, v_homepage_533_);
lean_ctor_set(v_reuseFailAlloc_547_, 22, v_license_534_);
lean_ctor_set(v_reuseFailAlloc_547_, 23, v_licenseFiles_535_);
lean_ctor_set(v_reuseFailAlloc_547_, 24, v_readmeFile_536_);
lean_ctor_set(v_reuseFailAlloc_547_, 25, v_enableArtifactCache_x3f_538_);
lean_ctor_set(v_reuseFailAlloc_547_, 26, v_restoreAllArtifacts_x3f_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*27, v_bootstrap_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*27 + 1, v_precompileModules_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*27 + 2, v_preferReleaseBuild_524_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*27 + 3, v_reservoir_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, sizeof(void*)*27 + 5, v_allowImportAll_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object* v_f_550_, lean_object* v_cfg_551_){
_start:
{
lean_object* v_toWorkspaceConfig_552_; lean_object* v_toLeanConfig_553_; uint8_t v_bootstrap_554_; lean_object* v_manifestFile_555_; lean_object* v_extraDepTargets_556_; uint8_t v_precompileModules_557_; lean_object* v_moreGlobalServerArgs_558_; lean_object* v_srcDir_559_; lean_object* v_buildDir_560_; lean_object* v_leanLibDir_561_; lean_object* v_nativeLibDir_562_; lean_object* v_binDir_563_; lean_object* v_irDir_564_; lean_object* v_releaseRepo_565_; lean_object* v_buildArchive_566_; uint8_t v_preferReleaseBuild_567_; lean_object* v_testDriver_568_; lean_object* v_testDriverArgs_569_; lean_object* v_lintDriver_570_; lean_object* v_lintDriverArgs_571_; lean_object* v_version_572_; lean_object* v_versionTags_573_; lean_object* v_description_574_; lean_object* v_keywords_575_; lean_object* v_homepage_576_; lean_object* v_license_577_; lean_object* v_licenseFiles_578_; lean_object* v_readmeFile_579_; uint8_t v_reservoir_580_; lean_object* v_enableArtifactCache_x3f_581_; lean_object* v_restoreAllArtifacts_x3f_582_; uint8_t v_libPrefixOnWindows_583_; uint8_t v_allowImportAll_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_toWorkspaceConfig_552_ = lean_ctor_get(v_cfg_551_, 0);
v_toLeanConfig_553_ = lean_ctor_get(v_cfg_551_, 1);
v_bootstrap_554_ = lean_ctor_get_uint8(v_cfg_551_, sizeof(void*)*27);
v_manifestFile_555_ = lean_ctor_get(v_cfg_551_, 2);
v_extraDepTargets_556_ = lean_ctor_get(v_cfg_551_, 3);
v_precompileModules_557_ = lean_ctor_get_uint8(v_cfg_551_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_558_ = lean_ctor_get(v_cfg_551_, 4);
v_srcDir_559_ = lean_ctor_get(v_cfg_551_, 5);
v_buildDir_560_ = lean_ctor_get(v_cfg_551_, 6);
v_leanLibDir_561_ = lean_ctor_get(v_cfg_551_, 7);
v_nativeLibDir_562_ = lean_ctor_get(v_cfg_551_, 8);
v_binDir_563_ = lean_ctor_get(v_cfg_551_, 9);
v_irDir_564_ = lean_ctor_get(v_cfg_551_, 10);
v_releaseRepo_565_ = lean_ctor_get(v_cfg_551_, 11);
v_buildArchive_566_ = lean_ctor_get(v_cfg_551_, 12);
v_preferReleaseBuild_567_ = lean_ctor_get_uint8(v_cfg_551_, sizeof(void*)*27 + 2);
v_testDriver_568_ = lean_ctor_get(v_cfg_551_, 13);
v_testDriverArgs_569_ = lean_ctor_get(v_cfg_551_, 14);
v_lintDriver_570_ = lean_ctor_get(v_cfg_551_, 15);
v_lintDriverArgs_571_ = lean_ctor_get(v_cfg_551_, 16);
v_version_572_ = lean_ctor_get(v_cfg_551_, 17);
v_versionTags_573_ = lean_ctor_get(v_cfg_551_, 18);
v_description_574_ = lean_ctor_get(v_cfg_551_, 19);
v_keywords_575_ = lean_ctor_get(v_cfg_551_, 20);
v_homepage_576_ = lean_ctor_get(v_cfg_551_, 21);
v_license_577_ = lean_ctor_get(v_cfg_551_, 22);
v_licenseFiles_578_ = lean_ctor_get(v_cfg_551_, 23);
v_readmeFile_579_ = lean_ctor_get(v_cfg_551_, 24);
v_reservoir_580_ = lean_ctor_get_uint8(v_cfg_551_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_581_ = lean_ctor_get(v_cfg_551_, 25);
v_restoreAllArtifacts_x3f_582_ = lean_ctor_get(v_cfg_551_, 26);
v_libPrefixOnWindows_583_ = lean_ctor_get_uint8(v_cfg_551_, sizeof(void*)*27 + 4);
v_allowImportAll_584_ = lean_ctor_get_uint8(v_cfg_551_, sizeof(void*)*27 + 5);
v_isSharedCheck_592_ = !lean_is_exclusive(v_cfg_551_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v_cfg_551_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_582_);
lean_inc(v_enableArtifactCache_x3f_581_);
lean_inc(v_readmeFile_579_);
lean_inc(v_licenseFiles_578_);
lean_inc(v_license_577_);
lean_inc(v_homepage_576_);
lean_inc(v_keywords_575_);
lean_inc(v_description_574_);
lean_inc(v_versionTags_573_);
lean_inc(v_version_572_);
lean_inc(v_lintDriverArgs_571_);
lean_inc(v_lintDriver_570_);
lean_inc(v_testDriverArgs_569_);
lean_inc(v_testDriver_568_);
lean_inc(v_buildArchive_566_);
lean_inc(v_releaseRepo_565_);
lean_inc(v_irDir_564_);
lean_inc(v_binDir_563_);
lean_inc(v_nativeLibDir_562_);
lean_inc(v_leanLibDir_561_);
lean_inc(v_buildDir_560_);
lean_inc(v_srcDir_559_);
lean_inc(v_moreGlobalServerArgs_558_);
lean_inc(v_extraDepTargets_556_);
lean_inc(v_manifestFile_555_);
lean_inc(v_toLeanConfig_553_);
lean_inc(v_toWorkspaceConfig_552_);
lean_dec(v_cfg_551_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_apply_1(v_f_550_, v_moreGlobalServerArgs_558_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 4, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_toWorkspaceConfig_552_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_toLeanConfig_553_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_manifestFile_555_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_extraDepTargets_556_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v_srcDir_559_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_buildDir_560_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_leanLibDir_561_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_nativeLibDir_562_);
lean_ctor_set(v_reuseFailAlloc_591_, 9, v_binDir_563_);
lean_ctor_set(v_reuseFailAlloc_591_, 10, v_irDir_564_);
lean_ctor_set(v_reuseFailAlloc_591_, 11, v_releaseRepo_565_);
lean_ctor_set(v_reuseFailAlloc_591_, 12, v_buildArchive_566_);
lean_ctor_set(v_reuseFailAlloc_591_, 13, v_testDriver_568_);
lean_ctor_set(v_reuseFailAlloc_591_, 14, v_testDriverArgs_569_);
lean_ctor_set(v_reuseFailAlloc_591_, 15, v_lintDriver_570_);
lean_ctor_set(v_reuseFailAlloc_591_, 16, v_lintDriverArgs_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 17, v_version_572_);
lean_ctor_set(v_reuseFailAlloc_591_, 18, v_versionTags_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 19, v_description_574_);
lean_ctor_set(v_reuseFailAlloc_591_, 20, v_keywords_575_);
lean_ctor_set(v_reuseFailAlloc_591_, 21, v_homepage_576_);
lean_ctor_set(v_reuseFailAlloc_591_, 22, v_license_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 23, v_licenseFiles_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 24, v_readmeFile_579_);
lean_ctor_set(v_reuseFailAlloc_591_, 25, v_enableArtifactCache_x3f_581_);
lean_ctor_set(v_reuseFailAlloc_591_, 26, v_restoreAllArtifacts_x3f_582_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*27, v_bootstrap_554_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*27 + 1, v_precompileModules_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*27 + 2, v_preferReleaseBuild_567_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*27 + 3, v_reservoir_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*27 + 5, v_allowImportAll_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0));
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* v_x_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(v_x_597_);
lean_dec_ref(v_x_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_608_, lean_object* v_n_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_611_, lean_object* v_n_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_611_, v_n_612_);
lean_dec(v_n_612_);
lean_dec(v_p_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_614_, lean_object* v_n_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_614_, v_n_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_617_, lean_object* v_n_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_617_, v_n_618_);
lean_dec(v_n_618_);
lean_dec(v_p_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_620_, lean_object* v_n_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_620_, v_n_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_623_, lean_object* v_n_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_623_, v_n_624_);
lean_dec(v_n_624_);
lean_dec(v_p_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* v_cfg_626_){
_start:
{
lean_object* v_srcDir_627_; 
v_srcDir_627_ = lean_ctor_get(v_cfg_626_, 5);
lean_inc_ref(v_srcDir_627_);
return v_srcDir_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lake_PackageConfig_srcDir___proj___lam__0(v_cfg_628_);
lean_dec_ref(v_cfg_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* v_val_630_, lean_object* v_cfg_631_){
_start:
{
lean_object* v_toWorkspaceConfig_632_; lean_object* v_toLeanConfig_633_; uint8_t v_bootstrap_634_; lean_object* v_manifestFile_635_; lean_object* v_extraDepTargets_636_; uint8_t v_precompileModules_637_; lean_object* v_moreGlobalServerArgs_638_; lean_object* v_buildDir_639_; lean_object* v_leanLibDir_640_; lean_object* v_nativeLibDir_641_; lean_object* v_binDir_642_; lean_object* v_irDir_643_; lean_object* v_releaseRepo_644_; lean_object* v_buildArchive_645_; uint8_t v_preferReleaseBuild_646_; lean_object* v_testDriver_647_; lean_object* v_testDriverArgs_648_; lean_object* v_lintDriver_649_; lean_object* v_lintDriverArgs_650_; lean_object* v_version_651_; lean_object* v_versionTags_652_; lean_object* v_description_653_; lean_object* v_keywords_654_; lean_object* v_homepage_655_; lean_object* v_license_656_; lean_object* v_licenseFiles_657_; lean_object* v_readmeFile_658_; uint8_t v_reservoir_659_; lean_object* v_enableArtifactCache_x3f_660_; lean_object* v_restoreAllArtifacts_x3f_661_; uint8_t v_libPrefixOnWindows_662_; uint8_t v_allowImportAll_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_toWorkspaceConfig_632_ = lean_ctor_get(v_cfg_631_, 0);
v_toLeanConfig_633_ = lean_ctor_get(v_cfg_631_, 1);
v_bootstrap_634_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*27);
v_manifestFile_635_ = lean_ctor_get(v_cfg_631_, 2);
v_extraDepTargets_636_ = lean_ctor_get(v_cfg_631_, 3);
v_precompileModules_637_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_638_ = lean_ctor_get(v_cfg_631_, 4);
v_buildDir_639_ = lean_ctor_get(v_cfg_631_, 6);
v_leanLibDir_640_ = lean_ctor_get(v_cfg_631_, 7);
v_nativeLibDir_641_ = lean_ctor_get(v_cfg_631_, 8);
v_binDir_642_ = lean_ctor_get(v_cfg_631_, 9);
v_irDir_643_ = lean_ctor_get(v_cfg_631_, 10);
v_releaseRepo_644_ = lean_ctor_get(v_cfg_631_, 11);
v_buildArchive_645_ = lean_ctor_get(v_cfg_631_, 12);
v_preferReleaseBuild_646_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*27 + 2);
v_testDriver_647_ = lean_ctor_get(v_cfg_631_, 13);
v_testDriverArgs_648_ = lean_ctor_get(v_cfg_631_, 14);
v_lintDriver_649_ = lean_ctor_get(v_cfg_631_, 15);
v_lintDriverArgs_650_ = lean_ctor_get(v_cfg_631_, 16);
v_version_651_ = lean_ctor_get(v_cfg_631_, 17);
v_versionTags_652_ = lean_ctor_get(v_cfg_631_, 18);
v_description_653_ = lean_ctor_get(v_cfg_631_, 19);
v_keywords_654_ = lean_ctor_get(v_cfg_631_, 20);
v_homepage_655_ = lean_ctor_get(v_cfg_631_, 21);
v_license_656_ = lean_ctor_get(v_cfg_631_, 22);
v_licenseFiles_657_ = lean_ctor_get(v_cfg_631_, 23);
v_readmeFile_658_ = lean_ctor_get(v_cfg_631_, 24);
v_reservoir_659_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_660_ = lean_ctor_get(v_cfg_631_, 25);
v_restoreAllArtifacts_x3f_661_ = lean_ctor_get(v_cfg_631_, 26);
v_libPrefixOnWindows_662_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*27 + 4);
v_allowImportAll_663_ = lean_ctor_get_uint8(v_cfg_631_, sizeof(void*)*27 + 5);
v_isSharedCheck_670_ = !lean_is_exclusive(v_cfg_631_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_cfg_631_, 5);
lean_dec(v_unused_671_);
v___x_665_ = v_cfg_631_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
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
lean_inc(v_buildDir_639_);
lean_inc(v_moreGlobalServerArgs_638_);
lean_inc(v_extraDepTargets_636_);
lean_inc(v_manifestFile_635_);
lean_inc(v_toLeanConfig_633_);
lean_inc(v_toWorkspaceConfig_632_);
lean_dec(v_cfg_631_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 5, v_val_630_);
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_toWorkspaceConfig_632_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_toLeanConfig_633_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_manifestFile_635_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_extraDepTargets_636_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_moreGlobalServerArgs_638_);
lean_ctor_set(v_reuseFailAlloc_669_, 5, v_val_630_);
lean_ctor_set(v_reuseFailAlloc_669_, 6, v_buildDir_639_);
lean_ctor_set(v_reuseFailAlloc_669_, 7, v_leanLibDir_640_);
lean_ctor_set(v_reuseFailAlloc_669_, 8, v_nativeLibDir_641_);
lean_ctor_set(v_reuseFailAlloc_669_, 9, v_binDir_642_);
lean_ctor_set(v_reuseFailAlloc_669_, 10, v_irDir_643_);
lean_ctor_set(v_reuseFailAlloc_669_, 11, v_releaseRepo_644_);
lean_ctor_set(v_reuseFailAlloc_669_, 12, v_buildArchive_645_);
lean_ctor_set(v_reuseFailAlloc_669_, 13, v_testDriver_647_);
lean_ctor_set(v_reuseFailAlloc_669_, 14, v_testDriverArgs_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 15, v_lintDriver_649_);
lean_ctor_set(v_reuseFailAlloc_669_, 16, v_lintDriverArgs_650_);
lean_ctor_set(v_reuseFailAlloc_669_, 17, v_version_651_);
lean_ctor_set(v_reuseFailAlloc_669_, 18, v_versionTags_652_);
lean_ctor_set(v_reuseFailAlloc_669_, 19, v_description_653_);
lean_ctor_set(v_reuseFailAlloc_669_, 20, v_keywords_654_);
lean_ctor_set(v_reuseFailAlloc_669_, 21, v_homepage_655_);
lean_ctor_set(v_reuseFailAlloc_669_, 22, v_license_656_);
lean_ctor_set(v_reuseFailAlloc_669_, 23, v_licenseFiles_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 24, v_readmeFile_658_);
lean_ctor_set(v_reuseFailAlloc_669_, 25, v_enableArtifactCache_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 26, v_restoreAllArtifacts_x3f_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*27, v_bootstrap_634_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*27 + 1, v_precompileModules_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*27 + 2, v_preferReleaseBuild_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*27 + 3, v_reservoir_659_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*27 + 5, v_allowImportAll_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* v_f_672_, lean_object* v_cfg_673_){
_start:
{
lean_object* v_toWorkspaceConfig_674_; lean_object* v_toLeanConfig_675_; uint8_t v_bootstrap_676_; lean_object* v_manifestFile_677_; lean_object* v_extraDepTargets_678_; uint8_t v_precompileModules_679_; lean_object* v_moreGlobalServerArgs_680_; lean_object* v_srcDir_681_; lean_object* v_buildDir_682_; lean_object* v_leanLibDir_683_; lean_object* v_nativeLibDir_684_; lean_object* v_binDir_685_; lean_object* v_irDir_686_; lean_object* v_releaseRepo_687_; lean_object* v_buildArchive_688_; uint8_t v_preferReleaseBuild_689_; lean_object* v_testDriver_690_; lean_object* v_testDriverArgs_691_; lean_object* v_lintDriver_692_; lean_object* v_lintDriverArgs_693_; lean_object* v_version_694_; lean_object* v_versionTags_695_; lean_object* v_description_696_; lean_object* v_keywords_697_; lean_object* v_homepage_698_; lean_object* v_license_699_; lean_object* v_licenseFiles_700_; lean_object* v_readmeFile_701_; uint8_t v_reservoir_702_; lean_object* v_enableArtifactCache_x3f_703_; lean_object* v_restoreAllArtifacts_x3f_704_; uint8_t v_libPrefixOnWindows_705_; uint8_t v_allowImportAll_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_toWorkspaceConfig_674_ = lean_ctor_get(v_cfg_673_, 0);
v_toLeanConfig_675_ = lean_ctor_get(v_cfg_673_, 1);
v_bootstrap_676_ = lean_ctor_get_uint8(v_cfg_673_, sizeof(void*)*27);
v_manifestFile_677_ = lean_ctor_get(v_cfg_673_, 2);
v_extraDepTargets_678_ = lean_ctor_get(v_cfg_673_, 3);
v_precompileModules_679_ = lean_ctor_get_uint8(v_cfg_673_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_680_ = lean_ctor_get(v_cfg_673_, 4);
v_srcDir_681_ = lean_ctor_get(v_cfg_673_, 5);
v_buildDir_682_ = lean_ctor_get(v_cfg_673_, 6);
v_leanLibDir_683_ = lean_ctor_get(v_cfg_673_, 7);
v_nativeLibDir_684_ = lean_ctor_get(v_cfg_673_, 8);
v_binDir_685_ = lean_ctor_get(v_cfg_673_, 9);
v_irDir_686_ = lean_ctor_get(v_cfg_673_, 10);
v_releaseRepo_687_ = lean_ctor_get(v_cfg_673_, 11);
v_buildArchive_688_ = lean_ctor_get(v_cfg_673_, 12);
v_preferReleaseBuild_689_ = lean_ctor_get_uint8(v_cfg_673_, sizeof(void*)*27 + 2);
v_testDriver_690_ = lean_ctor_get(v_cfg_673_, 13);
v_testDriverArgs_691_ = lean_ctor_get(v_cfg_673_, 14);
v_lintDriver_692_ = lean_ctor_get(v_cfg_673_, 15);
v_lintDriverArgs_693_ = lean_ctor_get(v_cfg_673_, 16);
v_version_694_ = lean_ctor_get(v_cfg_673_, 17);
v_versionTags_695_ = lean_ctor_get(v_cfg_673_, 18);
v_description_696_ = lean_ctor_get(v_cfg_673_, 19);
v_keywords_697_ = lean_ctor_get(v_cfg_673_, 20);
v_homepage_698_ = lean_ctor_get(v_cfg_673_, 21);
v_license_699_ = lean_ctor_get(v_cfg_673_, 22);
v_licenseFiles_700_ = lean_ctor_get(v_cfg_673_, 23);
v_readmeFile_701_ = lean_ctor_get(v_cfg_673_, 24);
v_reservoir_702_ = lean_ctor_get_uint8(v_cfg_673_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_703_ = lean_ctor_get(v_cfg_673_, 25);
v_restoreAllArtifacts_x3f_704_ = lean_ctor_get(v_cfg_673_, 26);
v_libPrefixOnWindows_705_ = lean_ctor_get_uint8(v_cfg_673_, sizeof(void*)*27 + 4);
v_allowImportAll_706_ = lean_ctor_get_uint8(v_cfg_673_, sizeof(void*)*27 + 5);
v_isSharedCheck_714_ = !lean_is_exclusive(v_cfg_673_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v_cfg_673_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
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
lean_inc(v_manifestFile_677_);
lean_inc(v_toLeanConfig_675_);
lean_inc(v_toWorkspaceConfig_674_);
lean_dec(v_cfg_673_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_apply_1(v_f_672_, v_srcDir_681_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 5, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_toWorkspaceConfig_674_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_toLeanConfig_675_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_manifestFile_677_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_extraDepTargets_678_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_moreGlobalServerArgs_680_);
lean_ctor_set(v_reuseFailAlloc_713_, 5, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 6, v_buildDir_682_);
lean_ctor_set(v_reuseFailAlloc_713_, 7, v_leanLibDir_683_);
lean_ctor_set(v_reuseFailAlloc_713_, 8, v_nativeLibDir_684_);
lean_ctor_set(v_reuseFailAlloc_713_, 9, v_binDir_685_);
lean_ctor_set(v_reuseFailAlloc_713_, 10, v_irDir_686_);
lean_ctor_set(v_reuseFailAlloc_713_, 11, v_releaseRepo_687_);
lean_ctor_set(v_reuseFailAlloc_713_, 12, v_buildArchive_688_);
lean_ctor_set(v_reuseFailAlloc_713_, 13, v_testDriver_690_);
lean_ctor_set(v_reuseFailAlloc_713_, 14, v_testDriverArgs_691_);
lean_ctor_set(v_reuseFailAlloc_713_, 15, v_lintDriver_692_);
lean_ctor_set(v_reuseFailAlloc_713_, 16, v_lintDriverArgs_693_);
lean_ctor_set(v_reuseFailAlloc_713_, 17, v_version_694_);
lean_ctor_set(v_reuseFailAlloc_713_, 18, v_versionTags_695_);
lean_ctor_set(v_reuseFailAlloc_713_, 19, v_description_696_);
lean_ctor_set(v_reuseFailAlloc_713_, 20, v_keywords_697_);
lean_ctor_set(v_reuseFailAlloc_713_, 21, v_homepage_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 22, v_license_699_);
lean_ctor_set(v_reuseFailAlloc_713_, 23, v_licenseFiles_700_);
lean_ctor_set(v_reuseFailAlloc_713_, 24, v_readmeFile_701_);
lean_ctor_set(v_reuseFailAlloc_713_, 25, v_enableArtifactCache_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_713_, 26, v_restoreAllArtifacts_x3f_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*27, v_bootstrap_676_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*27 + 1, v_precompileModules_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*27 + 2, v_preferReleaseBuild_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*27 + 3, v_reservoir_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*27 + 5, v_allowImportAll_706_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0));
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lake_PackageConfig_srcDir___proj___lam__3(v_x_718_);
lean_dec_ref(v_x_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_729_, lean_object* v_n_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_732_, lean_object* v_n_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lake_PackageConfig_srcDir___proj(v_p_732_, v_n_733_);
lean_dec(v_n_733_);
lean_dec(v_p_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_735_, lean_object* v_n_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lake_PackageConfig_srcDir___proj(v_p_735_, v_n_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_738_, lean_object* v_n_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_738_, v_n_739_);
lean_dec(v_n_739_);
lean_dec(v_p_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* v_cfg_741_){
_start:
{
lean_object* v_buildDir_742_; 
v_buildDir_742_ = lean_ctor_get(v_cfg_741_, 6);
lean_inc_ref(v_buildDir_742_);
return v_buildDir_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* v_cfg_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lake_PackageConfig_buildDir___proj___lam__0(v_cfg_743_);
lean_dec_ref(v_cfg_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* v_val_745_, lean_object* v_cfg_746_){
_start:
{
lean_object* v_toWorkspaceConfig_747_; lean_object* v_toLeanConfig_748_; uint8_t v_bootstrap_749_; lean_object* v_manifestFile_750_; lean_object* v_extraDepTargets_751_; uint8_t v_precompileModules_752_; lean_object* v_moreGlobalServerArgs_753_; lean_object* v_srcDir_754_; lean_object* v_leanLibDir_755_; lean_object* v_nativeLibDir_756_; lean_object* v_binDir_757_; lean_object* v_irDir_758_; lean_object* v_releaseRepo_759_; lean_object* v_buildArchive_760_; uint8_t v_preferReleaseBuild_761_; lean_object* v_testDriver_762_; lean_object* v_testDriverArgs_763_; lean_object* v_lintDriver_764_; lean_object* v_lintDriverArgs_765_; lean_object* v_version_766_; lean_object* v_versionTags_767_; lean_object* v_description_768_; lean_object* v_keywords_769_; lean_object* v_homepage_770_; lean_object* v_license_771_; lean_object* v_licenseFiles_772_; lean_object* v_readmeFile_773_; uint8_t v_reservoir_774_; lean_object* v_enableArtifactCache_x3f_775_; lean_object* v_restoreAllArtifacts_x3f_776_; uint8_t v_libPrefixOnWindows_777_; uint8_t v_allowImportAll_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_toWorkspaceConfig_747_ = lean_ctor_get(v_cfg_746_, 0);
v_toLeanConfig_748_ = lean_ctor_get(v_cfg_746_, 1);
v_bootstrap_749_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*27);
v_manifestFile_750_ = lean_ctor_get(v_cfg_746_, 2);
v_extraDepTargets_751_ = lean_ctor_get(v_cfg_746_, 3);
v_precompileModules_752_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_753_ = lean_ctor_get(v_cfg_746_, 4);
v_srcDir_754_ = lean_ctor_get(v_cfg_746_, 5);
v_leanLibDir_755_ = lean_ctor_get(v_cfg_746_, 7);
v_nativeLibDir_756_ = lean_ctor_get(v_cfg_746_, 8);
v_binDir_757_ = lean_ctor_get(v_cfg_746_, 9);
v_irDir_758_ = lean_ctor_get(v_cfg_746_, 10);
v_releaseRepo_759_ = lean_ctor_get(v_cfg_746_, 11);
v_buildArchive_760_ = lean_ctor_get(v_cfg_746_, 12);
v_preferReleaseBuild_761_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*27 + 2);
v_testDriver_762_ = lean_ctor_get(v_cfg_746_, 13);
v_testDriverArgs_763_ = lean_ctor_get(v_cfg_746_, 14);
v_lintDriver_764_ = lean_ctor_get(v_cfg_746_, 15);
v_lintDriverArgs_765_ = lean_ctor_get(v_cfg_746_, 16);
v_version_766_ = lean_ctor_get(v_cfg_746_, 17);
v_versionTags_767_ = lean_ctor_get(v_cfg_746_, 18);
v_description_768_ = lean_ctor_get(v_cfg_746_, 19);
v_keywords_769_ = lean_ctor_get(v_cfg_746_, 20);
v_homepage_770_ = lean_ctor_get(v_cfg_746_, 21);
v_license_771_ = lean_ctor_get(v_cfg_746_, 22);
v_licenseFiles_772_ = lean_ctor_get(v_cfg_746_, 23);
v_readmeFile_773_ = lean_ctor_get(v_cfg_746_, 24);
v_reservoir_774_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_775_ = lean_ctor_get(v_cfg_746_, 25);
v_restoreAllArtifacts_x3f_776_ = lean_ctor_get(v_cfg_746_, 26);
v_libPrefixOnWindows_777_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*27 + 4);
v_allowImportAll_778_ = lean_ctor_get_uint8(v_cfg_746_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_776_);
lean_inc(v_enableArtifactCache_x3f_775_);
lean_inc(v_readmeFile_773_);
lean_inc(v_licenseFiles_772_);
lean_inc(v_license_771_);
lean_inc(v_homepage_770_);
lean_inc(v_keywords_769_);
lean_inc(v_description_768_);
lean_inc(v_versionTags_767_);
lean_inc(v_version_766_);
lean_inc(v_lintDriverArgs_765_);
lean_inc(v_lintDriver_764_);
lean_inc(v_testDriverArgs_763_);
lean_inc(v_testDriver_762_);
lean_inc(v_buildArchive_760_);
lean_inc(v_releaseRepo_759_);
lean_inc(v_irDir_758_);
lean_inc(v_binDir_757_);
lean_inc(v_nativeLibDir_756_);
lean_inc(v_leanLibDir_755_);
lean_inc(v_srcDir_754_);
lean_inc(v_moreGlobalServerArgs_753_);
lean_inc(v_extraDepTargets_751_);
lean_inc(v_manifestFile_750_);
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
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_toWorkspaceConfig_747_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_toLeanConfig_748_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_manifestFile_750_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_extraDepTargets_751_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_moreGlobalServerArgs_753_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_srcDir_754_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_val_745_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_leanLibDir_755_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_nativeLibDir_756_);
lean_ctor_set(v_reuseFailAlloc_784_, 9, v_binDir_757_);
lean_ctor_set(v_reuseFailAlloc_784_, 10, v_irDir_758_);
lean_ctor_set(v_reuseFailAlloc_784_, 11, v_releaseRepo_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 12, v_buildArchive_760_);
lean_ctor_set(v_reuseFailAlloc_784_, 13, v_testDriver_762_);
lean_ctor_set(v_reuseFailAlloc_784_, 14, v_testDriverArgs_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 15, v_lintDriver_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 16, v_lintDriverArgs_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 17, v_version_766_);
lean_ctor_set(v_reuseFailAlloc_784_, 18, v_versionTags_767_);
lean_ctor_set(v_reuseFailAlloc_784_, 19, v_description_768_);
lean_ctor_set(v_reuseFailAlloc_784_, 20, v_keywords_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 21, v_homepage_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 22, v_license_771_);
lean_ctor_set(v_reuseFailAlloc_784_, 23, v_licenseFiles_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 24, v_readmeFile_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 25, v_enableArtifactCache_x3f_775_);
lean_ctor_set(v_reuseFailAlloc_784_, 26, v_restoreAllArtifacts_x3f_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*27, v_bootstrap_749_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*27 + 1, v_precompileModules_752_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*27 + 2, v_preferReleaseBuild_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*27 + 3, v_reservoir_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*27 + 5, v_allowImportAll_778_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* v_f_787_, lean_object* v_cfg_788_){
_start:
{
lean_object* v_toWorkspaceConfig_789_; lean_object* v_toLeanConfig_790_; uint8_t v_bootstrap_791_; lean_object* v_manifestFile_792_; lean_object* v_extraDepTargets_793_; uint8_t v_precompileModules_794_; lean_object* v_moreGlobalServerArgs_795_; lean_object* v_srcDir_796_; lean_object* v_buildDir_797_; lean_object* v_leanLibDir_798_; lean_object* v_nativeLibDir_799_; lean_object* v_binDir_800_; lean_object* v_irDir_801_; lean_object* v_releaseRepo_802_; lean_object* v_buildArchive_803_; uint8_t v_preferReleaseBuild_804_; lean_object* v_testDriver_805_; lean_object* v_testDriverArgs_806_; lean_object* v_lintDriver_807_; lean_object* v_lintDriverArgs_808_; lean_object* v_version_809_; lean_object* v_versionTags_810_; lean_object* v_description_811_; lean_object* v_keywords_812_; lean_object* v_homepage_813_; lean_object* v_license_814_; lean_object* v_licenseFiles_815_; lean_object* v_readmeFile_816_; uint8_t v_reservoir_817_; lean_object* v_enableArtifactCache_x3f_818_; lean_object* v_restoreAllArtifacts_x3f_819_; uint8_t v_libPrefixOnWindows_820_; uint8_t v_allowImportAll_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_toWorkspaceConfig_789_ = lean_ctor_get(v_cfg_788_, 0);
v_toLeanConfig_790_ = lean_ctor_get(v_cfg_788_, 1);
v_bootstrap_791_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*27);
v_manifestFile_792_ = lean_ctor_get(v_cfg_788_, 2);
v_extraDepTargets_793_ = lean_ctor_get(v_cfg_788_, 3);
v_precompileModules_794_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_795_ = lean_ctor_get(v_cfg_788_, 4);
v_srcDir_796_ = lean_ctor_get(v_cfg_788_, 5);
v_buildDir_797_ = lean_ctor_get(v_cfg_788_, 6);
v_leanLibDir_798_ = lean_ctor_get(v_cfg_788_, 7);
v_nativeLibDir_799_ = lean_ctor_get(v_cfg_788_, 8);
v_binDir_800_ = lean_ctor_get(v_cfg_788_, 9);
v_irDir_801_ = lean_ctor_get(v_cfg_788_, 10);
v_releaseRepo_802_ = lean_ctor_get(v_cfg_788_, 11);
v_buildArchive_803_ = lean_ctor_get(v_cfg_788_, 12);
v_preferReleaseBuild_804_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*27 + 2);
v_testDriver_805_ = lean_ctor_get(v_cfg_788_, 13);
v_testDriverArgs_806_ = lean_ctor_get(v_cfg_788_, 14);
v_lintDriver_807_ = lean_ctor_get(v_cfg_788_, 15);
v_lintDriverArgs_808_ = lean_ctor_get(v_cfg_788_, 16);
v_version_809_ = lean_ctor_get(v_cfg_788_, 17);
v_versionTags_810_ = lean_ctor_get(v_cfg_788_, 18);
v_description_811_ = lean_ctor_get(v_cfg_788_, 19);
v_keywords_812_ = lean_ctor_get(v_cfg_788_, 20);
v_homepage_813_ = lean_ctor_get(v_cfg_788_, 21);
v_license_814_ = lean_ctor_get(v_cfg_788_, 22);
v_licenseFiles_815_ = lean_ctor_get(v_cfg_788_, 23);
v_readmeFile_816_ = lean_ctor_get(v_cfg_788_, 24);
v_reservoir_817_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_818_ = lean_ctor_get(v_cfg_788_, 25);
v_restoreAllArtifacts_x3f_819_ = lean_ctor_get(v_cfg_788_, 26);
v_libPrefixOnWindows_820_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*27 + 4);
v_allowImportAll_821_ = lean_ctor_get_uint8(v_cfg_788_, sizeof(void*)*27 + 5);
v_isSharedCheck_829_ = !lean_is_exclusive(v_cfg_788_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v_cfg_788_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_819_);
lean_inc(v_enableArtifactCache_x3f_818_);
lean_inc(v_readmeFile_816_);
lean_inc(v_licenseFiles_815_);
lean_inc(v_license_814_);
lean_inc(v_homepage_813_);
lean_inc(v_keywords_812_);
lean_inc(v_description_811_);
lean_inc(v_versionTags_810_);
lean_inc(v_version_809_);
lean_inc(v_lintDriverArgs_808_);
lean_inc(v_lintDriver_807_);
lean_inc(v_testDriverArgs_806_);
lean_inc(v_testDriver_805_);
lean_inc(v_buildArchive_803_);
lean_inc(v_releaseRepo_802_);
lean_inc(v_irDir_801_);
lean_inc(v_binDir_800_);
lean_inc(v_nativeLibDir_799_);
lean_inc(v_leanLibDir_798_);
lean_inc(v_buildDir_797_);
lean_inc(v_srcDir_796_);
lean_inc(v_moreGlobalServerArgs_795_);
lean_inc(v_extraDepTargets_793_);
lean_inc(v_manifestFile_792_);
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
v___x_825_ = lean_apply_1(v_f_787_, v_buildDir_797_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 6, v___x_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_toWorkspaceConfig_789_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_toLeanConfig_790_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_manifestFile_792_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_extraDepTargets_793_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_moreGlobalServerArgs_795_);
lean_ctor_set(v_reuseFailAlloc_828_, 5, v_srcDir_796_);
lean_ctor_set(v_reuseFailAlloc_828_, 6, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 7, v_leanLibDir_798_);
lean_ctor_set(v_reuseFailAlloc_828_, 8, v_nativeLibDir_799_);
lean_ctor_set(v_reuseFailAlloc_828_, 9, v_binDir_800_);
lean_ctor_set(v_reuseFailAlloc_828_, 10, v_irDir_801_);
lean_ctor_set(v_reuseFailAlloc_828_, 11, v_releaseRepo_802_);
lean_ctor_set(v_reuseFailAlloc_828_, 12, v_buildArchive_803_);
lean_ctor_set(v_reuseFailAlloc_828_, 13, v_testDriver_805_);
lean_ctor_set(v_reuseFailAlloc_828_, 14, v_testDriverArgs_806_);
lean_ctor_set(v_reuseFailAlloc_828_, 15, v_lintDriver_807_);
lean_ctor_set(v_reuseFailAlloc_828_, 16, v_lintDriverArgs_808_);
lean_ctor_set(v_reuseFailAlloc_828_, 17, v_version_809_);
lean_ctor_set(v_reuseFailAlloc_828_, 18, v_versionTags_810_);
lean_ctor_set(v_reuseFailAlloc_828_, 19, v_description_811_);
lean_ctor_set(v_reuseFailAlloc_828_, 20, v_keywords_812_);
lean_ctor_set(v_reuseFailAlloc_828_, 21, v_homepage_813_);
lean_ctor_set(v_reuseFailAlloc_828_, 22, v_license_814_);
lean_ctor_set(v_reuseFailAlloc_828_, 23, v_licenseFiles_815_);
lean_ctor_set(v_reuseFailAlloc_828_, 24, v_readmeFile_816_);
lean_ctor_set(v_reuseFailAlloc_828_, 25, v_enableArtifactCache_x3f_818_);
lean_ctor_set(v_reuseFailAlloc_828_, 26, v_restoreAllArtifacts_x3f_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*27, v_bootstrap_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*27 + 1, v_precompileModules_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*27 + 2, v_preferReleaseBuild_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*27 + 3, v_reservoir_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_828_, sizeof(void*)*27 + 5, v_allowImportAll_821_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lake_defaultBuildDir;
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_PackageConfig_buildDir___proj___lam__3(v_x_832_);
lean_dec_ref(v_x_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_843_, lean_object* v_n_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_846_, lean_object* v_n_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lake_PackageConfig_buildDir___proj(v_p_846_, v_n_847_);
lean_dec(v_n_847_);
lean_dec(v_p_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_849_, lean_object* v_n_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lake_PackageConfig_buildDir___proj(v_p_849_, v_n_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_852_, lean_object* v_n_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_852_, v_n_853_);
lean_dec(v_n_853_);
lean_dec(v_p_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* v_cfg_855_){
_start:
{
lean_object* v_leanLibDir_856_; 
v_leanLibDir_856_ = lean_ctor_get(v_cfg_855_, 7);
lean_inc_ref(v_leanLibDir_856_);
return v_leanLibDir_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* v_cfg_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lake_PackageConfig_leanLibDir___proj___lam__0(v_cfg_857_);
lean_dec_ref(v_cfg_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* v_val_859_, lean_object* v_cfg_860_){
_start:
{
lean_object* v_toWorkspaceConfig_861_; lean_object* v_toLeanConfig_862_; uint8_t v_bootstrap_863_; lean_object* v_manifestFile_864_; lean_object* v_extraDepTargets_865_; uint8_t v_precompileModules_866_; lean_object* v_moreGlobalServerArgs_867_; lean_object* v_srcDir_868_; lean_object* v_buildDir_869_; lean_object* v_nativeLibDir_870_; lean_object* v_binDir_871_; lean_object* v_irDir_872_; lean_object* v_releaseRepo_873_; lean_object* v_buildArchive_874_; uint8_t v_preferReleaseBuild_875_; lean_object* v_testDriver_876_; lean_object* v_testDriverArgs_877_; lean_object* v_lintDriver_878_; lean_object* v_lintDriverArgs_879_; lean_object* v_version_880_; lean_object* v_versionTags_881_; lean_object* v_description_882_; lean_object* v_keywords_883_; lean_object* v_homepage_884_; lean_object* v_license_885_; lean_object* v_licenseFiles_886_; lean_object* v_readmeFile_887_; uint8_t v_reservoir_888_; lean_object* v_enableArtifactCache_x3f_889_; lean_object* v_restoreAllArtifacts_x3f_890_; uint8_t v_libPrefixOnWindows_891_; uint8_t v_allowImportAll_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_toWorkspaceConfig_861_ = lean_ctor_get(v_cfg_860_, 0);
v_toLeanConfig_862_ = lean_ctor_get(v_cfg_860_, 1);
v_bootstrap_863_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*27);
v_manifestFile_864_ = lean_ctor_get(v_cfg_860_, 2);
v_extraDepTargets_865_ = lean_ctor_get(v_cfg_860_, 3);
v_precompileModules_866_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_867_ = lean_ctor_get(v_cfg_860_, 4);
v_srcDir_868_ = lean_ctor_get(v_cfg_860_, 5);
v_buildDir_869_ = lean_ctor_get(v_cfg_860_, 6);
v_nativeLibDir_870_ = lean_ctor_get(v_cfg_860_, 8);
v_binDir_871_ = lean_ctor_get(v_cfg_860_, 9);
v_irDir_872_ = lean_ctor_get(v_cfg_860_, 10);
v_releaseRepo_873_ = lean_ctor_get(v_cfg_860_, 11);
v_buildArchive_874_ = lean_ctor_get(v_cfg_860_, 12);
v_preferReleaseBuild_875_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*27 + 2);
v_testDriver_876_ = lean_ctor_get(v_cfg_860_, 13);
v_testDriverArgs_877_ = lean_ctor_get(v_cfg_860_, 14);
v_lintDriver_878_ = lean_ctor_get(v_cfg_860_, 15);
v_lintDriverArgs_879_ = lean_ctor_get(v_cfg_860_, 16);
v_version_880_ = lean_ctor_get(v_cfg_860_, 17);
v_versionTags_881_ = lean_ctor_get(v_cfg_860_, 18);
v_description_882_ = lean_ctor_get(v_cfg_860_, 19);
v_keywords_883_ = lean_ctor_get(v_cfg_860_, 20);
v_homepage_884_ = lean_ctor_get(v_cfg_860_, 21);
v_license_885_ = lean_ctor_get(v_cfg_860_, 22);
v_licenseFiles_886_ = lean_ctor_get(v_cfg_860_, 23);
v_readmeFile_887_ = lean_ctor_get(v_cfg_860_, 24);
v_reservoir_888_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_889_ = lean_ctor_get(v_cfg_860_, 25);
v_restoreAllArtifacts_x3f_890_ = lean_ctor_get(v_cfg_860_, 26);
v_libPrefixOnWindows_891_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*27 + 4);
v_allowImportAll_892_ = lean_ctor_get_uint8(v_cfg_860_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_890_);
lean_inc(v_enableArtifactCache_x3f_889_);
lean_inc(v_readmeFile_887_);
lean_inc(v_licenseFiles_886_);
lean_inc(v_license_885_);
lean_inc(v_homepage_884_);
lean_inc(v_keywords_883_);
lean_inc(v_description_882_);
lean_inc(v_versionTags_881_);
lean_inc(v_version_880_);
lean_inc(v_lintDriverArgs_879_);
lean_inc(v_lintDriver_878_);
lean_inc(v_testDriverArgs_877_);
lean_inc(v_testDriver_876_);
lean_inc(v_buildArchive_874_);
lean_inc(v_releaseRepo_873_);
lean_inc(v_irDir_872_);
lean_inc(v_binDir_871_);
lean_inc(v_nativeLibDir_870_);
lean_inc(v_buildDir_869_);
lean_inc(v_srcDir_868_);
lean_inc(v_moreGlobalServerArgs_867_);
lean_inc(v_extraDepTargets_865_);
lean_inc(v_manifestFile_864_);
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
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_toWorkspaceConfig_861_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_toLeanConfig_862_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_manifestFile_864_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_extraDepTargets_865_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_moreGlobalServerArgs_867_);
lean_ctor_set(v_reuseFailAlloc_898_, 5, v_srcDir_868_);
lean_ctor_set(v_reuseFailAlloc_898_, 6, v_buildDir_869_);
lean_ctor_set(v_reuseFailAlloc_898_, 7, v_val_859_);
lean_ctor_set(v_reuseFailAlloc_898_, 8, v_nativeLibDir_870_);
lean_ctor_set(v_reuseFailAlloc_898_, 9, v_binDir_871_);
lean_ctor_set(v_reuseFailAlloc_898_, 10, v_irDir_872_);
lean_ctor_set(v_reuseFailAlloc_898_, 11, v_releaseRepo_873_);
lean_ctor_set(v_reuseFailAlloc_898_, 12, v_buildArchive_874_);
lean_ctor_set(v_reuseFailAlloc_898_, 13, v_testDriver_876_);
lean_ctor_set(v_reuseFailAlloc_898_, 14, v_testDriverArgs_877_);
lean_ctor_set(v_reuseFailAlloc_898_, 15, v_lintDriver_878_);
lean_ctor_set(v_reuseFailAlloc_898_, 16, v_lintDriverArgs_879_);
lean_ctor_set(v_reuseFailAlloc_898_, 17, v_version_880_);
lean_ctor_set(v_reuseFailAlloc_898_, 18, v_versionTags_881_);
lean_ctor_set(v_reuseFailAlloc_898_, 19, v_description_882_);
lean_ctor_set(v_reuseFailAlloc_898_, 20, v_keywords_883_);
lean_ctor_set(v_reuseFailAlloc_898_, 21, v_homepage_884_);
lean_ctor_set(v_reuseFailAlloc_898_, 22, v_license_885_);
lean_ctor_set(v_reuseFailAlloc_898_, 23, v_licenseFiles_886_);
lean_ctor_set(v_reuseFailAlloc_898_, 24, v_readmeFile_887_);
lean_ctor_set(v_reuseFailAlloc_898_, 25, v_enableArtifactCache_x3f_889_);
lean_ctor_set(v_reuseFailAlloc_898_, 26, v_restoreAllArtifacts_x3f_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*27, v_bootstrap_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*27 + 1, v_precompileModules_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*27 + 2, v_preferReleaseBuild_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*27 + 3, v_reservoir_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_898_, sizeof(void*)*27 + 5, v_allowImportAll_892_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* v_f_901_, lean_object* v_cfg_902_){
_start:
{
lean_object* v_toWorkspaceConfig_903_; lean_object* v_toLeanConfig_904_; uint8_t v_bootstrap_905_; lean_object* v_manifestFile_906_; lean_object* v_extraDepTargets_907_; uint8_t v_precompileModules_908_; lean_object* v_moreGlobalServerArgs_909_; lean_object* v_srcDir_910_; lean_object* v_buildDir_911_; lean_object* v_leanLibDir_912_; lean_object* v_nativeLibDir_913_; lean_object* v_binDir_914_; lean_object* v_irDir_915_; lean_object* v_releaseRepo_916_; lean_object* v_buildArchive_917_; uint8_t v_preferReleaseBuild_918_; lean_object* v_testDriver_919_; lean_object* v_testDriverArgs_920_; lean_object* v_lintDriver_921_; lean_object* v_lintDriverArgs_922_; lean_object* v_version_923_; lean_object* v_versionTags_924_; lean_object* v_description_925_; lean_object* v_keywords_926_; lean_object* v_homepage_927_; lean_object* v_license_928_; lean_object* v_licenseFiles_929_; lean_object* v_readmeFile_930_; uint8_t v_reservoir_931_; lean_object* v_enableArtifactCache_x3f_932_; lean_object* v_restoreAllArtifacts_x3f_933_; uint8_t v_libPrefixOnWindows_934_; uint8_t v_allowImportAll_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_943_; 
v_toWorkspaceConfig_903_ = lean_ctor_get(v_cfg_902_, 0);
v_toLeanConfig_904_ = lean_ctor_get(v_cfg_902_, 1);
v_bootstrap_905_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*27);
v_manifestFile_906_ = lean_ctor_get(v_cfg_902_, 2);
v_extraDepTargets_907_ = lean_ctor_get(v_cfg_902_, 3);
v_precompileModules_908_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_909_ = lean_ctor_get(v_cfg_902_, 4);
v_srcDir_910_ = lean_ctor_get(v_cfg_902_, 5);
v_buildDir_911_ = lean_ctor_get(v_cfg_902_, 6);
v_leanLibDir_912_ = lean_ctor_get(v_cfg_902_, 7);
v_nativeLibDir_913_ = lean_ctor_get(v_cfg_902_, 8);
v_binDir_914_ = lean_ctor_get(v_cfg_902_, 9);
v_irDir_915_ = lean_ctor_get(v_cfg_902_, 10);
v_releaseRepo_916_ = lean_ctor_get(v_cfg_902_, 11);
v_buildArchive_917_ = lean_ctor_get(v_cfg_902_, 12);
v_preferReleaseBuild_918_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*27 + 2);
v_testDriver_919_ = lean_ctor_get(v_cfg_902_, 13);
v_testDriverArgs_920_ = lean_ctor_get(v_cfg_902_, 14);
v_lintDriver_921_ = lean_ctor_get(v_cfg_902_, 15);
v_lintDriverArgs_922_ = lean_ctor_get(v_cfg_902_, 16);
v_version_923_ = lean_ctor_get(v_cfg_902_, 17);
v_versionTags_924_ = lean_ctor_get(v_cfg_902_, 18);
v_description_925_ = lean_ctor_get(v_cfg_902_, 19);
v_keywords_926_ = lean_ctor_get(v_cfg_902_, 20);
v_homepage_927_ = lean_ctor_get(v_cfg_902_, 21);
v_license_928_ = lean_ctor_get(v_cfg_902_, 22);
v_licenseFiles_929_ = lean_ctor_get(v_cfg_902_, 23);
v_readmeFile_930_ = lean_ctor_get(v_cfg_902_, 24);
v_reservoir_931_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_932_ = lean_ctor_get(v_cfg_902_, 25);
v_restoreAllArtifacts_x3f_933_ = lean_ctor_get(v_cfg_902_, 26);
v_libPrefixOnWindows_934_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*27 + 4);
v_allowImportAll_935_ = lean_ctor_get_uint8(v_cfg_902_, sizeof(void*)*27 + 5);
v_isSharedCheck_943_ = !lean_is_exclusive(v_cfg_902_);
if (v_isSharedCheck_943_ == 0)
{
v___x_937_ = v_cfg_902_;
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_933_);
lean_inc(v_enableArtifactCache_x3f_932_);
lean_inc(v_readmeFile_930_);
lean_inc(v_licenseFiles_929_);
lean_inc(v_license_928_);
lean_inc(v_homepage_927_);
lean_inc(v_keywords_926_);
lean_inc(v_description_925_);
lean_inc(v_versionTags_924_);
lean_inc(v_version_923_);
lean_inc(v_lintDriverArgs_922_);
lean_inc(v_lintDriver_921_);
lean_inc(v_testDriverArgs_920_);
lean_inc(v_testDriver_919_);
lean_inc(v_buildArchive_917_);
lean_inc(v_releaseRepo_916_);
lean_inc(v_irDir_915_);
lean_inc(v_binDir_914_);
lean_inc(v_nativeLibDir_913_);
lean_inc(v_leanLibDir_912_);
lean_inc(v_buildDir_911_);
lean_inc(v_srcDir_910_);
lean_inc(v_moreGlobalServerArgs_909_);
lean_inc(v_extraDepTargets_907_);
lean_inc(v_manifestFile_906_);
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
v___x_939_ = lean_apply_1(v_f_901_, v_leanLibDir_912_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 7, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_toWorkspaceConfig_903_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_toLeanConfig_904_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_manifestFile_906_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_extraDepTargets_907_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_moreGlobalServerArgs_909_);
lean_ctor_set(v_reuseFailAlloc_942_, 5, v_srcDir_910_);
lean_ctor_set(v_reuseFailAlloc_942_, 6, v_buildDir_911_);
lean_ctor_set(v_reuseFailAlloc_942_, 7, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 8, v_nativeLibDir_913_);
lean_ctor_set(v_reuseFailAlloc_942_, 9, v_binDir_914_);
lean_ctor_set(v_reuseFailAlloc_942_, 10, v_irDir_915_);
lean_ctor_set(v_reuseFailAlloc_942_, 11, v_releaseRepo_916_);
lean_ctor_set(v_reuseFailAlloc_942_, 12, v_buildArchive_917_);
lean_ctor_set(v_reuseFailAlloc_942_, 13, v_testDriver_919_);
lean_ctor_set(v_reuseFailAlloc_942_, 14, v_testDriverArgs_920_);
lean_ctor_set(v_reuseFailAlloc_942_, 15, v_lintDriver_921_);
lean_ctor_set(v_reuseFailAlloc_942_, 16, v_lintDriverArgs_922_);
lean_ctor_set(v_reuseFailAlloc_942_, 17, v_version_923_);
lean_ctor_set(v_reuseFailAlloc_942_, 18, v_versionTags_924_);
lean_ctor_set(v_reuseFailAlloc_942_, 19, v_description_925_);
lean_ctor_set(v_reuseFailAlloc_942_, 20, v_keywords_926_);
lean_ctor_set(v_reuseFailAlloc_942_, 21, v_homepage_927_);
lean_ctor_set(v_reuseFailAlloc_942_, 22, v_license_928_);
lean_ctor_set(v_reuseFailAlloc_942_, 23, v_licenseFiles_929_);
lean_ctor_set(v_reuseFailAlloc_942_, 24, v_readmeFile_930_);
lean_ctor_set(v_reuseFailAlloc_942_, 25, v_enableArtifactCache_x3f_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 26, v_restoreAllArtifacts_x3f_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*27, v_bootstrap_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*27 + 1, v_precompileModules_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*27 + 2, v_preferReleaseBuild_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*27 + 3, v_reservoir_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*27 + 5, v_allowImportAll_935_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lake_defaultLeanLibDir;
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* v_x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lake_PackageConfig_leanLibDir___proj___lam__3(v_x_946_);
lean_dec_ref(v_x_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_957_, lean_object* v_n_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_960_, lean_object* v_n_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_960_, v_n_961_);
lean_dec(v_n_961_);
lean_dec(v_p_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_963_, lean_object* v_n_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_963_, v_n_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_966_, lean_object* v_n_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_966_, v_n_967_);
lean_dec(v_n_967_);
lean_dec(v_p_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* v_cfg_969_){
_start:
{
lean_object* v_nativeLibDir_970_; 
v_nativeLibDir_970_ = lean_ctor_get(v_cfg_969_, 8);
lean_inc_ref(v_nativeLibDir_970_);
return v_nativeLibDir_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* v_cfg_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(v_cfg_971_);
lean_dec_ref(v_cfg_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* v_val_973_, lean_object* v_cfg_974_){
_start:
{
lean_object* v_toWorkspaceConfig_975_; lean_object* v_toLeanConfig_976_; uint8_t v_bootstrap_977_; lean_object* v_manifestFile_978_; lean_object* v_extraDepTargets_979_; uint8_t v_precompileModules_980_; lean_object* v_moreGlobalServerArgs_981_; lean_object* v_srcDir_982_; lean_object* v_buildDir_983_; lean_object* v_leanLibDir_984_; lean_object* v_binDir_985_; lean_object* v_irDir_986_; lean_object* v_releaseRepo_987_; lean_object* v_buildArchive_988_; uint8_t v_preferReleaseBuild_989_; lean_object* v_testDriver_990_; lean_object* v_testDriverArgs_991_; lean_object* v_lintDriver_992_; lean_object* v_lintDriverArgs_993_; lean_object* v_version_994_; lean_object* v_versionTags_995_; lean_object* v_description_996_; lean_object* v_keywords_997_; lean_object* v_homepage_998_; lean_object* v_license_999_; lean_object* v_licenseFiles_1000_; lean_object* v_readmeFile_1001_; uint8_t v_reservoir_1002_; lean_object* v_enableArtifactCache_x3f_1003_; lean_object* v_restoreAllArtifacts_x3f_1004_; uint8_t v_libPrefixOnWindows_1005_; uint8_t v_allowImportAll_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_toWorkspaceConfig_975_ = lean_ctor_get(v_cfg_974_, 0);
v_toLeanConfig_976_ = lean_ctor_get(v_cfg_974_, 1);
v_bootstrap_977_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*27);
v_manifestFile_978_ = lean_ctor_get(v_cfg_974_, 2);
v_extraDepTargets_979_ = lean_ctor_get(v_cfg_974_, 3);
v_precompileModules_980_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_981_ = lean_ctor_get(v_cfg_974_, 4);
v_srcDir_982_ = lean_ctor_get(v_cfg_974_, 5);
v_buildDir_983_ = lean_ctor_get(v_cfg_974_, 6);
v_leanLibDir_984_ = lean_ctor_get(v_cfg_974_, 7);
v_binDir_985_ = lean_ctor_get(v_cfg_974_, 9);
v_irDir_986_ = lean_ctor_get(v_cfg_974_, 10);
v_releaseRepo_987_ = lean_ctor_get(v_cfg_974_, 11);
v_buildArchive_988_ = lean_ctor_get(v_cfg_974_, 12);
v_preferReleaseBuild_989_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*27 + 2);
v_testDriver_990_ = lean_ctor_get(v_cfg_974_, 13);
v_testDriverArgs_991_ = lean_ctor_get(v_cfg_974_, 14);
v_lintDriver_992_ = lean_ctor_get(v_cfg_974_, 15);
v_lintDriverArgs_993_ = lean_ctor_get(v_cfg_974_, 16);
v_version_994_ = lean_ctor_get(v_cfg_974_, 17);
v_versionTags_995_ = lean_ctor_get(v_cfg_974_, 18);
v_description_996_ = lean_ctor_get(v_cfg_974_, 19);
v_keywords_997_ = lean_ctor_get(v_cfg_974_, 20);
v_homepage_998_ = lean_ctor_get(v_cfg_974_, 21);
v_license_999_ = lean_ctor_get(v_cfg_974_, 22);
v_licenseFiles_1000_ = lean_ctor_get(v_cfg_974_, 23);
v_readmeFile_1001_ = lean_ctor_get(v_cfg_974_, 24);
v_reservoir_1002_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1003_ = lean_ctor_get(v_cfg_974_, 25);
v_restoreAllArtifacts_x3f_1004_ = lean_ctor_get(v_cfg_974_, 26);
v_libPrefixOnWindows_1005_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*27 + 4);
v_allowImportAll_1006_ = lean_ctor_get_uint8(v_cfg_974_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_1004_);
lean_inc(v_enableArtifactCache_x3f_1003_);
lean_inc(v_readmeFile_1001_);
lean_inc(v_licenseFiles_1000_);
lean_inc(v_license_999_);
lean_inc(v_homepage_998_);
lean_inc(v_keywords_997_);
lean_inc(v_description_996_);
lean_inc(v_versionTags_995_);
lean_inc(v_version_994_);
lean_inc(v_lintDriverArgs_993_);
lean_inc(v_lintDriver_992_);
lean_inc(v_testDriverArgs_991_);
lean_inc(v_testDriver_990_);
lean_inc(v_buildArchive_988_);
lean_inc(v_releaseRepo_987_);
lean_inc(v_irDir_986_);
lean_inc(v_binDir_985_);
lean_inc(v_leanLibDir_984_);
lean_inc(v_buildDir_983_);
lean_inc(v_srcDir_982_);
lean_inc(v_moreGlobalServerArgs_981_);
lean_inc(v_extraDepTargets_979_);
lean_inc(v_manifestFile_978_);
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
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_toWorkspaceConfig_975_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_toLeanConfig_976_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_manifestFile_978_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_extraDepTargets_979_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_moreGlobalServerArgs_981_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_srcDir_982_);
lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_buildDir_983_);
lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_leanLibDir_984_);
lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_val_973_);
lean_ctor_set(v_reuseFailAlloc_1012_, 9, v_binDir_985_);
lean_ctor_set(v_reuseFailAlloc_1012_, 10, v_irDir_986_);
lean_ctor_set(v_reuseFailAlloc_1012_, 11, v_releaseRepo_987_);
lean_ctor_set(v_reuseFailAlloc_1012_, 12, v_buildArchive_988_);
lean_ctor_set(v_reuseFailAlloc_1012_, 13, v_testDriver_990_);
lean_ctor_set(v_reuseFailAlloc_1012_, 14, v_testDriverArgs_991_);
lean_ctor_set(v_reuseFailAlloc_1012_, 15, v_lintDriver_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 16, v_lintDriverArgs_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 17, v_version_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 18, v_versionTags_995_);
lean_ctor_set(v_reuseFailAlloc_1012_, 19, v_description_996_);
lean_ctor_set(v_reuseFailAlloc_1012_, 20, v_keywords_997_);
lean_ctor_set(v_reuseFailAlloc_1012_, 21, v_homepage_998_);
lean_ctor_set(v_reuseFailAlloc_1012_, 22, v_license_999_);
lean_ctor_set(v_reuseFailAlloc_1012_, 23, v_licenseFiles_1000_);
lean_ctor_set(v_reuseFailAlloc_1012_, 24, v_readmeFile_1001_);
lean_ctor_set(v_reuseFailAlloc_1012_, 25, v_enableArtifactCache_x3f_1003_);
lean_ctor_set(v_reuseFailAlloc_1012_, 26, v_restoreAllArtifacts_x3f_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*27, v_bootstrap_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*27 + 1, v_precompileModules_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*27 + 2, v_preferReleaseBuild_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*27 + 3, v_reservoir_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*27 + 5, v_allowImportAll_1006_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* v_f_1015_, lean_object* v_cfg_1016_){
_start:
{
lean_object* v_toWorkspaceConfig_1017_; lean_object* v_toLeanConfig_1018_; uint8_t v_bootstrap_1019_; lean_object* v_manifestFile_1020_; lean_object* v_extraDepTargets_1021_; uint8_t v_precompileModules_1022_; lean_object* v_moreGlobalServerArgs_1023_; lean_object* v_srcDir_1024_; lean_object* v_buildDir_1025_; lean_object* v_leanLibDir_1026_; lean_object* v_nativeLibDir_1027_; lean_object* v_binDir_1028_; lean_object* v_irDir_1029_; lean_object* v_releaseRepo_1030_; lean_object* v_buildArchive_1031_; uint8_t v_preferReleaseBuild_1032_; lean_object* v_testDriver_1033_; lean_object* v_testDriverArgs_1034_; lean_object* v_lintDriver_1035_; lean_object* v_lintDriverArgs_1036_; lean_object* v_version_1037_; lean_object* v_versionTags_1038_; lean_object* v_description_1039_; lean_object* v_keywords_1040_; lean_object* v_homepage_1041_; lean_object* v_license_1042_; lean_object* v_licenseFiles_1043_; lean_object* v_readmeFile_1044_; uint8_t v_reservoir_1045_; lean_object* v_enableArtifactCache_x3f_1046_; lean_object* v_restoreAllArtifacts_x3f_1047_; uint8_t v_libPrefixOnWindows_1048_; uint8_t v_allowImportAll_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_toWorkspaceConfig_1017_ = lean_ctor_get(v_cfg_1016_, 0);
v_toLeanConfig_1018_ = lean_ctor_get(v_cfg_1016_, 1);
v_bootstrap_1019_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*27);
v_manifestFile_1020_ = lean_ctor_get(v_cfg_1016_, 2);
v_extraDepTargets_1021_ = lean_ctor_get(v_cfg_1016_, 3);
v_precompileModules_1022_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1023_ = lean_ctor_get(v_cfg_1016_, 4);
v_srcDir_1024_ = lean_ctor_get(v_cfg_1016_, 5);
v_buildDir_1025_ = lean_ctor_get(v_cfg_1016_, 6);
v_leanLibDir_1026_ = lean_ctor_get(v_cfg_1016_, 7);
v_nativeLibDir_1027_ = lean_ctor_get(v_cfg_1016_, 8);
v_binDir_1028_ = lean_ctor_get(v_cfg_1016_, 9);
v_irDir_1029_ = lean_ctor_get(v_cfg_1016_, 10);
v_releaseRepo_1030_ = lean_ctor_get(v_cfg_1016_, 11);
v_buildArchive_1031_ = lean_ctor_get(v_cfg_1016_, 12);
v_preferReleaseBuild_1032_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*27 + 2);
v_testDriver_1033_ = lean_ctor_get(v_cfg_1016_, 13);
v_testDriverArgs_1034_ = lean_ctor_get(v_cfg_1016_, 14);
v_lintDriver_1035_ = lean_ctor_get(v_cfg_1016_, 15);
v_lintDriverArgs_1036_ = lean_ctor_get(v_cfg_1016_, 16);
v_version_1037_ = lean_ctor_get(v_cfg_1016_, 17);
v_versionTags_1038_ = lean_ctor_get(v_cfg_1016_, 18);
v_description_1039_ = lean_ctor_get(v_cfg_1016_, 19);
v_keywords_1040_ = lean_ctor_get(v_cfg_1016_, 20);
v_homepage_1041_ = lean_ctor_get(v_cfg_1016_, 21);
v_license_1042_ = lean_ctor_get(v_cfg_1016_, 22);
v_licenseFiles_1043_ = lean_ctor_get(v_cfg_1016_, 23);
v_readmeFile_1044_ = lean_ctor_get(v_cfg_1016_, 24);
v_reservoir_1045_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1046_ = lean_ctor_get(v_cfg_1016_, 25);
v_restoreAllArtifacts_x3f_1047_ = lean_ctor_get(v_cfg_1016_, 26);
v_libPrefixOnWindows_1048_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*27 + 4);
v_allowImportAll_1049_ = lean_ctor_get_uint8(v_cfg_1016_, sizeof(void*)*27 + 5);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_cfg_1016_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1051_ = v_cfg_1016_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1047_);
lean_inc(v_enableArtifactCache_x3f_1046_);
lean_inc(v_readmeFile_1044_);
lean_inc(v_licenseFiles_1043_);
lean_inc(v_license_1042_);
lean_inc(v_homepage_1041_);
lean_inc(v_keywords_1040_);
lean_inc(v_description_1039_);
lean_inc(v_versionTags_1038_);
lean_inc(v_version_1037_);
lean_inc(v_lintDriverArgs_1036_);
lean_inc(v_lintDriver_1035_);
lean_inc(v_testDriverArgs_1034_);
lean_inc(v_testDriver_1033_);
lean_inc(v_buildArchive_1031_);
lean_inc(v_releaseRepo_1030_);
lean_inc(v_irDir_1029_);
lean_inc(v_binDir_1028_);
lean_inc(v_nativeLibDir_1027_);
lean_inc(v_leanLibDir_1026_);
lean_inc(v_buildDir_1025_);
lean_inc(v_srcDir_1024_);
lean_inc(v_moreGlobalServerArgs_1023_);
lean_inc(v_extraDepTargets_1021_);
lean_inc(v_manifestFile_1020_);
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
v___x_1053_ = lean_apply_1(v_f_1015_, v_nativeLibDir_1027_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 8, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_toWorkspaceConfig_1017_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_toLeanConfig_1018_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_manifestFile_1020_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_extraDepTargets_1021_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v_moreGlobalServerArgs_1023_);
lean_ctor_set(v_reuseFailAlloc_1056_, 5, v_srcDir_1024_);
lean_ctor_set(v_reuseFailAlloc_1056_, 6, v_buildDir_1025_);
lean_ctor_set(v_reuseFailAlloc_1056_, 7, v_leanLibDir_1026_);
lean_ctor_set(v_reuseFailAlloc_1056_, 8, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 9, v_binDir_1028_);
lean_ctor_set(v_reuseFailAlloc_1056_, 10, v_irDir_1029_);
lean_ctor_set(v_reuseFailAlloc_1056_, 11, v_releaseRepo_1030_);
lean_ctor_set(v_reuseFailAlloc_1056_, 12, v_buildArchive_1031_);
lean_ctor_set(v_reuseFailAlloc_1056_, 13, v_testDriver_1033_);
lean_ctor_set(v_reuseFailAlloc_1056_, 14, v_testDriverArgs_1034_);
lean_ctor_set(v_reuseFailAlloc_1056_, 15, v_lintDriver_1035_);
lean_ctor_set(v_reuseFailAlloc_1056_, 16, v_lintDriverArgs_1036_);
lean_ctor_set(v_reuseFailAlloc_1056_, 17, v_version_1037_);
lean_ctor_set(v_reuseFailAlloc_1056_, 18, v_versionTags_1038_);
lean_ctor_set(v_reuseFailAlloc_1056_, 19, v_description_1039_);
lean_ctor_set(v_reuseFailAlloc_1056_, 20, v_keywords_1040_);
lean_ctor_set(v_reuseFailAlloc_1056_, 21, v_homepage_1041_);
lean_ctor_set(v_reuseFailAlloc_1056_, 22, v_license_1042_);
lean_ctor_set(v_reuseFailAlloc_1056_, 23, v_licenseFiles_1043_);
lean_ctor_set(v_reuseFailAlloc_1056_, 24, v_readmeFile_1044_);
lean_ctor_set(v_reuseFailAlloc_1056_, 25, v_enableArtifactCache_x3f_1046_);
lean_ctor_set(v_reuseFailAlloc_1056_, 26, v_restoreAllArtifacts_x3f_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*27, v_bootstrap_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*27 + 1, v_precompileModules_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*27 + 3, v_reservoir_1045_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*27 + 5, v_allowImportAll_1049_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lake_defaultNativeLibDir;
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* v_x_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(v_x_1060_);
lean_dec_ref(v_x_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_1071_, lean_object* v_n_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_1074_, lean_object* v_n_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1074_, v_n_1075_);
lean_dec(v_n_1075_);
lean_dec(v_p_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_1077_, lean_object* v_n_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1077_, v_n_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_1080_, lean_object* v_n_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_1080_, v_n_1081_);
lean_dec(v_n_1081_);
lean_dec(v_p_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* v_cfg_1083_){
_start:
{
lean_object* v_binDir_1084_; 
v_binDir_1084_ = lean_ctor_get(v_cfg_1083_, 9);
lean_inc_ref(v_binDir_1084_);
return v_binDir_1084_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* v_cfg_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lake_PackageConfig_binDir___proj___lam__0(v_cfg_1085_);
lean_dec_ref(v_cfg_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* v_val_1087_, lean_object* v_cfg_1088_){
_start:
{
lean_object* v_toWorkspaceConfig_1089_; lean_object* v_toLeanConfig_1090_; uint8_t v_bootstrap_1091_; lean_object* v_manifestFile_1092_; lean_object* v_extraDepTargets_1093_; uint8_t v_precompileModules_1094_; lean_object* v_moreGlobalServerArgs_1095_; lean_object* v_srcDir_1096_; lean_object* v_buildDir_1097_; lean_object* v_leanLibDir_1098_; lean_object* v_nativeLibDir_1099_; lean_object* v_irDir_1100_; lean_object* v_releaseRepo_1101_; lean_object* v_buildArchive_1102_; uint8_t v_preferReleaseBuild_1103_; lean_object* v_testDriver_1104_; lean_object* v_testDriverArgs_1105_; lean_object* v_lintDriver_1106_; lean_object* v_lintDriverArgs_1107_; lean_object* v_version_1108_; lean_object* v_versionTags_1109_; lean_object* v_description_1110_; lean_object* v_keywords_1111_; lean_object* v_homepage_1112_; lean_object* v_license_1113_; lean_object* v_licenseFiles_1114_; lean_object* v_readmeFile_1115_; uint8_t v_reservoir_1116_; lean_object* v_enableArtifactCache_x3f_1117_; lean_object* v_restoreAllArtifacts_x3f_1118_; uint8_t v_libPrefixOnWindows_1119_; uint8_t v_allowImportAll_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_toWorkspaceConfig_1089_ = lean_ctor_get(v_cfg_1088_, 0);
v_toLeanConfig_1090_ = lean_ctor_get(v_cfg_1088_, 1);
v_bootstrap_1091_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*27);
v_manifestFile_1092_ = lean_ctor_get(v_cfg_1088_, 2);
v_extraDepTargets_1093_ = lean_ctor_get(v_cfg_1088_, 3);
v_precompileModules_1094_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1095_ = lean_ctor_get(v_cfg_1088_, 4);
v_srcDir_1096_ = lean_ctor_get(v_cfg_1088_, 5);
v_buildDir_1097_ = lean_ctor_get(v_cfg_1088_, 6);
v_leanLibDir_1098_ = lean_ctor_get(v_cfg_1088_, 7);
v_nativeLibDir_1099_ = lean_ctor_get(v_cfg_1088_, 8);
v_irDir_1100_ = lean_ctor_get(v_cfg_1088_, 10);
v_releaseRepo_1101_ = lean_ctor_get(v_cfg_1088_, 11);
v_buildArchive_1102_ = lean_ctor_get(v_cfg_1088_, 12);
v_preferReleaseBuild_1103_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*27 + 2);
v_testDriver_1104_ = lean_ctor_get(v_cfg_1088_, 13);
v_testDriverArgs_1105_ = lean_ctor_get(v_cfg_1088_, 14);
v_lintDriver_1106_ = lean_ctor_get(v_cfg_1088_, 15);
v_lintDriverArgs_1107_ = lean_ctor_get(v_cfg_1088_, 16);
v_version_1108_ = lean_ctor_get(v_cfg_1088_, 17);
v_versionTags_1109_ = lean_ctor_get(v_cfg_1088_, 18);
v_description_1110_ = lean_ctor_get(v_cfg_1088_, 19);
v_keywords_1111_ = lean_ctor_get(v_cfg_1088_, 20);
v_homepage_1112_ = lean_ctor_get(v_cfg_1088_, 21);
v_license_1113_ = lean_ctor_get(v_cfg_1088_, 22);
v_licenseFiles_1114_ = lean_ctor_get(v_cfg_1088_, 23);
v_readmeFile_1115_ = lean_ctor_get(v_cfg_1088_, 24);
v_reservoir_1116_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1117_ = lean_ctor_get(v_cfg_1088_, 25);
v_restoreAllArtifacts_x3f_1118_ = lean_ctor_get(v_cfg_1088_, 26);
v_libPrefixOnWindows_1119_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*27 + 4);
v_allowImportAll_1120_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_1118_);
lean_inc(v_enableArtifactCache_x3f_1117_);
lean_inc(v_readmeFile_1115_);
lean_inc(v_licenseFiles_1114_);
lean_inc(v_license_1113_);
lean_inc(v_homepage_1112_);
lean_inc(v_keywords_1111_);
lean_inc(v_description_1110_);
lean_inc(v_versionTags_1109_);
lean_inc(v_version_1108_);
lean_inc(v_lintDriverArgs_1107_);
lean_inc(v_lintDriver_1106_);
lean_inc(v_testDriverArgs_1105_);
lean_inc(v_testDriver_1104_);
lean_inc(v_buildArchive_1102_);
lean_inc(v_releaseRepo_1101_);
lean_inc(v_irDir_1100_);
lean_inc(v_nativeLibDir_1099_);
lean_inc(v_leanLibDir_1098_);
lean_inc(v_buildDir_1097_);
lean_inc(v_srcDir_1096_);
lean_inc(v_moreGlobalServerArgs_1095_);
lean_inc(v_extraDepTargets_1093_);
lean_inc(v_manifestFile_1092_);
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
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_toWorkspaceConfig_1089_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_toLeanConfig_1090_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_manifestFile_1092_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_extraDepTargets_1093_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_moreGlobalServerArgs_1095_);
lean_ctor_set(v_reuseFailAlloc_1126_, 5, v_srcDir_1096_);
lean_ctor_set(v_reuseFailAlloc_1126_, 6, v_buildDir_1097_);
lean_ctor_set(v_reuseFailAlloc_1126_, 7, v_leanLibDir_1098_);
lean_ctor_set(v_reuseFailAlloc_1126_, 8, v_nativeLibDir_1099_);
lean_ctor_set(v_reuseFailAlloc_1126_, 9, v_val_1087_);
lean_ctor_set(v_reuseFailAlloc_1126_, 10, v_irDir_1100_);
lean_ctor_set(v_reuseFailAlloc_1126_, 11, v_releaseRepo_1101_);
lean_ctor_set(v_reuseFailAlloc_1126_, 12, v_buildArchive_1102_);
lean_ctor_set(v_reuseFailAlloc_1126_, 13, v_testDriver_1104_);
lean_ctor_set(v_reuseFailAlloc_1126_, 14, v_testDriverArgs_1105_);
lean_ctor_set(v_reuseFailAlloc_1126_, 15, v_lintDriver_1106_);
lean_ctor_set(v_reuseFailAlloc_1126_, 16, v_lintDriverArgs_1107_);
lean_ctor_set(v_reuseFailAlloc_1126_, 17, v_version_1108_);
lean_ctor_set(v_reuseFailAlloc_1126_, 18, v_versionTags_1109_);
lean_ctor_set(v_reuseFailAlloc_1126_, 19, v_description_1110_);
lean_ctor_set(v_reuseFailAlloc_1126_, 20, v_keywords_1111_);
lean_ctor_set(v_reuseFailAlloc_1126_, 21, v_homepage_1112_);
lean_ctor_set(v_reuseFailAlloc_1126_, 22, v_license_1113_);
lean_ctor_set(v_reuseFailAlloc_1126_, 23, v_licenseFiles_1114_);
lean_ctor_set(v_reuseFailAlloc_1126_, 24, v_readmeFile_1115_);
lean_ctor_set(v_reuseFailAlloc_1126_, 25, v_enableArtifactCache_x3f_1117_);
lean_ctor_set(v_reuseFailAlloc_1126_, 26, v_restoreAllArtifacts_x3f_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*27, v_bootstrap_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*27 + 1, v_precompileModules_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*27 + 3, v_reservoir_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*27 + 5, v_allowImportAll_1120_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* v_f_1129_, lean_object* v_cfg_1130_){
_start:
{
lean_object* v_toWorkspaceConfig_1131_; lean_object* v_toLeanConfig_1132_; uint8_t v_bootstrap_1133_; lean_object* v_manifestFile_1134_; lean_object* v_extraDepTargets_1135_; uint8_t v_precompileModules_1136_; lean_object* v_moreGlobalServerArgs_1137_; lean_object* v_srcDir_1138_; lean_object* v_buildDir_1139_; lean_object* v_leanLibDir_1140_; lean_object* v_nativeLibDir_1141_; lean_object* v_binDir_1142_; lean_object* v_irDir_1143_; lean_object* v_releaseRepo_1144_; lean_object* v_buildArchive_1145_; uint8_t v_preferReleaseBuild_1146_; lean_object* v_testDriver_1147_; lean_object* v_testDriverArgs_1148_; lean_object* v_lintDriver_1149_; lean_object* v_lintDriverArgs_1150_; lean_object* v_version_1151_; lean_object* v_versionTags_1152_; lean_object* v_description_1153_; lean_object* v_keywords_1154_; lean_object* v_homepage_1155_; lean_object* v_license_1156_; lean_object* v_licenseFiles_1157_; lean_object* v_readmeFile_1158_; uint8_t v_reservoir_1159_; lean_object* v_enableArtifactCache_x3f_1160_; lean_object* v_restoreAllArtifacts_x3f_1161_; uint8_t v_libPrefixOnWindows_1162_; uint8_t v_allowImportAll_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_toWorkspaceConfig_1131_ = lean_ctor_get(v_cfg_1130_, 0);
v_toLeanConfig_1132_ = lean_ctor_get(v_cfg_1130_, 1);
v_bootstrap_1133_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*27);
v_manifestFile_1134_ = lean_ctor_get(v_cfg_1130_, 2);
v_extraDepTargets_1135_ = lean_ctor_get(v_cfg_1130_, 3);
v_precompileModules_1136_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1137_ = lean_ctor_get(v_cfg_1130_, 4);
v_srcDir_1138_ = lean_ctor_get(v_cfg_1130_, 5);
v_buildDir_1139_ = lean_ctor_get(v_cfg_1130_, 6);
v_leanLibDir_1140_ = lean_ctor_get(v_cfg_1130_, 7);
v_nativeLibDir_1141_ = lean_ctor_get(v_cfg_1130_, 8);
v_binDir_1142_ = lean_ctor_get(v_cfg_1130_, 9);
v_irDir_1143_ = lean_ctor_get(v_cfg_1130_, 10);
v_releaseRepo_1144_ = lean_ctor_get(v_cfg_1130_, 11);
v_buildArchive_1145_ = lean_ctor_get(v_cfg_1130_, 12);
v_preferReleaseBuild_1146_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*27 + 2);
v_testDriver_1147_ = lean_ctor_get(v_cfg_1130_, 13);
v_testDriverArgs_1148_ = lean_ctor_get(v_cfg_1130_, 14);
v_lintDriver_1149_ = lean_ctor_get(v_cfg_1130_, 15);
v_lintDriverArgs_1150_ = lean_ctor_get(v_cfg_1130_, 16);
v_version_1151_ = lean_ctor_get(v_cfg_1130_, 17);
v_versionTags_1152_ = lean_ctor_get(v_cfg_1130_, 18);
v_description_1153_ = lean_ctor_get(v_cfg_1130_, 19);
v_keywords_1154_ = lean_ctor_get(v_cfg_1130_, 20);
v_homepage_1155_ = lean_ctor_get(v_cfg_1130_, 21);
v_license_1156_ = lean_ctor_get(v_cfg_1130_, 22);
v_licenseFiles_1157_ = lean_ctor_get(v_cfg_1130_, 23);
v_readmeFile_1158_ = lean_ctor_get(v_cfg_1130_, 24);
v_reservoir_1159_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1160_ = lean_ctor_get(v_cfg_1130_, 25);
v_restoreAllArtifacts_x3f_1161_ = lean_ctor_get(v_cfg_1130_, 26);
v_libPrefixOnWindows_1162_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*27 + 4);
v_allowImportAll_1163_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*27 + 5);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_cfg_1130_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v_cfg_1130_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1161_);
lean_inc(v_enableArtifactCache_x3f_1160_);
lean_inc(v_readmeFile_1158_);
lean_inc(v_licenseFiles_1157_);
lean_inc(v_license_1156_);
lean_inc(v_homepage_1155_);
lean_inc(v_keywords_1154_);
lean_inc(v_description_1153_);
lean_inc(v_versionTags_1152_);
lean_inc(v_version_1151_);
lean_inc(v_lintDriverArgs_1150_);
lean_inc(v_lintDriver_1149_);
lean_inc(v_testDriverArgs_1148_);
lean_inc(v_testDriver_1147_);
lean_inc(v_buildArchive_1145_);
lean_inc(v_releaseRepo_1144_);
lean_inc(v_irDir_1143_);
lean_inc(v_binDir_1142_);
lean_inc(v_nativeLibDir_1141_);
lean_inc(v_leanLibDir_1140_);
lean_inc(v_buildDir_1139_);
lean_inc(v_srcDir_1138_);
lean_inc(v_moreGlobalServerArgs_1137_);
lean_inc(v_extraDepTargets_1135_);
lean_inc(v_manifestFile_1134_);
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
v___x_1167_ = lean_apply_1(v_f_1129_, v_binDir_1142_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 9, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_toWorkspaceConfig_1131_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_toLeanConfig_1132_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_manifestFile_1134_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_extraDepTargets_1135_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_moreGlobalServerArgs_1137_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_srcDir_1138_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_buildDir_1139_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_leanLibDir_1140_);
lean_ctor_set(v_reuseFailAlloc_1170_, 8, v_nativeLibDir_1141_);
lean_ctor_set(v_reuseFailAlloc_1170_, 9, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 10, v_irDir_1143_);
lean_ctor_set(v_reuseFailAlloc_1170_, 11, v_releaseRepo_1144_);
lean_ctor_set(v_reuseFailAlloc_1170_, 12, v_buildArchive_1145_);
lean_ctor_set(v_reuseFailAlloc_1170_, 13, v_testDriver_1147_);
lean_ctor_set(v_reuseFailAlloc_1170_, 14, v_testDriverArgs_1148_);
lean_ctor_set(v_reuseFailAlloc_1170_, 15, v_lintDriver_1149_);
lean_ctor_set(v_reuseFailAlloc_1170_, 16, v_lintDriverArgs_1150_);
lean_ctor_set(v_reuseFailAlloc_1170_, 17, v_version_1151_);
lean_ctor_set(v_reuseFailAlloc_1170_, 18, v_versionTags_1152_);
lean_ctor_set(v_reuseFailAlloc_1170_, 19, v_description_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 20, v_keywords_1154_);
lean_ctor_set(v_reuseFailAlloc_1170_, 21, v_homepage_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 22, v_license_1156_);
lean_ctor_set(v_reuseFailAlloc_1170_, 23, v_licenseFiles_1157_);
lean_ctor_set(v_reuseFailAlloc_1170_, 24, v_readmeFile_1158_);
lean_ctor_set(v_reuseFailAlloc_1170_, 25, v_enableArtifactCache_x3f_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 26, v_restoreAllArtifacts_x3f_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*27, v_bootstrap_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*27 + 1, v_precompileModules_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*27 + 3, v_reservoir_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*27 + 5, v_allowImportAll_1163_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* v_x_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lake_defaultBinDir;
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lake_PackageConfig_binDir___proj___lam__3(v_x_1174_);
lean_dec_ref(v_x_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1185_, lean_object* v_n_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1188_, lean_object* v_n_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_PackageConfig_binDir___proj(v_p_1188_, v_n_1189_);
lean_dec(v_n_1189_);
lean_dec(v_p_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1191_, lean_object* v_n_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lake_PackageConfig_binDir___proj(v_p_1191_, v_n_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1194_, lean_object* v_n_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1194_, v_n_1195_);
lean_dec(v_n_1195_);
lean_dec(v_p_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* v_cfg_1197_){
_start:
{
lean_object* v_irDir_1198_; 
v_irDir_1198_ = lean_ctor_get(v_cfg_1197_, 10);
lean_inc_ref(v_irDir_1198_);
return v_irDir_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* v_cfg_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lake_PackageConfig_irDir___proj___lam__0(v_cfg_1199_);
lean_dec_ref(v_cfg_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* v_val_1201_, lean_object* v_cfg_1202_){
_start:
{
lean_object* v_toWorkspaceConfig_1203_; lean_object* v_toLeanConfig_1204_; uint8_t v_bootstrap_1205_; lean_object* v_manifestFile_1206_; lean_object* v_extraDepTargets_1207_; uint8_t v_precompileModules_1208_; lean_object* v_moreGlobalServerArgs_1209_; lean_object* v_srcDir_1210_; lean_object* v_buildDir_1211_; lean_object* v_leanLibDir_1212_; lean_object* v_nativeLibDir_1213_; lean_object* v_binDir_1214_; lean_object* v_releaseRepo_1215_; lean_object* v_buildArchive_1216_; uint8_t v_preferReleaseBuild_1217_; lean_object* v_testDriver_1218_; lean_object* v_testDriverArgs_1219_; lean_object* v_lintDriver_1220_; lean_object* v_lintDriverArgs_1221_; lean_object* v_version_1222_; lean_object* v_versionTags_1223_; lean_object* v_description_1224_; lean_object* v_keywords_1225_; lean_object* v_homepage_1226_; lean_object* v_license_1227_; lean_object* v_licenseFiles_1228_; lean_object* v_readmeFile_1229_; uint8_t v_reservoir_1230_; lean_object* v_enableArtifactCache_x3f_1231_; lean_object* v_restoreAllArtifacts_x3f_1232_; uint8_t v_libPrefixOnWindows_1233_; uint8_t v_allowImportAll_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_toWorkspaceConfig_1203_ = lean_ctor_get(v_cfg_1202_, 0);
v_toLeanConfig_1204_ = lean_ctor_get(v_cfg_1202_, 1);
v_bootstrap_1205_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*27);
v_manifestFile_1206_ = lean_ctor_get(v_cfg_1202_, 2);
v_extraDepTargets_1207_ = lean_ctor_get(v_cfg_1202_, 3);
v_precompileModules_1208_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1209_ = lean_ctor_get(v_cfg_1202_, 4);
v_srcDir_1210_ = lean_ctor_get(v_cfg_1202_, 5);
v_buildDir_1211_ = lean_ctor_get(v_cfg_1202_, 6);
v_leanLibDir_1212_ = lean_ctor_get(v_cfg_1202_, 7);
v_nativeLibDir_1213_ = lean_ctor_get(v_cfg_1202_, 8);
v_binDir_1214_ = lean_ctor_get(v_cfg_1202_, 9);
v_releaseRepo_1215_ = lean_ctor_get(v_cfg_1202_, 11);
v_buildArchive_1216_ = lean_ctor_get(v_cfg_1202_, 12);
v_preferReleaseBuild_1217_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*27 + 2);
v_testDriver_1218_ = lean_ctor_get(v_cfg_1202_, 13);
v_testDriverArgs_1219_ = lean_ctor_get(v_cfg_1202_, 14);
v_lintDriver_1220_ = lean_ctor_get(v_cfg_1202_, 15);
v_lintDriverArgs_1221_ = lean_ctor_get(v_cfg_1202_, 16);
v_version_1222_ = lean_ctor_get(v_cfg_1202_, 17);
v_versionTags_1223_ = lean_ctor_get(v_cfg_1202_, 18);
v_description_1224_ = lean_ctor_get(v_cfg_1202_, 19);
v_keywords_1225_ = lean_ctor_get(v_cfg_1202_, 20);
v_homepage_1226_ = lean_ctor_get(v_cfg_1202_, 21);
v_license_1227_ = lean_ctor_get(v_cfg_1202_, 22);
v_licenseFiles_1228_ = lean_ctor_get(v_cfg_1202_, 23);
v_readmeFile_1229_ = lean_ctor_get(v_cfg_1202_, 24);
v_reservoir_1230_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1231_ = lean_ctor_get(v_cfg_1202_, 25);
v_restoreAllArtifacts_x3f_1232_ = lean_ctor_get(v_cfg_1202_, 26);
v_libPrefixOnWindows_1233_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*27 + 4);
v_allowImportAll_1234_ = lean_ctor_get_uint8(v_cfg_1202_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_1232_);
lean_inc(v_enableArtifactCache_x3f_1231_);
lean_inc(v_readmeFile_1229_);
lean_inc(v_licenseFiles_1228_);
lean_inc(v_license_1227_);
lean_inc(v_homepage_1226_);
lean_inc(v_keywords_1225_);
lean_inc(v_description_1224_);
lean_inc(v_versionTags_1223_);
lean_inc(v_version_1222_);
lean_inc(v_lintDriverArgs_1221_);
lean_inc(v_lintDriver_1220_);
lean_inc(v_testDriverArgs_1219_);
lean_inc(v_testDriver_1218_);
lean_inc(v_buildArchive_1216_);
lean_inc(v_releaseRepo_1215_);
lean_inc(v_binDir_1214_);
lean_inc(v_nativeLibDir_1213_);
lean_inc(v_leanLibDir_1212_);
lean_inc(v_buildDir_1211_);
lean_inc(v_srcDir_1210_);
lean_inc(v_moreGlobalServerArgs_1209_);
lean_inc(v_extraDepTargets_1207_);
lean_inc(v_manifestFile_1206_);
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
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_toWorkspaceConfig_1203_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_toLeanConfig_1204_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_manifestFile_1206_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_extraDepTargets_1207_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_moreGlobalServerArgs_1209_);
lean_ctor_set(v_reuseFailAlloc_1240_, 5, v_srcDir_1210_);
lean_ctor_set(v_reuseFailAlloc_1240_, 6, v_buildDir_1211_);
lean_ctor_set(v_reuseFailAlloc_1240_, 7, v_leanLibDir_1212_);
lean_ctor_set(v_reuseFailAlloc_1240_, 8, v_nativeLibDir_1213_);
lean_ctor_set(v_reuseFailAlloc_1240_, 9, v_binDir_1214_);
lean_ctor_set(v_reuseFailAlloc_1240_, 10, v_val_1201_);
lean_ctor_set(v_reuseFailAlloc_1240_, 11, v_releaseRepo_1215_);
lean_ctor_set(v_reuseFailAlloc_1240_, 12, v_buildArchive_1216_);
lean_ctor_set(v_reuseFailAlloc_1240_, 13, v_testDriver_1218_);
lean_ctor_set(v_reuseFailAlloc_1240_, 14, v_testDriverArgs_1219_);
lean_ctor_set(v_reuseFailAlloc_1240_, 15, v_lintDriver_1220_);
lean_ctor_set(v_reuseFailAlloc_1240_, 16, v_lintDriverArgs_1221_);
lean_ctor_set(v_reuseFailAlloc_1240_, 17, v_version_1222_);
lean_ctor_set(v_reuseFailAlloc_1240_, 18, v_versionTags_1223_);
lean_ctor_set(v_reuseFailAlloc_1240_, 19, v_description_1224_);
lean_ctor_set(v_reuseFailAlloc_1240_, 20, v_keywords_1225_);
lean_ctor_set(v_reuseFailAlloc_1240_, 21, v_homepage_1226_);
lean_ctor_set(v_reuseFailAlloc_1240_, 22, v_license_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 23, v_licenseFiles_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 24, v_readmeFile_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 25, v_enableArtifactCache_x3f_1231_);
lean_ctor_set(v_reuseFailAlloc_1240_, 26, v_restoreAllArtifacts_x3f_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*27, v_bootstrap_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*27 + 1, v_precompileModules_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*27 + 3, v_reservoir_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*27 + 5, v_allowImportAll_1234_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* v_f_1243_, lean_object* v_cfg_1244_){
_start:
{
lean_object* v_toWorkspaceConfig_1245_; lean_object* v_toLeanConfig_1246_; uint8_t v_bootstrap_1247_; lean_object* v_manifestFile_1248_; lean_object* v_extraDepTargets_1249_; uint8_t v_precompileModules_1250_; lean_object* v_moreGlobalServerArgs_1251_; lean_object* v_srcDir_1252_; lean_object* v_buildDir_1253_; lean_object* v_leanLibDir_1254_; lean_object* v_nativeLibDir_1255_; lean_object* v_binDir_1256_; lean_object* v_irDir_1257_; lean_object* v_releaseRepo_1258_; lean_object* v_buildArchive_1259_; uint8_t v_preferReleaseBuild_1260_; lean_object* v_testDriver_1261_; lean_object* v_testDriverArgs_1262_; lean_object* v_lintDriver_1263_; lean_object* v_lintDriverArgs_1264_; lean_object* v_version_1265_; lean_object* v_versionTags_1266_; lean_object* v_description_1267_; lean_object* v_keywords_1268_; lean_object* v_homepage_1269_; lean_object* v_license_1270_; lean_object* v_licenseFiles_1271_; lean_object* v_readmeFile_1272_; uint8_t v_reservoir_1273_; lean_object* v_enableArtifactCache_x3f_1274_; lean_object* v_restoreAllArtifacts_x3f_1275_; uint8_t v_libPrefixOnWindows_1276_; uint8_t v_allowImportAll_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_toWorkspaceConfig_1245_ = lean_ctor_get(v_cfg_1244_, 0);
v_toLeanConfig_1246_ = lean_ctor_get(v_cfg_1244_, 1);
v_bootstrap_1247_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*27);
v_manifestFile_1248_ = lean_ctor_get(v_cfg_1244_, 2);
v_extraDepTargets_1249_ = lean_ctor_get(v_cfg_1244_, 3);
v_precompileModules_1250_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1251_ = lean_ctor_get(v_cfg_1244_, 4);
v_srcDir_1252_ = lean_ctor_get(v_cfg_1244_, 5);
v_buildDir_1253_ = lean_ctor_get(v_cfg_1244_, 6);
v_leanLibDir_1254_ = lean_ctor_get(v_cfg_1244_, 7);
v_nativeLibDir_1255_ = lean_ctor_get(v_cfg_1244_, 8);
v_binDir_1256_ = lean_ctor_get(v_cfg_1244_, 9);
v_irDir_1257_ = lean_ctor_get(v_cfg_1244_, 10);
v_releaseRepo_1258_ = lean_ctor_get(v_cfg_1244_, 11);
v_buildArchive_1259_ = lean_ctor_get(v_cfg_1244_, 12);
v_preferReleaseBuild_1260_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*27 + 2);
v_testDriver_1261_ = lean_ctor_get(v_cfg_1244_, 13);
v_testDriverArgs_1262_ = lean_ctor_get(v_cfg_1244_, 14);
v_lintDriver_1263_ = lean_ctor_get(v_cfg_1244_, 15);
v_lintDriverArgs_1264_ = lean_ctor_get(v_cfg_1244_, 16);
v_version_1265_ = lean_ctor_get(v_cfg_1244_, 17);
v_versionTags_1266_ = lean_ctor_get(v_cfg_1244_, 18);
v_description_1267_ = lean_ctor_get(v_cfg_1244_, 19);
v_keywords_1268_ = lean_ctor_get(v_cfg_1244_, 20);
v_homepage_1269_ = lean_ctor_get(v_cfg_1244_, 21);
v_license_1270_ = lean_ctor_get(v_cfg_1244_, 22);
v_licenseFiles_1271_ = lean_ctor_get(v_cfg_1244_, 23);
v_readmeFile_1272_ = lean_ctor_get(v_cfg_1244_, 24);
v_reservoir_1273_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1274_ = lean_ctor_get(v_cfg_1244_, 25);
v_restoreAllArtifacts_x3f_1275_ = lean_ctor_get(v_cfg_1244_, 26);
v_libPrefixOnWindows_1276_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*27 + 4);
v_allowImportAll_1277_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*27 + 5);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_cfg_1244_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v_cfg_1244_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1275_);
lean_inc(v_enableArtifactCache_x3f_1274_);
lean_inc(v_readmeFile_1272_);
lean_inc(v_licenseFiles_1271_);
lean_inc(v_license_1270_);
lean_inc(v_homepage_1269_);
lean_inc(v_keywords_1268_);
lean_inc(v_description_1267_);
lean_inc(v_versionTags_1266_);
lean_inc(v_version_1265_);
lean_inc(v_lintDriverArgs_1264_);
lean_inc(v_lintDriver_1263_);
lean_inc(v_testDriverArgs_1262_);
lean_inc(v_testDriver_1261_);
lean_inc(v_buildArchive_1259_);
lean_inc(v_releaseRepo_1258_);
lean_inc(v_irDir_1257_);
lean_inc(v_binDir_1256_);
lean_inc(v_nativeLibDir_1255_);
lean_inc(v_leanLibDir_1254_);
lean_inc(v_buildDir_1253_);
lean_inc(v_srcDir_1252_);
lean_inc(v_moreGlobalServerArgs_1251_);
lean_inc(v_extraDepTargets_1249_);
lean_inc(v_manifestFile_1248_);
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
v___x_1281_ = lean_apply_1(v_f_1243_, v_irDir_1257_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 10, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_toWorkspaceConfig_1245_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_toLeanConfig_1246_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_manifestFile_1248_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_extraDepTargets_1249_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_moreGlobalServerArgs_1251_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_srcDir_1252_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_buildDir_1253_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_leanLibDir_1254_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_nativeLibDir_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_binDir_1256_);
lean_ctor_set(v_reuseFailAlloc_1284_, 10, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1284_, 11, v_releaseRepo_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 12, v_buildArchive_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 13, v_testDriver_1261_);
lean_ctor_set(v_reuseFailAlloc_1284_, 14, v_testDriverArgs_1262_);
lean_ctor_set(v_reuseFailAlloc_1284_, 15, v_lintDriver_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 16, v_lintDriverArgs_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 17, v_version_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 18, v_versionTags_1266_);
lean_ctor_set(v_reuseFailAlloc_1284_, 19, v_description_1267_);
lean_ctor_set(v_reuseFailAlloc_1284_, 20, v_keywords_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 21, v_homepage_1269_);
lean_ctor_set(v_reuseFailAlloc_1284_, 22, v_license_1270_);
lean_ctor_set(v_reuseFailAlloc_1284_, 23, v_licenseFiles_1271_);
lean_ctor_set(v_reuseFailAlloc_1284_, 24, v_readmeFile_1272_);
lean_ctor_set(v_reuseFailAlloc_1284_, 25, v_enableArtifactCache_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1284_, 26, v_restoreAllArtifacts_x3f_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*27, v_bootstrap_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*27 + 1, v_precompileModules_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*27 + 3, v_reservoir_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*27 + 5, v_allowImportAll_1277_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* v_x_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lake_defaultIrDir;
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* v_x_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lake_PackageConfig_irDir___proj___lam__3(v_x_1288_);
lean_dec_ref(v_x_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1299_, lean_object* v_n_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1302_, lean_object* v_n_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lake_PackageConfig_irDir___proj(v_p_1302_, v_n_1303_);
lean_dec(v_n_1303_);
lean_dec(v_p_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1305_, lean_object* v_n_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lake_PackageConfig_irDir___proj(v_p_1305_, v_n_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1308_, lean_object* v_n_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1308_, v_n_1309_);
lean_dec(v_n_1309_);
lean_dec(v_p_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* v_cfg_1311_){
_start:
{
lean_object* v_releaseRepo_1312_; 
v_releaseRepo_1312_ = lean_ctor_get(v_cfg_1311_, 11);
lean_inc(v_releaseRepo_1312_);
return v_releaseRepo_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* v_cfg_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lake_PackageConfig_releaseRepo___proj___lam__0(v_cfg_1313_);
lean_dec_ref(v_cfg_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* v_val_1315_, lean_object* v_cfg_1316_){
_start:
{
lean_object* v_toWorkspaceConfig_1317_; lean_object* v_toLeanConfig_1318_; uint8_t v_bootstrap_1319_; lean_object* v_manifestFile_1320_; lean_object* v_extraDepTargets_1321_; uint8_t v_precompileModules_1322_; lean_object* v_moreGlobalServerArgs_1323_; lean_object* v_srcDir_1324_; lean_object* v_buildDir_1325_; lean_object* v_leanLibDir_1326_; lean_object* v_nativeLibDir_1327_; lean_object* v_binDir_1328_; lean_object* v_irDir_1329_; lean_object* v_buildArchive_1330_; uint8_t v_preferReleaseBuild_1331_; lean_object* v_testDriver_1332_; lean_object* v_testDriverArgs_1333_; lean_object* v_lintDriver_1334_; lean_object* v_lintDriverArgs_1335_; lean_object* v_version_1336_; lean_object* v_versionTags_1337_; lean_object* v_description_1338_; lean_object* v_keywords_1339_; lean_object* v_homepage_1340_; lean_object* v_license_1341_; lean_object* v_licenseFiles_1342_; lean_object* v_readmeFile_1343_; uint8_t v_reservoir_1344_; lean_object* v_enableArtifactCache_x3f_1345_; lean_object* v_restoreAllArtifacts_x3f_1346_; uint8_t v_libPrefixOnWindows_1347_; uint8_t v_allowImportAll_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_toWorkspaceConfig_1317_ = lean_ctor_get(v_cfg_1316_, 0);
v_toLeanConfig_1318_ = lean_ctor_get(v_cfg_1316_, 1);
v_bootstrap_1319_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*27);
v_manifestFile_1320_ = lean_ctor_get(v_cfg_1316_, 2);
v_extraDepTargets_1321_ = lean_ctor_get(v_cfg_1316_, 3);
v_precompileModules_1322_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1323_ = lean_ctor_get(v_cfg_1316_, 4);
v_srcDir_1324_ = lean_ctor_get(v_cfg_1316_, 5);
v_buildDir_1325_ = lean_ctor_get(v_cfg_1316_, 6);
v_leanLibDir_1326_ = lean_ctor_get(v_cfg_1316_, 7);
v_nativeLibDir_1327_ = lean_ctor_get(v_cfg_1316_, 8);
v_binDir_1328_ = lean_ctor_get(v_cfg_1316_, 9);
v_irDir_1329_ = lean_ctor_get(v_cfg_1316_, 10);
v_buildArchive_1330_ = lean_ctor_get(v_cfg_1316_, 12);
v_preferReleaseBuild_1331_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*27 + 2);
v_testDriver_1332_ = lean_ctor_get(v_cfg_1316_, 13);
v_testDriverArgs_1333_ = lean_ctor_get(v_cfg_1316_, 14);
v_lintDriver_1334_ = lean_ctor_get(v_cfg_1316_, 15);
v_lintDriverArgs_1335_ = lean_ctor_get(v_cfg_1316_, 16);
v_version_1336_ = lean_ctor_get(v_cfg_1316_, 17);
v_versionTags_1337_ = lean_ctor_get(v_cfg_1316_, 18);
v_description_1338_ = lean_ctor_get(v_cfg_1316_, 19);
v_keywords_1339_ = lean_ctor_get(v_cfg_1316_, 20);
v_homepage_1340_ = lean_ctor_get(v_cfg_1316_, 21);
v_license_1341_ = lean_ctor_get(v_cfg_1316_, 22);
v_licenseFiles_1342_ = lean_ctor_get(v_cfg_1316_, 23);
v_readmeFile_1343_ = lean_ctor_get(v_cfg_1316_, 24);
v_reservoir_1344_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1345_ = lean_ctor_get(v_cfg_1316_, 25);
v_restoreAllArtifacts_x3f_1346_ = lean_ctor_get(v_cfg_1316_, 26);
v_libPrefixOnWindows_1347_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*27 + 4);
v_allowImportAll_1348_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*27 + 5);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_cfg_1316_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v_cfg_1316_, 11);
lean_dec(v_unused_1356_);
v___x_1350_ = v_cfg_1316_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1346_);
lean_inc(v_enableArtifactCache_x3f_1345_);
lean_inc(v_readmeFile_1343_);
lean_inc(v_licenseFiles_1342_);
lean_inc(v_license_1341_);
lean_inc(v_homepage_1340_);
lean_inc(v_keywords_1339_);
lean_inc(v_description_1338_);
lean_inc(v_versionTags_1337_);
lean_inc(v_version_1336_);
lean_inc(v_lintDriverArgs_1335_);
lean_inc(v_lintDriver_1334_);
lean_inc(v_testDriverArgs_1333_);
lean_inc(v_testDriver_1332_);
lean_inc(v_buildArchive_1330_);
lean_inc(v_irDir_1329_);
lean_inc(v_binDir_1328_);
lean_inc(v_nativeLibDir_1327_);
lean_inc(v_leanLibDir_1326_);
lean_inc(v_buildDir_1325_);
lean_inc(v_srcDir_1324_);
lean_inc(v_moreGlobalServerArgs_1323_);
lean_inc(v_extraDepTargets_1321_);
lean_inc(v_manifestFile_1320_);
lean_inc(v_toLeanConfig_1318_);
lean_inc(v_toWorkspaceConfig_1317_);
lean_dec(v_cfg_1316_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 11, v_val_1315_);
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_toWorkspaceConfig_1317_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_toLeanConfig_1318_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_manifestFile_1320_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_extraDepTargets_1321_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_moreGlobalServerArgs_1323_);
lean_ctor_set(v_reuseFailAlloc_1354_, 5, v_srcDir_1324_);
lean_ctor_set(v_reuseFailAlloc_1354_, 6, v_buildDir_1325_);
lean_ctor_set(v_reuseFailAlloc_1354_, 7, v_leanLibDir_1326_);
lean_ctor_set(v_reuseFailAlloc_1354_, 8, v_nativeLibDir_1327_);
lean_ctor_set(v_reuseFailAlloc_1354_, 9, v_binDir_1328_);
lean_ctor_set(v_reuseFailAlloc_1354_, 10, v_irDir_1329_);
lean_ctor_set(v_reuseFailAlloc_1354_, 11, v_val_1315_);
lean_ctor_set(v_reuseFailAlloc_1354_, 12, v_buildArchive_1330_);
lean_ctor_set(v_reuseFailAlloc_1354_, 13, v_testDriver_1332_);
lean_ctor_set(v_reuseFailAlloc_1354_, 14, v_testDriverArgs_1333_);
lean_ctor_set(v_reuseFailAlloc_1354_, 15, v_lintDriver_1334_);
lean_ctor_set(v_reuseFailAlloc_1354_, 16, v_lintDriverArgs_1335_);
lean_ctor_set(v_reuseFailAlloc_1354_, 17, v_version_1336_);
lean_ctor_set(v_reuseFailAlloc_1354_, 18, v_versionTags_1337_);
lean_ctor_set(v_reuseFailAlloc_1354_, 19, v_description_1338_);
lean_ctor_set(v_reuseFailAlloc_1354_, 20, v_keywords_1339_);
lean_ctor_set(v_reuseFailAlloc_1354_, 21, v_homepage_1340_);
lean_ctor_set(v_reuseFailAlloc_1354_, 22, v_license_1341_);
lean_ctor_set(v_reuseFailAlloc_1354_, 23, v_licenseFiles_1342_);
lean_ctor_set(v_reuseFailAlloc_1354_, 24, v_readmeFile_1343_);
lean_ctor_set(v_reuseFailAlloc_1354_, 25, v_enableArtifactCache_x3f_1345_);
lean_ctor_set(v_reuseFailAlloc_1354_, 26, v_restoreAllArtifacts_x3f_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*27, v_bootstrap_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*27 + 1, v_precompileModules_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*27 + 3, v_reservoir_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*27 + 5, v_allowImportAll_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* v_f_1357_, lean_object* v_cfg_1358_){
_start:
{
lean_object* v_toWorkspaceConfig_1359_; lean_object* v_toLeanConfig_1360_; uint8_t v_bootstrap_1361_; lean_object* v_manifestFile_1362_; lean_object* v_extraDepTargets_1363_; uint8_t v_precompileModules_1364_; lean_object* v_moreGlobalServerArgs_1365_; lean_object* v_srcDir_1366_; lean_object* v_buildDir_1367_; lean_object* v_leanLibDir_1368_; lean_object* v_nativeLibDir_1369_; lean_object* v_binDir_1370_; lean_object* v_irDir_1371_; lean_object* v_releaseRepo_1372_; lean_object* v_buildArchive_1373_; uint8_t v_preferReleaseBuild_1374_; lean_object* v_testDriver_1375_; lean_object* v_testDriverArgs_1376_; lean_object* v_lintDriver_1377_; lean_object* v_lintDriverArgs_1378_; lean_object* v_version_1379_; lean_object* v_versionTags_1380_; lean_object* v_description_1381_; lean_object* v_keywords_1382_; lean_object* v_homepage_1383_; lean_object* v_license_1384_; lean_object* v_licenseFiles_1385_; lean_object* v_readmeFile_1386_; uint8_t v_reservoir_1387_; lean_object* v_enableArtifactCache_x3f_1388_; lean_object* v_restoreAllArtifacts_x3f_1389_; uint8_t v_libPrefixOnWindows_1390_; uint8_t v_allowImportAll_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1399_; 
v_toWorkspaceConfig_1359_ = lean_ctor_get(v_cfg_1358_, 0);
v_toLeanConfig_1360_ = lean_ctor_get(v_cfg_1358_, 1);
v_bootstrap_1361_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*27);
v_manifestFile_1362_ = lean_ctor_get(v_cfg_1358_, 2);
v_extraDepTargets_1363_ = lean_ctor_get(v_cfg_1358_, 3);
v_precompileModules_1364_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1365_ = lean_ctor_get(v_cfg_1358_, 4);
v_srcDir_1366_ = lean_ctor_get(v_cfg_1358_, 5);
v_buildDir_1367_ = lean_ctor_get(v_cfg_1358_, 6);
v_leanLibDir_1368_ = lean_ctor_get(v_cfg_1358_, 7);
v_nativeLibDir_1369_ = lean_ctor_get(v_cfg_1358_, 8);
v_binDir_1370_ = lean_ctor_get(v_cfg_1358_, 9);
v_irDir_1371_ = lean_ctor_get(v_cfg_1358_, 10);
v_releaseRepo_1372_ = lean_ctor_get(v_cfg_1358_, 11);
v_buildArchive_1373_ = lean_ctor_get(v_cfg_1358_, 12);
v_preferReleaseBuild_1374_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*27 + 2);
v_testDriver_1375_ = lean_ctor_get(v_cfg_1358_, 13);
v_testDriverArgs_1376_ = lean_ctor_get(v_cfg_1358_, 14);
v_lintDriver_1377_ = lean_ctor_get(v_cfg_1358_, 15);
v_lintDriverArgs_1378_ = lean_ctor_get(v_cfg_1358_, 16);
v_version_1379_ = lean_ctor_get(v_cfg_1358_, 17);
v_versionTags_1380_ = lean_ctor_get(v_cfg_1358_, 18);
v_description_1381_ = lean_ctor_get(v_cfg_1358_, 19);
v_keywords_1382_ = lean_ctor_get(v_cfg_1358_, 20);
v_homepage_1383_ = lean_ctor_get(v_cfg_1358_, 21);
v_license_1384_ = lean_ctor_get(v_cfg_1358_, 22);
v_licenseFiles_1385_ = lean_ctor_get(v_cfg_1358_, 23);
v_readmeFile_1386_ = lean_ctor_get(v_cfg_1358_, 24);
v_reservoir_1387_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1388_ = lean_ctor_get(v_cfg_1358_, 25);
v_restoreAllArtifacts_x3f_1389_ = lean_ctor_get(v_cfg_1358_, 26);
v_libPrefixOnWindows_1390_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*27 + 4);
v_allowImportAll_1391_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*27 + 5);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_cfg_1358_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1393_ = v_cfg_1358_;
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1389_);
lean_inc(v_enableArtifactCache_x3f_1388_);
lean_inc(v_readmeFile_1386_);
lean_inc(v_licenseFiles_1385_);
lean_inc(v_license_1384_);
lean_inc(v_homepage_1383_);
lean_inc(v_keywords_1382_);
lean_inc(v_description_1381_);
lean_inc(v_versionTags_1380_);
lean_inc(v_version_1379_);
lean_inc(v_lintDriverArgs_1378_);
lean_inc(v_lintDriver_1377_);
lean_inc(v_testDriverArgs_1376_);
lean_inc(v_testDriver_1375_);
lean_inc(v_buildArchive_1373_);
lean_inc(v_releaseRepo_1372_);
lean_inc(v_irDir_1371_);
lean_inc(v_binDir_1370_);
lean_inc(v_nativeLibDir_1369_);
lean_inc(v_leanLibDir_1368_);
lean_inc(v_buildDir_1367_);
lean_inc(v_srcDir_1366_);
lean_inc(v_moreGlobalServerArgs_1365_);
lean_inc(v_extraDepTargets_1363_);
lean_inc(v_manifestFile_1362_);
lean_inc(v_toLeanConfig_1360_);
lean_inc(v_toWorkspaceConfig_1359_);
lean_dec(v_cfg_1358_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_apply_1(v_f_1357_, v_releaseRepo_1372_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 11, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_toWorkspaceConfig_1359_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_toLeanConfig_1360_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_manifestFile_1362_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_extraDepTargets_1363_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_moreGlobalServerArgs_1365_);
lean_ctor_set(v_reuseFailAlloc_1398_, 5, v_srcDir_1366_);
lean_ctor_set(v_reuseFailAlloc_1398_, 6, v_buildDir_1367_);
lean_ctor_set(v_reuseFailAlloc_1398_, 7, v_leanLibDir_1368_);
lean_ctor_set(v_reuseFailAlloc_1398_, 8, v_nativeLibDir_1369_);
lean_ctor_set(v_reuseFailAlloc_1398_, 9, v_binDir_1370_);
lean_ctor_set(v_reuseFailAlloc_1398_, 10, v_irDir_1371_);
lean_ctor_set(v_reuseFailAlloc_1398_, 11, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1398_, 12, v_buildArchive_1373_);
lean_ctor_set(v_reuseFailAlloc_1398_, 13, v_testDriver_1375_);
lean_ctor_set(v_reuseFailAlloc_1398_, 14, v_testDriverArgs_1376_);
lean_ctor_set(v_reuseFailAlloc_1398_, 15, v_lintDriver_1377_);
lean_ctor_set(v_reuseFailAlloc_1398_, 16, v_lintDriverArgs_1378_);
lean_ctor_set(v_reuseFailAlloc_1398_, 17, v_version_1379_);
lean_ctor_set(v_reuseFailAlloc_1398_, 18, v_versionTags_1380_);
lean_ctor_set(v_reuseFailAlloc_1398_, 19, v_description_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 20, v_keywords_1382_);
lean_ctor_set(v_reuseFailAlloc_1398_, 21, v_homepage_1383_);
lean_ctor_set(v_reuseFailAlloc_1398_, 22, v_license_1384_);
lean_ctor_set(v_reuseFailAlloc_1398_, 23, v_licenseFiles_1385_);
lean_ctor_set(v_reuseFailAlloc_1398_, 24, v_readmeFile_1386_);
lean_ctor_set(v_reuseFailAlloc_1398_, 25, v_enableArtifactCache_x3f_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 26, v_restoreAllArtifacts_x3f_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*27, v_bootstrap_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*27 + 1, v_precompileModules_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*27 + 3, v_reservoir_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*27 + 5, v_allowImportAll_1391_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1408_, lean_object* v_n_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__3));
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1411_, lean_object* v_n_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1411_, v_n_1412_);
lean_dec(v_n_1412_);
lean_dec(v_p_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1414_, lean_object* v_n_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1414_, v_n_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1417_, lean_object* v_n_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1417_, v_n_1418_);
lean_dec(v_n_1418_);
lean_dec(v_p_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1420_, lean_object* v_n_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1420_, v_n_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1423_, lean_object* v_n_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1423_, v_n_1424_);
lean_dec(v_n_1424_);
lean_dec(v_p_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* v_cfg_1426_){
_start:
{
lean_object* v_buildArchive_1427_; 
v_buildArchive_1427_ = lean_ctor_get(v_cfg_1426_, 12);
lean_inc(v_buildArchive_1427_);
return v_buildArchive_1427_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* v_cfg_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lake_PackageConfig_buildArchive___proj___lam__0(v_cfg_1428_);
lean_dec_ref(v_cfg_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* v_val_1430_, lean_object* v_cfg_1431_){
_start:
{
lean_object* v_toWorkspaceConfig_1432_; lean_object* v_toLeanConfig_1433_; uint8_t v_bootstrap_1434_; lean_object* v_manifestFile_1435_; lean_object* v_extraDepTargets_1436_; uint8_t v_precompileModules_1437_; lean_object* v_moreGlobalServerArgs_1438_; lean_object* v_srcDir_1439_; lean_object* v_buildDir_1440_; lean_object* v_leanLibDir_1441_; lean_object* v_nativeLibDir_1442_; lean_object* v_binDir_1443_; lean_object* v_irDir_1444_; lean_object* v_releaseRepo_1445_; uint8_t v_preferReleaseBuild_1446_; lean_object* v_testDriver_1447_; lean_object* v_testDriverArgs_1448_; lean_object* v_lintDriver_1449_; lean_object* v_lintDriverArgs_1450_; lean_object* v_version_1451_; lean_object* v_versionTags_1452_; lean_object* v_description_1453_; lean_object* v_keywords_1454_; lean_object* v_homepage_1455_; lean_object* v_license_1456_; lean_object* v_licenseFiles_1457_; lean_object* v_readmeFile_1458_; uint8_t v_reservoir_1459_; lean_object* v_enableArtifactCache_x3f_1460_; lean_object* v_restoreAllArtifacts_x3f_1461_; uint8_t v_libPrefixOnWindows_1462_; uint8_t v_allowImportAll_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_toWorkspaceConfig_1432_ = lean_ctor_get(v_cfg_1431_, 0);
v_toLeanConfig_1433_ = lean_ctor_get(v_cfg_1431_, 1);
v_bootstrap_1434_ = lean_ctor_get_uint8(v_cfg_1431_, sizeof(void*)*27);
v_manifestFile_1435_ = lean_ctor_get(v_cfg_1431_, 2);
v_extraDepTargets_1436_ = lean_ctor_get(v_cfg_1431_, 3);
v_precompileModules_1437_ = lean_ctor_get_uint8(v_cfg_1431_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1438_ = lean_ctor_get(v_cfg_1431_, 4);
v_srcDir_1439_ = lean_ctor_get(v_cfg_1431_, 5);
v_buildDir_1440_ = lean_ctor_get(v_cfg_1431_, 6);
v_leanLibDir_1441_ = lean_ctor_get(v_cfg_1431_, 7);
v_nativeLibDir_1442_ = lean_ctor_get(v_cfg_1431_, 8);
v_binDir_1443_ = lean_ctor_get(v_cfg_1431_, 9);
v_irDir_1444_ = lean_ctor_get(v_cfg_1431_, 10);
v_releaseRepo_1445_ = lean_ctor_get(v_cfg_1431_, 11);
v_preferReleaseBuild_1446_ = lean_ctor_get_uint8(v_cfg_1431_, sizeof(void*)*27 + 2);
v_testDriver_1447_ = lean_ctor_get(v_cfg_1431_, 13);
v_testDriverArgs_1448_ = lean_ctor_get(v_cfg_1431_, 14);
v_lintDriver_1449_ = lean_ctor_get(v_cfg_1431_, 15);
v_lintDriverArgs_1450_ = lean_ctor_get(v_cfg_1431_, 16);
v_version_1451_ = lean_ctor_get(v_cfg_1431_, 17);
v_versionTags_1452_ = lean_ctor_get(v_cfg_1431_, 18);
v_description_1453_ = lean_ctor_get(v_cfg_1431_, 19);
v_keywords_1454_ = lean_ctor_get(v_cfg_1431_, 20);
v_homepage_1455_ = lean_ctor_get(v_cfg_1431_, 21);
v_license_1456_ = lean_ctor_get(v_cfg_1431_, 22);
v_licenseFiles_1457_ = lean_ctor_get(v_cfg_1431_, 23);
v_readmeFile_1458_ = lean_ctor_get(v_cfg_1431_, 24);
v_reservoir_1459_ = lean_ctor_get_uint8(v_cfg_1431_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1460_ = lean_ctor_get(v_cfg_1431_, 25);
v_restoreAllArtifacts_x3f_1461_ = lean_ctor_get(v_cfg_1431_, 26);
v_libPrefixOnWindows_1462_ = lean_ctor_get_uint8(v_cfg_1431_, sizeof(void*)*27 + 4);
v_allowImportAll_1463_ = lean_ctor_get_uint8(v_cfg_1431_, sizeof(void*)*27 + 5);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_cfg_1431_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_cfg_1431_, 12);
lean_dec(v_unused_1471_);
v___x_1465_ = v_cfg_1431_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1461_);
lean_inc(v_enableArtifactCache_x3f_1460_);
lean_inc(v_readmeFile_1458_);
lean_inc(v_licenseFiles_1457_);
lean_inc(v_license_1456_);
lean_inc(v_homepage_1455_);
lean_inc(v_keywords_1454_);
lean_inc(v_description_1453_);
lean_inc(v_versionTags_1452_);
lean_inc(v_version_1451_);
lean_inc(v_lintDriverArgs_1450_);
lean_inc(v_lintDriver_1449_);
lean_inc(v_testDriverArgs_1448_);
lean_inc(v_testDriver_1447_);
lean_inc(v_releaseRepo_1445_);
lean_inc(v_irDir_1444_);
lean_inc(v_binDir_1443_);
lean_inc(v_nativeLibDir_1442_);
lean_inc(v_leanLibDir_1441_);
lean_inc(v_buildDir_1440_);
lean_inc(v_srcDir_1439_);
lean_inc(v_moreGlobalServerArgs_1438_);
lean_inc(v_extraDepTargets_1436_);
lean_inc(v_manifestFile_1435_);
lean_inc(v_toLeanConfig_1433_);
lean_inc(v_toWorkspaceConfig_1432_);
lean_dec(v_cfg_1431_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 12, v_val_1430_);
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_toWorkspaceConfig_1432_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_toLeanConfig_1433_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_manifestFile_1435_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_extraDepTargets_1436_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_moreGlobalServerArgs_1438_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v_srcDir_1439_);
lean_ctor_set(v_reuseFailAlloc_1469_, 6, v_buildDir_1440_);
lean_ctor_set(v_reuseFailAlloc_1469_, 7, v_leanLibDir_1441_);
lean_ctor_set(v_reuseFailAlloc_1469_, 8, v_nativeLibDir_1442_);
lean_ctor_set(v_reuseFailAlloc_1469_, 9, v_binDir_1443_);
lean_ctor_set(v_reuseFailAlloc_1469_, 10, v_irDir_1444_);
lean_ctor_set(v_reuseFailAlloc_1469_, 11, v_releaseRepo_1445_);
lean_ctor_set(v_reuseFailAlloc_1469_, 12, v_val_1430_);
lean_ctor_set(v_reuseFailAlloc_1469_, 13, v_testDriver_1447_);
lean_ctor_set(v_reuseFailAlloc_1469_, 14, v_testDriverArgs_1448_);
lean_ctor_set(v_reuseFailAlloc_1469_, 15, v_lintDriver_1449_);
lean_ctor_set(v_reuseFailAlloc_1469_, 16, v_lintDriverArgs_1450_);
lean_ctor_set(v_reuseFailAlloc_1469_, 17, v_version_1451_);
lean_ctor_set(v_reuseFailAlloc_1469_, 18, v_versionTags_1452_);
lean_ctor_set(v_reuseFailAlloc_1469_, 19, v_description_1453_);
lean_ctor_set(v_reuseFailAlloc_1469_, 20, v_keywords_1454_);
lean_ctor_set(v_reuseFailAlloc_1469_, 21, v_homepage_1455_);
lean_ctor_set(v_reuseFailAlloc_1469_, 22, v_license_1456_);
lean_ctor_set(v_reuseFailAlloc_1469_, 23, v_licenseFiles_1457_);
lean_ctor_set(v_reuseFailAlloc_1469_, 24, v_readmeFile_1458_);
lean_ctor_set(v_reuseFailAlloc_1469_, 25, v_enableArtifactCache_x3f_1460_);
lean_ctor_set(v_reuseFailAlloc_1469_, 26, v_restoreAllArtifacts_x3f_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*27, v_bootstrap_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*27 + 1, v_precompileModules_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*27 + 3, v_reservoir_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*27 + 5, v_allowImportAll_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* v_f_1472_, lean_object* v_cfg_1473_){
_start:
{
lean_object* v_toWorkspaceConfig_1474_; lean_object* v_toLeanConfig_1475_; uint8_t v_bootstrap_1476_; lean_object* v_manifestFile_1477_; lean_object* v_extraDepTargets_1478_; uint8_t v_precompileModules_1479_; lean_object* v_moreGlobalServerArgs_1480_; lean_object* v_srcDir_1481_; lean_object* v_buildDir_1482_; lean_object* v_leanLibDir_1483_; lean_object* v_nativeLibDir_1484_; lean_object* v_binDir_1485_; lean_object* v_irDir_1486_; lean_object* v_releaseRepo_1487_; lean_object* v_buildArchive_1488_; uint8_t v_preferReleaseBuild_1489_; lean_object* v_testDriver_1490_; lean_object* v_testDriverArgs_1491_; lean_object* v_lintDriver_1492_; lean_object* v_lintDriverArgs_1493_; lean_object* v_version_1494_; lean_object* v_versionTags_1495_; lean_object* v_description_1496_; lean_object* v_keywords_1497_; lean_object* v_homepage_1498_; lean_object* v_license_1499_; lean_object* v_licenseFiles_1500_; lean_object* v_readmeFile_1501_; uint8_t v_reservoir_1502_; lean_object* v_enableArtifactCache_x3f_1503_; lean_object* v_restoreAllArtifacts_x3f_1504_; uint8_t v_libPrefixOnWindows_1505_; uint8_t v_allowImportAll_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1514_; 
v_toWorkspaceConfig_1474_ = lean_ctor_get(v_cfg_1473_, 0);
v_toLeanConfig_1475_ = lean_ctor_get(v_cfg_1473_, 1);
v_bootstrap_1476_ = lean_ctor_get_uint8(v_cfg_1473_, sizeof(void*)*27);
v_manifestFile_1477_ = lean_ctor_get(v_cfg_1473_, 2);
v_extraDepTargets_1478_ = lean_ctor_get(v_cfg_1473_, 3);
v_precompileModules_1479_ = lean_ctor_get_uint8(v_cfg_1473_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1480_ = lean_ctor_get(v_cfg_1473_, 4);
v_srcDir_1481_ = lean_ctor_get(v_cfg_1473_, 5);
v_buildDir_1482_ = lean_ctor_get(v_cfg_1473_, 6);
v_leanLibDir_1483_ = lean_ctor_get(v_cfg_1473_, 7);
v_nativeLibDir_1484_ = lean_ctor_get(v_cfg_1473_, 8);
v_binDir_1485_ = lean_ctor_get(v_cfg_1473_, 9);
v_irDir_1486_ = lean_ctor_get(v_cfg_1473_, 10);
v_releaseRepo_1487_ = lean_ctor_get(v_cfg_1473_, 11);
v_buildArchive_1488_ = lean_ctor_get(v_cfg_1473_, 12);
v_preferReleaseBuild_1489_ = lean_ctor_get_uint8(v_cfg_1473_, sizeof(void*)*27 + 2);
v_testDriver_1490_ = lean_ctor_get(v_cfg_1473_, 13);
v_testDriverArgs_1491_ = lean_ctor_get(v_cfg_1473_, 14);
v_lintDriver_1492_ = lean_ctor_get(v_cfg_1473_, 15);
v_lintDriverArgs_1493_ = lean_ctor_get(v_cfg_1473_, 16);
v_version_1494_ = lean_ctor_get(v_cfg_1473_, 17);
v_versionTags_1495_ = lean_ctor_get(v_cfg_1473_, 18);
v_description_1496_ = lean_ctor_get(v_cfg_1473_, 19);
v_keywords_1497_ = lean_ctor_get(v_cfg_1473_, 20);
v_homepage_1498_ = lean_ctor_get(v_cfg_1473_, 21);
v_license_1499_ = lean_ctor_get(v_cfg_1473_, 22);
v_licenseFiles_1500_ = lean_ctor_get(v_cfg_1473_, 23);
v_readmeFile_1501_ = lean_ctor_get(v_cfg_1473_, 24);
v_reservoir_1502_ = lean_ctor_get_uint8(v_cfg_1473_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1503_ = lean_ctor_get(v_cfg_1473_, 25);
v_restoreAllArtifacts_x3f_1504_ = lean_ctor_get(v_cfg_1473_, 26);
v_libPrefixOnWindows_1505_ = lean_ctor_get_uint8(v_cfg_1473_, sizeof(void*)*27 + 4);
v_allowImportAll_1506_ = lean_ctor_get_uint8(v_cfg_1473_, sizeof(void*)*27 + 5);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_cfg_1473_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1508_ = v_cfg_1473_;
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1504_);
lean_inc(v_enableArtifactCache_x3f_1503_);
lean_inc(v_readmeFile_1501_);
lean_inc(v_licenseFiles_1500_);
lean_inc(v_license_1499_);
lean_inc(v_homepage_1498_);
lean_inc(v_keywords_1497_);
lean_inc(v_description_1496_);
lean_inc(v_versionTags_1495_);
lean_inc(v_version_1494_);
lean_inc(v_lintDriverArgs_1493_);
lean_inc(v_lintDriver_1492_);
lean_inc(v_testDriverArgs_1491_);
lean_inc(v_testDriver_1490_);
lean_inc(v_buildArchive_1488_);
lean_inc(v_releaseRepo_1487_);
lean_inc(v_irDir_1486_);
lean_inc(v_binDir_1485_);
lean_inc(v_nativeLibDir_1484_);
lean_inc(v_leanLibDir_1483_);
lean_inc(v_buildDir_1482_);
lean_inc(v_srcDir_1481_);
lean_inc(v_moreGlobalServerArgs_1480_);
lean_inc(v_extraDepTargets_1478_);
lean_inc(v_manifestFile_1477_);
lean_inc(v_toLeanConfig_1475_);
lean_inc(v_toWorkspaceConfig_1474_);
lean_dec(v_cfg_1473_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_apply_1(v_f_1472_, v_buildArchive_1488_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 12, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_toWorkspaceConfig_1474_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_toLeanConfig_1475_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_manifestFile_1477_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_extraDepTargets_1478_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_moreGlobalServerArgs_1480_);
lean_ctor_set(v_reuseFailAlloc_1513_, 5, v_srcDir_1481_);
lean_ctor_set(v_reuseFailAlloc_1513_, 6, v_buildDir_1482_);
lean_ctor_set(v_reuseFailAlloc_1513_, 7, v_leanLibDir_1483_);
lean_ctor_set(v_reuseFailAlloc_1513_, 8, v_nativeLibDir_1484_);
lean_ctor_set(v_reuseFailAlloc_1513_, 9, v_binDir_1485_);
lean_ctor_set(v_reuseFailAlloc_1513_, 10, v_irDir_1486_);
lean_ctor_set(v_reuseFailAlloc_1513_, 11, v_releaseRepo_1487_);
lean_ctor_set(v_reuseFailAlloc_1513_, 12, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 13, v_testDriver_1490_);
lean_ctor_set(v_reuseFailAlloc_1513_, 14, v_testDriverArgs_1491_);
lean_ctor_set(v_reuseFailAlloc_1513_, 15, v_lintDriver_1492_);
lean_ctor_set(v_reuseFailAlloc_1513_, 16, v_lintDriverArgs_1493_);
lean_ctor_set(v_reuseFailAlloc_1513_, 17, v_version_1494_);
lean_ctor_set(v_reuseFailAlloc_1513_, 18, v_versionTags_1495_);
lean_ctor_set(v_reuseFailAlloc_1513_, 19, v_description_1496_);
lean_ctor_set(v_reuseFailAlloc_1513_, 20, v_keywords_1497_);
lean_ctor_set(v_reuseFailAlloc_1513_, 21, v_homepage_1498_);
lean_ctor_set(v_reuseFailAlloc_1513_, 22, v_license_1499_);
lean_ctor_set(v_reuseFailAlloc_1513_, 23, v_licenseFiles_1500_);
lean_ctor_set(v_reuseFailAlloc_1513_, 24, v_readmeFile_1501_);
lean_ctor_set(v_reuseFailAlloc_1513_, 25, v_enableArtifactCache_x3f_1503_);
lean_ctor_set(v_reuseFailAlloc_1513_, 26, v_restoreAllArtifacts_x3f_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*27, v_bootstrap_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*27 + 1, v_precompileModules_1479_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*27 + 3, v_reservoir_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1513_, sizeof(void*)*27 + 5, v_allowImportAll_1506_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1523_, lean_object* v_n_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1526_, lean_object* v_n_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1526_, v_n_1527_);
lean_dec(v_n_1527_);
lean_dec(v_p_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1529_, lean_object* v_n_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1529_, v_n_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1532_, lean_object* v_n_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1532_, v_n_1533_);
lean_dec(v_n_1533_);
lean_dec(v_p_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1535_, lean_object* v_n_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1535_, v_n_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1538_, lean_object* v_n_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1538_, v_n_1539_);
lean_dec(v_n_1539_);
lean_dec(v_p_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* v_cfg_1541_){
_start:
{
uint8_t v_preferReleaseBuild_1542_; 
v_preferReleaseBuild_1542_ = lean_ctor_get_uint8(v_cfg_1541_, sizeof(void*)*27 + 2);
return v_preferReleaseBuild_1542_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* v_cfg_1543_){
_start:
{
uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(v_cfg_1543_);
lean_dec_ref(v_cfg_1543_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t v_val_1546_, lean_object* v_cfg_1547_){
_start:
{
lean_object* v_toWorkspaceConfig_1548_; lean_object* v_toLeanConfig_1549_; uint8_t v_bootstrap_1550_; lean_object* v_manifestFile_1551_; lean_object* v_extraDepTargets_1552_; uint8_t v_precompileModules_1553_; lean_object* v_moreGlobalServerArgs_1554_; lean_object* v_srcDir_1555_; lean_object* v_buildDir_1556_; lean_object* v_leanLibDir_1557_; lean_object* v_nativeLibDir_1558_; lean_object* v_binDir_1559_; lean_object* v_irDir_1560_; lean_object* v_releaseRepo_1561_; lean_object* v_buildArchive_1562_; lean_object* v_testDriver_1563_; lean_object* v_testDriverArgs_1564_; lean_object* v_lintDriver_1565_; lean_object* v_lintDriverArgs_1566_; lean_object* v_version_1567_; lean_object* v_versionTags_1568_; lean_object* v_description_1569_; lean_object* v_keywords_1570_; lean_object* v_homepage_1571_; lean_object* v_license_1572_; lean_object* v_licenseFiles_1573_; lean_object* v_readmeFile_1574_; uint8_t v_reservoir_1575_; lean_object* v_enableArtifactCache_x3f_1576_; lean_object* v_restoreAllArtifacts_x3f_1577_; uint8_t v_libPrefixOnWindows_1578_; uint8_t v_allowImportAll_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_toWorkspaceConfig_1548_ = lean_ctor_get(v_cfg_1547_, 0);
v_toLeanConfig_1549_ = lean_ctor_get(v_cfg_1547_, 1);
v_bootstrap_1550_ = lean_ctor_get_uint8(v_cfg_1547_, sizeof(void*)*27);
v_manifestFile_1551_ = lean_ctor_get(v_cfg_1547_, 2);
v_extraDepTargets_1552_ = lean_ctor_get(v_cfg_1547_, 3);
v_precompileModules_1553_ = lean_ctor_get_uint8(v_cfg_1547_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1554_ = lean_ctor_get(v_cfg_1547_, 4);
v_srcDir_1555_ = lean_ctor_get(v_cfg_1547_, 5);
v_buildDir_1556_ = lean_ctor_get(v_cfg_1547_, 6);
v_leanLibDir_1557_ = lean_ctor_get(v_cfg_1547_, 7);
v_nativeLibDir_1558_ = lean_ctor_get(v_cfg_1547_, 8);
v_binDir_1559_ = lean_ctor_get(v_cfg_1547_, 9);
v_irDir_1560_ = lean_ctor_get(v_cfg_1547_, 10);
v_releaseRepo_1561_ = lean_ctor_get(v_cfg_1547_, 11);
v_buildArchive_1562_ = lean_ctor_get(v_cfg_1547_, 12);
v_testDriver_1563_ = lean_ctor_get(v_cfg_1547_, 13);
v_testDriverArgs_1564_ = lean_ctor_get(v_cfg_1547_, 14);
v_lintDriver_1565_ = lean_ctor_get(v_cfg_1547_, 15);
v_lintDriverArgs_1566_ = lean_ctor_get(v_cfg_1547_, 16);
v_version_1567_ = lean_ctor_get(v_cfg_1547_, 17);
v_versionTags_1568_ = lean_ctor_get(v_cfg_1547_, 18);
v_description_1569_ = lean_ctor_get(v_cfg_1547_, 19);
v_keywords_1570_ = lean_ctor_get(v_cfg_1547_, 20);
v_homepage_1571_ = lean_ctor_get(v_cfg_1547_, 21);
v_license_1572_ = lean_ctor_get(v_cfg_1547_, 22);
v_licenseFiles_1573_ = lean_ctor_get(v_cfg_1547_, 23);
v_readmeFile_1574_ = lean_ctor_get(v_cfg_1547_, 24);
v_reservoir_1575_ = lean_ctor_get_uint8(v_cfg_1547_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1576_ = lean_ctor_get(v_cfg_1547_, 25);
v_restoreAllArtifacts_x3f_1577_ = lean_ctor_get(v_cfg_1547_, 26);
v_libPrefixOnWindows_1578_ = lean_ctor_get_uint8(v_cfg_1547_, sizeof(void*)*27 + 4);
v_allowImportAll_1579_ = lean_ctor_get_uint8(v_cfg_1547_, sizeof(void*)*27 + 5);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_cfg_1547_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v_cfg_1547_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1577_);
lean_inc(v_enableArtifactCache_x3f_1576_);
lean_inc(v_readmeFile_1574_);
lean_inc(v_licenseFiles_1573_);
lean_inc(v_license_1572_);
lean_inc(v_homepage_1571_);
lean_inc(v_keywords_1570_);
lean_inc(v_description_1569_);
lean_inc(v_versionTags_1568_);
lean_inc(v_version_1567_);
lean_inc(v_lintDriverArgs_1566_);
lean_inc(v_lintDriver_1565_);
lean_inc(v_testDriverArgs_1564_);
lean_inc(v_testDriver_1563_);
lean_inc(v_buildArchive_1562_);
lean_inc(v_releaseRepo_1561_);
lean_inc(v_irDir_1560_);
lean_inc(v_binDir_1559_);
lean_inc(v_nativeLibDir_1558_);
lean_inc(v_leanLibDir_1557_);
lean_inc(v_buildDir_1556_);
lean_inc(v_srcDir_1555_);
lean_inc(v_moreGlobalServerArgs_1554_);
lean_inc(v_extraDepTargets_1552_);
lean_inc(v_manifestFile_1551_);
lean_inc(v_toLeanConfig_1549_);
lean_inc(v_toWorkspaceConfig_1548_);
lean_dec(v_cfg_1547_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_toWorkspaceConfig_1548_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_toLeanConfig_1549_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_manifestFile_1551_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_extraDepTargets_1552_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_moreGlobalServerArgs_1554_);
lean_ctor_set(v_reuseFailAlloc_1585_, 5, v_srcDir_1555_);
lean_ctor_set(v_reuseFailAlloc_1585_, 6, v_buildDir_1556_);
lean_ctor_set(v_reuseFailAlloc_1585_, 7, v_leanLibDir_1557_);
lean_ctor_set(v_reuseFailAlloc_1585_, 8, v_nativeLibDir_1558_);
lean_ctor_set(v_reuseFailAlloc_1585_, 9, v_binDir_1559_);
lean_ctor_set(v_reuseFailAlloc_1585_, 10, v_irDir_1560_);
lean_ctor_set(v_reuseFailAlloc_1585_, 11, v_releaseRepo_1561_);
lean_ctor_set(v_reuseFailAlloc_1585_, 12, v_buildArchive_1562_);
lean_ctor_set(v_reuseFailAlloc_1585_, 13, v_testDriver_1563_);
lean_ctor_set(v_reuseFailAlloc_1585_, 14, v_testDriverArgs_1564_);
lean_ctor_set(v_reuseFailAlloc_1585_, 15, v_lintDriver_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 16, v_lintDriverArgs_1566_);
lean_ctor_set(v_reuseFailAlloc_1585_, 17, v_version_1567_);
lean_ctor_set(v_reuseFailAlloc_1585_, 18, v_versionTags_1568_);
lean_ctor_set(v_reuseFailAlloc_1585_, 19, v_description_1569_);
lean_ctor_set(v_reuseFailAlloc_1585_, 20, v_keywords_1570_);
lean_ctor_set(v_reuseFailAlloc_1585_, 21, v_homepage_1571_);
lean_ctor_set(v_reuseFailAlloc_1585_, 22, v_license_1572_);
lean_ctor_set(v_reuseFailAlloc_1585_, 23, v_licenseFiles_1573_);
lean_ctor_set(v_reuseFailAlloc_1585_, 24, v_readmeFile_1574_);
lean_ctor_set(v_reuseFailAlloc_1585_, 25, v_enableArtifactCache_x3f_1576_);
lean_ctor_set(v_reuseFailAlloc_1585_, 26, v_restoreAllArtifacts_x3f_1577_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*27, v_bootstrap_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*27 + 1, v_precompileModules_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*27 + 3, v_reservoir_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*27 + 5, v_allowImportAll_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*27 + 2, v_val_1546_);
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* v_val_1587_, lean_object* v_cfg_1588_){
_start:
{
uint8_t v_val_134__boxed_1589_; lean_object* v_res_1590_; 
v_val_134__boxed_1589_ = lean_unbox(v_val_1587_);
v_res_1590_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(v_val_134__boxed_1589_, v_cfg_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* v_f_1591_, lean_object* v_cfg_1592_){
_start:
{
lean_object* v_toWorkspaceConfig_1593_; lean_object* v_toLeanConfig_1594_; uint8_t v_bootstrap_1595_; lean_object* v_manifestFile_1596_; lean_object* v_extraDepTargets_1597_; uint8_t v_precompileModules_1598_; lean_object* v_moreGlobalServerArgs_1599_; lean_object* v_srcDir_1600_; lean_object* v_buildDir_1601_; lean_object* v_leanLibDir_1602_; lean_object* v_nativeLibDir_1603_; lean_object* v_binDir_1604_; lean_object* v_irDir_1605_; lean_object* v_releaseRepo_1606_; lean_object* v_buildArchive_1607_; uint8_t v_preferReleaseBuild_1608_; lean_object* v_testDriver_1609_; lean_object* v_testDriverArgs_1610_; lean_object* v_lintDriver_1611_; lean_object* v_lintDriverArgs_1612_; lean_object* v_version_1613_; lean_object* v_versionTags_1614_; lean_object* v_description_1615_; lean_object* v_keywords_1616_; lean_object* v_homepage_1617_; lean_object* v_license_1618_; lean_object* v_licenseFiles_1619_; lean_object* v_readmeFile_1620_; uint8_t v_reservoir_1621_; lean_object* v_enableArtifactCache_x3f_1622_; lean_object* v_restoreAllArtifacts_x3f_1623_; uint8_t v_libPrefixOnWindows_1624_; uint8_t v_allowImportAll_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1635_; 
v_toWorkspaceConfig_1593_ = lean_ctor_get(v_cfg_1592_, 0);
v_toLeanConfig_1594_ = lean_ctor_get(v_cfg_1592_, 1);
v_bootstrap_1595_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*27);
v_manifestFile_1596_ = lean_ctor_get(v_cfg_1592_, 2);
v_extraDepTargets_1597_ = lean_ctor_get(v_cfg_1592_, 3);
v_precompileModules_1598_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1599_ = lean_ctor_get(v_cfg_1592_, 4);
v_srcDir_1600_ = lean_ctor_get(v_cfg_1592_, 5);
v_buildDir_1601_ = lean_ctor_get(v_cfg_1592_, 6);
v_leanLibDir_1602_ = lean_ctor_get(v_cfg_1592_, 7);
v_nativeLibDir_1603_ = lean_ctor_get(v_cfg_1592_, 8);
v_binDir_1604_ = lean_ctor_get(v_cfg_1592_, 9);
v_irDir_1605_ = lean_ctor_get(v_cfg_1592_, 10);
v_releaseRepo_1606_ = lean_ctor_get(v_cfg_1592_, 11);
v_buildArchive_1607_ = lean_ctor_get(v_cfg_1592_, 12);
v_preferReleaseBuild_1608_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*27 + 2);
v_testDriver_1609_ = lean_ctor_get(v_cfg_1592_, 13);
v_testDriverArgs_1610_ = lean_ctor_get(v_cfg_1592_, 14);
v_lintDriver_1611_ = lean_ctor_get(v_cfg_1592_, 15);
v_lintDriverArgs_1612_ = lean_ctor_get(v_cfg_1592_, 16);
v_version_1613_ = lean_ctor_get(v_cfg_1592_, 17);
v_versionTags_1614_ = lean_ctor_get(v_cfg_1592_, 18);
v_description_1615_ = lean_ctor_get(v_cfg_1592_, 19);
v_keywords_1616_ = lean_ctor_get(v_cfg_1592_, 20);
v_homepage_1617_ = lean_ctor_get(v_cfg_1592_, 21);
v_license_1618_ = lean_ctor_get(v_cfg_1592_, 22);
v_licenseFiles_1619_ = lean_ctor_get(v_cfg_1592_, 23);
v_readmeFile_1620_ = lean_ctor_get(v_cfg_1592_, 24);
v_reservoir_1621_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1622_ = lean_ctor_get(v_cfg_1592_, 25);
v_restoreAllArtifacts_x3f_1623_ = lean_ctor_get(v_cfg_1592_, 26);
v_libPrefixOnWindows_1624_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*27 + 4);
v_allowImportAll_1625_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*27 + 5);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_cfg_1592_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1627_ = v_cfg_1592_;
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1623_);
lean_inc(v_enableArtifactCache_x3f_1622_);
lean_inc(v_readmeFile_1620_);
lean_inc(v_licenseFiles_1619_);
lean_inc(v_license_1618_);
lean_inc(v_homepage_1617_);
lean_inc(v_keywords_1616_);
lean_inc(v_description_1615_);
lean_inc(v_versionTags_1614_);
lean_inc(v_version_1613_);
lean_inc(v_lintDriverArgs_1612_);
lean_inc(v_lintDriver_1611_);
lean_inc(v_testDriverArgs_1610_);
lean_inc(v_testDriver_1609_);
lean_inc(v_buildArchive_1607_);
lean_inc(v_releaseRepo_1606_);
lean_inc(v_irDir_1605_);
lean_inc(v_binDir_1604_);
lean_inc(v_nativeLibDir_1603_);
lean_inc(v_leanLibDir_1602_);
lean_inc(v_buildDir_1601_);
lean_inc(v_srcDir_1600_);
lean_inc(v_moreGlobalServerArgs_1599_);
lean_inc(v_extraDepTargets_1597_);
lean_inc(v_manifestFile_1596_);
lean_inc(v_toLeanConfig_1594_);
lean_inc(v_toWorkspaceConfig_1593_);
lean_dec(v_cfg_1592_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1629_ = lean_box(v_preferReleaseBuild_1608_);
v___x_1630_ = lean_apply_1(v_f_1591_, v___x_1629_);
if (v_isShared_1628_ == 0)
{
v___x_1632_ = v___x_1627_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_toWorkspaceConfig_1593_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_toLeanConfig_1594_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_manifestFile_1596_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_extraDepTargets_1597_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_moreGlobalServerArgs_1599_);
lean_ctor_set(v_reuseFailAlloc_1634_, 5, v_srcDir_1600_);
lean_ctor_set(v_reuseFailAlloc_1634_, 6, v_buildDir_1601_);
lean_ctor_set(v_reuseFailAlloc_1634_, 7, v_leanLibDir_1602_);
lean_ctor_set(v_reuseFailAlloc_1634_, 8, v_nativeLibDir_1603_);
lean_ctor_set(v_reuseFailAlloc_1634_, 9, v_binDir_1604_);
lean_ctor_set(v_reuseFailAlloc_1634_, 10, v_irDir_1605_);
lean_ctor_set(v_reuseFailAlloc_1634_, 11, v_releaseRepo_1606_);
lean_ctor_set(v_reuseFailAlloc_1634_, 12, v_buildArchive_1607_);
lean_ctor_set(v_reuseFailAlloc_1634_, 13, v_testDriver_1609_);
lean_ctor_set(v_reuseFailAlloc_1634_, 14, v_testDriverArgs_1610_);
lean_ctor_set(v_reuseFailAlloc_1634_, 15, v_lintDriver_1611_);
lean_ctor_set(v_reuseFailAlloc_1634_, 16, v_lintDriverArgs_1612_);
lean_ctor_set(v_reuseFailAlloc_1634_, 17, v_version_1613_);
lean_ctor_set(v_reuseFailAlloc_1634_, 18, v_versionTags_1614_);
lean_ctor_set(v_reuseFailAlloc_1634_, 19, v_description_1615_);
lean_ctor_set(v_reuseFailAlloc_1634_, 20, v_keywords_1616_);
lean_ctor_set(v_reuseFailAlloc_1634_, 21, v_homepage_1617_);
lean_ctor_set(v_reuseFailAlloc_1634_, 22, v_license_1618_);
lean_ctor_set(v_reuseFailAlloc_1634_, 23, v_licenseFiles_1619_);
lean_ctor_set(v_reuseFailAlloc_1634_, 24, v_readmeFile_1620_);
lean_ctor_set(v_reuseFailAlloc_1634_, 25, v_enableArtifactCache_x3f_1622_);
lean_ctor_set(v_reuseFailAlloc_1634_, 26, v_restoreAllArtifacts_x3f_1623_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*27, v_bootstrap_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*27 + 1, v_precompileModules_1598_);
v___x_1632_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_unbox(v___x_1630_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*27 + 2, v___x_1633_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*27 + 3, v_reservoir_1621_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1624_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*27 + 5, v_allowImportAll_1625_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1644_, lean_object* v_n_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1647_, lean_object* v_n_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1647_, v_n_1648_);
lean_dec(v_n_1648_);
lean_dec(v_p_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1650_, lean_object* v_n_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1650_, v_n_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1653_, lean_object* v_n_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1653_, v_n_1654_);
lean_dec(v_n_1654_);
lean_dec(v_p_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* v_cfg_1656_){
_start:
{
lean_object* v_testDriver_1657_; 
v_testDriver_1657_ = lean_ctor_get(v_cfg_1656_, 13);
lean_inc_ref(v_testDriver_1657_);
return v_testDriver_1657_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* v_cfg_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lake_PackageConfig_testDriver___proj___lam__0(v_cfg_1658_);
lean_dec_ref(v_cfg_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* v_val_1660_, lean_object* v_cfg_1661_){
_start:
{
lean_object* v_toWorkspaceConfig_1662_; lean_object* v_toLeanConfig_1663_; uint8_t v_bootstrap_1664_; lean_object* v_manifestFile_1665_; lean_object* v_extraDepTargets_1666_; uint8_t v_precompileModules_1667_; lean_object* v_moreGlobalServerArgs_1668_; lean_object* v_srcDir_1669_; lean_object* v_buildDir_1670_; lean_object* v_leanLibDir_1671_; lean_object* v_nativeLibDir_1672_; lean_object* v_binDir_1673_; lean_object* v_irDir_1674_; lean_object* v_releaseRepo_1675_; lean_object* v_buildArchive_1676_; uint8_t v_preferReleaseBuild_1677_; lean_object* v_testDriverArgs_1678_; lean_object* v_lintDriver_1679_; lean_object* v_lintDriverArgs_1680_; lean_object* v_version_1681_; lean_object* v_versionTags_1682_; lean_object* v_description_1683_; lean_object* v_keywords_1684_; lean_object* v_homepage_1685_; lean_object* v_license_1686_; lean_object* v_licenseFiles_1687_; lean_object* v_readmeFile_1688_; uint8_t v_reservoir_1689_; lean_object* v_enableArtifactCache_x3f_1690_; lean_object* v_restoreAllArtifacts_x3f_1691_; uint8_t v_libPrefixOnWindows_1692_; uint8_t v_allowImportAll_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_toWorkspaceConfig_1662_ = lean_ctor_get(v_cfg_1661_, 0);
v_toLeanConfig_1663_ = lean_ctor_get(v_cfg_1661_, 1);
v_bootstrap_1664_ = lean_ctor_get_uint8(v_cfg_1661_, sizeof(void*)*27);
v_manifestFile_1665_ = lean_ctor_get(v_cfg_1661_, 2);
v_extraDepTargets_1666_ = lean_ctor_get(v_cfg_1661_, 3);
v_precompileModules_1667_ = lean_ctor_get_uint8(v_cfg_1661_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1668_ = lean_ctor_get(v_cfg_1661_, 4);
v_srcDir_1669_ = lean_ctor_get(v_cfg_1661_, 5);
v_buildDir_1670_ = lean_ctor_get(v_cfg_1661_, 6);
v_leanLibDir_1671_ = lean_ctor_get(v_cfg_1661_, 7);
v_nativeLibDir_1672_ = lean_ctor_get(v_cfg_1661_, 8);
v_binDir_1673_ = lean_ctor_get(v_cfg_1661_, 9);
v_irDir_1674_ = lean_ctor_get(v_cfg_1661_, 10);
v_releaseRepo_1675_ = lean_ctor_get(v_cfg_1661_, 11);
v_buildArchive_1676_ = lean_ctor_get(v_cfg_1661_, 12);
v_preferReleaseBuild_1677_ = lean_ctor_get_uint8(v_cfg_1661_, sizeof(void*)*27 + 2);
v_testDriverArgs_1678_ = lean_ctor_get(v_cfg_1661_, 14);
v_lintDriver_1679_ = lean_ctor_get(v_cfg_1661_, 15);
v_lintDriverArgs_1680_ = lean_ctor_get(v_cfg_1661_, 16);
v_version_1681_ = lean_ctor_get(v_cfg_1661_, 17);
v_versionTags_1682_ = lean_ctor_get(v_cfg_1661_, 18);
v_description_1683_ = lean_ctor_get(v_cfg_1661_, 19);
v_keywords_1684_ = lean_ctor_get(v_cfg_1661_, 20);
v_homepage_1685_ = lean_ctor_get(v_cfg_1661_, 21);
v_license_1686_ = lean_ctor_get(v_cfg_1661_, 22);
v_licenseFiles_1687_ = lean_ctor_get(v_cfg_1661_, 23);
v_readmeFile_1688_ = lean_ctor_get(v_cfg_1661_, 24);
v_reservoir_1689_ = lean_ctor_get_uint8(v_cfg_1661_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1690_ = lean_ctor_get(v_cfg_1661_, 25);
v_restoreAllArtifacts_x3f_1691_ = lean_ctor_get(v_cfg_1661_, 26);
v_libPrefixOnWindows_1692_ = lean_ctor_get_uint8(v_cfg_1661_, sizeof(void*)*27 + 4);
v_allowImportAll_1693_ = lean_ctor_get_uint8(v_cfg_1661_, sizeof(void*)*27 + 5);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_cfg_1661_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_cfg_1661_, 13);
lean_dec(v_unused_1701_);
v___x_1695_ = v_cfg_1661_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1691_);
lean_inc(v_enableArtifactCache_x3f_1690_);
lean_inc(v_readmeFile_1688_);
lean_inc(v_licenseFiles_1687_);
lean_inc(v_license_1686_);
lean_inc(v_homepage_1685_);
lean_inc(v_keywords_1684_);
lean_inc(v_description_1683_);
lean_inc(v_versionTags_1682_);
lean_inc(v_version_1681_);
lean_inc(v_lintDriverArgs_1680_);
lean_inc(v_lintDriver_1679_);
lean_inc(v_testDriverArgs_1678_);
lean_inc(v_buildArchive_1676_);
lean_inc(v_releaseRepo_1675_);
lean_inc(v_irDir_1674_);
lean_inc(v_binDir_1673_);
lean_inc(v_nativeLibDir_1672_);
lean_inc(v_leanLibDir_1671_);
lean_inc(v_buildDir_1670_);
lean_inc(v_srcDir_1669_);
lean_inc(v_moreGlobalServerArgs_1668_);
lean_inc(v_extraDepTargets_1666_);
lean_inc(v_manifestFile_1665_);
lean_inc(v_toLeanConfig_1663_);
lean_inc(v_toWorkspaceConfig_1662_);
lean_dec(v_cfg_1661_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 13, v_val_1660_);
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_toWorkspaceConfig_1662_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_toLeanConfig_1663_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_manifestFile_1665_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_extraDepTargets_1666_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_moreGlobalServerArgs_1668_);
lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_srcDir_1669_);
lean_ctor_set(v_reuseFailAlloc_1699_, 6, v_buildDir_1670_);
lean_ctor_set(v_reuseFailAlloc_1699_, 7, v_leanLibDir_1671_);
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v_nativeLibDir_1672_);
lean_ctor_set(v_reuseFailAlloc_1699_, 9, v_binDir_1673_);
lean_ctor_set(v_reuseFailAlloc_1699_, 10, v_irDir_1674_);
lean_ctor_set(v_reuseFailAlloc_1699_, 11, v_releaseRepo_1675_);
lean_ctor_set(v_reuseFailAlloc_1699_, 12, v_buildArchive_1676_);
lean_ctor_set(v_reuseFailAlloc_1699_, 13, v_val_1660_);
lean_ctor_set(v_reuseFailAlloc_1699_, 14, v_testDriverArgs_1678_);
lean_ctor_set(v_reuseFailAlloc_1699_, 15, v_lintDriver_1679_);
lean_ctor_set(v_reuseFailAlloc_1699_, 16, v_lintDriverArgs_1680_);
lean_ctor_set(v_reuseFailAlloc_1699_, 17, v_version_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 18, v_versionTags_1682_);
lean_ctor_set(v_reuseFailAlloc_1699_, 19, v_description_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 20, v_keywords_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 21, v_homepage_1685_);
lean_ctor_set(v_reuseFailAlloc_1699_, 22, v_license_1686_);
lean_ctor_set(v_reuseFailAlloc_1699_, 23, v_licenseFiles_1687_);
lean_ctor_set(v_reuseFailAlloc_1699_, 24, v_readmeFile_1688_);
lean_ctor_set(v_reuseFailAlloc_1699_, 25, v_enableArtifactCache_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 26, v_restoreAllArtifacts_x3f_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*27, v_bootstrap_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*27 + 1, v_precompileModules_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*27 + 3, v_reservoir_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*27 + 5, v_allowImportAll_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* v_f_1702_, lean_object* v_cfg_1703_){
_start:
{
lean_object* v_toWorkspaceConfig_1704_; lean_object* v_toLeanConfig_1705_; uint8_t v_bootstrap_1706_; lean_object* v_manifestFile_1707_; lean_object* v_extraDepTargets_1708_; uint8_t v_precompileModules_1709_; lean_object* v_moreGlobalServerArgs_1710_; lean_object* v_srcDir_1711_; lean_object* v_buildDir_1712_; lean_object* v_leanLibDir_1713_; lean_object* v_nativeLibDir_1714_; lean_object* v_binDir_1715_; lean_object* v_irDir_1716_; lean_object* v_releaseRepo_1717_; lean_object* v_buildArchive_1718_; uint8_t v_preferReleaseBuild_1719_; lean_object* v_testDriver_1720_; lean_object* v_testDriverArgs_1721_; lean_object* v_lintDriver_1722_; lean_object* v_lintDriverArgs_1723_; lean_object* v_version_1724_; lean_object* v_versionTags_1725_; lean_object* v_description_1726_; lean_object* v_keywords_1727_; lean_object* v_homepage_1728_; lean_object* v_license_1729_; lean_object* v_licenseFiles_1730_; lean_object* v_readmeFile_1731_; uint8_t v_reservoir_1732_; lean_object* v_enableArtifactCache_x3f_1733_; lean_object* v_restoreAllArtifacts_x3f_1734_; uint8_t v_libPrefixOnWindows_1735_; uint8_t v_allowImportAll_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1744_; 
v_toWorkspaceConfig_1704_ = lean_ctor_get(v_cfg_1703_, 0);
v_toLeanConfig_1705_ = lean_ctor_get(v_cfg_1703_, 1);
v_bootstrap_1706_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*27);
v_manifestFile_1707_ = lean_ctor_get(v_cfg_1703_, 2);
v_extraDepTargets_1708_ = lean_ctor_get(v_cfg_1703_, 3);
v_precompileModules_1709_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1710_ = lean_ctor_get(v_cfg_1703_, 4);
v_srcDir_1711_ = lean_ctor_get(v_cfg_1703_, 5);
v_buildDir_1712_ = lean_ctor_get(v_cfg_1703_, 6);
v_leanLibDir_1713_ = lean_ctor_get(v_cfg_1703_, 7);
v_nativeLibDir_1714_ = lean_ctor_get(v_cfg_1703_, 8);
v_binDir_1715_ = lean_ctor_get(v_cfg_1703_, 9);
v_irDir_1716_ = lean_ctor_get(v_cfg_1703_, 10);
v_releaseRepo_1717_ = lean_ctor_get(v_cfg_1703_, 11);
v_buildArchive_1718_ = lean_ctor_get(v_cfg_1703_, 12);
v_preferReleaseBuild_1719_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*27 + 2);
v_testDriver_1720_ = lean_ctor_get(v_cfg_1703_, 13);
v_testDriverArgs_1721_ = lean_ctor_get(v_cfg_1703_, 14);
v_lintDriver_1722_ = lean_ctor_get(v_cfg_1703_, 15);
v_lintDriverArgs_1723_ = lean_ctor_get(v_cfg_1703_, 16);
v_version_1724_ = lean_ctor_get(v_cfg_1703_, 17);
v_versionTags_1725_ = lean_ctor_get(v_cfg_1703_, 18);
v_description_1726_ = lean_ctor_get(v_cfg_1703_, 19);
v_keywords_1727_ = lean_ctor_get(v_cfg_1703_, 20);
v_homepage_1728_ = lean_ctor_get(v_cfg_1703_, 21);
v_license_1729_ = lean_ctor_get(v_cfg_1703_, 22);
v_licenseFiles_1730_ = lean_ctor_get(v_cfg_1703_, 23);
v_readmeFile_1731_ = lean_ctor_get(v_cfg_1703_, 24);
v_reservoir_1732_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1733_ = lean_ctor_get(v_cfg_1703_, 25);
v_restoreAllArtifacts_x3f_1734_ = lean_ctor_get(v_cfg_1703_, 26);
v_libPrefixOnWindows_1735_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*27 + 4);
v_allowImportAll_1736_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*27 + 5);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_cfg_1703_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1738_ = v_cfg_1703_;
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1734_);
lean_inc(v_enableArtifactCache_x3f_1733_);
lean_inc(v_readmeFile_1731_);
lean_inc(v_licenseFiles_1730_);
lean_inc(v_license_1729_);
lean_inc(v_homepage_1728_);
lean_inc(v_keywords_1727_);
lean_inc(v_description_1726_);
lean_inc(v_versionTags_1725_);
lean_inc(v_version_1724_);
lean_inc(v_lintDriverArgs_1723_);
lean_inc(v_lintDriver_1722_);
lean_inc(v_testDriverArgs_1721_);
lean_inc(v_testDriver_1720_);
lean_inc(v_buildArchive_1718_);
lean_inc(v_releaseRepo_1717_);
lean_inc(v_irDir_1716_);
lean_inc(v_binDir_1715_);
lean_inc(v_nativeLibDir_1714_);
lean_inc(v_leanLibDir_1713_);
lean_inc(v_buildDir_1712_);
lean_inc(v_srcDir_1711_);
lean_inc(v_moreGlobalServerArgs_1710_);
lean_inc(v_extraDepTargets_1708_);
lean_inc(v_manifestFile_1707_);
lean_inc(v_toLeanConfig_1705_);
lean_inc(v_toWorkspaceConfig_1704_);
lean_dec(v_cfg_1703_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_apply_1(v_f_1702_, v_testDriver_1720_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 13, v___x_1740_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_toWorkspaceConfig_1704_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_toLeanConfig_1705_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_manifestFile_1707_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_extraDepTargets_1708_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_moreGlobalServerArgs_1710_);
lean_ctor_set(v_reuseFailAlloc_1743_, 5, v_srcDir_1711_);
lean_ctor_set(v_reuseFailAlloc_1743_, 6, v_buildDir_1712_);
lean_ctor_set(v_reuseFailAlloc_1743_, 7, v_leanLibDir_1713_);
lean_ctor_set(v_reuseFailAlloc_1743_, 8, v_nativeLibDir_1714_);
lean_ctor_set(v_reuseFailAlloc_1743_, 9, v_binDir_1715_);
lean_ctor_set(v_reuseFailAlloc_1743_, 10, v_irDir_1716_);
lean_ctor_set(v_reuseFailAlloc_1743_, 11, v_releaseRepo_1717_);
lean_ctor_set(v_reuseFailAlloc_1743_, 12, v_buildArchive_1718_);
lean_ctor_set(v_reuseFailAlloc_1743_, 13, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1743_, 14, v_testDriverArgs_1721_);
lean_ctor_set(v_reuseFailAlloc_1743_, 15, v_lintDriver_1722_);
lean_ctor_set(v_reuseFailAlloc_1743_, 16, v_lintDriverArgs_1723_);
lean_ctor_set(v_reuseFailAlloc_1743_, 17, v_version_1724_);
lean_ctor_set(v_reuseFailAlloc_1743_, 18, v_versionTags_1725_);
lean_ctor_set(v_reuseFailAlloc_1743_, 19, v_description_1726_);
lean_ctor_set(v_reuseFailAlloc_1743_, 20, v_keywords_1727_);
lean_ctor_set(v_reuseFailAlloc_1743_, 21, v_homepage_1728_);
lean_ctor_set(v_reuseFailAlloc_1743_, 22, v_license_1729_);
lean_ctor_set(v_reuseFailAlloc_1743_, 23, v_licenseFiles_1730_);
lean_ctor_set(v_reuseFailAlloc_1743_, 24, v_readmeFile_1731_);
lean_ctor_set(v_reuseFailAlloc_1743_, 25, v_enableArtifactCache_x3f_1733_);
lean_ctor_set(v_reuseFailAlloc_1743_, 26, v_restoreAllArtifacts_x3f_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*27, v_bootstrap_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*27 + 1, v_precompileModules_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*27 + 3, v_reservoir_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*27 + 5, v_allowImportAll_1736_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* v_x_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* v_x_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lake_PackageConfig_testDriver___proj___lam__3(v_x_1747_);
lean_dec_ref(v_x_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1758_, lean_object* v_n_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1761_, lean_object* v_n_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lake_PackageConfig_testDriver___proj(v_p_1761_, v_n_1762_);
lean_dec(v_n_1762_);
lean_dec(v_p_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1764_, lean_object* v_n_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lake_PackageConfig_testDriver___proj(v_p_1764_, v_n_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1767_, lean_object* v_n_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1767_, v_n_1768_);
lean_dec(v_n_1768_);
lean_dec(v_p_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1770_, lean_object* v_n_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lake_PackageConfig_testDriver___proj(v_p_1770_, v_n_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1773_, lean_object* v_n_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1773_, v_n_1774_);
lean_dec(v_n_1774_);
lean_dec(v_p_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* v_cfg_1776_){
_start:
{
lean_object* v_testDriverArgs_1777_; 
v_testDriverArgs_1777_ = lean_ctor_get(v_cfg_1776_, 14);
lean_inc_ref(v_testDriverArgs_1777_);
return v_testDriverArgs_1777_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(v_cfg_1778_);
lean_dec_ref(v_cfg_1778_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* v_val_1780_, lean_object* v_cfg_1781_){
_start:
{
lean_object* v_toWorkspaceConfig_1782_; lean_object* v_toLeanConfig_1783_; uint8_t v_bootstrap_1784_; lean_object* v_manifestFile_1785_; lean_object* v_extraDepTargets_1786_; uint8_t v_precompileModules_1787_; lean_object* v_moreGlobalServerArgs_1788_; lean_object* v_srcDir_1789_; lean_object* v_buildDir_1790_; lean_object* v_leanLibDir_1791_; lean_object* v_nativeLibDir_1792_; lean_object* v_binDir_1793_; lean_object* v_irDir_1794_; lean_object* v_releaseRepo_1795_; lean_object* v_buildArchive_1796_; uint8_t v_preferReleaseBuild_1797_; lean_object* v_testDriver_1798_; lean_object* v_lintDriver_1799_; lean_object* v_lintDriverArgs_1800_; lean_object* v_version_1801_; lean_object* v_versionTags_1802_; lean_object* v_description_1803_; lean_object* v_keywords_1804_; lean_object* v_homepage_1805_; lean_object* v_license_1806_; lean_object* v_licenseFiles_1807_; lean_object* v_readmeFile_1808_; uint8_t v_reservoir_1809_; lean_object* v_enableArtifactCache_x3f_1810_; lean_object* v_restoreAllArtifacts_x3f_1811_; uint8_t v_libPrefixOnWindows_1812_; uint8_t v_allowImportAll_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_toWorkspaceConfig_1782_ = lean_ctor_get(v_cfg_1781_, 0);
v_toLeanConfig_1783_ = lean_ctor_get(v_cfg_1781_, 1);
v_bootstrap_1784_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*27);
v_manifestFile_1785_ = lean_ctor_get(v_cfg_1781_, 2);
v_extraDepTargets_1786_ = lean_ctor_get(v_cfg_1781_, 3);
v_precompileModules_1787_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1788_ = lean_ctor_get(v_cfg_1781_, 4);
v_srcDir_1789_ = lean_ctor_get(v_cfg_1781_, 5);
v_buildDir_1790_ = lean_ctor_get(v_cfg_1781_, 6);
v_leanLibDir_1791_ = lean_ctor_get(v_cfg_1781_, 7);
v_nativeLibDir_1792_ = lean_ctor_get(v_cfg_1781_, 8);
v_binDir_1793_ = lean_ctor_get(v_cfg_1781_, 9);
v_irDir_1794_ = lean_ctor_get(v_cfg_1781_, 10);
v_releaseRepo_1795_ = lean_ctor_get(v_cfg_1781_, 11);
v_buildArchive_1796_ = lean_ctor_get(v_cfg_1781_, 12);
v_preferReleaseBuild_1797_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*27 + 2);
v_testDriver_1798_ = lean_ctor_get(v_cfg_1781_, 13);
v_lintDriver_1799_ = lean_ctor_get(v_cfg_1781_, 15);
v_lintDriverArgs_1800_ = lean_ctor_get(v_cfg_1781_, 16);
v_version_1801_ = lean_ctor_get(v_cfg_1781_, 17);
v_versionTags_1802_ = lean_ctor_get(v_cfg_1781_, 18);
v_description_1803_ = lean_ctor_get(v_cfg_1781_, 19);
v_keywords_1804_ = lean_ctor_get(v_cfg_1781_, 20);
v_homepage_1805_ = lean_ctor_get(v_cfg_1781_, 21);
v_license_1806_ = lean_ctor_get(v_cfg_1781_, 22);
v_licenseFiles_1807_ = lean_ctor_get(v_cfg_1781_, 23);
v_readmeFile_1808_ = lean_ctor_get(v_cfg_1781_, 24);
v_reservoir_1809_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1810_ = lean_ctor_get(v_cfg_1781_, 25);
v_restoreAllArtifacts_x3f_1811_ = lean_ctor_get(v_cfg_1781_, 26);
v_libPrefixOnWindows_1812_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*27 + 4);
v_allowImportAll_1813_ = lean_ctor_get_uint8(v_cfg_1781_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_1811_);
lean_inc(v_enableArtifactCache_x3f_1810_);
lean_inc(v_readmeFile_1808_);
lean_inc(v_licenseFiles_1807_);
lean_inc(v_license_1806_);
lean_inc(v_homepage_1805_);
lean_inc(v_keywords_1804_);
lean_inc(v_description_1803_);
lean_inc(v_versionTags_1802_);
lean_inc(v_version_1801_);
lean_inc(v_lintDriverArgs_1800_);
lean_inc(v_lintDriver_1799_);
lean_inc(v_testDriver_1798_);
lean_inc(v_buildArchive_1796_);
lean_inc(v_releaseRepo_1795_);
lean_inc(v_irDir_1794_);
lean_inc(v_binDir_1793_);
lean_inc(v_nativeLibDir_1792_);
lean_inc(v_leanLibDir_1791_);
lean_inc(v_buildDir_1790_);
lean_inc(v_srcDir_1789_);
lean_inc(v_moreGlobalServerArgs_1788_);
lean_inc(v_extraDepTargets_1786_);
lean_inc(v_manifestFile_1785_);
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
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_toWorkspaceConfig_1782_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_toLeanConfig_1783_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_manifestFile_1785_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_extraDepTargets_1786_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_moreGlobalServerArgs_1788_);
lean_ctor_set(v_reuseFailAlloc_1819_, 5, v_srcDir_1789_);
lean_ctor_set(v_reuseFailAlloc_1819_, 6, v_buildDir_1790_);
lean_ctor_set(v_reuseFailAlloc_1819_, 7, v_leanLibDir_1791_);
lean_ctor_set(v_reuseFailAlloc_1819_, 8, v_nativeLibDir_1792_);
lean_ctor_set(v_reuseFailAlloc_1819_, 9, v_binDir_1793_);
lean_ctor_set(v_reuseFailAlloc_1819_, 10, v_irDir_1794_);
lean_ctor_set(v_reuseFailAlloc_1819_, 11, v_releaseRepo_1795_);
lean_ctor_set(v_reuseFailAlloc_1819_, 12, v_buildArchive_1796_);
lean_ctor_set(v_reuseFailAlloc_1819_, 13, v_testDriver_1798_);
lean_ctor_set(v_reuseFailAlloc_1819_, 14, v_val_1780_);
lean_ctor_set(v_reuseFailAlloc_1819_, 15, v_lintDriver_1799_);
lean_ctor_set(v_reuseFailAlloc_1819_, 16, v_lintDriverArgs_1800_);
lean_ctor_set(v_reuseFailAlloc_1819_, 17, v_version_1801_);
lean_ctor_set(v_reuseFailAlloc_1819_, 18, v_versionTags_1802_);
lean_ctor_set(v_reuseFailAlloc_1819_, 19, v_description_1803_);
lean_ctor_set(v_reuseFailAlloc_1819_, 20, v_keywords_1804_);
lean_ctor_set(v_reuseFailAlloc_1819_, 21, v_homepage_1805_);
lean_ctor_set(v_reuseFailAlloc_1819_, 22, v_license_1806_);
lean_ctor_set(v_reuseFailAlloc_1819_, 23, v_licenseFiles_1807_);
lean_ctor_set(v_reuseFailAlloc_1819_, 24, v_readmeFile_1808_);
lean_ctor_set(v_reuseFailAlloc_1819_, 25, v_enableArtifactCache_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1819_, 26, v_restoreAllArtifacts_x3f_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*27, v_bootstrap_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*27 + 1, v_precompileModules_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*27 + 3, v_reservoir_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*27 + 5, v_allowImportAll_1813_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* v_f_1822_, lean_object* v_cfg_1823_){
_start:
{
lean_object* v_toWorkspaceConfig_1824_; lean_object* v_toLeanConfig_1825_; uint8_t v_bootstrap_1826_; lean_object* v_manifestFile_1827_; lean_object* v_extraDepTargets_1828_; uint8_t v_precompileModules_1829_; lean_object* v_moreGlobalServerArgs_1830_; lean_object* v_srcDir_1831_; lean_object* v_buildDir_1832_; lean_object* v_leanLibDir_1833_; lean_object* v_nativeLibDir_1834_; lean_object* v_binDir_1835_; lean_object* v_irDir_1836_; lean_object* v_releaseRepo_1837_; lean_object* v_buildArchive_1838_; uint8_t v_preferReleaseBuild_1839_; lean_object* v_testDriver_1840_; lean_object* v_testDriverArgs_1841_; lean_object* v_lintDriver_1842_; lean_object* v_lintDriverArgs_1843_; lean_object* v_version_1844_; lean_object* v_versionTags_1845_; lean_object* v_description_1846_; lean_object* v_keywords_1847_; lean_object* v_homepage_1848_; lean_object* v_license_1849_; lean_object* v_licenseFiles_1850_; lean_object* v_readmeFile_1851_; uint8_t v_reservoir_1852_; lean_object* v_enableArtifactCache_x3f_1853_; lean_object* v_restoreAllArtifacts_x3f_1854_; uint8_t v_libPrefixOnWindows_1855_; uint8_t v_allowImportAll_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
v_toWorkspaceConfig_1824_ = lean_ctor_get(v_cfg_1823_, 0);
v_toLeanConfig_1825_ = lean_ctor_get(v_cfg_1823_, 1);
v_bootstrap_1826_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*27);
v_manifestFile_1827_ = lean_ctor_get(v_cfg_1823_, 2);
v_extraDepTargets_1828_ = lean_ctor_get(v_cfg_1823_, 3);
v_precompileModules_1829_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1830_ = lean_ctor_get(v_cfg_1823_, 4);
v_srcDir_1831_ = lean_ctor_get(v_cfg_1823_, 5);
v_buildDir_1832_ = lean_ctor_get(v_cfg_1823_, 6);
v_leanLibDir_1833_ = lean_ctor_get(v_cfg_1823_, 7);
v_nativeLibDir_1834_ = lean_ctor_get(v_cfg_1823_, 8);
v_binDir_1835_ = lean_ctor_get(v_cfg_1823_, 9);
v_irDir_1836_ = lean_ctor_get(v_cfg_1823_, 10);
v_releaseRepo_1837_ = lean_ctor_get(v_cfg_1823_, 11);
v_buildArchive_1838_ = lean_ctor_get(v_cfg_1823_, 12);
v_preferReleaseBuild_1839_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*27 + 2);
v_testDriver_1840_ = lean_ctor_get(v_cfg_1823_, 13);
v_testDriverArgs_1841_ = lean_ctor_get(v_cfg_1823_, 14);
v_lintDriver_1842_ = lean_ctor_get(v_cfg_1823_, 15);
v_lintDriverArgs_1843_ = lean_ctor_get(v_cfg_1823_, 16);
v_version_1844_ = lean_ctor_get(v_cfg_1823_, 17);
v_versionTags_1845_ = lean_ctor_get(v_cfg_1823_, 18);
v_description_1846_ = lean_ctor_get(v_cfg_1823_, 19);
v_keywords_1847_ = lean_ctor_get(v_cfg_1823_, 20);
v_homepage_1848_ = lean_ctor_get(v_cfg_1823_, 21);
v_license_1849_ = lean_ctor_get(v_cfg_1823_, 22);
v_licenseFiles_1850_ = lean_ctor_get(v_cfg_1823_, 23);
v_readmeFile_1851_ = lean_ctor_get(v_cfg_1823_, 24);
v_reservoir_1852_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1853_ = lean_ctor_get(v_cfg_1823_, 25);
v_restoreAllArtifacts_x3f_1854_ = lean_ctor_get(v_cfg_1823_, 26);
v_libPrefixOnWindows_1855_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*27 + 4);
v_allowImportAll_1856_ = lean_ctor_get_uint8(v_cfg_1823_, sizeof(void*)*27 + 5);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_cfg_1823_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v_cfg_1823_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1854_);
lean_inc(v_enableArtifactCache_x3f_1853_);
lean_inc(v_readmeFile_1851_);
lean_inc(v_licenseFiles_1850_);
lean_inc(v_license_1849_);
lean_inc(v_homepage_1848_);
lean_inc(v_keywords_1847_);
lean_inc(v_description_1846_);
lean_inc(v_versionTags_1845_);
lean_inc(v_version_1844_);
lean_inc(v_lintDriverArgs_1843_);
lean_inc(v_lintDriver_1842_);
lean_inc(v_testDriverArgs_1841_);
lean_inc(v_testDriver_1840_);
lean_inc(v_buildArchive_1838_);
lean_inc(v_releaseRepo_1837_);
lean_inc(v_irDir_1836_);
lean_inc(v_binDir_1835_);
lean_inc(v_nativeLibDir_1834_);
lean_inc(v_leanLibDir_1833_);
lean_inc(v_buildDir_1832_);
lean_inc(v_srcDir_1831_);
lean_inc(v_moreGlobalServerArgs_1830_);
lean_inc(v_extraDepTargets_1828_);
lean_inc(v_manifestFile_1827_);
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
v___x_1860_ = lean_apply_1(v_f_1822_, v_testDriverArgs_1841_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 14, v___x_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_toWorkspaceConfig_1824_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_toLeanConfig_1825_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_manifestFile_1827_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_extraDepTargets_1828_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_moreGlobalServerArgs_1830_);
lean_ctor_set(v_reuseFailAlloc_1863_, 5, v_srcDir_1831_);
lean_ctor_set(v_reuseFailAlloc_1863_, 6, v_buildDir_1832_);
lean_ctor_set(v_reuseFailAlloc_1863_, 7, v_leanLibDir_1833_);
lean_ctor_set(v_reuseFailAlloc_1863_, 8, v_nativeLibDir_1834_);
lean_ctor_set(v_reuseFailAlloc_1863_, 9, v_binDir_1835_);
lean_ctor_set(v_reuseFailAlloc_1863_, 10, v_irDir_1836_);
lean_ctor_set(v_reuseFailAlloc_1863_, 11, v_releaseRepo_1837_);
lean_ctor_set(v_reuseFailAlloc_1863_, 12, v_buildArchive_1838_);
lean_ctor_set(v_reuseFailAlloc_1863_, 13, v_testDriver_1840_);
lean_ctor_set(v_reuseFailAlloc_1863_, 14, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1863_, 15, v_lintDriver_1842_);
lean_ctor_set(v_reuseFailAlloc_1863_, 16, v_lintDriverArgs_1843_);
lean_ctor_set(v_reuseFailAlloc_1863_, 17, v_version_1844_);
lean_ctor_set(v_reuseFailAlloc_1863_, 18, v_versionTags_1845_);
lean_ctor_set(v_reuseFailAlloc_1863_, 19, v_description_1846_);
lean_ctor_set(v_reuseFailAlloc_1863_, 20, v_keywords_1847_);
lean_ctor_set(v_reuseFailAlloc_1863_, 21, v_homepage_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 22, v_license_1849_);
lean_ctor_set(v_reuseFailAlloc_1863_, 23, v_licenseFiles_1850_);
lean_ctor_set(v_reuseFailAlloc_1863_, 24, v_readmeFile_1851_);
lean_ctor_set(v_reuseFailAlloc_1863_, 25, v_enableArtifactCache_x3f_1853_);
lean_ctor_set(v_reuseFailAlloc_1863_, 26, v_restoreAllArtifacts_x3f_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*27, v_bootstrap_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*27 + 1, v_precompileModules_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*27 + 3, v_reservoir_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*27 + 5, v_allowImportAll_1856_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1873_, lean_object* v_n_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1876_, lean_object* v_n_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1876_, v_n_1877_);
lean_dec(v_n_1877_);
lean_dec(v_p_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_1879_, lean_object* v_n_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1879_, v_n_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_1882_, lean_object* v_n_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_1882_, v_n_1883_);
lean_dec(v_n_1883_);
lean_dec(v_p_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* v_cfg_1885_){
_start:
{
lean_object* v_lintDriver_1886_; 
v_lintDriver_1886_ = lean_ctor_get(v_cfg_1885_, 15);
lean_inc_ref(v_lintDriver_1886_);
return v_lintDriver_1886_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* v_cfg_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lake_PackageConfig_lintDriver___proj___lam__0(v_cfg_1887_);
lean_dec_ref(v_cfg_1887_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* v_val_1889_, lean_object* v_cfg_1890_){
_start:
{
lean_object* v_toWorkspaceConfig_1891_; lean_object* v_toLeanConfig_1892_; uint8_t v_bootstrap_1893_; lean_object* v_manifestFile_1894_; lean_object* v_extraDepTargets_1895_; uint8_t v_precompileModules_1896_; lean_object* v_moreGlobalServerArgs_1897_; lean_object* v_srcDir_1898_; lean_object* v_buildDir_1899_; lean_object* v_leanLibDir_1900_; lean_object* v_nativeLibDir_1901_; lean_object* v_binDir_1902_; lean_object* v_irDir_1903_; lean_object* v_releaseRepo_1904_; lean_object* v_buildArchive_1905_; uint8_t v_preferReleaseBuild_1906_; lean_object* v_testDriver_1907_; lean_object* v_testDriverArgs_1908_; lean_object* v_lintDriverArgs_1909_; lean_object* v_version_1910_; lean_object* v_versionTags_1911_; lean_object* v_description_1912_; lean_object* v_keywords_1913_; lean_object* v_homepage_1914_; lean_object* v_license_1915_; lean_object* v_licenseFiles_1916_; lean_object* v_readmeFile_1917_; uint8_t v_reservoir_1918_; lean_object* v_enableArtifactCache_x3f_1919_; lean_object* v_restoreAllArtifacts_x3f_1920_; uint8_t v_libPrefixOnWindows_1921_; uint8_t v_allowImportAll_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_toWorkspaceConfig_1891_ = lean_ctor_get(v_cfg_1890_, 0);
v_toLeanConfig_1892_ = lean_ctor_get(v_cfg_1890_, 1);
v_bootstrap_1893_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*27);
v_manifestFile_1894_ = lean_ctor_get(v_cfg_1890_, 2);
v_extraDepTargets_1895_ = lean_ctor_get(v_cfg_1890_, 3);
v_precompileModules_1896_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1897_ = lean_ctor_get(v_cfg_1890_, 4);
v_srcDir_1898_ = lean_ctor_get(v_cfg_1890_, 5);
v_buildDir_1899_ = lean_ctor_get(v_cfg_1890_, 6);
v_leanLibDir_1900_ = lean_ctor_get(v_cfg_1890_, 7);
v_nativeLibDir_1901_ = lean_ctor_get(v_cfg_1890_, 8);
v_binDir_1902_ = lean_ctor_get(v_cfg_1890_, 9);
v_irDir_1903_ = lean_ctor_get(v_cfg_1890_, 10);
v_releaseRepo_1904_ = lean_ctor_get(v_cfg_1890_, 11);
v_buildArchive_1905_ = lean_ctor_get(v_cfg_1890_, 12);
v_preferReleaseBuild_1906_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*27 + 2);
v_testDriver_1907_ = lean_ctor_get(v_cfg_1890_, 13);
v_testDriverArgs_1908_ = lean_ctor_get(v_cfg_1890_, 14);
v_lintDriverArgs_1909_ = lean_ctor_get(v_cfg_1890_, 16);
v_version_1910_ = lean_ctor_get(v_cfg_1890_, 17);
v_versionTags_1911_ = lean_ctor_get(v_cfg_1890_, 18);
v_description_1912_ = lean_ctor_get(v_cfg_1890_, 19);
v_keywords_1913_ = lean_ctor_get(v_cfg_1890_, 20);
v_homepage_1914_ = lean_ctor_get(v_cfg_1890_, 21);
v_license_1915_ = lean_ctor_get(v_cfg_1890_, 22);
v_licenseFiles_1916_ = lean_ctor_get(v_cfg_1890_, 23);
v_readmeFile_1917_ = lean_ctor_get(v_cfg_1890_, 24);
v_reservoir_1918_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1919_ = lean_ctor_get(v_cfg_1890_, 25);
v_restoreAllArtifacts_x3f_1920_ = lean_ctor_get(v_cfg_1890_, 26);
v_libPrefixOnWindows_1921_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*27 + 4);
v_allowImportAll_1922_ = lean_ctor_get_uint8(v_cfg_1890_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_1920_);
lean_inc(v_enableArtifactCache_x3f_1919_);
lean_inc(v_readmeFile_1917_);
lean_inc(v_licenseFiles_1916_);
lean_inc(v_license_1915_);
lean_inc(v_homepage_1914_);
lean_inc(v_keywords_1913_);
lean_inc(v_description_1912_);
lean_inc(v_versionTags_1911_);
lean_inc(v_version_1910_);
lean_inc(v_lintDriverArgs_1909_);
lean_inc(v_testDriverArgs_1908_);
lean_inc(v_testDriver_1907_);
lean_inc(v_buildArchive_1905_);
lean_inc(v_releaseRepo_1904_);
lean_inc(v_irDir_1903_);
lean_inc(v_binDir_1902_);
lean_inc(v_nativeLibDir_1901_);
lean_inc(v_leanLibDir_1900_);
lean_inc(v_buildDir_1899_);
lean_inc(v_srcDir_1898_);
lean_inc(v_moreGlobalServerArgs_1897_);
lean_inc(v_extraDepTargets_1895_);
lean_inc(v_manifestFile_1894_);
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
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_toWorkspaceConfig_1891_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_toLeanConfig_1892_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_manifestFile_1894_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_extraDepTargets_1895_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_moreGlobalServerArgs_1897_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_srcDir_1898_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_buildDir_1899_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_leanLibDir_1900_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v_nativeLibDir_1901_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_binDir_1902_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v_irDir_1903_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_releaseRepo_1904_);
lean_ctor_set(v_reuseFailAlloc_1928_, 12, v_buildArchive_1905_);
lean_ctor_set(v_reuseFailAlloc_1928_, 13, v_testDriver_1907_);
lean_ctor_set(v_reuseFailAlloc_1928_, 14, v_testDriverArgs_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 15, v_val_1889_);
lean_ctor_set(v_reuseFailAlloc_1928_, 16, v_lintDriverArgs_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 17, v_version_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 18, v_versionTags_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 19, v_description_1912_);
lean_ctor_set(v_reuseFailAlloc_1928_, 20, v_keywords_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 21, v_homepage_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 22, v_license_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 23, v_licenseFiles_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 24, v_readmeFile_1917_);
lean_ctor_set(v_reuseFailAlloc_1928_, 25, v_enableArtifactCache_x3f_1919_);
lean_ctor_set(v_reuseFailAlloc_1928_, 26, v_restoreAllArtifacts_x3f_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*27, v_bootstrap_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*27 + 1, v_precompileModules_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*27 + 3, v_reservoir_1918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*27 + 5, v_allowImportAll_1922_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* v_f_1931_, lean_object* v_cfg_1932_){
_start:
{
lean_object* v_toWorkspaceConfig_1933_; lean_object* v_toLeanConfig_1934_; uint8_t v_bootstrap_1935_; lean_object* v_manifestFile_1936_; lean_object* v_extraDepTargets_1937_; uint8_t v_precompileModules_1938_; lean_object* v_moreGlobalServerArgs_1939_; lean_object* v_srcDir_1940_; lean_object* v_buildDir_1941_; lean_object* v_leanLibDir_1942_; lean_object* v_nativeLibDir_1943_; lean_object* v_binDir_1944_; lean_object* v_irDir_1945_; lean_object* v_releaseRepo_1946_; lean_object* v_buildArchive_1947_; uint8_t v_preferReleaseBuild_1948_; lean_object* v_testDriver_1949_; lean_object* v_testDriverArgs_1950_; lean_object* v_lintDriver_1951_; lean_object* v_lintDriverArgs_1952_; lean_object* v_version_1953_; lean_object* v_versionTags_1954_; lean_object* v_description_1955_; lean_object* v_keywords_1956_; lean_object* v_homepage_1957_; lean_object* v_license_1958_; lean_object* v_licenseFiles_1959_; lean_object* v_readmeFile_1960_; uint8_t v_reservoir_1961_; lean_object* v_enableArtifactCache_x3f_1962_; lean_object* v_restoreAllArtifacts_x3f_1963_; uint8_t v_libPrefixOnWindows_1964_; uint8_t v_allowImportAll_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_toWorkspaceConfig_1933_ = lean_ctor_get(v_cfg_1932_, 0);
v_toLeanConfig_1934_ = lean_ctor_get(v_cfg_1932_, 1);
v_bootstrap_1935_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*27);
v_manifestFile_1936_ = lean_ctor_get(v_cfg_1932_, 2);
v_extraDepTargets_1937_ = lean_ctor_get(v_cfg_1932_, 3);
v_precompileModules_1938_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1939_ = lean_ctor_get(v_cfg_1932_, 4);
v_srcDir_1940_ = lean_ctor_get(v_cfg_1932_, 5);
v_buildDir_1941_ = lean_ctor_get(v_cfg_1932_, 6);
v_leanLibDir_1942_ = lean_ctor_get(v_cfg_1932_, 7);
v_nativeLibDir_1943_ = lean_ctor_get(v_cfg_1932_, 8);
v_binDir_1944_ = lean_ctor_get(v_cfg_1932_, 9);
v_irDir_1945_ = lean_ctor_get(v_cfg_1932_, 10);
v_releaseRepo_1946_ = lean_ctor_get(v_cfg_1932_, 11);
v_buildArchive_1947_ = lean_ctor_get(v_cfg_1932_, 12);
v_preferReleaseBuild_1948_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*27 + 2);
v_testDriver_1949_ = lean_ctor_get(v_cfg_1932_, 13);
v_testDriverArgs_1950_ = lean_ctor_get(v_cfg_1932_, 14);
v_lintDriver_1951_ = lean_ctor_get(v_cfg_1932_, 15);
v_lintDriverArgs_1952_ = lean_ctor_get(v_cfg_1932_, 16);
v_version_1953_ = lean_ctor_get(v_cfg_1932_, 17);
v_versionTags_1954_ = lean_ctor_get(v_cfg_1932_, 18);
v_description_1955_ = lean_ctor_get(v_cfg_1932_, 19);
v_keywords_1956_ = lean_ctor_get(v_cfg_1932_, 20);
v_homepage_1957_ = lean_ctor_get(v_cfg_1932_, 21);
v_license_1958_ = lean_ctor_get(v_cfg_1932_, 22);
v_licenseFiles_1959_ = lean_ctor_get(v_cfg_1932_, 23);
v_readmeFile_1960_ = lean_ctor_get(v_cfg_1932_, 24);
v_reservoir_1961_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1962_ = lean_ctor_get(v_cfg_1932_, 25);
v_restoreAllArtifacts_x3f_1963_ = lean_ctor_get(v_cfg_1932_, 26);
v_libPrefixOnWindows_1964_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*27 + 4);
v_allowImportAll_1965_ = lean_ctor_get_uint8(v_cfg_1932_, sizeof(void*)*27 + 5);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_cfg_1932_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v_cfg_1932_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1963_);
lean_inc(v_enableArtifactCache_x3f_1962_);
lean_inc(v_readmeFile_1960_);
lean_inc(v_licenseFiles_1959_);
lean_inc(v_license_1958_);
lean_inc(v_homepage_1957_);
lean_inc(v_keywords_1956_);
lean_inc(v_description_1955_);
lean_inc(v_versionTags_1954_);
lean_inc(v_version_1953_);
lean_inc(v_lintDriverArgs_1952_);
lean_inc(v_lintDriver_1951_);
lean_inc(v_testDriverArgs_1950_);
lean_inc(v_testDriver_1949_);
lean_inc(v_buildArchive_1947_);
lean_inc(v_releaseRepo_1946_);
lean_inc(v_irDir_1945_);
lean_inc(v_binDir_1944_);
lean_inc(v_nativeLibDir_1943_);
lean_inc(v_leanLibDir_1942_);
lean_inc(v_buildDir_1941_);
lean_inc(v_srcDir_1940_);
lean_inc(v_moreGlobalServerArgs_1939_);
lean_inc(v_extraDepTargets_1937_);
lean_inc(v_manifestFile_1936_);
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
v___x_1969_ = lean_apply_1(v_f_1931_, v_lintDriver_1951_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 15, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_toWorkspaceConfig_1933_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_toLeanConfig_1934_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_manifestFile_1936_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_extraDepTargets_1937_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_moreGlobalServerArgs_1939_);
lean_ctor_set(v_reuseFailAlloc_1972_, 5, v_srcDir_1940_);
lean_ctor_set(v_reuseFailAlloc_1972_, 6, v_buildDir_1941_);
lean_ctor_set(v_reuseFailAlloc_1972_, 7, v_leanLibDir_1942_);
lean_ctor_set(v_reuseFailAlloc_1972_, 8, v_nativeLibDir_1943_);
lean_ctor_set(v_reuseFailAlloc_1972_, 9, v_binDir_1944_);
lean_ctor_set(v_reuseFailAlloc_1972_, 10, v_irDir_1945_);
lean_ctor_set(v_reuseFailAlloc_1972_, 11, v_releaseRepo_1946_);
lean_ctor_set(v_reuseFailAlloc_1972_, 12, v_buildArchive_1947_);
lean_ctor_set(v_reuseFailAlloc_1972_, 13, v_testDriver_1949_);
lean_ctor_set(v_reuseFailAlloc_1972_, 14, v_testDriverArgs_1950_);
lean_ctor_set(v_reuseFailAlloc_1972_, 15, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1972_, 16, v_lintDriverArgs_1952_);
lean_ctor_set(v_reuseFailAlloc_1972_, 17, v_version_1953_);
lean_ctor_set(v_reuseFailAlloc_1972_, 18, v_versionTags_1954_);
lean_ctor_set(v_reuseFailAlloc_1972_, 19, v_description_1955_);
lean_ctor_set(v_reuseFailAlloc_1972_, 20, v_keywords_1956_);
lean_ctor_set(v_reuseFailAlloc_1972_, 21, v_homepage_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 22, v_license_1958_);
lean_ctor_set(v_reuseFailAlloc_1972_, 23, v_licenseFiles_1959_);
lean_ctor_set(v_reuseFailAlloc_1972_, 24, v_readmeFile_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 25, v_enableArtifactCache_x3f_1962_);
lean_ctor_set(v_reuseFailAlloc_1972_, 26, v_restoreAllArtifacts_x3f_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*27, v_bootstrap_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*27 + 1, v_precompileModules_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*27 + 3, v_reservoir_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*27 + 5, v_allowImportAll_1965_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_1982_, lean_object* v_n_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_1985_, lean_object* v_n_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1985_, v_n_1986_);
lean_dec(v_n_1986_);
lean_dec(v_p_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_1988_, lean_object* v_n_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1988_, v_n_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_1991_, lean_object* v_n_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_1991_, v_n_1992_);
lean_dec(v_n_1992_);
lean_dec(v_p_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* v_cfg_1994_){
_start:
{
lean_object* v_lintDriverArgs_1995_; 
v_lintDriverArgs_1995_ = lean_ctor_get(v_cfg_1994_, 16);
lean_inc_ref(v_lintDriverArgs_1995_);
return v_lintDriverArgs_1995_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(v_cfg_1996_);
lean_dec_ref(v_cfg_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* v_val_1998_, lean_object* v_cfg_1999_){
_start:
{
lean_object* v_toWorkspaceConfig_2000_; lean_object* v_toLeanConfig_2001_; uint8_t v_bootstrap_2002_; lean_object* v_manifestFile_2003_; lean_object* v_extraDepTargets_2004_; uint8_t v_precompileModules_2005_; lean_object* v_moreGlobalServerArgs_2006_; lean_object* v_srcDir_2007_; lean_object* v_buildDir_2008_; lean_object* v_leanLibDir_2009_; lean_object* v_nativeLibDir_2010_; lean_object* v_binDir_2011_; lean_object* v_irDir_2012_; lean_object* v_releaseRepo_2013_; lean_object* v_buildArchive_2014_; uint8_t v_preferReleaseBuild_2015_; lean_object* v_testDriver_2016_; lean_object* v_testDriverArgs_2017_; lean_object* v_lintDriver_2018_; lean_object* v_version_2019_; lean_object* v_versionTags_2020_; lean_object* v_description_2021_; lean_object* v_keywords_2022_; lean_object* v_homepage_2023_; lean_object* v_license_2024_; lean_object* v_licenseFiles_2025_; lean_object* v_readmeFile_2026_; uint8_t v_reservoir_2027_; lean_object* v_enableArtifactCache_x3f_2028_; lean_object* v_restoreAllArtifacts_x3f_2029_; uint8_t v_libPrefixOnWindows_2030_; uint8_t v_allowImportAll_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_toWorkspaceConfig_2000_ = lean_ctor_get(v_cfg_1999_, 0);
v_toLeanConfig_2001_ = lean_ctor_get(v_cfg_1999_, 1);
v_bootstrap_2002_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*27);
v_manifestFile_2003_ = lean_ctor_get(v_cfg_1999_, 2);
v_extraDepTargets_2004_ = lean_ctor_get(v_cfg_1999_, 3);
v_precompileModules_2005_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2006_ = lean_ctor_get(v_cfg_1999_, 4);
v_srcDir_2007_ = lean_ctor_get(v_cfg_1999_, 5);
v_buildDir_2008_ = lean_ctor_get(v_cfg_1999_, 6);
v_leanLibDir_2009_ = lean_ctor_get(v_cfg_1999_, 7);
v_nativeLibDir_2010_ = lean_ctor_get(v_cfg_1999_, 8);
v_binDir_2011_ = lean_ctor_get(v_cfg_1999_, 9);
v_irDir_2012_ = lean_ctor_get(v_cfg_1999_, 10);
v_releaseRepo_2013_ = lean_ctor_get(v_cfg_1999_, 11);
v_buildArchive_2014_ = lean_ctor_get(v_cfg_1999_, 12);
v_preferReleaseBuild_2015_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*27 + 2);
v_testDriver_2016_ = lean_ctor_get(v_cfg_1999_, 13);
v_testDriverArgs_2017_ = lean_ctor_get(v_cfg_1999_, 14);
v_lintDriver_2018_ = lean_ctor_get(v_cfg_1999_, 15);
v_version_2019_ = lean_ctor_get(v_cfg_1999_, 17);
v_versionTags_2020_ = lean_ctor_get(v_cfg_1999_, 18);
v_description_2021_ = lean_ctor_get(v_cfg_1999_, 19);
v_keywords_2022_ = lean_ctor_get(v_cfg_1999_, 20);
v_homepage_2023_ = lean_ctor_get(v_cfg_1999_, 21);
v_license_2024_ = lean_ctor_get(v_cfg_1999_, 22);
v_licenseFiles_2025_ = lean_ctor_get(v_cfg_1999_, 23);
v_readmeFile_2026_ = lean_ctor_get(v_cfg_1999_, 24);
v_reservoir_2027_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2028_ = lean_ctor_get(v_cfg_1999_, 25);
v_restoreAllArtifacts_x3f_2029_ = lean_ctor_get(v_cfg_1999_, 26);
v_libPrefixOnWindows_2030_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*27 + 4);
v_allowImportAll_2031_ = lean_ctor_get_uint8(v_cfg_1999_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_2029_);
lean_inc(v_enableArtifactCache_x3f_2028_);
lean_inc(v_readmeFile_2026_);
lean_inc(v_licenseFiles_2025_);
lean_inc(v_license_2024_);
lean_inc(v_homepage_2023_);
lean_inc(v_keywords_2022_);
lean_inc(v_description_2021_);
lean_inc(v_versionTags_2020_);
lean_inc(v_version_2019_);
lean_inc(v_lintDriver_2018_);
lean_inc(v_testDriverArgs_2017_);
lean_inc(v_testDriver_2016_);
lean_inc(v_buildArchive_2014_);
lean_inc(v_releaseRepo_2013_);
lean_inc(v_irDir_2012_);
lean_inc(v_binDir_2011_);
lean_inc(v_nativeLibDir_2010_);
lean_inc(v_leanLibDir_2009_);
lean_inc(v_buildDir_2008_);
lean_inc(v_srcDir_2007_);
lean_inc(v_moreGlobalServerArgs_2006_);
lean_inc(v_extraDepTargets_2004_);
lean_inc(v_manifestFile_2003_);
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
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_toWorkspaceConfig_2000_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_toLeanConfig_2001_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_manifestFile_2003_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v_extraDepTargets_2004_);
lean_ctor_set(v_reuseFailAlloc_2037_, 4, v_moreGlobalServerArgs_2006_);
lean_ctor_set(v_reuseFailAlloc_2037_, 5, v_srcDir_2007_);
lean_ctor_set(v_reuseFailAlloc_2037_, 6, v_buildDir_2008_);
lean_ctor_set(v_reuseFailAlloc_2037_, 7, v_leanLibDir_2009_);
lean_ctor_set(v_reuseFailAlloc_2037_, 8, v_nativeLibDir_2010_);
lean_ctor_set(v_reuseFailAlloc_2037_, 9, v_binDir_2011_);
lean_ctor_set(v_reuseFailAlloc_2037_, 10, v_irDir_2012_);
lean_ctor_set(v_reuseFailAlloc_2037_, 11, v_releaseRepo_2013_);
lean_ctor_set(v_reuseFailAlloc_2037_, 12, v_buildArchive_2014_);
lean_ctor_set(v_reuseFailAlloc_2037_, 13, v_testDriver_2016_);
lean_ctor_set(v_reuseFailAlloc_2037_, 14, v_testDriverArgs_2017_);
lean_ctor_set(v_reuseFailAlloc_2037_, 15, v_lintDriver_2018_);
lean_ctor_set(v_reuseFailAlloc_2037_, 16, v_val_1998_);
lean_ctor_set(v_reuseFailAlloc_2037_, 17, v_version_2019_);
lean_ctor_set(v_reuseFailAlloc_2037_, 18, v_versionTags_2020_);
lean_ctor_set(v_reuseFailAlloc_2037_, 19, v_description_2021_);
lean_ctor_set(v_reuseFailAlloc_2037_, 20, v_keywords_2022_);
lean_ctor_set(v_reuseFailAlloc_2037_, 21, v_homepage_2023_);
lean_ctor_set(v_reuseFailAlloc_2037_, 22, v_license_2024_);
lean_ctor_set(v_reuseFailAlloc_2037_, 23, v_licenseFiles_2025_);
lean_ctor_set(v_reuseFailAlloc_2037_, 24, v_readmeFile_2026_);
lean_ctor_set(v_reuseFailAlloc_2037_, 25, v_enableArtifactCache_x3f_2028_);
lean_ctor_set(v_reuseFailAlloc_2037_, 26, v_restoreAllArtifacts_x3f_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*27, v_bootstrap_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*27 + 1, v_precompileModules_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*27 + 3, v_reservoir_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*27 + 5, v_allowImportAll_2031_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* v_f_2040_, lean_object* v_cfg_2041_){
_start:
{
lean_object* v_toWorkspaceConfig_2042_; lean_object* v_toLeanConfig_2043_; uint8_t v_bootstrap_2044_; lean_object* v_manifestFile_2045_; lean_object* v_extraDepTargets_2046_; uint8_t v_precompileModules_2047_; lean_object* v_moreGlobalServerArgs_2048_; lean_object* v_srcDir_2049_; lean_object* v_buildDir_2050_; lean_object* v_leanLibDir_2051_; lean_object* v_nativeLibDir_2052_; lean_object* v_binDir_2053_; lean_object* v_irDir_2054_; lean_object* v_releaseRepo_2055_; lean_object* v_buildArchive_2056_; uint8_t v_preferReleaseBuild_2057_; lean_object* v_testDriver_2058_; lean_object* v_testDriverArgs_2059_; lean_object* v_lintDriver_2060_; lean_object* v_lintDriverArgs_2061_; lean_object* v_version_2062_; lean_object* v_versionTags_2063_; lean_object* v_description_2064_; lean_object* v_keywords_2065_; lean_object* v_homepage_2066_; lean_object* v_license_2067_; lean_object* v_licenseFiles_2068_; lean_object* v_readmeFile_2069_; uint8_t v_reservoir_2070_; lean_object* v_enableArtifactCache_x3f_2071_; lean_object* v_restoreAllArtifacts_x3f_2072_; uint8_t v_libPrefixOnWindows_2073_; uint8_t v_allowImportAll_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_toWorkspaceConfig_2042_ = lean_ctor_get(v_cfg_2041_, 0);
v_toLeanConfig_2043_ = lean_ctor_get(v_cfg_2041_, 1);
v_bootstrap_2044_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*27);
v_manifestFile_2045_ = lean_ctor_get(v_cfg_2041_, 2);
v_extraDepTargets_2046_ = lean_ctor_get(v_cfg_2041_, 3);
v_precompileModules_2047_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2048_ = lean_ctor_get(v_cfg_2041_, 4);
v_srcDir_2049_ = lean_ctor_get(v_cfg_2041_, 5);
v_buildDir_2050_ = lean_ctor_get(v_cfg_2041_, 6);
v_leanLibDir_2051_ = lean_ctor_get(v_cfg_2041_, 7);
v_nativeLibDir_2052_ = lean_ctor_get(v_cfg_2041_, 8);
v_binDir_2053_ = lean_ctor_get(v_cfg_2041_, 9);
v_irDir_2054_ = lean_ctor_get(v_cfg_2041_, 10);
v_releaseRepo_2055_ = lean_ctor_get(v_cfg_2041_, 11);
v_buildArchive_2056_ = lean_ctor_get(v_cfg_2041_, 12);
v_preferReleaseBuild_2057_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*27 + 2);
v_testDriver_2058_ = lean_ctor_get(v_cfg_2041_, 13);
v_testDriverArgs_2059_ = lean_ctor_get(v_cfg_2041_, 14);
v_lintDriver_2060_ = lean_ctor_get(v_cfg_2041_, 15);
v_lintDriverArgs_2061_ = lean_ctor_get(v_cfg_2041_, 16);
v_version_2062_ = lean_ctor_get(v_cfg_2041_, 17);
v_versionTags_2063_ = lean_ctor_get(v_cfg_2041_, 18);
v_description_2064_ = lean_ctor_get(v_cfg_2041_, 19);
v_keywords_2065_ = lean_ctor_get(v_cfg_2041_, 20);
v_homepage_2066_ = lean_ctor_get(v_cfg_2041_, 21);
v_license_2067_ = lean_ctor_get(v_cfg_2041_, 22);
v_licenseFiles_2068_ = lean_ctor_get(v_cfg_2041_, 23);
v_readmeFile_2069_ = lean_ctor_get(v_cfg_2041_, 24);
v_reservoir_2070_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2071_ = lean_ctor_get(v_cfg_2041_, 25);
v_restoreAllArtifacts_x3f_2072_ = lean_ctor_get(v_cfg_2041_, 26);
v_libPrefixOnWindows_2073_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*27 + 4);
v_allowImportAll_2074_ = lean_ctor_get_uint8(v_cfg_2041_, sizeof(void*)*27 + 5);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_cfg_2041_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v_cfg_2041_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2072_);
lean_inc(v_enableArtifactCache_x3f_2071_);
lean_inc(v_readmeFile_2069_);
lean_inc(v_licenseFiles_2068_);
lean_inc(v_license_2067_);
lean_inc(v_homepage_2066_);
lean_inc(v_keywords_2065_);
lean_inc(v_description_2064_);
lean_inc(v_versionTags_2063_);
lean_inc(v_version_2062_);
lean_inc(v_lintDriverArgs_2061_);
lean_inc(v_lintDriver_2060_);
lean_inc(v_testDriverArgs_2059_);
lean_inc(v_testDriver_2058_);
lean_inc(v_buildArchive_2056_);
lean_inc(v_releaseRepo_2055_);
lean_inc(v_irDir_2054_);
lean_inc(v_binDir_2053_);
lean_inc(v_nativeLibDir_2052_);
lean_inc(v_leanLibDir_2051_);
lean_inc(v_buildDir_2050_);
lean_inc(v_srcDir_2049_);
lean_inc(v_moreGlobalServerArgs_2048_);
lean_inc(v_extraDepTargets_2046_);
lean_inc(v_manifestFile_2045_);
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
v___x_2078_ = lean_apply_1(v_f_2040_, v_lintDriverArgs_2061_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 16, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_toWorkspaceConfig_2042_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_toLeanConfig_2043_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_manifestFile_2045_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_extraDepTargets_2046_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_moreGlobalServerArgs_2048_);
lean_ctor_set(v_reuseFailAlloc_2081_, 5, v_srcDir_2049_);
lean_ctor_set(v_reuseFailAlloc_2081_, 6, v_buildDir_2050_);
lean_ctor_set(v_reuseFailAlloc_2081_, 7, v_leanLibDir_2051_);
lean_ctor_set(v_reuseFailAlloc_2081_, 8, v_nativeLibDir_2052_);
lean_ctor_set(v_reuseFailAlloc_2081_, 9, v_binDir_2053_);
lean_ctor_set(v_reuseFailAlloc_2081_, 10, v_irDir_2054_);
lean_ctor_set(v_reuseFailAlloc_2081_, 11, v_releaseRepo_2055_);
lean_ctor_set(v_reuseFailAlloc_2081_, 12, v_buildArchive_2056_);
lean_ctor_set(v_reuseFailAlloc_2081_, 13, v_testDriver_2058_);
lean_ctor_set(v_reuseFailAlloc_2081_, 14, v_testDriverArgs_2059_);
lean_ctor_set(v_reuseFailAlloc_2081_, 15, v_lintDriver_2060_);
lean_ctor_set(v_reuseFailAlloc_2081_, 16, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2081_, 17, v_version_2062_);
lean_ctor_set(v_reuseFailAlloc_2081_, 18, v_versionTags_2063_);
lean_ctor_set(v_reuseFailAlloc_2081_, 19, v_description_2064_);
lean_ctor_set(v_reuseFailAlloc_2081_, 20, v_keywords_2065_);
lean_ctor_set(v_reuseFailAlloc_2081_, 21, v_homepage_2066_);
lean_ctor_set(v_reuseFailAlloc_2081_, 22, v_license_2067_);
lean_ctor_set(v_reuseFailAlloc_2081_, 23, v_licenseFiles_2068_);
lean_ctor_set(v_reuseFailAlloc_2081_, 24, v_readmeFile_2069_);
lean_ctor_set(v_reuseFailAlloc_2081_, 25, v_enableArtifactCache_x3f_2071_);
lean_ctor_set(v_reuseFailAlloc_2081_, 26, v_restoreAllArtifacts_x3f_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*27, v_bootstrap_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*27 + 1, v_precompileModules_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2057_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*27 + 3, v_reservoir_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2081_, sizeof(void*)*27 + 5, v_allowImportAll_2074_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2091_, lean_object* v_n_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2094_, lean_object* v_n_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2094_, v_n_2095_);
lean_dec(v_n_2095_);
lean_dec(v_p_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2097_, lean_object* v_n_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2097_, v_n_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2100_, lean_object* v_n_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2100_, v_n_2101_);
lean_dec(v_n_2101_);
lean_dec(v_p_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* v_cfg_2103_){
_start:
{
lean_object* v_version_2104_; 
v_version_2104_ = lean_ctor_get(v_cfg_2103_, 17);
lean_inc_ref(v_version_2104_);
return v_version_2104_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* v_cfg_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lake_PackageConfig_version___proj___lam__0(v_cfg_2105_);
lean_dec_ref(v_cfg_2105_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* v_val_2107_, lean_object* v_cfg_2108_){
_start:
{
lean_object* v_toWorkspaceConfig_2109_; lean_object* v_toLeanConfig_2110_; uint8_t v_bootstrap_2111_; lean_object* v_manifestFile_2112_; lean_object* v_extraDepTargets_2113_; uint8_t v_precompileModules_2114_; lean_object* v_moreGlobalServerArgs_2115_; lean_object* v_srcDir_2116_; lean_object* v_buildDir_2117_; lean_object* v_leanLibDir_2118_; lean_object* v_nativeLibDir_2119_; lean_object* v_binDir_2120_; lean_object* v_irDir_2121_; lean_object* v_releaseRepo_2122_; lean_object* v_buildArchive_2123_; uint8_t v_preferReleaseBuild_2124_; lean_object* v_testDriver_2125_; lean_object* v_testDriverArgs_2126_; lean_object* v_lintDriver_2127_; lean_object* v_lintDriverArgs_2128_; lean_object* v_versionTags_2129_; lean_object* v_description_2130_; lean_object* v_keywords_2131_; lean_object* v_homepage_2132_; lean_object* v_license_2133_; lean_object* v_licenseFiles_2134_; lean_object* v_readmeFile_2135_; uint8_t v_reservoir_2136_; lean_object* v_enableArtifactCache_x3f_2137_; lean_object* v_restoreAllArtifacts_x3f_2138_; uint8_t v_libPrefixOnWindows_2139_; uint8_t v_allowImportAll_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_toWorkspaceConfig_2109_ = lean_ctor_get(v_cfg_2108_, 0);
v_toLeanConfig_2110_ = lean_ctor_get(v_cfg_2108_, 1);
v_bootstrap_2111_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*27);
v_manifestFile_2112_ = lean_ctor_get(v_cfg_2108_, 2);
v_extraDepTargets_2113_ = lean_ctor_get(v_cfg_2108_, 3);
v_precompileModules_2114_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2115_ = lean_ctor_get(v_cfg_2108_, 4);
v_srcDir_2116_ = lean_ctor_get(v_cfg_2108_, 5);
v_buildDir_2117_ = lean_ctor_get(v_cfg_2108_, 6);
v_leanLibDir_2118_ = lean_ctor_get(v_cfg_2108_, 7);
v_nativeLibDir_2119_ = lean_ctor_get(v_cfg_2108_, 8);
v_binDir_2120_ = lean_ctor_get(v_cfg_2108_, 9);
v_irDir_2121_ = lean_ctor_get(v_cfg_2108_, 10);
v_releaseRepo_2122_ = lean_ctor_get(v_cfg_2108_, 11);
v_buildArchive_2123_ = lean_ctor_get(v_cfg_2108_, 12);
v_preferReleaseBuild_2124_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*27 + 2);
v_testDriver_2125_ = lean_ctor_get(v_cfg_2108_, 13);
v_testDriverArgs_2126_ = lean_ctor_get(v_cfg_2108_, 14);
v_lintDriver_2127_ = lean_ctor_get(v_cfg_2108_, 15);
v_lintDriverArgs_2128_ = lean_ctor_get(v_cfg_2108_, 16);
v_versionTags_2129_ = lean_ctor_get(v_cfg_2108_, 18);
v_description_2130_ = lean_ctor_get(v_cfg_2108_, 19);
v_keywords_2131_ = lean_ctor_get(v_cfg_2108_, 20);
v_homepage_2132_ = lean_ctor_get(v_cfg_2108_, 21);
v_license_2133_ = lean_ctor_get(v_cfg_2108_, 22);
v_licenseFiles_2134_ = lean_ctor_get(v_cfg_2108_, 23);
v_readmeFile_2135_ = lean_ctor_get(v_cfg_2108_, 24);
v_reservoir_2136_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2137_ = lean_ctor_get(v_cfg_2108_, 25);
v_restoreAllArtifacts_x3f_2138_ = lean_ctor_get(v_cfg_2108_, 26);
v_libPrefixOnWindows_2139_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*27 + 4);
v_allowImportAll_2140_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*27 + 5);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_cfg_2108_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v_cfg_2108_, 17);
lean_dec(v_unused_2148_);
v___x_2142_ = v_cfg_2108_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2138_);
lean_inc(v_enableArtifactCache_x3f_2137_);
lean_inc(v_readmeFile_2135_);
lean_inc(v_licenseFiles_2134_);
lean_inc(v_license_2133_);
lean_inc(v_homepage_2132_);
lean_inc(v_keywords_2131_);
lean_inc(v_description_2130_);
lean_inc(v_versionTags_2129_);
lean_inc(v_lintDriverArgs_2128_);
lean_inc(v_lintDriver_2127_);
lean_inc(v_testDriverArgs_2126_);
lean_inc(v_testDriver_2125_);
lean_inc(v_buildArchive_2123_);
lean_inc(v_releaseRepo_2122_);
lean_inc(v_irDir_2121_);
lean_inc(v_binDir_2120_);
lean_inc(v_nativeLibDir_2119_);
lean_inc(v_leanLibDir_2118_);
lean_inc(v_buildDir_2117_);
lean_inc(v_srcDir_2116_);
lean_inc(v_moreGlobalServerArgs_2115_);
lean_inc(v_extraDepTargets_2113_);
lean_inc(v_manifestFile_2112_);
lean_inc(v_toLeanConfig_2110_);
lean_inc(v_toWorkspaceConfig_2109_);
lean_dec(v_cfg_2108_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 17, v_val_2107_);
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_toWorkspaceConfig_2109_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_toLeanConfig_2110_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_manifestFile_2112_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_extraDepTargets_2113_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_moreGlobalServerArgs_2115_);
lean_ctor_set(v_reuseFailAlloc_2146_, 5, v_srcDir_2116_);
lean_ctor_set(v_reuseFailAlloc_2146_, 6, v_buildDir_2117_);
lean_ctor_set(v_reuseFailAlloc_2146_, 7, v_leanLibDir_2118_);
lean_ctor_set(v_reuseFailAlloc_2146_, 8, v_nativeLibDir_2119_);
lean_ctor_set(v_reuseFailAlloc_2146_, 9, v_binDir_2120_);
lean_ctor_set(v_reuseFailAlloc_2146_, 10, v_irDir_2121_);
lean_ctor_set(v_reuseFailAlloc_2146_, 11, v_releaseRepo_2122_);
lean_ctor_set(v_reuseFailAlloc_2146_, 12, v_buildArchive_2123_);
lean_ctor_set(v_reuseFailAlloc_2146_, 13, v_testDriver_2125_);
lean_ctor_set(v_reuseFailAlloc_2146_, 14, v_testDriverArgs_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 15, v_lintDriver_2127_);
lean_ctor_set(v_reuseFailAlloc_2146_, 16, v_lintDriverArgs_2128_);
lean_ctor_set(v_reuseFailAlloc_2146_, 17, v_val_2107_);
lean_ctor_set(v_reuseFailAlloc_2146_, 18, v_versionTags_2129_);
lean_ctor_set(v_reuseFailAlloc_2146_, 19, v_description_2130_);
lean_ctor_set(v_reuseFailAlloc_2146_, 20, v_keywords_2131_);
lean_ctor_set(v_reuseFailAlloc_2146_, 21, v_homepage_2132_);
lean_ctor_set(v_reuseFailAlloc_2146_, 22, v_license_2133_);
lean_ctor_set(v_reuseFailAlloc_2146_, 23, v_licenseFiles_2134_);
lean_ctor_set(v_reuseFailAlloc_2146_, 24, v_readmeFile_2135_);
lean_ctor_set(v_reuseFailAlloc_2146_, 25, v_enableArtifactCache_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2146_, 26, v_restoreAllArtifacts_x3f_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*27, v_bootstrap_2111_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*27 + 1, v_precompileModules_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*27 + 3, v_reservoir_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*27 + 5, v_allowImportAll_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* v_f_2149_, lean_object* v_cfg_2150_){
_start:
{
lean_object* v_toWorkspaceConfig_2151_; lean_object* v_toLeanConfig_2152_; uint8_t v_bootstrap_2153_; lean_object* v_manifestFile_2154_; lean_object* v_extraDepTargets_2155_; uint8_t v_precompileModules_2156_; lean_object* v_moreGlobalServerArgs_2157_; lean_object* v_srcDir_2158_; lean_object* v_buildDir_2159_; lean_object* v_leanLibDir_2160_; lean_object* v_nativeLibDir_2161_; lean_object* v_binDir_2162_; lean_object* v_irDir_2163_; lean_object* v_releaseRepo_2164_; lean_object* v_buildArchive_2165_; uint8_t v_preferReleaseBuild_2166_; lean_object* v_testDriver_2167_; lean_object* v_testDriverArgs_2168_; lean_object* v_lintDriver_2169_; lean_object* v_lintDriverArgs_2170_; lean_object* v_version_2171_; lean_object* v_versionTags_2172_; lean_object* v_description_2173_; lean_object* v_keywords_2174_; lean_object* v_homepage_2175_; lean_object* v_license_2176_; lean_object* v_licenseFiles_2177_; lean_object* v_readmeFile_2178_; uint8_t v_reservoir_2179_; lean_object* v_enableArtifactCache_x3f_2180_; lean_object* v_restoreAllArtifacts_x3f_2181_; uint8_t v_libPrefixOnWindows_2182_; uint8_t v_allowImportAll_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2191_; 
v_toWorkspaceConfig_2151_ = lean_ctor_get(v_cfg_2150_, 0);
v_toLeanConfig_2152_ = lean_ctor_get(v_cfg_2150_, 1);
v_bootstrap_2153_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*27);
v_manifestFile_2154_ = lean_ctor_get(v_cfg_2150_, 2);
v_extraDepTargets_2155_ = lean_ctor_get(v_cfg_2150_, 3);
v_precompileModules_2156_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2157_ = lean_ctor_get(v_cfg_2150_, 4);
v_srcDir_2158_ = lean_ctor_get(v_cfg_2150_, 5);
v_buildDir_2159_ = lean_ctor_get(v_cfg_2150_, 6);
v_leanLibDir_2160_ = lean_ctor_get(v_cfg_2150_, 7);
v_nativeLibDir_2161_ = lean_ctor_get(v_cfg_2150_, 8);
v_binDir_2162_ = lean_ctor_get(v_cfg_2150_, 9);
v_irDir_2163_ = lean_ctor_get(v_cfg_2150_, 10);
v_releaseRepo_2164_ = lean_ctor_get(v_cfg_2150_, 11);
v_buildArchive_2165_ = lean_ctor_get(v_cfg_2150_, 12);
v_preferReleaseBuild_2166_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*27 + 2);
v_testDriver_2167_ = lean_ctor_get(v_cfg_2150_, 13);
v_testDriverArgs_2168_ = lean_ctor_get(v_cfg_2150_, 14);
v_lintDriver_2169_ = lean_ctor_get(v_cfg_2150_, 15);
v_lintDriverArgs_2170_ = lean_ctor_get(v_cfg_2150_, 16);
v_version_2171_ = lean_ctor_get(v_cfg_2150_, 17);
v_versionTags_2172_ = lean_ctor_get(v_cfg_2150_, 18);
v_description_2173_ = lean_ctor_get(v_cfg_2150_, 19);
v_keywords_2174_ = lean_ctor_get(v_cfg_2150_, 20);
v_homepage_2175_ = lean_ctor_get(v_cfg_2150_, 21);
v_license_2176_ = lean_ctor_get(v_cfg_2150_, 22);
v_licenseFiles_2177_ = lean_ctor_get(v_cfg_2150_, 23);
v_readmeFile_2178_ = lean_ctor_get(v_cfg_2150_, 24);
v_reservoir_2179_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2180_ = lean_ctor_get(v_cfg_2150_, 25);
v_restoreAllArtifacts_x3f_2181_ = lean_ctor_get(v_cfg_2150_, 26);
v_libPrefixOnWindows_2182_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*27 + 4);
v_allowImportAll_2183_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*27 + 5);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_cfg_2150_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2185_ = v_cfg_2150_;
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2181_);
lean_inc(v_enableArtifactCache_x3f_2180_);
lean_inc(v_readmeFile_2178_);
lean_inc(v_licenseFiles_2177_);
lean_inc(v_license_2176_);
lean_inc(v_homepage_2175_);
lean_inc(v_keywords_2174_);
lean_inc(v_description_2173_);
lean_inc(v_versionTags_2172_);
lean_inc(v_version_2171_);
lean_inc(v_lintDriverArgs_2170_);
lean_inc(v_lintDriver_2169_);
lean_inc(v_testDriverArgs_2168_);
lean_inc(v_testDriver_2167_);
lean_inc(v_buildArchive_2165_);
lean_inc(v_releaseRepo_2164_);
lean_inc(v_irDir_2163_);
lean_inc(v_binDir_2162_);
lean_inc(v_nativeLibDir_2161_);
lean_inc(v_leanLibDir_2160_);
lean_inc(v_buildDir_2159_);
lean_inc(v_srcDir_2158_);
lean_inc(v_moreGlobalServerArgs_2157_);
lean_inc(v_extraDepTargets_2155_);
lean_inc(v_manifestFile_2154_);
lean_inc(v_toLeanConfig_2152_);
lean_inc(v_toWorkspaceConfig_2151_);
lean_dec(v_cfg_2150_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = lean_apply_1(v_f_2149_, v_version_2171_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 17, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_toWorkspaceConfig_2151_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_toLeanConfig_2152_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_manifestFile_2154_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_extraDepTargets_2155_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v_moreGlobalServerArgs_2157_);
lean_ctor_set(v_reuseFailAlloc_2190_, 5, v_srcDir_2158_);
lean_ctor_set(v_reuseFailAlloc_2190_, 6, v_buildDir_2159_);
lean_ctor_set(v_reuseFailAlloc_2190_, 7, v_leanLibDir_2160_);
lean_ctor_set(v_reuseFailAlloc_2190_, 8, v_nativeLibDir_2161_);
lean_ctor_set(v_reuseFailAlloc_2190_, 9, v_binDir_2162_);
lean_ctor_set(v_reuseFailAlloc_2190_, 10, v_irDir_2163_);
lean_ctor_set(v_reuseFailAlloc_2190_, 11, v_releaseRepo_2164_);
lean_ctor_set(v_reuseFailAlloc_2190_, 12, v_buildArchive_2165_);
lean_ctor_set(v_reuseFailAlloc_2190_, 13, v_testDriver_2167_);
lean_ctor_set(v_reuseFailAlloc_2190_, 14, v_testDriverArgs_2168_);
lean_ctor_set(v_reuseFailAlloc_2190_, 15, v_lintDriver_2169_);
lean_ctor_set(v_reuseFailAlloc_2190_, 16, v_lintDriverArgs_2170_);
lean_ctor_set(v_reuseFailAlloc_2190_, 17, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2190_, 18, v_versionTags_2172_);
lean_ctor_set(v_reuseFailAlloc_2190_, 19, v_description_2173_);
lean_ctor_set(v_reuseFailAlloc_2190_, 20, v_keywords_2174_);
lean_ctor_set(v_reuseFailAlloc_2190_, 21, v_homepage_2175_);
lean_ctor_set(v_reuseFailAlloc_2190_, 22, v_license_2176_);
lean_ctor_set(v_reuseFailAlloc_2190_, 23, v_licenseFiles_2177_);
lean_ctor_set(v_reuseFailAlloc_2190_, 24, v_readmeFile_2178_);
lean_ctor_set(v_reuseFailAlloc_2190_, 25, v_enableArtifactCache_x3f_2180_);
lean_ctor_set(v_reuseFailAlloc_2190_, 26, v_restoreAllArtifacts_x3f_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*27, v_bootstrap_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*27 + 1, v_precompileModules_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*27 + 3, v_reservoir_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*27 + 5, v_allowImportAll_2183_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* v_x_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___lam__3___closed__1));
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* v_x_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lake_PackageConfig_version___proj___lam__3(v_x_2199_);
lean_dec_ref(v_x_2199_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2210_, lean_object* v_n_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2213_, lean_object* v_n_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lake_PackageConfig_version___proj(v_p_2213_, v_n_2214_);
lean_dec(v_n_2214_);
lean_dec(v_p_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2216_, lean_object* v_n_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lake_PackageConfig_version___proj(v_p_2216_, v_n_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2219_, lean_object* v_n_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lake_PackageConfig_version_instConfigField(v_p_2219_, v_n_2220_);
lean_dec(v_n_2220_);
lean_dec(v_p_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* v_cfg_2222_){
_start:
{
lean_object* v_versionTags_2223_; 
v_versionTags_2223_ = lean_ctor_get(v_cfg_2222_, 18);
lean_inc_ref(v_versionTags_2223_);
return v_versionTags_2223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* v_cfg_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lake_PackageConfig_versionTags___proj___lam__0(v_cfg_2224_);
lean_dec_ref(v_cfg_2224_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* v_val_2226_, lean_object* v_cfg_2227_){
_start:
{
lean_object* v_toWorkspaceConfig_2228_; lean_object* v_toLeanConfig_2229_; uint8_t v_bootstrap_2230_; lean_object* v_manifestFile_2231_; lean_object* v_extraDepTargets_2232_; uint8_t v_precompileModules_2233_; lean_object* v_moreGlobalServerArgs_2234_; lean_object* v_srcDir_2235_; lean_object* v_buildDir_2236_; lean_object* v_leanLibDir_2237_; lean_object* v_nativeLibDir_2238_; lean_object* v_binDir_2239_; lean_object* v_irDir_2240_; lean_object* v_releaseRepo_2241_; lean_object* v_buildArchive_2242_; uint8_t v_preferReleaseBuild_2243_; lean_object* v_testDriver_2244_; lean_object* v_testDriverArgs_2245_; lean_object* v_lintDriver_2246_; lean_object* v_lintDriverArgs_2247_; lean_object* v_version_2248_; lean_object* v_description_2249_; lean_object* v_keywords_2250_; lean_object* v_homepage_2251_; lean_object* v_license_2252_; lean_object* v_licenseFiles_2253_; lean_object* v_readmeFile_2254_; uint8_t v_reservoir_2255_; lean_object* v_enableArtifactCache_x3f_2256_; lean_object* v_restoreAllArtifacts_x3f_2257_; uint8_t v_libPrefixOnWindows_2258_; uint8_t v_allowImportAll_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_toWorkspaceConfig_2228_ = lean_ctor_get(v_cfg_2227_, 0);
v_toLeanConfig_2229_ = lean_ctor_get(v_cfg_2227_, 1);
v_bootstrap_2230_ = lean_ctor_get_uint8(v_cfg_2227_, sizeof(void*)*27);
v_manifestFile_2231_ = lean_ctor_get(v_cfg_2227_, 2);
v_extraDepTargets_2232_ = lean_ctor_get(v_cfg_2227_, 3);
v_precompileModules_2233_ = lean_ctor_get_uint8(v_cfg_2227_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2234_ = lean_ctor_get(v_cfg_2227_, 4);
v_srcDir_2235_ = lean_ctor_get(v_cfg_2227_, 5);
v_buildDir_2236_ = lean_ctor_get(v_cfg_2227_, 6);
v_leanLibDir_2237_ = lean_ctor_get(v_cfg_2227_, 7);
v_nativeLibDir_2238_ = lean_ctor_get(v_cfg_2227_, 8);
v_binDir_2239_ = lean_ctor_get(v_cfg_2227_, 9);
v_irDir_2240_ = lean_ctor_get(v_cfg_2227_, 10);
v_releaseRepo_2241_ = lean_ctor_get(v_cfg_2227_, 11);
v_buildArchive_2242_ = lean_ctor_get(v_cfg_2227_, 12);
v_preferReleaseBuild_2243_ = lean_ctor_get_uint8(v_cfg_2227_, sizeof(void*)*27 + 2);
v_testDriver_2244_ = lean_ctor_get(v_cfg_2227_, 13);
v_testDriverArgs_2245_ = lean_ctor_get(v_cfg_2227_, 14);
v_lintDriver_2246_ = lean_ctor_get(v_cfg_2227_, 15);
v_lintDriverArgs_2247_ = lean_ctor_get(v_cfg_2227_, 16);
v_version_2248_ = lean_ctor_get(v_cfg_2227_, 17);
v_description_2249_ = lean_ctor_get(v_cfg_2227_, 19);
v_keywords_2250_ = lean_ctor_get(v_cfg_2227_, 20);
v_homepage_2251_ = lean_ctor_get(v_cfg_2227_, 21);
v_license_2252_ = lean_ctor_get(v_cfg_2227_, 22);
v_licenseFiles_2253_ = lean_ctor_get(v_cfg_2227_, 23);
v_readmeFile_2254_ = lean_ctor_get(v_cfg_2227_, 24);
v_reservoir_2255_ = lean_ctor_get_uint8(v_cfg_2227_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2256_ = lean_ctor_get(v_cfg_2227_, 25);
v_restoreAllArtifacts_x3f_2257_ = lean_ctor_get(v_cfg_2227_, 26);
v_libPrefixOnWindows_2258_ = lean_ctor_get_uint8(v_cfg_2227_, sizeof(void*)*27 + 4);
v_allowImportAll_2259_ = lean_ctor_get_uint8(v_cfg_2227_, sizeof(void*)*27 + 5);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_cfg_2227_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; 
v_unused_2267_ = lean_ctor_get(v_cfg_2227_, 18);
lean_dec(v_unused_2267_);
v___x_2261_ = v_cfg_2227_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2257_);
lean_inc(v_enableArtifactCache_x3f_2256_);
lean_inc(v_readmeFile_2254_);
lean_inc(v_licenseFiles_2253_);
lean_inc(v_license_2252_);
lean_inc(v_homepage_2251_);
lean_inc(v_keywords_2250_);
lean_inc(v_description_2249_);
lean_inc(v_version_2248_);
lean_inc(v_lintDriverArgs_2247_);
lean_inc(v_lintDriver_2246_);
lean_inc(v_testDriverArgs_2245_);
lean_inc(v_testDriver_2244_);
lean_inc(v_buildArchive_2242_);
lean_inc(v_releaseRepo_2241_);
lean_inc(v_irDir_2240_);
lean_inc(v_binDir_2239_);
lean_inc(v_nativeLibDir_2238_);
lean_inc(v_leanLibDir_2237_);
lean_inc(v_buildDir_2236_);
lean_inc(v_srcDir_2235_);
lean_inc(v_moreGlobalServerArgs_2234_);
lean_inc(v_extraDepTargets_2232_);
lean_inc(v_manifestFile_2231_);
lean_inc(v_toLeanConfig_2229_);
lean_inc(v_toWorkspaceConfig_2228_);
lean_dec(v_cfg_2227_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 18, v_val_2226_);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_toWorkspaceConfig_2228_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_toLeanConfig_2229_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_manifestFile_2231_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_extraDepTargets_2232_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_moreGlobalServerArgs_2234_);
lean_ctor_set(v_reuseFailAlloc_2265_, 5, v_srcDir_2235_);
lean_ctor_set(v_reuseFailAlloc_2265_, 6, v_buildDir_2236_);
lean_ctor_set(v_reuseFailAlloc_2265_, 7, v_leanLibDir_2237_);
lean_ctor_set(v_reuseFailAlloc_2265_, 8, v_nativeLibDir_2238_);
lean_ctor_set(v_reuseFailAlloc_2265_, 9, v_binDir_2239_);
lean_ctor_set(v_reuseFailAlloc_2265_, 10, v_irDir_2240_);
lean_ctor_set(v_reuseFailAlloc_2265_, 11, v_releaseRepo_2241_);
lean_ctor_set(v_reuseFailAlloc_2265_, 12, v_buildArchive_2242_);
lean_ctor_set(v_reuseFailAlloc_2265_, 13, v_testDriver_2244_);
lean_ctor_set(v_reuseFailAlloc_2265_, 14, v_testDriverArgs_2245_);
lean_ctor_set(v_reuseFailAlloc_2265_, 15, v_lintDriver_2246_);
lean_ctor_set(v_reuseFailAlloc_2265_, 16, v_lintDriverArgs_2247_);
lean_ctor_set(v_reuseFailAlloc_2265_, 17, v_version_2248_);
lean_ctor_set(v_reuseFailAlloc_2265_, 18, v_val_2226_);
lean_ctor_set(v_reuseFailAlloc_2265_, 19, v_description_2249_);
lean_ctor_set(v_reuseFailAlloc_2265_, 20, v_keywords_2250_);
lean_ctor_set(v_reuseFailAlloc_2265_, 21, v_homepage_2251_);
lean_ctor_set(v_reuseFailAlloc_2265_, 22, v_license_2252_);
lean_ctor_set(v_reuseFailAlloc_2265_, 23, v_licenseFiles_2253_);
lean_ctor_set(v_reuseFailAlloc_2265_, 24, v_readmeFile_2254_);
lean_ctor_set(v_reuseFailAlloc_2265_, 25, v_enableArtifactCache_x3f_2256_);
lean_ctor_set(v_reuseFailAlloc_2265_, 26, v_restoreAllArtifacts_x3f_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*27, v_bootstrap_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*27 + 1, v_precompileModules_2233_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2243_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*27 + 3, v_reservoir_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*27 + 5, v_allowImportAll_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* v_f_2268_, lean_object* v_cfg_2269_){
_start:
{
lean_object* v_toWorkspaceConfig_2270_; lean_object* v_toLeanConfig_2271_; uint8_t v_bootstrap_2272_; lean_object* v_manifestFile_2273_; lean_object* v_extraDepTargets_2274_; uint8_t v_precompileModules_2275_; lean_object* v_moreGlobalServerArgs_2276_; lean_object* v_srcDir_2277_; lean_object* v_buildDir_2278_; lean_object* v_leanLibDir_2279_; lean_object* v_nativeLibDir_2280_; lean_object* v_binDir_2281_; lean_object* v_irDir_2282_; lean_object* v_releaseRepo_2283_; lean_object* v_buildArchive_2284_; uint8_t v_preferReleaseBuild_2285_; lean_object* v_testDriver_2286_; lean_object* v_testDriverArgs_2287_; lean_object* v_lintDriver_2288_; lean_object* v_lintDriverArgs_2289_; lean_object* v_version_2290_; lean_object* v_versionTags_2291_; lean_object* v_description_2292_; lean_object* v_keywords_2293_; lean_object* v_homepage_2294_; lean_object* v_license_2295_; lean_object* v_licenseFiles_2296_; lean_object* v_readmeFile_2297_; uint8_t v_reservoir_2298_; lean_object* v_enableArtifactCache_x3f_2299_; lean_object* v_restoreAllArtifacts_x3f_2300_; uint8_t v_libPrefixOnWindows_2301_; uint8_t v_allowImportAll_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2310_; 
v_toWorkspaceConfig_2270_ = lean_ctor_get(v_cfg_2269_, 0);
v_toLeanConfig_2271_ = lean_ctor_get(v_cfg_2269_, 1);
v_bootstrap_2272_ = lean_ctor_get_uint8(v_cfg_2269_, sizeof(void*)*27);
v_manifestFile_2273_ = lean_ctor_get(v_cfg_2269_, 2);
v_extraDepTargets_2274_ = lean_ctor_get(v_cfg_2269_, 3);
v_precompileModules_2275_ = lean_ctor_get_uint8(v_cfg_2269_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2276_ = lean_ctor_get(v_cfg_2269_, 4);
v_srcDir_2277_ = lean_ctor_get(v_cfg_2269_, 5);
v_buildDir_2278_ = lean_ctor_get(v_cfg_2269_, 6);
v_leanLibDir_2279_ = lean_ctor_get(v_cfg_2269_, 7);
v_nativeLibDir_2280_ = lean_ctor_get(v_cfg_2269_, 8);
v_binDir_2281_ = lean_ctor_get(v_cfg_2269_, 9);
v_irDir_2282_ = lean_ctor_get(v_cfg_2269_, 10);
v_releaseRepo_2283_ = lean_ctor_get(v_cfg_2269_, 11);
v_buildArchive_2284_ = lean_ctor_get(v_cfg_2269_, 12);
v_preferReleaseBuild_2285_ = lean_ctor_get_uint8(v_cfg_2269_, sizeof(void*)*27 + 2);
v_testDriver_2286_ = lean_ctor_get(v_cfg_2269_, 13);
v_testDriverArgs_2287_ = lean_ctor_get(v_cfg_2269_, 14);
v_lintDriver_2288_ = lean_ctor_get(v_cfg_2269_, 15);
v_lintDriverArgs_2289_ = lean_ctor_get(v_cfg_2269_, 16);
v_version_2290_ = lean_ctor_get(v_cfg_2269_, 17);
v_versionTags_2291_ = lean_ctor_get(v_cfg_2269_, 18);
v_description_2292_ = lean_ctor_get(v_cfg_2269_, 19);
v_keywords_2293_ = lean_ctor_get(v_cfg_2269_, 20);
v_homepage_2294_ = lean_ctor_get(v_cfg_2269_, 21);
v_license_2295_ = lean_ctor_get(v_cfg_2269_, 22);
v_licenseFiles_2296_ = lean_ctor_get(v_cfg_2269_, 23);
v_readmeFile_2297_ = lean_ctor_get(v_cfg_2269_, 24);
v_reservoir_2298_ = lean_ctor_get_uint8(v_cfg_2269_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2299_ = lean_ctor_get(v_cfg_2269_, 25);
v_restoreAllArtifacts_x3f_2300_ = lean_ctor_get(v_cfg_2269_, 26);
v_libPrefixOnWindows_2301_ = lean_ctor_get_uint8(v_cfg_2269_, sizeof(void*)*27 + 4);
v_allowImportAll_2302_ = lean_ctor_get_uint8(v_cfg_2269_, sizeof(void*)*27 + 5);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_cfg_2269_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2304_ = v_cfg_2269_;
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2300_);
lean_inc(v_enableArtifactCache_x3f_2299_);
lean_inc(v_readmeFile_2297_);
lean_inc(v_licenseFiles_2296_);
lean_inc(v_license_2295_);
lean_inc(v_homepage_2294_);
lean_inc(v_keywords_2293_);
lean_inc(v_description_2292_);
lean_inc(v_versionTags_2291_);
lean_inc(v_version_2290_);
lean_inc(v_lintDriverArgs_2289_);
lean_inc(v_lintDriver_2288_);
lean_inc(v_testDriverArgs_2287_);
lean_inc(v_testDriver_2286_);
lean_inc(v_buildArchive_2284_);
lean_inc(v_releaseRepo_2283_);
lean_inc(v_irDir_2282_);
lean_inc(v_binDir_2281_);
lean_inc(v_nativeLibDir_2280_);
lean_inc(v_leanLibDir_2279_);
lean_inc(v_buildDir_2278_);
lean_inc(v_srcDir_2277_);
lean_inc(v_moreGlobalServerArgs_2276_);
lean_inc(v_extraDepTargets_2274_);
lean_inc(v_manifestFile_2273_);
lean_inc(v_toLeanConfig_2271_);
lean_inc(v_toWorkspaceConfig_2270_);
lean_dec(v_cfg_2269_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = lean_apply_1(v_f_2268_, v_versionTags_2291_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 18, v___x_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_toWorkspaceConfig_2270_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_toLeanConfig_2271_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_manifestFile_2273_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_extraDepTargets_2274_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_moreGlobalServerArgs_2276_);
lean_ctor_set(v_reuseFailAlloc_2309_, 5, v_srcDir_2277_);
lean_ctor_set(v_reuseFailAlloc_2309_, 6, v_buildDir_2278_);
lean_ctor_set(v_reuseFailAlloc_2309_, 7, v_leanLibDir_2279_);
lean_ctor_set(v_reuseFailAlloc_2309_, 8, v_nativeLibDir_2280_);
lean_ctor_set(v_reuseFailAlloc_2309_, 9, v_binDir_2281_);
lean_ctor_set(v_reuseFailAlloc_2309_, 10, v_irDir_2282_);
lean_ctor_set(v_reuseFailAlloc_2309_, 11, v_releaseRepo_2283_);
lean_ctor_set(v_reuseFailAlloc_2309_, 12, v_buildArchive_2284_);
lean_ctor_set(v_reuseFailAlloc_2309_, 13, v_testDriver_2286_);
lean_ctor_set(v_reuseFailAlloc_2309_, 14, v_testDriverArgs_2287_);
lean_ctor_set(v_reuseFailAlloc_2309_, 15, v_lintDriver_2288_);
lean_ctor_set(v_reuseFailAlloc_2309_, 16, v_lintDriverArgs_2289_);
lean_ctor_set(v_reuseFailAlloc_2309_, 17, v_version_2290_);
lean_ctor_set(v_reuseFailAlloc_2309_, 18, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2309_, 19, v_description_2292_);
lean_ctor_set(v_reuseFailAlloc_2309_, 20, v_keywords_2293_);
lean_ctor_set(v_reuseFailAlloc_2309_, 21, v_homepage_2294_);
lean_ctor_set(v_reuseFailAlloc_2309_, 22, v_license_2295_);
lean_ctor_set(v_reuseFailAlloc_2309_, 23, v_licenseFiles_2296_);
lean_ctor_set(v_reuseFailAlloc_2309_, 24, v_readmeFile_2297_);
lean_ctor_set(v_reuseFailAlloc_2309_, 25, v_enableArtifactCache_x3f_2299_);
lean_ctor_set(v_reuseFailAlloc_2309_, 26, v_restoreAllArtifacts_x3f_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*27, v_bootstrap_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*27 + 1, v_precompileModules_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*27 + 3, v_reservoir_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*27 + 5, v_allowImportAll_2302_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* v_x_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lake_defaultVersionTags;
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* v_x_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lake_PackageConfig_versionTags___proj___lam__3(v_x_2313_);
lean_dec_ref(v_x_2313_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2324_, lean_object* v_n_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2327_, lean_object* v_n_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lake_PackageConfig_versionTags___proj(v_p_2327_, v_n_2328_);
lean_dec(v_n_2328_);
lean_dec(v_p_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2330_, lean_object* v_n_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lake_PackageConfig_versionTags___proj(v_p_2330_, v_n_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2333_, lean_object* v_n_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2333_, v_n_2334_);
lean_dec(v_n_2334_);
lean_dec(v_p_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* v_cfg_2336_){
_start:
{
lean_object* v_description_2337_; 
v_description_2337_ = lean_ctor_get(v_cfg_2336_, 19);
lean_inc_ref(v_description_2337_);
return v_description_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* v_cfg_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lake_PackageConfig_description___proj___lam__0(v_cfg_2338_);
lean_dec_ref(v_cfg_2338_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* v_val_2340_, lean_object* v_cfg_2341_){
_start:
{
lean_object* v_toWorkspaceConfig_2342_; lean_object* v_toLeanConfig_2343_; uint8_t v_bootstrap_2344_; lean_object* v_manifestFile_2345_; lean_object* v_extraDepTargets_2346_; uint8_t v_precompileModules_2347_; lean_object* v_moreGlobalServerArgs_2348_; lean_object* v_srcDir_2349_; lean_object* v_buildDir_2350_; lean_object* v_leanLibDir_2351_; lean_object* v_nativeLibDir_2352_; lean_object* v_binDir_2353_; lean_object* v_irDir_2354_; lean_object* v_releaseRepo_2355_; lean_object* v_buildArchive_2356_; uint8_t v_preferReleaseBuild_2357_; lean_object* v_testDriver_2358_; lean_object* v_testDriverArgs_2359_; lean_object* v_lintDriver_2360_; lean_object* v_lintDriverArgs_2361_; lean_object* v_version_2362_; lean_object* v_versionTags_2363_; lean_object* v_keywords_2364_; lean_object* v_homepage_2365_; lean_object* v_license_2366_; lean_object* v_licenseFiles_2367_; lean_object* v_readmeFile_2368_; uint8_t v_reservoir_2369_; lean_object* v_enableArtifactCache_x3f_2370_; lean_object* v_restoreAllArtifacts_x3f_2371_; uint8_t v_libPrefixOnWindows_2372_; uint8_t v_allowImportAll_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_toWorkspaceConfig_2342_ = lean_ctor_get(v_cfg_2341_, 0);
v_toLeanConfig_2343_ = lean_ctor_get(v_cfg_2341_, 1);
v_bootstrap_2344_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*27);
v_manifestFile_2345_ = lean_ctor_get(v_cfg_2341_, 2);
v_extraDepTargets_2346_ = lean_ctor_get(v_cfg_2341_, 3);
v_precompileModules_2347_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2348_ = lean_ctor_get(v_cfg_2341_, 4);
v_srcDir_2349_ = lean_ctor_get(v_cfg_2341_, 5);
v_buildDir_2350_ = lean_ctor_get(v_cfg_2341_, 6);
v_leanLibDir_2351_ = lean_ctor_get(v_cfg_2341_, 7);
v_nativeLibDir_2352_ = lean_ctor_get(v_cfg_2341_, 8);
v_binDir_2353_ = lean_ctor_get(v_cfg_2341_, 9);
v_irDir_2354_ = lean_ctor_get(v_cfg_2341_, 10);
v_releaseRepo_2355_ = lean_ctor_get(v_cfg_2341_, 11);
v_buildArchive_2356_ = lean_ctor_get(v_cfg_2341_, 12);
v_preferReleaseBuild_2357_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*27 + 2);
v_testDriver_2358_ = lean_ctor_get(v_cfg_2341_, 13);
v_testDriverArgs_2359_ = lean_ctor_get(v_cfg_2341_, 14);
v_lintDriver_2360_ = lean_ctor_get(v_cfg_2341_, 15);
v_lintDriverArgs_2361_ = lean_ctor_get(v_cfg_2341_, 16);
v_version_2362_ = lean_ctor_get(v_cfg_2341_, 17);
v_versionTags_2363_ = lean_ctor_get(v_cfg_2341_, 18);
v_keywords_2364_ = lean_ctor_get(v_cfg_2341_, 20);
v_homepage_2365_ = lean_ctor_get(v_cfg_2341_, 21);
v_license_2366_ = lean_ctor_get(v_cfg_2341_, 22);
v_licenseFiles_2367_ = lean_ctor_get(v_cfg_2341_, 23);
v_readmeFile_2368_ = lean_ctor_get(v_cfg_2341_, 24);
v_reservoir_2369_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2370_ = lean_ctor_get(v_cfg_2341_, 25);
v_restoreAllArtifacts_x3f_2371_ = lean_ctor_get(v_cfg_2341_, 26);
v_libPrefixOnWindows_2372_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*27 + 4);
v_allowImportAll_2373_ = lean_ctor_get_uint8(v_cfg_2341_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_2371_);
lean_inc(v_enableArtifactCache_x3f_2370_);
lean_inc(v_readmeFile_2368_);
lean_inc(v_licenseFiles_2367_);
lean_inc(v_license_2366_);
lean_inc(v_homepage_2365_);
lean_inc(v_keywords_2364_);
lean_inc(v_versionTags_2363_);
lean_inc(v_version_2362_);
lean_inc(v_lintDriverArgs_2361_);
lean_inc(v_lintDriver_2360_);
lean_inc(v_testDriverArgs_2359_);
lean_inc(v_testDriver_2358_);
lean_inc(v_buildArchive_2356_);
lean_inc(v_releaseRepo_2355_);
lean_inc(v_irDir_2354_);
lean_inc(v_binDir_2353_);
lean_inc(v_nativeLibDir_2352_);
lean_inc(v_leanLibDir_2351_);
lean_inc(v_buildDir_2350_);
lean_inc(v_srcDir_2349_);
lean_inc(v_moreGlobalServerArgs_2348_);
lean_inc(v_extraDepTargets_2346_);
lean_inc(v_manifestFile_2345_);
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
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_toWorkspaceConfig_2342_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_toLeanConfig_2343_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_manifestFile_2345_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_extraDepTargets_2346_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v_moreGlobalServerArgs_2348_);
lean_ctor_set(v_reuseFailAlloc_2379_, 5, v_srcDir_2349_);
lean_ctor_set(v_reuseFailAlloc_2379_, 6, v_buildDir_2350_);
lean_ctor_set(v_reuseFailAlloc_2379_, 7, v_leanLibDir_2351_);
lean_ctor_set(v_reuseFailAlloc_2379_, 8, v_nativeLibDir_2352_);
lean_ctor_set(v_reuseFailAlloc_2379_, 9, v_binDir_2353_);
lean_ctor_set(v_reuseFailAlloc_2379_, 10, v_irDir_2354_);
lean_ctor_set(v_reuseFailAlloc_2379_, 11, v_releaseRepo_2355_);
lean_ctor_set(v_reuseFailAlloc_2379_, 12, v_buildArchive_2356_);
lean_ctor_set(v_reuseFailAlloc_2379_, 13, v_testDriver_2358_);
lean_ctor_set(v_reuseFailAlloc_2379_, 14, v_testDriverArgs_2359_);
lean_ctor_set(v_reuseFailAlloc_2379_, 15, v_lintDriver_2360_);
lean_ctor_set(v_reuseFailAlloc_2379_, 16, v_lintDriverArgs_2361_);
lean_ctor_set(v_reuseFailAlloc_2379_, 17, v_version_2362_);
lean_ctor_set(v_reuseFailAlloc_2379_, 18, v_versionTags_2363_);
lean_ctor_set(v_reuseFailAlloc_2379_, 19, v_val_2340_);
lean_ctor_set(v_reuseFailAlloc_2379_, 20, v_keywords_2364_);
lean_ctor_set(v_reuseFailAlloc_2379_, 21, v_homepage_2365_);
lean_ctor_set(v_reuseFailAlloc_2379_, 22, v_license_2366_);
lean_ctor_set(v_reuseFailAlloc_2379_, 23, v_licenseFiles_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 24, v_readmeFile_2368_);
lean_ctor_set(v_reuseFailAlloc_2379_, 25, v_enableArtifactCache_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2379_, 26, v_restoreAllArtifacts_x3f_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*27, v_bootstrap_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*27 + 1, v_precompileModules_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*27 + 3, v_reservoir_2369_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2372_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*27 + 5, v_allowImportAll_2373_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* v_f_2382_, lean_object* v_cfg_2383_){
_start:
{
lean_object* v_toWorkspaceConfig_2384_; lean_object* v_toLeanConfig_2385_; uint8_t v_bootstrap_2386_; lean_object* v_manifestFile_2387_; lean_object* v_extraDepTargets_2388_; uint8_t v_precompileModules_2389_; lean_object* v_moreGlobalServerArgs_2390_; lean_object* v_srcDir_2391_; lean_object* v_buildDir_2392_; lean_object* v_leanLibDir_2393_; lean_object* v_nativeLibDir_2394_; lean_object* v_binDir_2395_; lean_object* v_irDir_2396_; lean_object* v_releaseRepo_2397_; lean_object* v_buildArchive_2398_; uint8_t v_preferReleaseBuild_2399_; lean_object* v_testDriver_2400_; lean_object* v_testDriverArgs_2401_; lean_object* v_lintDriver_2402_; lean_object* v_lintDriverArgs_2403_; lean_object* v_version_2404_; lean_object* v_versionTags_2405_; lean_object* v_description_2406_; lean_object* v_keywords_2407_; lean_object* v_homepage_2408_; lean_object* v_license_2409_; lean_object* v_licenseFiles_2410_; lean_object* v_readmeFile_2411_; uint8_t v_reservoir_2412_; lean_object* v_enableArtifactCache_x3f_2413_; lean_object* v_restoreAllArtifacts_x3f_2414_; uint8_t v_libPrefixOnWindows_2415_; uint8_t v_allowImportAll_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_toWorkspaceConfig_2384_ = lean_ctor_get(v_cfg_2383_, 0);
v_toLeanConfig_2385_ = lean_ctor_get(v_cfg_2383_, 1);
v_bootstrap_2386_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*27);
v_manifestFile_2387_ = lean_ctor_get(v_cfg_2383_, 2);
v_extraDepTargets_2388_ = lean_ctor_get(v_cfg_2383_, 3);
v_precompileModules_2389_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2390_ = lean_ctor_get(v_cfg_2383_, 4);
v_srcDir_2391_ = lean_ctor_get(v_cfg_2383_, 5);
v_buildDir_2392_ = lean_ctor_get(v_cfg_2383_, 6);
v_leanLibDir_2393_ = lean_ctor_get(v_cfg_2383_, 7);
v_nativeLibDir_2394_ = lean_ctor_get(v_cfg_2383_, 8);
v_binDir_2395_ = lean_ctor_get(v_cfg_2383_, 9);
v_irDir_2396_ = lean_ctor_get(v_cfg_2383_, 10);
v_releaseRepo_2397_ = lean_ctor_get(v_cfg_2383_, 11);
v_buildArchive_2398_ = lean_ctor_get(v_cfg_2383_, 12);
v_preferReleaseBuild_2399_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*27 + 2);
v_testDriver_2400_ = lean_ctor_get(v_cfg_2383_, 13);
v_testDriverArgs_2401_ = lean_ctor_get(v_cfg_2383_, 14);
v_lintDriver_2402_ = lean_ctor_get(v_cfg_2383_, 15);
v_lintDriverArgs_2403_ = lean_ctor_get(v_cfg_2383_, 16);
v_version_2404_ = lean_ctor_get(v_cfg_2383_, 17);
v_versionTags_2405_ = lean_ctor_get(v_cfg_2383_, 18);
v_description_2406_ = lean_ctor_get(v_cfg_2383_, 19);
v_keywords_2407_ = lean_ctor_get(v_cfg_2383_, 20);
v_homepage_2408_ = lean_ctor_get(v_cfg_2383_, 21);
v_license_2409_ = lean_ctor_get(v_cfg_2383_, 22);
v_licenseFiles_2410_ = lean_ctor_get(v_cfg_2383_, 23);
v_readmeFile_2411_ = lean_ctor_get(v_cfg_2383_, 24);
v_reservoir_2412_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2413_ = lean_ctor_get(v_cfg_2383_, 25);
v_restoreAllArtifacts_x3f_2414_ = lean_ctor_get(v_cfg_2383_, 26);
v_libPrefixOnWindows_2415_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*27 + 4);
v_allowImportAll_2416_ = lean_ctor_get_uint8(v_cfg_2383_, sizeof(void*)*27 + 5);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_cfg_2383_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v_cfg_2383_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2414_);
lean_inc(v_enableArtifactCache_x3f_2413_);
lean_inc(v_readmeFile_2411_);
lean_inc(v_licenseFiles_2410_);
lean_inc(v_license_2409_);
lean_inc(v_homepage_2408_);
lean_inc(v_keywords_2407_);
lean_inc(v_description_2406_);
lean_inc(v_versionTags_2405_);
lean_inc(v_version_2404_);
lean_inc(v_lintDriverArgs_2403_);
lean_inc(v_lintDriver_2402_);
lean_inc(v_testDriverArgs_2401_);
lean_inc(v_testDriver_2400_);
lean_inc(v_buildArchive_2398_);
lean_inc(v_releaseRepo_2397_);
lean_inc(v_irDir_2396_);
lean_inc(v_binDir_2395_);
lean_inc(v_nativeLibDir_2394_);
lean_inc(v_leanLibDir_2393_);
lean_inc(v_buildDir_2392_);
lean_inc(v_srcDir_2391_);
lean_inc(v_moreGlobalServerArgs_2390_);
lean_inc(v_extraDepTargets_2388_);
lean_inc(v_manifestFile_2387_);
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
v___x_2420_ = lean_apply_1(v_f_2382_, v_description_2406_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 19, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_toWorkspaceConfig_2384_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_toLeanConfig_2385_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_manifestFile_2387_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_extraDepTargets_2388_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_moreGlobalServerArgs_2390_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_srcDir_2391_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_buildDir_2392_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_leanLibDir_2393_);
lean_ctor_set(v_reuseFailAlloc_2423_, 8, v_nativeLibDir_2394_);
lean_ctor_set(v_reuseFailAlloc_2423_, 9, v_binDir_2395_);
lean_ctor_set(v_reuseFailAlloc_2423_, 10, v_irDir_2396_);
lean_ctor_set(v_reuseFailAlloc_2423_, 11, v_releaseRepo_2397_);
lean_ctor_set(v_reuseFailAlloc_2423_, 12, v_buildArchive_2398_);
lean_ctor_set(v_reuseFailAlloc_2423_, 13, v_testDriver_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 14, v_testDriverArgs_2401_);
lean_ctor_set(v_reuseFailAlloc_2423_, 15, v_lintDriver_2402_);
lean_ctor_set(v_reuseFailAlloc_2423_, 16, v_lintDriverArgs_2403_);
lean_ctor_set(v_reuseFailAlloc_2423_, 17, v_version_2404_);
lean_ctor_set(v_reuseFailAlloc_2423_, 18, v_versionTags_2405_);
lean_ctor_set(v_reuseFailAlloc_2423_, 19, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2423_, 20, v_keywords_2407_);
lean_ctor_set(v_reuseFailAlloc_2423_, 21, v_homepage_2408_);
lean_ctor_set(v_reuseFailAlloc_2423_, 22, v_license_2409_);
lean_ctor_set(v_reuseFailAlloc_2423_, 23, v_licenseFiles_2410_);
lean_ctor_set(v_reuseFailAlloc_2423_, 24, v_readmeFile_2411_);
lean_ctor_set(v_reuseFailAlloc_2423_, 25, v_enableArtifactCache_x3f_2413_);
lean_ctor_set(v_reuseFailAlloc_2423_, 26, v_restoreAllArtifacts_x3f_2414_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*27, v_bootstrap_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*27 + 1, v_precompileModules_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*27 + 3, v_reservoir_2412_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2415_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*27 + 5, v_allowImportAll_2416_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2433_, lean_object* v_n_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2436_, lean_object* v_n_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lake_PackageConfig_description___proj(v_p_2436_, v_n_2437_);
lean_dec(v_n_2437_);
lean_dec(v_p_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2439_, lean_object* v_n_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lake_PackageConfig_description___proj(v_p_2439_, v_n_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2442_, lean_object* v_n_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lake_PackageConfig_description_instConfigField(v_p_2442_, v_n_2443_);
lean_dec(v_n_2443_);
lean_dec(v_p_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* v_cfg_2445_){
_start:
{
lean_object* v_keywords_2446_; 
v_keywords_2446_ = lean_ctor_get(v_cfg_2445_, 20);
lean_inc_ref(v_keywords_2446_);
return v_keywords_2446_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* v_cfg_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lake_PackageConfig_keywords___proj___lam__0(v_cfg_2447_);
lean_dec_ref(v_cfg_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* v_val_2449_, lean_object* v_cfg_2450_){
_start:
{
lean_object* v_toWorkspaceConfig_2451_; lean_object* v_toLeanConfig_2452_; uint8_t v_bootstrap_2453_; lean_object* v_manifestFile_2454_; lean_object* v_extraDepTargets_2455_; uint8_t v_precompileModules_2456_; lean_object* v_moreGlobalServerArgs_2457_; lean_object* v_srcDir_2458_; lean_object* v_buildDir_2459_; lean_object* v_leanLibDir_2460_; lean_object* v_nativeLibDir_2461_; lean_object* v_binDir_2462_; lean_object* v_irDir_2463_; lean_object* v_releaseRepo_2464_; lean_object* v_buildArchive_2465_; uint8_t v_preferReleaseBuild_2466_; lean_object* v_testDriver_2467_; lean_object* v_testDriverArgs_2468_; lean_object* v_lintDriver_2469_; lean_object* v_lintDriverArgs_2470_; lean_object* v_version_2471_; lean_object* v_versionTags_2472_; lean_object* v_description_2473_; lean_object* v_homepage_2474_; lean_object* v_license_2475_; lean_object* v_licenseFiles_2476_; lean_object* v_readmeFile_2477_; uint8_t v_reservoir_2478_; lean_object* v_enableArtifactCache_x3f_2479_; lean_object* v_restoreAllArtifacts_x3f_2480_; uint8_t v_libPrefixOnWindows_2481_; uint8_t v_allowImportAll_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_toWorkspaceConfig_2451_ = lean_ctor_get(v_cfg_2450_, 0);
v_toLeanConfig_2452_ = lean_ctor_get(v_cfg_2450_, 1);
v_bootstrap_2453_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*27);
v_manifestFile_2454_ = lean_ctor_get(v_cfg_2450_, 2);
v_extraDepTargets_2455_ = lean_ctor_get(v_cfg_2450_, 3);
v_precompileModules_2456_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2457_ = lean_ctor_get(v_cfg_2450_, 4);
v_srcDir_2458_ = lean_ctor_get(v_cfg_2450_, 5);
v_buildDir_2459_ = lean_ctor_get(v_cfg_2450_, 6);
v_leanLibDir_2460_ = lean_ctor_get(v_cfg_2450_, 7);
v_nativeLibDir_2461_ = lean_ctor_get(v_cfg_2450_, 8);
v_binDir_2462_ = lean_ctor_get(v_cfg_2450_, 9);
v_irDir_2463_ = lean_ctor_get(v_cfg_2450_, 10);
v_releaseRepo_2464_ = lean_ctor_get(v_cfg_2450_, 11);
v_buildArchive_2465_ = lean_ctor_get(v_cfg_2450_, 12);
v_preferReleaseBuild_2466_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*27 + 2);
v_testDriver_2467_ = lean_ctor_get(v_cfg_2450_, 13);
v_testDriverArgs_2468_ = lean_ctor_get(v_cfg_2450_, 14);
v_lintDriver_2469_ = lean_ctor_get(v_cfg_2450_, 15);
v_lintDriverArgs_2470_ = lean_ctor_get(v_cfg_2450_, 16);
v_version_2471_ = lean_ctor_get(v_cfg_2450_, 17);
v_versionTags_2472_ = lean_ctor_get(v_cfg_2450_, 18);
v_description_2473_ = lean_ctor_get(v_cfg_2450_, 19);
v_homepage_2474_ = lean_ctor_get(v_cfg_2450_, 21);
v_license_2475_ = lean_ctor_get(v_cfg_2450_, 22);
v_licenseFiles_2476_ = lean_ctor_get(v_cfg_2450_, 23);
v_readmeFile_2477_ = lean_ctor_get(v_cfg_2450_, 24);
v_reservoir_2478_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2479_ = lean_ctor_get(v_cfg_2450_, 25);
v_restoreAllArtifacts_x3f_2480_ = lean_ctor_get(v_cfg_2450_, 26);
v_libPrefixOnWindows_2481_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*27 + 4);
v_allowImportAll_2482_ = lean_ctor_get_uint8(v_cfg_2450_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_2480_);
lean_inc(v_enableArtifactCache_x3f_2479_);
lean_inc(v_readmeFile_2477_);
lean_inc(v_licenseFiles_2476_);
lean_inc(v_license_2475_);
lean_inc(v_homepage_2474_);
lean_inc(v_description_2473_);
lean_inc(v_versionTags_2472_);
lean_inc(v_version_2471_);
lean_inc(v_lintDriverArgs_2470_);
lean_inc(v_lintDriver_2469_);
lean_inc(v_testDriverArgs_2468_);
lean_inc(v_testDriver_2467_);
lean_inc(v_buildArchive_2465_);
lean_inc(v_releaseRepo_2464_);
lean_inc(v_irDir_2463_);
lean_inc(v_binDir_2462_);
lean_inc(v_nativeLibDir_2461_);
lean_inc(v_leanLibDir_2460_);
lean_inc(v_buildDir_2459_);
lean_inc(v_srcDir_2458_);
lean_inc(v_moreGlobalServerArgs_2457_);
lean_inc(v_extraDepTargets_2455_);
lean_inc(v_manifestFile_2454_);
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
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_toWorkspaceConfig_2451_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_toLeanConfig_2452_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_manifestFile_2454_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_extraDepTargets_2455_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_moreGlobalServerArgs_2457_);
lean_ctor_set(v_reuseFailAlloc_2488_, 5, v_srcDir_2458_);
lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_buildDir_2459_);
lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_leanLibDir_2460_);
lean_ctor_set(v_reuseFailAlloc_2488_, 8, v_nativeLibDir_2461_);
lean_ctor_set(v_reuseFailAlloc_2488_, 9, v_binDir_2462_);
lean_ctor_set(v_reuseFailAlloc_2488_, 10, v_irDir_2463_);
lean_ctor_set(v_reuseFailAlloc_2488_, 11, v_releaseRepo_2464_);
lean_ctor_set(v_reuseFailAlloc_2488_, 12, v_buildArchive_2465_);
lean_ctor_set(v_reuseFailAlloc_2488_, 13, v_testDriver_2467_);
lean_ctor_set(v_reuseFailAlloc_2488_, 14, v_testDriverArgs_2468_);
lean_ctor_set(v_reuseFailAlloc_2488_, 15, v_lintDriver_2469_);
lean_ctor_set(v_reuseFailAlloc_2488_, 16, v_lintDriverArgs_2470_);
lean_ctor_set(v_reuseFailAlloc_2488_, 17, v_version_2471_);
lean_ctor_set(v_reuseFailAlloc_2488_, 18, v_versionTags_2472_);
lean_ctor_set(v_reuseFailAlloc_2488_, 19, v_description_2473_);
lean_ctor_set(v_reuseFailAlloc_2488_, 20, v_val_2449_);
lean_ctor_set(v_reuseFailAlloc_2488_, 21, v_homepage_2474_);
lean_ctor_set(v_reuseFailAlloc_2488_, 22, v_license_2475_);
lean_ctor_set(v_reuseFailAlloc_2488_, 23, v_licenseFiles_2476_);
lean_ctor_set(v_reuseFailAlloc_2488_, 24, v_readmeFile_2477_);
lean_ctor_set(v_reuseFailAlloc_2488_, 25, v_enableArtifactCache_x3f_2479_);
lean_ctor_set(v_reuseFailAlloc_2488_, 26, v_restoreAllArtifacts_x3f_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*27, v_bootstrap_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*27 + 1, v_precompileModules_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*27 + 3, v_reservoir_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*27 + 5, v_allowImportAll_2482_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* v_f_2491_, lean_object* v_cfg_2492_){
_start:
{
lean_object* v_toWorkspaceConfig_2493_; lean_object* v_toLeanConfig_2494_; uint8_t v_bootstrap_2495_; lean_object* v_manifestFile_2496_; lean_object* v_extraDepTargets_2497_; uint8_t v_precompileModules_2498_; lean_object* v_moreGlobalServerArgs_2499_; lean_object* v_srcDir_2500_; lean_object* v_buildDir_2501_; lean_object* v_leanLibDir_2502_; lean_object* v_nativeLibDir_2503_; lean_object* v_binDir_2504_; lean_object* v_irDir_2505_; lean_object* v_releaseRepo_2506_; lean_object* v_buildArchive_2507_; uint8_t v_preferReleaseBuild_2508_; lean_object* v_testDriver_2509_; lean_object* v_testDriverArgs_2510_; lean_object* v_lintDriver_2511_; lean_object* v_lintDriverArgs_2512_; lean_object* v_version_2513_; lean_object* v_versionTags_2514_; lean_object* v_description_2515_; lean_object* v_keywords_2516_; lean_object* v_homepage_2517_; lean_object* v_license_2518_; lean_object* v_licenseFiles_2519_; lean_object* v_readmeFile_2520_; uint8_t v_reservoir_2521_; lean_object* v_enableArtifactCache_x3f_2522_; lean_object* v_restoreAllArtifacts_x3f_2523_; uint8_t v_libPrefixOnWindows_2524_; uint8_t v_allowImportAll_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2533_; 
v_toWorkspaceConfig_2493_ = lean_ctor_get(v_cfg_2492_, 0);
v_toLeanConfig_2494_ = lean_ctor_get(v_cfg_2492_, 1);
v_bootstrap_2495_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*27);
v_manifestFile_2496_ = lean_ctor_get(v_cfg_2492_, 2);
v_extraDepTargets_2497_ = lean_ctor_get(v_cfg_2492_, 3);
v_precompileModules_2498_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2499_ = lean_ctor_get(v_cfg_2492_, 4);
v_srcDir_2500_ = lean_ctor_get(v_cfg_2492_, 5);
v_buildDir_2501_ = lean_ctor_get(v_cfg_2492_, 6);
v_leanLibDir_2502_ = lean_ctor_get(v_cfg_2492_, 7);
v_nativeLibDir_2503_ = lean_ctor_get(v_cfg_2492_, 8);
v_binDir_2504_ = lean_ctor_get(v_cfg_2492_, 9);
v_irDir_2505_ = lean_ctor_get(v_cfg_2492_, 10);
v_releaseRepo_2506_ = lean_ctor_get(v_cfg_2492_, 11);
v_buildArchive_2507_ = lean_ctor_get(v_cfg_2492_, 12);
v_preferReleaseBuild_2508_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*27 + 2);
v_testDriver_2509_ = lean_ctor_get(v_cfg_2492_, 13);
v_testDriverArgs_2510_ = lean_ctor_get(v_cfg_2492_, 14);
v_lintDriver_2511_ = lean_ctor_get(v_cfg_2492_, 15);
v_lintDriverArgs_2512_ = lean_ctor_get(v_cfg_2492_, 16);
v_version_2513_ = lean_ctor_get(v_cfg_2492_, 17);
v_versionTags_2514_ = lean_ctor_get(v_cfg_2492_, 18);
v_description_2515_ = lean_ctor_get(v_cfg_2492_, 19);
v_keywords_2516_ = lean_ctor_get(v_cfg_2492_, 20);
v_homepage_2517_ = lean_ctor_get(v_cfg_2492_, 21);
v_license_2518_ = lean_ctor_get(v_cfg_2492_, 22);
v_licenseFiles_2519_ = lean_ctor_get(v_cfg_2492_, 23);
v_readmeFile_2520_ = lean_ctor_get(v_cfg_2492_, 24);
v_reservoir_2521_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2522_ = lean_ctor_get(v_cfg_2492_, 25);
v_restoreAllArtifacts_x3f_2523_ = lean_ctor_get(v_cfg_2492_, 26);
v_libPrefixOnWindows_2524_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*27 + 4);
v_allowImportAll_2525_ = lean_ctor_get_uint8(v_cfg_2492_, sizeof(void*)*27 + 5);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_cfg_2492_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2527_ = v_cfg_2492_;
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2523_);
lean_inc(v_enableArtifactCache_x3f_2522_);
lean_inc(v_readmeFile_2520_);
lean_inc(v_licenseFiles_2519_);
lean_inc(v_license_2518_);
lean_inc(v_homepage_2517_);
lean_inc(v_keywords_2516_);
lean_inc(v_description_2515_);
lean_inc(v_versionTags_2514_);
lean_inc(v_version_2513_);
lean_inc(v_lintDriverArgs_2512_);
lean_inc(v_lintDriver_2511_);
lean_inc(v_testDriverArgs_2510_);
lean_inc(v_testDriver_2509_);
lean_inc(v_buildArchive_2507_);
lean_inc(v_releaseRepo_2506_);
lean_inc(v_irDir_2505_);
lean_inc(v_binDir_2504_);
lean_inc(v_nativeLibDir_2503_);
lean_inc(v_leanLibDir_2502_);
lean_inc(v_buildDir_2501_);
lean_inc(v_srcDir_2500_);
lean_inc(v_moreGlobalServerArgs_2499_);
lean_inc(v_extraDepTargets_2497_);
lean_inc(v_manifestFile_2496_);
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
v___x_2529_ = lean_apply_1(v_f_2491_, v_keywords_2516_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 20, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_toWorkspaceConfig_2493_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_toLeanConfig_2494_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_manifestFile_2496_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_extraDepTargets_2497_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_moreGlobalServerArgs_2499_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v_srcDir_2500_);
lean_ctor_set(v_reuseFailAlloc_2532_, 6, v_buildDir_2501_);
lean_ctor_set(v_reuseFailAlloc_2532_, 7, v_leanLibDir_2502_);
lean_ctor_set(v_reuseFailAlloc_2532_, 8, v_nativeLibDir_2503_);
lean_ctor_set(v_reuseFailAlloc_2532_, 9, v_binDir_2504_);
lean_ctor_set(v_reuseFailAlloc_2532_, 10, v_irDir_2505_);
lean_ctor_set(v_reuseFailAlloc_2532_, 11, v_releaseRepo_2506_);
lean_ctor_set(v_reuseFailAlloc_2532_, 12, v_buildArchive_2507_);
lean_ctor_set(v_reuseFailAlloc_2532_, 13, v_testDriver_2509_);
lean_ctor_set(v_reuseFailAlloc_2532_, 14, v_testDriverArgs_2510_);
lean_ctor_set(v_reuseFailAlloc_2532_, 15, v_lintDriver_2511_);
lean_ctor_set(v_reuseFailAlloc_2532_, 16, v_lintDriverArgs_2512_);
lean_ctor_set(v_reuseFailAlloc_2532_, 17, v_version_2513_);
lean_ctor_set(v_reuseFailAlloc_2532_, 18, v_versionTags_2514_);
lean_ctor_set(v_reuseFailAlloc_2532_, 19, v_description_2515_);
lean_ctor_set(v_reuseFailAlloc_2532_, 20, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2532_, 21, v_homepage_2517_);
lean_ctor_set(v_reuseFailAlloc_2532_, 22, v_license_2518_);
lean_ctor_set(v_reuseFailAlloc_2532_, 23, v_licenseFiles_2519_);
lean_ctor_set(v_reuseFailAlloc_2532_, 24, v_readmeFile_2520_);
lean_ctor_set(v_reuseFailAlloc_2532_, 25, v_enableArtifactCache_x3f_2522_);
lean_ctor_set(v_reuseFailAlloc_2532_, 26, v_restoreAllArtifacts_x3f_2523_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*27, v_bootstrap_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*27 + 1, v_precompileModules_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*27 + 3, v_reservoir_2521_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2524_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*27 + 5, v_allowImportAll_2525_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2542_, lean_object* v_n_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2545_, lean_object* v_n_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lake_PackageConfig_keywords___proj(v_p_2545_, v_n_2546_);
lean_dec(v_n_2546_);
lean_dec(v_p_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2548_, lean_object* v_n_2549_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lake_PackageConfig_keywords___proj(v_p_2548_, v_n_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2551_, lean_object* v_n_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2551_, v_n_2552_);
lean_dec(v_n_2552_);
lean_dec(v_p_2551_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* v_cfg_2554_){
_start:
{
lean_object* v_homepage_2555_; 
v_homepage_2555_ = lean_ctor_get(v_cfg_2554_, 21);
lean_inc_ref(v_homepage_2555_);
return v_homepage_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* v_cfg_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lake_PackageConfig_homepage___proj___lam__0(v_cfg_2556_);
lean_dec_ref(v_cfg_2556_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* v_val_2558_, lean_object* v_cfg_2559_){
_start:
{
lean_object* v_toWorkspaceConfig_2560_; lean_object* v_toLeanConfig_2561_; uint8_t v_bootstrap_2562_; lean_object* v_manifestFile_2563_; lean_object* v_extraDepTargets_2564_; uint8_t v_precompileModules_2565_; lean_object* v_moreGlobalServerArgs_2566_; lean_object* v_srcDir_2567_; lean_object* v_buildDir_2568_; lean_object* v_leanLibDir_2569_; lean_object* v_nativeLibDir_2570_; lean_object* v_binDir_2571_; lean_object* v_irDir_2572_; lean_object* v_releaseRepo_2573_; lean_object* v_buildArchive_2574_; uint8_t v_preferReleaseBuild_2575_; lean_object* v_testDriver_2576_; lean_object* v_testDriverArgs_2577_; lean_object* v_lintDriver_2578_; lean_object* v_lintDriverArgs_2579_; lean_object* v_version_2580_; lean_object* v_versionTags_2581_; lean_object* v_description_2582_; lean_object* v_keywords_2583_; lean_object* v_license_2584_; lean_object* v_licenseFiles_2585_; lean_object* v_readmeFile_2586_; uint8_t v_reservoir_2587_; lean_object* v_enableArtifactCache_x3f_2588_; lean_object* v_restoreAllArtifacts_x3f_2589_; uint8_t v_libPrefixOnWindows_2590_; uint8_t v_allowImportAll_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_toWorkspaceConfig_2560_ = lean_ctor_get(v_cfg_2559_, 0);
v_toLeanConfig_2561_ = lean_ctor_get(v_cfg_2559_, 1);
v_bootstrap_2562_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*27);
v_manifestFile_2563_ = lean_ctor_get(v_cfg_2559_, 2);
v_extraDepTargets_2564_ = lean_ctor_get(v_cfg_2559_, 3);
v_precompileModules_2565_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2566_ = lean_ctor_get(v_cfg_2559_, 4);
v_srcDir_2567_ = lean_ctor_get(v_cfg_2559_, 5);
v_buildDir_2568_ = lean_ctor_get(v_cfg_2559_, 6);
v_leanLibDir_2569_ = lean_ctor_get(v_cfg_2559_, 7);
v_nativeLibDir_2570_ = lean_ctor_get(v_cfg_2559_, 8);
v_binDir_2571_ = lean_ctor_get(v_cfg_2559_, 9);
v_irDir_2572_ = lean_ctor_get(v_cfg_2559_, 10);
v_releaseRepo_2573_ = lean_ctor_get(v_cfg_2559_, 11);
v_buildArchive_2574_ = lean_ctor_get(v_cfg_2559_, 12);
v_preferReleaseBuild_2575_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*27 + 2);
v_testDriver_2576_ = lean_ctor_get(v_cfg_2559_, 13);
v_testDriverArgs_2577_ = lean_ctor_get(v_cfg_2559_, 14);
v_lintDriver_2578_ = lean_ctor_get(v_cfg_2559_, 15);
v_lintDriverArgs_2579_ = lean_ctor_get(v_cfg_2559_, 16);
v_version_2580_ = lean_ctor_get(v_cfg_2559_, 17);
v_versionTags_2581_ = lean_ctor_get(v_cfg_2559_, 18);
v_description_2582_ = lean_ctor_get(v_cfg_2559_, 19);
v_keywords_2583_ = lean_ctor_get(v_cfg_2559_, 20);
v_license_2584_ = lean_ctor_get(v_cfg_2559_, 22);
v_licenseFiles_2585_ = lean_ctor_get(v_cfg_2559_, 23);
v_readmeFile_2586_ = lean_ctor_get(v_cfg_2559_, 24);
v_reservoir_2587_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2588_ = lean_ctor_get(v_cfg_2559_, 25);
v_restoreAllArtifacts_x3f_2589_ = lean_ctor_get(v_cfg_2559_, 26);
v_libPrefixOnWindows_2590_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*27 + 4);
v_allowImportAll_2591_ = lean_ctor_get_uint8(v_cfg_2559_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_2589_);
lean_inc(v_enableArtifactCache_x3f_2588_);
lean_inc(v_readmeFile_2586_);
lean_inc(v_licenseFiles_2585_);
lean_inc(v_license_2584_);
lean_inc(v_keywords_2583_);
lean_inc(v_description_2582_);
lean_inc(v_versionTags_2581_);
lean_inc(v_version_2580_);
lean_inc(v_lintDriverArgs_2579_);
lean_inc(v_lintDriver_2578_);
lean_inc(v_testDriverArgs_2577_);
lean_inc(v_testDriver_2576_);
lean_inc(v_buildArchive_2574_);
lean_inc(v_releaseRepo_2573_);
lean_inc(v_irDir_2572_);
lean_inc(v_binDir_2571_);
lean_inc(v_nativeLibDir_2570_);
lean_inc(v_leanLibDir_2569_);
lean_inc(v_buildDir_2568_);
lean_inc(v_srcDir_2567_);
lean_inc(v_moreGlobalServerArgs_2566_);
lean_inc(v_extraDepTargets_2564_);
lean_inc(v_manifestFile_2563_);
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
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_toWorkspaceConfig_2560_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_toLeanConfig_2561_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_manifestFile_2563_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_extraDepTargets_2564_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_moreGlobalServerArgs_2566_);
lean_ctor_set(v_reuseFailAlloc_2597_, 5, v_srcDir_2567_);
lean_ctor_set(v_reuseFailAlloc_2597_, 6, v_buildDir_2568_);
lean_ctor_set(v_reuseFailAlloc_2597_, 7, v_leanLibDir_2569_);
lean_ctor_set(v_reuseFailAlloc_2597_, 8, v_nativeLibDir_2570_);
lean_ctor_set(v_reuseFailAlloc_2597_, 9, v_binDir_2571_);
lean_ctor_set(v_reuseFailAlloc_2597_, 10, v_irDir_2572_);
lean_ctor_set(v_reuseFailAlloc_2597_, 11, v_releaseRepo_2573_);
lean_ctor_set(v_reuseFailAlloc_2597_, 12, v_buildArchive_2574_);
lean_ctor_set(v_reuseFailAlloc_2597_, 13, v_testDriver_2576_);
lean_ctor_set(v_reuseFailAlloc_2597_, 14, v_testDriverArgs_2577_);
lean_ctor_set(v_reuseFailAlloc_2597_, 15, v_lintDriver_2578_);
lean_ctor_set(v_reuseFailAlloc_2597_, 16, v_lintDriverArgs_2579_);
lean_ctor_set(v_reuseFailAlloc_2597_, 17, v_version_2580_);
lean_ctor_set(v_reuseFailAlloc_2597_, 18, v_versionTags_2581_);
lean_ctor_set(v_reuseFailAlloc_2597_, 19, v_description_2582_);
lean_ctor_set(v_reuseFailAlloc_2597_, 20, v_keywords_2583_);
lean_ctor_set(v_reuseFailAlloc_2597_, 21, v_val_2558_);
lean_ctor_set(v_reuseFailAlloc_2597_, 22, v_license_2584_);
lean_ctor_set(v_reuseFailAlloc_2597_, 23, v_licenseFiles_2585_);
lean_ctor_set(v_reuseFailAlloc_2597_, 24, v_readmeFile_2586_);
lean_ctor_set(v_reuseFailAlloc_2597_, 25, v_enableArtifactCache_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2597_, 26, v_restoreAllArtifacts_x3f_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*27, v_bootstrap_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*27 + 1, v_precompileModules_2565_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*27 + 3, v_reservoir_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*27 + 5, v_allowImportAll_2591_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* v_f_2600_, lean_object* v_cfg_2601_){
_start:
{
lean_object* v_toWorkspaceConfig_2602_; lean_object* v_toLeanConfig_2603_; uint8_t v_bootstrap_2604_; lean_object* v_manifestFile_2605_; lean_object* v_extraDepTargets_2606_; uint8_t v_precompileModules_2607_; lean_object* v_moreGlobalServerArgs_2608_; lean_object* v_srcDir_2609_; lean_object* v_buildDir_2610_; lean_object* v_leanLibDir_2611_; lean_object* v_nativeLibDir_2612_; lean_object* v_binDir_2613_; lean_object* v_irDir_2614_; lean_object* v_releaseRepo_2615_; lean_object* v_buildArchive_2616_; uint8_t v_preferReleaseBuild_2617_; lean_object* v_testDriver_2618_; lean_object* v_testDriverArgs_2619_; lean_object* v_lintDriver_2620_; lean_object* v_lintDriverArgs_2621_; lean_object* v_version_2622_; lean_object* v_versionTags_2623_; lean_object* v_description_2624_; lean_object* v_keywords_2625_; lean_object* v_homepage_2626_; lean_object* v_license_2627_; lean_object* v_licenseFiles_2628_; lean_object* v_readmeFile_2629_; uint8_t v_reservoir_2630_; lean_object* v_enableArtifactCache_x3f_2631_; lean_object* v_restoreAllArtifacts_x3f_2632_; uint8_t v_libPrefixOnWindows_2633_; uint8_t v_allowImportAll_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v_toWorkspaceConfig_2602_ = lean_ctor_get(v_cfg_2601_, 0);
v_toLeanConfig_2603_ = lean_ctor_get(v_cfg_2601_, 1);
v_bootstrap_2604_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*27);
v_manifestFile_2605_ = lean_ctor_get(v_cfg_2601_, 2);
v_extraDepTargets_2606_ = lean_ctor_get(v_cfg_2601_, 3);
v_precompileModules_2607_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2608_ = lean_ctor_get(v_cfg_2601_, 4);
v_srcDir_2609_ = lean_ctor_get(v_cfg_2601_, 5);
v_buildDir_2610_ = lean_ctor_get(v_cfg_2601_, 6);
v_leanLibDir_2611_ = lean_ctor_get(v_cfg_2601_, 7);
v_nativeLibDir_2612_ = lean_ctor_get(v_cfg_2601_, 8);
v_binDir_2613_ = lean_ctor_get(v_cfg_2601_, 9);
v_irDir_2614_ = lean_ctor_get(v_cfg_2601_, 10);
v_releaseRepo_2615_ = lean_ctor_get(v_cfg_2601_, 11);
v_buildArchive_2616_ = lean_ctor_get(v_cfg_2601_, 12);
v_preferReleaseBuild_2617_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*27 + 2);
v_testDriver_2618_ = lean_ctor_get(v_cfg_2601_, 13);
v_testDriverArgs_2619_ = lean_ctor_get(v_cfg_2601_, 14);
v_lintDriver_2620_ = lean_ctor_get(v_cfg_2601_, 15);
v_lintDriverArgs_2621_ = lean_ctor_get(v_cfg_2601_, 16);
v_version_2622_ = lean_ctor_get(v_cfg_2601_, 17);
v_versionTags_2623_ = lean_ctor_get(v_cfg_2601_, 18);
v_description_2624_ = lean_ctor_get(v_cfg_2601_, 19);
v_keywords_2625_ = lean_ctor_get(v_cfg_2601_, 20);
v_homepage_2626_ = lean_ctor_get(v_cfg_2601_, 21);
v_license_2627_ = lean_ctor_get(v_cfg_2601_, 22);
v_licenseFiles_2628_ = lean_ctor_get(v_cfg_2601_, 23);
v_readmeFile_2629_ = lean_ctor_get(v_cfg_2601_, 24);
v_reservoir_2630_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2631_ = lean_ctor_get(v_cfg_2601_, 25);
v_restoreAllArtifacts_x3f_2632_ = lean_ctor_get(v_cfg_2601_, 26);
v_libPrefixOnWindows_2633_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*27 + 4);
v_allowImportAll_2634_ = lean_ctor_get_uint8(v_cfg_2601_, sizeof(void*)*27 + 5);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_cfg_2601_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2636_ = v_cfg_2601_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2632_);
lean_inc(v_enableArtifactCache_x3f_2631_);
lean_inc(v_readmeFile_2629_);
lean_inc(v_licenseFiles_2628_);
lean_inc(v_license_2627_);
lean_inc(v_homepage_2626_);
lean_inc(v_keywords_2625_);
lean_inc(v_description_2624_);
lean_inc(v_versionTags_2623_);
lean_inc(v_version_2622_);
lean_inc(v_lintDriverArgs_2621_);
lean_inc(v_lintDriver_2620_);
lean_inc(v_testDriverArgs_2619_);
lean_inc(v_testDriver_2618_);
lean_inc(v_buildArchive_2616_);
lean_inc(v_releaseRepo_2615_);
lean_inc(v_irDir_2614_);
lean_inc(v_binDir_2613_);
lean_inc(v_nativeLibDir_2612_);
lean_inc(v_leanLibDir_2611_);
lean_inc(v_buildDir_2610_);
lean_inc(v_srcDir_2609_);
lean_inc(v_moreGlobalServerArgs_2608_);
lean_inc(v_extraDepTargets_2606_);
lean_inc(v_manifestFile_2605_);
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
v___x_2638_ = lean_apply_1(v_f_2600_, v_homepage_2626_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 21, v___x_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_toWorkspaceConfig_2602_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_toLeanConfig_2603_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_manifestFile_2605_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_extraDepTargets_2606_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_moreGlobalServerArgs_2608_);
lean_ctor_set(v_reuseFailAlloc_2641_, 5, v_srcDir_2609_);
lean_ctor_set(v_reuseFailAlloc_2641_, 6, v_buildDir_2610_);
lean_ctor_set(v_reuseFailAlloc_2641_, 7, v_leanLibDir_2611_);
lean_ctor_set(v_reuseFailAlloc_2641_, 8, v_nativeLibDir_2612_);
lean_ctor_set(v_reuseFailAlloc_2641_, 9, v_binDir_2613_);
lean_ctor_set(v_reuseFailAlloc_2641_, 10, v_irDir_2614_);
lean_ctor_set(v_reuseFailAlloc_2641_, 11, v_releaseRepo_2615_);
lean_ctor_set(v_reuseFailAlloc_2641_, 12, v_buildArchive_2616_);
lean_ctor_set(v_reuseFailAlloc_2641_, 13, v_testDriver_2618_);
lean_ctor_set(v_reuseFailAlloc_2641_, 14, v_testDriverArgs_2619_);
lean_ctor_set(v_reuseFailAlloc_2641_, 15, v_lintDriver_2620_);
lean_ctor_set(v_reuseFailAlloc_2641_, 16, v_lintDriverArgs_2621_);
lean_ctor_set(v_reuseFailAlloc_2641_, 17, v_version_2622_);
lean_ctor_set(v_reuseFailAlloc_2641_, 18, v_versionTags_2623_);
lean_ctor_set(v_reuseFailAlloc_2641_, 19, v_description_2624_);
lean_ctor_set(v_reuseFailAlloc_2641_, 20, v_keywords_2625_);
lean_ctor_set(v_reuseFailAlloc_2641_, 21, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2641_, 22, v_license_2627_);
lean_ctor_set(v_reuseFailAlloc_2641_, 23, v_licenseFiles_2628_);
lean_ctor_set(v_reuseFailAlloc_2641_, 24, v_readmeFile_2629_);
lean_ctor_set(v_reuseFailAlloc_2641_, 25, v_enableArtifactCache_x3f_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 26, v_restoreAllArtifacts_x3f_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*27, v_bootstrap_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*27 + 1, v_precompileModules_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*27 + 3, v_reservoir_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, sizeof(void*)*27 + 5, v_allowImportAll_2634_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2651_, lean_object* v_n_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2654_, lean_object* v_n_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lake_PackageConfig_homepage___proj(v_p_2654_, v_n_2655_);
lean_dec(v_n_2655_);
lean_dec(v_p_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2657_, lean_object* v_n_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lake_PackageConfig_homepage___proj(v_p_2657_, v_n_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2660_, lean_object* v_n_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2660_, v_n_2661_);
lean_dec(v_n_2661_);
lean_dec(v_p_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* v_cfg_2663_){
_start:
{
lean_object* v_license_2664_; 
v_license_2664_ = lean_ctor_get(v_cfg_2663_, 22);
lean_inc_ref(v_license_2664_);
return v_license_2664_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* v_cfg_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lake_PackageConfig_license___proj___lam__0(v_cfg_2665_);
lean_dec_ref(v_cfg_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* v_val_2667_, lean_object* v_cfg_2668_){
_start:
{
lean_object* v_toWorkspaceConfig_2669_; lean_object* v_toLeanConfig_2670_; uint8_t v_bootstrap_2671_; lean_object* v_manifestFile_2672_; lean_object* v_extraDepTargets_2673_; uint8_t v_precompileModules_2674_; lean_object* v_moreGlobalServerArgs_2675_; lean_object* v_srcDir_2676_; lean_object* v_buildDir_2677_; lean_object* v_leanLibDir_2678_; lean_object* v_nativeLibDir_2679_; lean_object* v_binDir_2680_; lean_object* v_irDir_2681_; lean_object* v_releaseRepo_2682_; lean_object* v_buildArchive_2683_; uint8_t v_preferReleaseBuild_2684_; lean_object* v_testDriver_2685_; lean_object* v_testDriverArgs_2686_; lean_object* v_lintDriver_2687_; lean_object* v_lintDriverArgs_2688_; lean_object* v_version_2689_; lean_object* v_versionTags_2690_; lean_object* v_description_2691_; lean_object* v_keywords_2692_; lean_object* v_homepage_2693_; lean_object* v_licenseFiles_2694_; lean_object* v_readmeFile_2695_; uint8_t v_reservoir_2696_; lean_object* v_enableArtifactCache_x3f_2697_; lean_object* v_restoreAllArtifacts_x3f_2698_; uint8_t v_libPrefixOnWindows_2699_; uint8_t v_allowImportAll_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_toWorkspaceConfig_2669_ = lean_ctor_get(v_cfg_2668_, 0);
v_toLeanConfig_2670_ = lean_ctor_get(v_cfg_2668_, 1);
v_bootstrap_2671_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*27);
v_manifestFile_2672_ = lean_ctor_get(v_cfg_2668_, 2);
v_extraDepTargets_2673_ = lean_ctor_get(v_cfg_2668_, 3);
v_precompileModules_2674_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2675_ = lean_ctor_get(v_cfg_2668_, 4);
v_srcDir_2676_ = lean_ctor_get(v_cfg_2668_, 5);
v_buildDir_2677_ = lean_ctor_get(v_cfg_2668_, 6);
v_leanLibDir_2678_ = lean_ctor_get(v_cfg_2668_, 7);
v_nativeLibDir_2679_ = lean_ctor_get(v_cfg_2668_, 8);
v_binDir_2680_ = lean_ctor_get(v_cfg_2668_, 9);
v_irDir_2681_ = lean_ctor_get(v_cfg_2668_, 10);
v_releaseRepo_2682_ = lean_ctor_get(v_cfg_2668_, 11);
v_buildArchive_2683_ = lean_ctor_get(v_cfg_2668_, 12);
v_preferReleaseBuild_2684_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*27 + 2);
v_testDriver_2685_ = lean_ctor_get(v_cfg_2668_, 13);
v_testDriverArgs_2686_ = lean_ctor_get(v_cfg_2668_, 14);
v_lintDriver_2687_ = lean_ctor_get(v_cfg_2668_, 15);
v_lintDriverArgs_2688_ = lean_ctor_get(v_cfg_2668_, 16);
v_version_2689_ = lean_ctor_get(v_cfg_2668_, 17);
v_versionTags_2690_ = lean_ctor_get(v_cfg_2668_, 18);
v_description_2691_ = lean_ctor_get(v_cfg_2668_, 19);
v_keywords_2692_ = lean_ctor_get(v_cfg_2668_, 20);
v_homepage_2693_ = lean_ctor_get(v_cfg_2668_, 21);
v_licenseFiles_2694_ = lean_ctor_get(v_cfg_2668_, 23);
v_readmeFile_2695_ = lean_ctor_get(v_cfg_2668_, 24);
v_reservoir_2696_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2697_ = lean_ctor_get(v_cfg_2668_, 25);
v_restoreAllArtifacts_x3f_2698_ = lean_ctor_get(v_cfg_2668_, 26);
v_libPrefixOnWindows_2699_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*27 + 4);
v_allowImportAll_2700_ = lean_ctor_get_uint8(v_cfg_2668_, sizeof(void*)*27 + 5);
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
lean_inc(v_restoreAllArtifacts_x3f_2698_);
lean_inc(v_enableArtifactCache_x3f_2697_);
lean_inc(v_readmeFile_2695_);
lean_inc(v_licenseFiles_2694_);
lean_inc(v_homepage_2693_);
lean_inc(v_keywords_2692_);
lean_inc(v_description_2691_);
lean_inc(v_versionTags_2690_);
lean_inc(v_version_2689_);
lean_inc(v_lintDriverArgs_2688_);
lean_inc(v_lintDriver_2687_);
lean_inc(v_testDriverArgs_2686_);
lean_inc(v_testDriver_2685_);
lean_inc(v_buildArchive_2683_);
lean_inc(v_releaseRepo_2682_);
lean_inc(v_irDir_2681_);
lean_inc(v_binDir_2680_);
lean_inc(v_nativeLibDir_2679_);
lean_inc(v_leanLibDir_2678_);
lean_inc(v_buildDir_2677_);
lean_inc(v_srcDir_2676_);
lean_inc(v_moreGlobalServerArgs_2675_);
lean_inc(v_extraDepTargets_2673_);
lean_inc(v_manifestFile_2672_);
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
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_toWorkspaceConfig_2669_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_toLeanConfig_2670_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_manifestFile_2672_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_extraDepTargets_2673_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_moreGlobalServerArgs_2675_);
lean_ctor_set(v_reuseFailAlloc_2706_, 5, v_srcDir_2676_);
lean_ctor_set(v_reuseFailAlloc_2706_, 6, v_buildDir_2677_);
lean_ctor_set(v_reuseFailAlloc_2706_, 7, v_leanLibDir_2678_);
lean_ctor_set(v_reuseFailAlloc_2706_, 8, v_nativeLibDir_2679_);
lean_ctor_set(v_reuseFailAlloc_2706_, 9, v_binDir_2680_);
lean_ctor_set(v_reuseFailAlloc_2706_, 10, v_irDir_2681_);
lean_ctor_set(v_reuseFailAlloc_2706_, 11, v_releaseRepo_2682_);
lean_ctor_set(v_reuseFailAlloc_2706_, 12, v_buildArchive_2683_);
lean_ctor_set(v_reuseFailAlloc_2706_, 13, v_testDriver_2685_);
lean_ctor_set(v_reuseFailAlloc_2706_, 14, v_testDriverArgs_2686_);
lean_ctor_set(v_reuseFailAlloc_2706_, 15, v_lintDriver_2687_);
lean_ctor_set(v_reuseFailAlloc_2706_, 16, v_lintDriverArgs_2688_);
lean_ctor_set(v_reuseFailAlloc_2706_, 17, v_version_2689_);
lean_ctor_set(v_reuseFailAlloc_2706_, 18, v_versionTags_2690_);
lean_ctor_set(v_reuseFailAlloc_2706_, 19, v_description_2691_);
lean_ctor_set(v_reuseFailAlloc_2706_, 20, v_keywords_2692_);
lean_ctor_set(v_reuseFailAlloc_2706_, 21, v_homepage_2693_);
lean_ctor_set(v_reuseFailAlloc_2706_, 22, v_val_2667_);
lean_ctor_set(v_reuseFailAlloc_2706_, 23, v_licenseFiles_2694_);
lean_ctor_set(v_reuseFailAlloc_2706_, 24, v_readmeFile_2695_);
lean_ctor_set(v_reuseFailAlloc_2706_, 25, v_enableArtifactCache_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2706_, 26, v_restoreAllArtifacts_x3f_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*27, v_bootstrap_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*27 + 1, v_precompileModules_2674_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*27 + 3, v_reservoir_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*27 + 5, v_allowImportAll_2700_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* v_f_2709_, lean_object* v_cfg_2710_){
_start:
{
lean_object* v_toWorkspaceConfig_2711_; lean_object* v_toLeanConfig_2712_; uint8_t v_bootstrap_2713_; lean_object* v_manifestFile_2714_; lean_object* v_extraDepTargets_2715_; uint8_t v_precompileModules_2716_; lean_object* v_moreGlobalServerArgs_2717_; lean_object* v_srcDir_2718_; lean_object* v_buildDir_2719_; lean_object* v_leanLibDir_2720_; lean_object* v_nativeLibDir_2721_; lean_object* v_binDir_2722_; lean_object* v_irDir_2723_; lean_object* v_releaseRepo_2724_; lean_object* v_buildArchive_2725_; uint8_t v_preferReleaseBuild_2726_; lean_object* v_testDriver_2727_; lean_object* v_testDriverArgs_2728_; lean_object* v_lintDriver_2729_; lean_object* v_lintDriverArgs_2730_; lean_object* v_version_2731_; lean_object* v_versionTags_2732_; lean_object* v_description_2733_; lean_object* v_keywords_2734_; lean_object* v_homepage_2735_; lean_object* v_license_2736_; lean_object* v_licenseFiles_2737_; lean_object* v_readmeFile_2738_; uint8_t v_reservoir_2739_; lean_object* v_enableArtifactCache_x3f_2740_; lean_object* v_restoreAllArtifacts_x3f_2741_; uint8_t v_libPrefixOnWindows_2742_; uint8_t v_allowImportAll_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v_toWorkspaceConfig_2711_ = lean_ctor_get(v_cfg_2710_, 0);
v_toLeanConfig_2712_ = lean_ctor_get(v_cfg_2710_, 1);
v_bootstrap_2713_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*27);
v_manifestFile_2714_ = lean_ctor_get(v_cfg_2710_, 2);
v_extraDepTargets_2715_ = lean_ctor_get(v_cfg_2710_, 3);
v_precompileModules_2716_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2717_ = lean_ctor_get(v_cfg_2710_, 4);
v_srcDir_2718_ = lean_ctor_get(v_cfg_2710_, 5);
v_buildDir_2719_ = lean_ctor_get(v_cfg_2710_, 6);
v_leanLibDir_2720_ = lean_ctor_get(v_cfg_2710_, 7);
v_nativeLibDir_2721_ = lean_ctor_get(v_cfg_2710_, 8);
v_binDir_2722_ = lean_ctor_get(v_cfg_2710_, 9);
v_irDir_2723_ = lean_ctor_get(v_cfg_2710_, 10);
v_releaseRepo_2724_ = lean_ctor_get(v_cfg_2710_, 11);
v_buildArchive_2725_ = lean_ctor_get(v_cfg_2710_, 12);
v_preferReleaseBuild_2726_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*27 + 2);
v_testDriver_2727_ = lean_ctor_get(v_cfg_2710_, 13);
v_testDriverArgs_2728_ = lean_ctor_get(v_cfg_2710_, 14);
v_lintDriver_2729_ = lean_ctor_get(v_cfg_2710_, 15);
v_lintDriverArgs_2730_ = lean_ctor_get(v_cfg_2710_, 16);
v_version_2731_ = lean_ctor_get(v_cfg_2710_, 17);
v_versionTags_2732_ = lean_ctor_get(v_cfg_2710_, 18);
v_description_2733_ = lean_ctor_get(v_cfg_2710_, 19);
v_keywords_2734_ = lean_ctor_get(v_cfg_2710_, 20);
v_homepage_2735_ = lean_ctor_get(v_cfg_2710_, 21);
v_license_2736_ = lean_ctor_get(v_cfg_2710_, 22);
v_licenseFiles_2737_ = lean_ctor_get(v_cfg_2710_, 23);
v_readmeFile_2738_ = lean_ctor_get(v_cfg_2710_, 24);
v_reservoir_2739_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2740_ = lean_ctor_get(v_cfg_2710_, 25);
v_restoreAllArtifacts_x3f_2741_ = lean_ctor_get(v_cfg_2710_, 26);
v_libPrefixOnWindows_2742_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*27 + 4);
v_allowImportAll_2743_ = lean_ctor_get_uint8(v_cfg_2710_, sizeof(void*)*27 + 5);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_cfg_2710_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2745_ = v_cfg_2710_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2741_);
lean_inc(v_enableArtifactCache_x3f_2740_);
lean_inc(v_readmeFile_2738_);
lean_inc(v_licenseFiles_2737_);
lean_inc(v_license_2736_);
lean_inc(v_homepage_2735_);
lean_inc(v_keywords_2734_);
lean_inc(v_description_2733_);
lean_inc(v_versionTags_2732_);
lean_inc(v_version_2731_);
lean_inc(v_lintDriverArgs_2730_);
lean_inc(v_lintDriver_2729_);
lean_inc(v_testDriverArgs_2728_);
lean_inc(v_testDriver_2727_);
lean_inc(v_buildArchive_2725_);
lean_inc(v_releaseRepo_2724_);
lean_inc(v_irDir_2723_);
lean_inc(v_binDir_2722_);
lean_inc(v_nativeLibDir_2721_);
lean_inc(v_leanLibDir_2720_);
lean_inc(v_buildDir_2719_);
lean_inc(v_srcDir_2718_);
lean_inc(v_moreGlobalServerArgs_2717_);
lean_inc(v_extraDepTargets_2715_);
lean_inc(v_manifestFile_2714_);
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
v___x_2747_ = lean_apply_1(v_f_2709_, v_license_2736_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 22, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_toWorkspaceConfig_2711_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_toLeanConfig_2712_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_manifestFile_2714_);
lean_ctor_set(v_reuseFailAlloc_2750_, 3, v_extraDepTargets_2715_);
lean_ctor_set(v_reuseFailAlloc_2750_, 4, v_moreGlobalServerArgs_2717_);
lean_ctor_set(v_reuseFailAlloc_2750_, 5, v_srcDir_2718_);
lean_ctor_set(v_reuseFailAlloc_2750_, 6, v_buildDir_2719_);
lean_ctor_set(v_reuseFailAlloc_2750_, 7, v_leanLibDir_2720_);
lean_ctor_set(v_reuseFailAlloc_2750_, 8, v_nativeLibDir_2721_);
lean_ctor_set(v_reuseFailAlloc_2750_, 9, v_binDir_2722_);
lean_ctor_set(v_reuseFailAlloc_2750_, 10, v_irDir_2723_);
lean_ctor_set(v_reuseFailAlloc_2750_, 11, v_releaseRepo_2724_);
lean_ctor_set(v_reuseFailAlloc_2750_, 12, v_buildArchive_2725_);
lean_ctor_set(v_reuseFailAlloc_2750_, 13, v_testDriver_2727_);
lean_ctor_set(v_reuseFailAlloc_2750_, 14, v_testDriverArgs_2728_);
lean_ctor_set(v_reuseFailAlloc_2750_, 15, v_lintDriver_2729_);
lean_ctor_set(v_reuseFailAlloc_2750_, 16, v_lintDriverArgs_2730_);
lean_ctor_set(v_reuseFailAlloc_2750_, 17, v_version_2731_);
lean_ctor_set(v_reuseFailAlloc_2750_, 18, v_versionTags_2732_);
lean_ctor_set(v_reuseFailAlloc_2750_, 19, v_description_2733_);
lean_ctor_set(v_reuseFailAlloc_2750_, 20, v_keywords_2734_);
lean_ctor_set(v_reuseFailAlloc_2750_, 21, v_homepage_2735_);
lean_ctor_set(v_reuseFailAlloc_2750_, 22, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2750_, 23, v_licenseFiles_2737_);
lean_ctor_set(v_reuseFailAlloc_2750_, 24, v_readmeFile_2738_);
lean_ctor_set(v_reuseFailAlloc_2750_, 25, v_enableArtifactCache_x3f_2740_);
lean_ctor_set(v_reuseFailAlloc_2750_, 26, v_restoreAllArtifacts_x3f_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*27, v_bootstrap_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*27 + 1, v_precompileModules_2716_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*27 + 3, v_reservoir_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*27 + 5, v_allowImportAll_2743_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2760_, lean_object* v_n_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2763_, lean_object* v_n_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lake_PackageConfig_license___proj(v_p_2763_, v_n_2764_);
lean_dec(v_n_2764_);
lean_dec(v_p_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2766_, lean_object* v_n_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lake_PackageConfig_license___proj(v_p_2766_, v_n_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2769_, lean_object* v_n_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lake_PackageConfig_license_instConfigField(v_p_2769_, v_n_2770_);
lean_dec(v_n_2770_);
lean_dec(v_p_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* v_cfg_2772_){
_start:
{
lean_object* v_licenseFiles_2773_; 
v_licenseFiles_2773_ = lean_ctor_get(v_cfg_2772_, 23);
lean_inc_ref(v_licenseFiles_2773_);
return v_licenseFiles_2773_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* v_cfg_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lake_PackageConfig_licenseFiles___proj___lam__0(v_cfg_2774_);
lean_dec_ref(v_cfg_2774_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* v_val_2776_, lean_object* v_cfg_2777_){
_start:
{
lean_object* v_toWorkspaceConfig_2778_; lean_object* v_toLeanConfig_2779_; uint8_t v_bootstrap_2780_; lean_object* v_manifestFile_2781_; lean_object* v_extraDepTargets_2782_; uint8_t v_precompileModules_2783_; lean_object* v_moreGlobalServerArgs_2784_; lean_object* v_srcDir_2785_; lean_object* v_buildDir_2786_; lean_object* v_leanLibDir_2787_; lean_object* v_nativeLibDir_2788_; lean_object* v_binDir_2789_; lean_object* v_irDir_2790_; lean_object* v_releaseRepo_2791_; lean_object* v_buildArchive_2792_; uint8_t v_preferReleaseBuild_2793_; lean_object* v_testDriver_2794_; lean_object* v_testDriverArgs_2795_; lean_object* v_lintDriver_2796_; lean_object* v_lintDriverArgs_2797_; lean_object* v_version_2798_; lean_object* v_versionTags_2799_; lean_object* v_description_2800_; lean_object* v_keywords_2801_; lean_object* v_homepage_2802_; lean_object* v_license_2803_; lean_object* v_readmeFile_2804_; uint8_t v_reservoir_2805_; lean_object* v_enableArtifactCache_x3f_2806_; lean_object* v_restoreAllArtifacts_x3f_2807_; uint8_t v_libPrefixOnWindows_2808_; uint8_t v_allowImportAll_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_toWorkspaceConfig_2778_ = lean_ctor_get(v_cfg_2777_, 0);
v_toLeanConfig_2779_ = lean_ctor_get(v_cfg_2777_, 1);
v_bootstrap_2780_ = lean_ctor_get_uint8(v_cfg_2777_, sizeof(void*)*27);
v_manifestFile_2781_ = lean_ctor_get(v_cfg_2777_, 2);
v_extraDepTargets_2782_ = lean_ctor_get(v_cfg_2777_, 3);
v_precompileModules_2783_ = lean_ctor_get_uint8(v_cfg_2777_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2784_ = lean_ctor_get(v_cfg_2777_, 4);
v_srcDir_2785_ = lean_ctor_get(v_cfg_2777_, 5);
v_buildDir_2786_ = lean_ctor_get(v_cfg_2777_, 6);
v_leanLibDir_2787_ = lean_ctor_get(v_cfg_2777_, 7);
v_nativeLibDir_2788_ = lean_ctor_get(v_cfg_2777_, 8);
v_binDir_2789_ = lean_ctor_get(v_cfg_2777_, 9);
v_irDir_2790_ = lean_ctor_get(v_cfg_2777_, 10);
v_releaseRepo_2791_ = lean_ctor_get(v_cfg_2777_, 11);
v_buildArchive_2792_ = lean_ctor_get(v_cfg_2777_, 12);
v_preferReleaseBuild_2793_ = lean_ctor_get_uint8(v_cfg_2777_, sizeof(void*)*27 + 2);
v_testDriver_2794_ = lean_ctor_get(v_cfg_2777_, 13);
v_testDriverArgs_2795_ = lean_ctor_get(v_cfg_2777_, 14);
v_lintDriver_2796_ = lean_ctor_get(v_cfg_2777_, 15);
v_lintDriverArgs_2797_ = lean_ctor_get(v_cfg_2777_, 16);
v_version_2798_ = lean_ctor_get(v_cfg_2777_, 17);
v_versionTags_2799_ = lean_ctor_get(v_cfg_2777_, 18);
v_description_2800_ = lean_ctor_get(v_cfg_2777_, 19);
v_keywords_2801_ = lean_ctor_get(v_cfg_2777_, 20);
v_homepage_2802_ = lean_ctor_get(v_cfg_2777_, 21);
v_license_2803_ = lean_ctor_get(v_cfg_2777_, 22);
v_readmeFile_2804_ = lean_ctor_get(v_cfg_2777_, 24);
v_reservoir_2805_ = lean_ctor_get_uint8(v_cfg_2777_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2806_ = lean_ctor_get(v_cfg_2777_, 25);
v_restoreAllArtifacts_x3f_2807_ = lean_ctor_get(v_cfg_2777_, 26);
v_libPrefixOnWindows_2808_ = lean_ctor_get_uint8(v_cfg_2777_, sizeof(void*)*27 + 4);
v_allowImportAll_2809_ = lean_ctor_get_uint8(v_cfg_2777_, sizeof(void*)*27 + 5);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_cfg_2777_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v_cfg_2777_, 23);
lean_dec(v_unused_2817_);
v___x_2811_ = v_cfg_2777_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2807_);
lean_inc(v_enableArtifactCache_x3f_2806_);
lean_inc(v_readmeFile_2804_);
lean_inc(v_license_2803_);
lean_inc(v_homepage_2802_);
lean_inc(v_keywords_2801_);
lean_inc(v_description_2800_);
lean_inc(v_versionTags_2799_);
lean_inc(v_version_2798_);
lean_inc(v_lintDriverArgs_2797_);
lean_inc(v_lintDriver_2796_);
lean_inc(v_testDriverArgs_2795_);
lean_inc(v_testDriver_2794_);
lean_inc(v_buildArchive_2792_);
lean_inc(v_releaseRepo_2791_);
lean_inc(v_irDir_2790_);
lean_inc(v_binDir_2789_);
lean_inc(v_nativeLibDir_2788_);
lean_inc(v_leanLibDir_2787_);
lean_inc(v_buildDir_2786_);
lean_inc(v_srcDir_2785_);
lean_inc(v_moreGlobalServerArgs_2784_);
lean_inc(v_extraDepTargets_2782_);
lean_inc(v_manifestFile_2781_);
lean_inc(v_toLeanConfig_2779_);
lean_inc(v_toWorkspaceConfig_2778_);
lean_dec(v_cfg_2777_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 23, v_val_2776_);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_toWorkspaceConfig_2778_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_toLeanConfig_2779_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_manifestFile_2781_);
lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_extraDepTargets_2782_);
lean_ctor_set(v_reuseFailAlloc_2815_, 4, v_moreGlobalServerArgs_2784_);
lean_ctor_set(v_reuseFailAlloc_2815_, 5, v_srcDir_2785_);
lean_ctor_set(v_reuseFailAlloc_2815_, 6, v_buildDir_2786_);
lean_ctor_set(v_reuseFailAlloc_2815_, 7, v_leanLibDir_2787_);
lean_ctor_set(v_reuseFailAlloc_2815_, 8, v_nativeLibDir_2788_);
lean_ctor_set(v_reuseFailAlloc_2815_, 9, v_binDir_2789_);
lean_ctor_set(v_reuseFailAlloc_2815_, 10, v_irDir_2790_);
lean_ctor_set(v_reuseFailAlloc_2815_, 11, v_releaseRepo_2791_);
lean_ctor_set(v_reuseFailAlloc_2815_, 12, v_buildArchive_2792_);
lean_ctor_set(v_reuseFailAlloc_2815_, 13, v_testDriver_2794_);
lean_ctor_set(v_reuseFailAlloc_2815_, 14, v_testDriverArgs_2795_);
lean_ctor_set(v_reuseFailAlloc_2815_, 15, v_lintDriver_2796_);
lean_ctor_set(v_reuseFailAlloc_2815_, 16, v_lintDriverArgs_2797_);
lean_ctor_set(v_reuseFailAlloc_2815_, 17, v_version_2798_);
lean_ctor_set(v_reuseFailAlloc_2815_, 18, v_versionTags_2799_);
lean_ctor_set(v_reuseFailAlloc_2815_, 19, v_description_2800_);
lean_ctor_set(v_reuseFailAlloc_2815_, 20, v_keywords_2801_);
lean_ctor_set(v_reuseFailAlloc_2815_, 21, v_homepage_2802_);
lean_ctor_set(v_reuseFailAlloc_2815_, 22, v_license_2803_);
lean_ctor_set(v_reuseFailAlloc_2815_, 23, v_val_2776_);
lean_ctor_set(v_reuseFailAlloc_2815_, 24, v_readmeFile_2804_);
lean_ctor_set(v_reuseFailAlloc_2815_, 25, v_enableArtifactCache_x3f_2806_);
lean_ctor_set(v_reuseFailAlloc_2815_, 26, v_restoreAllArtifacts_x3f_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2815_, sizeof(void*)*27, v_bootstrap_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2815_, sizeof(void*)*27 + 1, v_precompileModules_2783_);
lean_ctor_set_uint8(v_reuseFailAlloc_2815_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2815_, sizeof(void*)*27 + 3, v_reservoir_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2815_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2815_, sizeof(void*)*27 + 5, v_allowImportAll_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* v_f_2818_, lean_object* v_cfg_2819_){
_start:
{
lean_object* v_toWorkspaceConfig_2820_; lean_object* v_toLeanConfig_2821_; uint8_t v_bootstrap_2822_; lean_object* v_manifestFile_2823_; lean_object* v_extraDepTargets_2824_; uint8_t v_precompileModules_2825_; lean_object* v_moreGlobalServerArgs_2826_; lean_object* v_srcDir_2827_; lean_object* v_buildDir_2828_; lean_object* v_leanLibDir_2829_; lean_object* v_nativeLibDir_2830_; lean_object* v_binDir_2831_; lean_object* v_irDir_2832_; lean_object* v_releaseRepo_2833_; lean_object* v_buildArchive_2834_; uint8_t v_preferReleaseBuild_2835_; lean_object* v_testDriver_2836_; lean_object* v_testDriverArgs_2837_; lean_object* v_lintDriver_2838_; lean_object* v_lintDriverArgs_2839_; lean_object* v_version_2840_; lean_object* v_versionTags_2841_; lean_object* v_description_2842_; lean_object* v_keywords_2843_; lean_object* v_homepage_2844_; lean_object* v_license_2845_; lean_object* v_licenseFiles_2846_; lean_object* v_readmeFile_2847_; uint8_t v_reservoir_2848_; lean_object* v_enableArtifactCache_x3f_2849_; lean_object* v_restoreAllArtifacts_x3f_2850_; uint8_t v_libPrefixOnWindows_2851_; uint8_t v_allowImportAll_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2860_; 
v_toWorkspaceConfig_2820_ = lean_ctor_get(v_cfg_2819_, 0);
v_toLeanConfig_2821_ = lean_ctor_get(v_cfg_2819_, 1);
v_bootstrap_2822_ = lean_ctor_get_uint8(v_cfg_2819_, sizeof(void*)*27);
v_manifestFile_2823_ = lean_ctor_get(v_cfg_2819_, 2);
v_extraDepTargets_2824_ = lean_ctor_get(v_cfg_2819_, 3);
v_precompileModules_2825_ = lean_ctor_get_uint8(v_cfg_2819_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2826_ = lean_ctor_get(v_cfg_2819_, 4);
v_srcDir_2827_ = lean_ctor_get(v_cfg_2819_, 5);
v_buildDir_2828_ = lean_ctor_get(v_cfg_2819_, 6);
v_leanLibDir_2829_ = lean_ctor_get(v_cfg_2819_, 7);
v_nativeLibDir_2830_ = lean_ctor_get(v_cfg_2819_, 8);
v_binDir_2831_ = lean_ctor_get(v_cfg_2819_, 9);
v_irDir_2832_ = lean_ctor_get(v_cfg_2819_, 10);
v_releaseRepo_2833_ = lean_ctor_get(v_cfg_2819_, 11);
v_buildArchive_2834_ = lean_ctor_get(v_cfg_2819_, 12);
v_preferReleaseBuild_2835_ = lean_ctor_get_uint8(v_cfg_2819_, sizeof(void*)*27 + 2);
v_testDriver_2836_ = lean_ctor_get(v_cfg_2819_, 13);
v_testDriverArgs_2837_ = lean_ctor_get(v_cfg_2819_, 14);
v_lintDriver_2838_ = lean_ctor_get(v_cfg_2819_, 15);
v_lintDriverArgs_2839_ = lean_ctor_get(v_cfg_2819_, 16);
v_version_2840_ = lean_ctor_get(v_cfg_2819_, 17);
v_versionTags_2841_ = lean_ctor_get(v_cfg_2819_, 18);
v_description_2842_ = lean_ctor_get(v_cfg_2819_, 19);
v_keywords_2843_ = lean_ctor_get(v_cfg_2819_, 20);
v_homepage_2844_ = lean_ctor_get(v_cfg_2819_, 21);
v_license_2845_ = lean_ctor_get(v_cfg_2819_, 22);
v_licenseFiles_2846_ = lean_ctor_get(v_cfg_2819_, 23);
v_readmeFile_2847_ = lean_ctor_get(v_cfg_2819_, 24);
v_reservoir_2848_ = lean_ctor_get_uint8(v_cfg_2819_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2849_ = lean_ctor_get(v_cfg_2819_, 25);
v_restoreAllArtifacts_x3f_2850_ = lean_ctor_get(v_cfg_2819_, 26);
v_libPrefixOnWindows_2851_ = lean_ctor_get_uint8(v_cfg_2819_, sizeof(void*)*27 + 4);
v_allowImportAll_2852_ = lean_ctor_get_uint8(v_cfg_2819_, sizeof(void*)*27 + 5);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_cfg_2819_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2854_ = v_cfg_2819_;
v_isShared_2855_ = v_isSharedCheck_2860_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2850_);
lean_inc(v_enableArtifactCache_x3f_2849_);
lean_inc(v_readmeFile_2847_);
lean_inc(v_licenseFiles_2846_);
lean_inc(v_license_2845_);
lean_inc(v_homepage_2844_);
lean_inc(v_keywords_2843_);
lean_inc(v_description_2842_);
lean_inc(v_versionTags_2841_);
lean_inc(v_version_2840_);
lean_inc(v_lintDriverArgs_2839_);
lean_inc(v_lintDriver_2838_);
lean_inc(v_testDriverArgs_2837_);
lean_inc(v_testDriver_2836_);
lean_inc(v_buildArchive_2834_);
lean_inc(v_releaseRepo_2833_);
lean_inc(v_irDir_2832_);
lean_inc(v_binDir_2831_);
lean_inc(v_nativeLibDir_2830_);
lean_inc(v_leanLibDir_2829_);
lean_inc(v_buildDir_2828_);
lean_inc(v_srcDir_2827_);
lean_inc(v_moreGlobalServerArgs_2826_);
lean_inc(v_extraDepTargets_2824_);
lean_inc(v_manifestFile_2823_);
lean_inc(v_toLeanConfig_2821_);
lean_inc(v_toWorkspaceConfig_2820_);
lean_dec(v_cfg_2819_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2860_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
v___x_2856_ = lean_apply_1(v_f_2818_, v_licenseFiles_2846_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 23, v___x_2856_);
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_toWorkspaceConfig_2820_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_toLeanConfig_2821_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_manifestFile_2823_);
lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_extraDepTargets_2824_);
lean_ctor_set(v_reuseFailAlloc_2859_, 4, v_moreGlobalServerArgs_2826_);
lean_ctor_set(v_reuseFailAlloc_2859_, 5, v_srcDir_2827_);
lean_ctor_set(v_reuseFailAlloc_2859_, 6, v_buildDir_2828_);
lean_ctor_set(v_reuseFailAlloc_2859_, 7, v_leanLibDir_2829_);
lean_ctor_set(v_reuseFailAlloc_2859_, 8, v_nativeLibDir_2830_);
lean_ctor_set(v_reuseFailAlloc_2859_, 9, v_binDir_2831_);
lean_ctor_set(v_reuseFailAlloc_2859_, 10, v_irDir_2832_);
lean_ctor_set(v_reuseFailAlloc_2859_, 11, v_releaseRepo_2833_);
lean_ctor_set(v_reuseFailAlloc_2859_, 12, v_buildArchive_2834_);
lean_ctor_set(v_reuseFailAlloc_2859_, 13, v_testDriver_2836_);
lean_ctor_set(v_reuseFailAlloc_2859_, 14, v_testDriverArgs_2837_);
lean_ctor_set(v_reuseFailAlloc_2859_, 15, v_lintDriver_2838_);
lean_ctor_set(v_reuseFailAlloc_2859_, 16, v_lintDriverArgs_2839_);
lean_ctor_set(v_reuseFailAlloc_2859_, 17, v_version_2840_);
lean_ctor_set(v_reuseFailAlloc_2859_, 18, v_versionTags_2841_);
lean_ctor_set(v_reuseFailAlloc_2859_, 19, v_description_2842_);
lean_ctor_set(v_reuseFailAlloc_2859_, 20, v_keywords_2843_);
lean_ctor_set(v_reuseFailAlloc_2859_, 21, v_homepage_2844_);
lean_ctor_set(v_reuseFailAlloc_2859_, 22, v_license_2845_);
lean_ctor_set(v_reuseFailAlloc_2859_, 23, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2859_, 24, v_readmeFile_2847_);
lean_ctor_set(v_reuseFailAlloc_2859_, 25, v_enableArtifactCache_x3f_2849_);
lean_ctor_set(v_reuseFailAlloc_2859_, 26, v_restoreAllArtifacts_x3f_2850_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*27, v_bootstrap_2822_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*27 + 1, v_precompileModules_2825_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2835_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*27 + 3, v_reservoir_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2851_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*27 + 5, v_allowImportAll_2852_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* v_x_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1));
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* v_x_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lake_PackageConfig_licenseFiles___proj___lam__3(v_x_2868_);
lean_dec_ref(v_x_2868_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_2879_, lean_object* v_n_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_2882_, lean_object* v_n_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2882_, v_n_2883_);
lean_dec(v_n_2883_);
lean_dec(v_p_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_2885_, lean_object* v_n_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2885_, v_n_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_2888_, lean_object* v_n_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_2888_, v_n_2889_);
lean_dec(v_n_2889_);
lean_dec(v_p_2888_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* v_cfg_2891_){
_start:
{
lean_object* v_readmeFile_2892_; 
v_readmeFile_2892_ = lean_ctor_get(v_cfg_2891_, 24);
lean_inc_ref(v_readmeFile_2892_);
return v_readmeFile_2892_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* v_cfg_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lake_PackageConfig_readmeFile___proj___lam__0(v_cfg_2893_);
lean_dec_ref(v_cfg_2893_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* v_val_2895_, lean_object* v_cfg_2896_){
_start:
{
lean_object* v_toWorkspaceConfig_2897_; lean_object* v_toLeanConfig_2898_; uint8_t v_bootstrap_2899_; lean_object* v_manifestFile_2900_; lean_object* v_extraDepTargets_2901_; uint8_t v_precompileModules_2902_; lean_object* v_moreGlobalServerArgs_2903_; lean_object* v_srcDir_2904_; lean_object* v_buildDir_2905_; lean_object* v_leanLibDir_2906_; lean_object* v_nativeLibDir_2907_; lean_object* v_binDir_2908_; lean_object* v_irDir_2909_; lean_object* v_releaseRepo_2910_; lean_object* v_buildArchive_2911_; uint8_t v_preferReleaseBuild_2912_; lean_object* v_testDriver_2913_; lean_object* v_testDriverArgs_2914_; lean_object* v_lintDriver_2915_; lean_object* v_lintDriverArgs_2916_; lean_object* v_version_2917_; lean_object* v_versionTags_2918_; lean_object* v_description_2919_; lean_object* v_keywords_2920_; lean_object* v_homepage_2921_; lean_object* v_license_2922_; lean_object* v_licenseFiles_2923_; uint8_t v_reservoir_2924_; lean_object* v_enableArtifactCache_x3f_2925_; lean_object* v_restoreAllArtifacts_x3f_2926_; uint8_t v_libPrefixOnWindows_2927_; uint8_t v_allowImportAll_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
v_toWorkspaceConfig_2897_ = lean_ctor_get(v_cfg_2896_, 0);
v_toLeanConfig_2898_ = lean_ctor_get(v_cfg_2896_, 1);
v_bootstrap_2899_ = lean_ctor_get_uint8(v_cfg_2896_, sizeof(void*)*27);
v_manifestFile_2900_ = lean_ctor_get(v_cfg_2896_, 2);
v_extraDepTargets_2901_ = lean_ctor_get(v_cfg_2896_, 3);
v_precompileModules_2902_ = lean_ctor_get_uint8(v_cfg_2896_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2903_ = lean_ctor_get(v_cfg_2896_, 4);
v_srcDir_2904_ = lean_ctor_get(v_cfg_2896_, 5);
v_buildDir_2905_ = lean_ctor_get(v_cfg_2896_, 6);
v_leanLibDir_2906_ = lean_ctor_get(v_cfg_2896_, 7);
v_nativeLibDir_2907_ = lean_ctor_get(v_cfg_2896_, 8);
v_binDir_2908_ = lean_ctor_get(v_cfg_2896_, 9);
v_irDir_2909_ = lean_ctor_get(v_cfg_2896_, 10);
v_releaseRepo_2910_ = lean_ctor_get(v_cfg_2896_, 11);
v_buildArchive_2911_ = lean_ctor_get(v_cfg_2896_, 12);
v_preferReleaseBuild_2912_ = lean_ctor_get_uint8(v_cfg_2896_, sizeof(void*)*27 + 2);
v_testDriver_2913_ = lean_ctor_get(v_cfg_2896_, 13);
v_testDriverArgs_2914_ = lean_ctor_get(v_cfg_2896_, 14);
v_lintDriver_2915_ = lean_ctor_get(v_cfg_2896_, 15);
v_lintDriverArgs_2916_ = lean_ctor_get(v_cfg_2896_, 16);
v_version_2917_ = lean_ctor_get(v_cfg_2896_, 17);
v_versionTags_2918_ = lean_ctor_get(v_cfg_2896_, 18);
v_description_2919_ = lean_ctor_get(v_cfg_2896_, 19);
v_keywords_2920_ = lean_ctor_get(v_cfg_2896_, 20);
v_homepage_2921_ = lean_ctor_get(v_cfg_2896_, 21);
v_license_2922_ = lean_ctor_get(v_cfg_2896_, 22);
v_licenseFiles_2923_ = lean_ctor_get(v_cfg_2896_, 23);
v_reservoir_2924_ = lean_ctor_get_uint8(v_cfg_2896_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2925_ = lean_ctor_get(v_cfg_2896_, 25);
v_restoreAllArtifacts_x3f_2926_ = lean_ctor_get(v_cfg_2896_, 26);
v_libPrefixOnWindows_2927_ = lean_ctor_get_uint8(v_cfg_2896_, sizeof(void*)*27 + 4);
v_allowImportAll_2928_ = lean_ctor_get_uint8(v_cfg_2896_, sizeof(void*)*27 + 5);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_cfg_2896_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; 
v_unused_2936_ = lean_ctor_get(v_cfg_2896_, 24);
lean_dec(v_unused_2936_);
v___x_2930_ = v_cfg_2896_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2926_);
lean_inc(v_enableArtifactCache_x3f_2925_);
lean_inc(v_licenseFiles_2923_);
lean_inc(v_license_2922_);
lean_inc(v_homepage_2921_);
lean_inc(v_keywords_2920_);
lean_inc(v_description_2919_);
lean_inc(v_versionTags_2918_);
lean_inc(v_version_2917_);
lean_inc(v_lintDriverArgs_2916_);
lean_inc(v_lintDriver_2915_);
lean_inc(v_testDriverArgs_2914_);
lean_inc(v_testDriver_2913_);
lean_inc(v_buildArchive_2911_);
lean_inc(v_releaseRepo_2910_);
lean_inc(v_irDir_2909_);
lean_inc(v_binDir_2908_);
lean_inc(v_nativeLibDir_2907_);
lean_inc(v_leanLibDir_2906_);
lean_inc(v_buildDir_2905_);
lean_inc(v_srcDir_2904_);
lean_inc(v_moreGlobalServerArgs_2903_);
lean_inc(v_extraDepTargets_2901_);
lean_inc(v_manifestFile_2900_);
lean_inc(v_toLeanConfig_2898_);
lean_inc(v_toWorkspaceConfig_2897_);
lean_dec(v_cfg_2896_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 24, v_val_2895_);
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_toWorkspaceConfig_2897_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_toLeanConfig_2898_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_manifestFile_2900_);
lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_extraDepTargets_2901_);
lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_moreGlobalServerArgs_2903_);
lean_ctor_set(v_reuseFailAlloc_2934_, 5, v_srcDir_2904_);
lean_ctor_set(v_reuseFailAlloc_2934_, 6, v_buildDir_2905_);
lean_ctor_set(v_reuseFailAlloc_2934_, 7, v_leanLibDir_2906_);
lean_ctor_set(v_reuseFailAlloc_2934_, 8, v_nativeLibDir_2907_);
lean_ctor_set(v_reuseFailAlloc_2934_, 9, v_binDir_2908_);
lean_ctor_set(v_reuseFailAlloc_2934_, 10, v_irDir_2909_);
lean_ctor_set(v_reuseFailAlloc_2934_, 11, v_releaseRepo_2910_);
lean_ctor_set(v_reuseFailAlloc_2934_, 12, v_buildArchive_2911_);
lean_ctor_set(v_reuseFailAlloc_2934_, 13, v_testDriver_2913_);
lean_ctor_set(v_reuseFailAlloc_2934_, 14, v_testDriverArgs_2914_);
lean_ctor_set(v_reuseFailAlloc_2934_, 15, v_lintDriver_2915_);
lean_ctor_set(v_reuseFailAlloc_2934_, 16, v_lintDriverArgs_2916_);
lean_ctor_set(v_reuseFailAlloc_2934_, 17, v_version_2917_);
lean_ctor_set(v_reuseFailAlloc_2934_, 18, v_versionTags_2918_);
lean_ctor_set(v_reuseFailAlloc_2934_, 19, v_description_2919_);
lean_ctor_set(v_reuseFailAlloc_2934_, 20, v_keywords_2920_);
lean_ctor_set(v_reuseFailAlloc_2934_, 21, v_homepage_2921_);
lean_ctor_set(v_reuseFailAlloc_2934_, 22, v_license_2922_);
lean_ctor_set(v_reuseFailAlloc_2934_, 23, v_licenseFiles_2923_);
lean_ctor_set(v_reuseFailAlloc_2934_, 24, v_val_2895_);
lean_ctor_set(v_reuseFailAlloc_2934_, 25, v_enableArtifactCache_x3f_2925_);
lean_ctor_set(v_reuseFailAlloc_2934_, 26, v_restoreAllArtifacts_x3f_2926_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*27, v_bootstrap_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*27 + 1, v_precompileModules_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2912_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*27 + 3, v_reservoir_2924_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2927_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*27 + 5, v_allowImportAll_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* v_f_2937_, lean_object* v_cfg_2938_){
_start:
{
lean_object* v_toWorkspaceConfig_2939_; lean_object* v_toLeanConfig_2940_; uint8_t v_bootstrap_2941_; lean_object* v_manifestFile_2942_; lean_object* v_extraDepTargets_2943_; uint8_t v_precompileModules_2944_; lean_object* v_moreGlobalServerArgs_2945_; lean_object* v_srcDir_2946_; lean_object* v_buildDir_2947_; lean_object* v_leanLibDir_2948_; lean_object* v_nativeLibDir_2949_; lean_object* v_binDir_2950_; lean_object* v_irDir_2951_; lean_object* v_releaseRepo_2952_; lean_object* v_buildArchive_2953_; uint8_t v_preferReleaseBuild_2954_; lean_object* v_testDriver_2955_; lean_object* v_testDriverArgs_2956_; lean_object* v_lintDriver_2957_; lean_object* v_lintDriverArgs_2958_; lean_object* v_version_2959_; lean_object* v_versionTags_2960_; lean_object* v_description_2961_; lean_object* v_keywords_2962_; lean_object* v_homepage_2963_; lean_object* v_license_2964_; lean_object* v_licenseFiles_2965_; lean_object* v_readmeFile_2966_; uint8_t v_reservoir_2967_; lean_object* v_enableArtifactCache_x3f_2968_; lean_object* v_restoreAllArtifacts_x3f_2969_; uint8_t v_libPrefixOnWindows_2970_; uint8_t v_allowImportAll_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2979_; 
v_toWorkspaceConfig_2939_ = lean_ctor_get(v_cfg_2938_, 0);
v_toLeanConfig_2940_ = lean_ctor_get(v_cfg_2938_, 1);
v_bootstrap_2941_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*27);
v_manifestFile_2942_ = lean_ctor_get(v_cfg_2938_, 2);
v_extraDepTargets_2943_ = lean_ctor_get(v_cfg_2938_, 3);
v_precompileModules_2944_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2945_ = lean_ctor_get(v_cfg_2938_, 4);
v_srcDir_2946_ = lean_ctor_get(v_cfg_2938_, 5);
v_buildDir_2947_ = lean_ctor_get(v_cfg_2938_, 6);
v_leanLibDir_2948_ = lean_ctor_get(v_cfg_2938_, 7);
v_nativeLibDir_2949_ = lean_ctor_get(v_cfg_2938_, 8);
v_binDir_2950_ = lean_ctor_get(v_cfg_2938_, 9);
v_irDir_2951_ = lean_ctor_get(v_cfg_2938_, 10);
v_releaseRepo_2952_ = lean_ctor_get(v_cfg_2938_, 11);
v_buildArchive_2953_ = lean_ctor_get(v_cfg_2938_, 12);
v_preferReleaseBuild_2954_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*27 + 2);
v_testDriver_2955_ = lean_ctor_get(v_cfg_2938_, 13);
v_testDriverArgs_2956_ = lean_ctor_get(v_cfg_2938_, 14);
v_lintDriver_2957_ = lean_ctor_get(v_cfg_2938_, 15);
v_lintDriverArgs_2958_ = lean_ctor_get(v_cfg_2938_, 16);
v_version_2959_ = lean_ctor_get(v_cfg_2938_, 17);
v_versionTags_2960_ = lean_ctor_get(v_cfg_2938_, 18);
v_description_2961_ = lean_ctor_get(v_cfg_2938_, 19);
v_keywords_2962_ = lean_ctor_get(v_cfg_2938_, 20);
v_homepage_2963_ = lean_ctor_get(v_cfg_2938_, 21);
v_license_2964_ = lean_ctor_get(v_cfg_2938_, 22);
v_licenseFiles_2965_ = lean_ctor_get(v_cfg_2938_, 23);
v_readmeFile_2966_ = lean_ctor_get(v_cfg_2938_, 24);
v_reservoir_2967_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2968_ = lean_ctor_get(v_cfg_2938_, 25);
v_restoreAllArtifacts_x3f_2969_ = lean_ctor_get(v_cfg_2938_, 26);
v_libPrefixOnWindows_2970_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*27 + 4);
v_allowImportAll_2971_ = lean_ctor_get_uint8(v_cfg_2938_, sizeof(void*)*27 + 5);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_cfg_2938_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2973_ = v_cfg_2938_;
v_isShared_2974_ = v_isSharedCheck_2979_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2969_);
lean_inc(v_enableArtifactCache_x3f_2968_);
lean_inc(v_readmeFile_2966_);
lean_inc(v_licenseFiles_2965_);
lean_inc(v_license_2964_);
lean_inc(v_homepage_2963_);
lean_inc(v_keywords_2962_);
lean_inc(v_description_2961_);
lean_inc(v_versionTags_2960_);
lean_inc(v_version_2959_);
lean_inc(v_lintDriverArgs_2958_);
lean_inc(v_lintDriver_2957_);
lean_inc(v_testDriverArgs_2956_);
lean_inc(v_testDriver_2955_);
lean_inc(v_buildArchive_2953_);
lean_inc(v_releaseRepo_2952_);
lean_inc(v_irDir_2951_);
lean_inc(v_binDir_2950_);
lean_inc(v_nativeLibDir_2949_);
lean_inc(v_leanLibDir_2948_);
lean_inc(v_buildDir_2947_);
lean_inc(v_srcDir_2946_);
lean_inc(v_moreGlobalServerArgs_2945_);
lean_inc(v_extraDepTargets_2943_);
lean_inc(v_manifestFile_2942_);
lean_inc(v_toLeanConfig_2940_);
lean_inc(v_toWorkspaceConfig_2939_);
lean_dec(v_cfg_2938_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2979_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2975_ = lean_apply_1(v_f_2937_, v_readmeFile_2966_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 24, v___x_2975_);
v___x_2977_ = v___x_2973_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_toWorkspaceConfig_2939_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_toLeanConfig_2940_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v_manifestFile_2942_);
lean_ctor_set(v_reuseFailAlloc_2978_, 3, v_extraDepTargets_2943_);
lean_ctor_set(v_reuseFailAlloc_2978_, 4, v_moreGlobalServerArgs_2945_);
lean_ctor_set(v_reuseFailAlloc_2978_, 5, v_srcDir_2946_);
lean_ctor_set(v_reuseFailAlloc_2978_, 6, v_buildDir_2947_);
lean_ctor_set(v_reuseFailAlloc_2978_, 7, v_leanLibDir_2948_);
lean_ctor_set(v_reuseFailAlloc_2978_, 8, v_nativeLibDir_2949_);
lean_ctor_set(v_reuseFailAlloc_2978_, 9, v_binDir_2950_);
lean_ctor_set(v_reuseFailAlloc_2978_, 10, v_irDir_2951_);
lean_ctor_set(v_reuseFailAlloc_2978_, 11, v_releaseRepo_2952_);
lean_ctor_set(v_reuseFailAlloc_2978_, 12, v_buildArchive_2953_);
lean_ctor_set(v_reuseFailAlloc_2978_, 13, v_testDriver_2955_);
lean_ctor_set(v_reuseFailAlloc_2978_, 14, v_testDriverArgs_2956_);
lean_ctor_set(v_reuseFailAlloc_2978_, 15, v_lintDriver_2957_);
lean_ctor_set(v_reuseFailAlloc_2978_, 16, v_lintDriverArgs_2958_);
lean_ctor_set(v_reuseFailAlloc_2978_, 17, v_version_2959_);
lean_ctor_set(v_reuseFailAlloc_2978_, 18, v_versionTags_2960_);
lean_ctor_set(v_reuseFailAlloc_2978_, 19, v_description_2961_);
lean_ctor_set(v_reuseFailAlloc_2978_, 20, v_keywords_2962_);
lean_ctor_set(v_reuseFailAlloc_2978_, 21, v_homepage_2963_);
lean_ctor_set(v_reuseFailAlloc_2978_, 22, v_license_2964_);
lean_ctor_set(v_reuseFailAlloc_2978_, 23, v_licenseFiles_2965_);
lean_ctor_set(v_reuseFailAlloc_2978_, 24, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2978_, 25, v_enableArtifactCache_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_2978_, 26, v_restoreAllArtifacts_x3f_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*27, v_bootstrap_2941_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*27 + 1, v_precompileModules_2944_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*27 + 3, v_reservoir_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2970_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*27 + 5, v_allowImportAll_2971_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* v_x_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0));
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* v_x_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lake_PackageConfig_readmeFile___proj___lam__3(v_x_2983_);
lean_dec_ref(v_x_2983_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_2994_, lean_object* v_n_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_2997_, lean_object* v_n_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2997_, v_n_2998_);
lean_dec(v_n_2998_);
lean_dec(v_p_2997_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_3000_, lean_object* v_n_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lake_PackageConfig_readmeFile___proj(v_p_3000_, v_n_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_3003_, lean_object* v_n_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_3003_, v_n_3004_);
lean_dec(v_n_3004_);
lean_dec(v_p_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* v_cfg_3006_){
_start:
{
uint8_t v_reservoir_3007_; 
v_reservoir_3007_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 3);
return v_reservoir_3007_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* v_cfg_3008_){
_start:
{
uint8_t v_res_3009_; lean_object* v_r_3010_; 
v_res_3009_ = l_Lake_PackageConfig_reservoir___proj___lam__0(v_cfg_3008_);
lean_dec_ref(v_cfg_3008_);
v_r_3010_ = lean_box(v_res_3009_);
return v_r_3010_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t v_val_3011_, lean_object* v_cfg_3012_){
_start:
{
lean_object* v_toWorkspaceConfig_3013_; lean_object* v_toLeanConfig_3014_; uint8_t v_bootstrap_3015_; lean_object* v_manifestFile_3016_; lean_object* v_extraDepTargets_3017_; uint8_t v_precompileModules_3018_; lean_object* v_moreGlobalServerArgs_3019_; lean_object* v_srcDir_3020_; lean_object* v_buildDir_3021_; lean_object* v_leanLibDir_3022_; lean_object* v_nativeLibDir_3023_; lean_object* v_binDir_3024_; lean_object* v_irDir_3025_; lean_object* v_releaseRepo_3026_; lean_object* v_buildArchive_3027_; uint8_t v_preferReleaseBuild_3028_; lean_object* v_testDriver_3029_; lean_object* v_testDriverArgs_3030_; lean_object* v_lintDriver_3031_; lean_object* v_lintDriverArgs_3032_; lean_object* v_version_3033_; lean_object* v_versionTags_3034_; lean_object* v_description_3035_; lean_object* v_keywords_3036_; lean_object* v_homepage_3037_; lean_object* v_license_3038_; lean_object* v_licenseFiles_3039_; lean_object* v_readmeFile_3040_; lean_object* v_enableArtifactCache_x3f_3041_; lean_object* v_restoreAllArtifacts_x3f_3042_; uint8_t v_libPrefixOnWindows_3043_; uint8_t v_allowImportAll_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_toWorkspaceConfig_3013_ = lean_ctor_get(v_cfg_3012_, 0);
v_toLeanConfig_3014_ = lean_ctor_get(v_cfg_3012_, 1);
v_bootstrap_3015_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*27);
v_manifestFile_3016_ = lean_ctor_get(v_cfg_3012_, 2);
v_extraDepTargets_3017_ = lean_ctor_get(v_cfg_3012_, 3);
v_precompileModules_3018_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3019_ = lean_ctor_get(v_cfg_3012_, 4);
v_srcDir_3020_ = lean_ctor_get(v_cfg_3012_, 5);
v_buildDir_3021_ = lean_ctor_get(v_cfg_3012_, 6);
v_leanLibDir_3022_ = lean_ctor_get(v_cfg_3012_, 7);
v_nativeLibDir_3023_ = lean_ctor_get(v_cfg_3012_, 8);
v_binDir_3024_ = lean_ctor_get(v_cfg_3012_, 9);
v_irDir_3025_ = lean_ctor_get(v_cfg_3012_, 10);
v_releaseRepo_3026_ = lean_ctor_get(v_cfg_3012_, 11);
v_buildArchive_3027_ = lean_ctor_get(v_cfg_3012_, 12);
v_preferReleaseBuild_3028_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*27 + 2);
v_testDriver_3029_ = lean_ctor_get(v_cfg_3012_, 13);
v_testDriverArgs_3030_ = lean_ctor_get(v_cfg_3012_, 14);
v_lintDriver_3031_ = lean_ctor_get(v_cfg_3012_, 15);
v_lintDriverArgs_3032_ = lean_ctor_get(v_cfg_3012_, 16);
v_version_3033_ = lean_ctor_get(v_cfg_3012_, 17);
v_versionTags_3034_ = lean_ctor_get(v_cfg_3012_, 18);
v_description_3035_ = lean_ctor_get(v_cfg_3012_, 19);
v_keywords_3036_ = lean_ctor_get(v_cfg_3012_, 20);
v_homepage_3037_ = lean_ctor_get(v_cfg_3012_, 21);
v_license_3038_ = lean_ctor_get(v_cfg_3012_, 22);
v_licenseFiles_3039_ = lean_ctor_get(v_cfg_3012_, 23);
v_readmeFile_3040_ = lean_ctor_get(v_cfg_3012_, 24);
v_enableArtifactCache_x3f_3041_ = lean_ctor_get(v_cfg_3012_, 25);
v_restoreAllArtifacts_x3f_3042_ = lean_ctor_get(v_cfg_3012_, 26);
v_libPrefixOnWindows_3043_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*27 + 4);
v_allowImportAll_3044_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*27 + 5);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_cfg_3012_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v_cfg_3012_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3042_);
lean_inc(v_enableArtifactCache_x3f_3041_);
lean_inc(v_readmeFile_3040_);
lean_inc(v_licenseFiles_3039_);
lean_inc(v_license_3038_);
lean_inc(v_homepage_3037_);
lean_inc(v_keywords_3036_);
lean_inc(v_description_3035_);
lean_inc(v_versionTags_3034_);
lean_inc(v_version_3033_);
lean_inc(v_lintDriverArgs_3032_);
lean_inc(v_lintDriver_3031_);
lean_inc(v_testDriverArgs_3030_);
lean_inc(v_testDriver_3029_);
lean_inc(v_buildArchive_3027_);
lean_inc(v_releaseRepo_3026_);
lean_inc(v_irDir_3025_);
lean_inc(v_binDir_3024_);
lean_inc(v_nativeLibDir_3023_);
lean_inc(v_leanLibDir_3022_);
lean_inc(v_buildDir_3021_);
lean_inc(v_srcDir_3020_);
lean_inc(v_moreGlobalServerArgs_3019_);
lean_inc(v_extraDepTargets_3017_);
lean_inc(v_manifestFile_3016_);
lean_inc(v_toLeanConfig_3014_);
lean_inc(v_toWorkspaceConfig_3013_);
lean_dec(v_cfg_3012_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_toWorkspaceConfig_3013_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_toLeanConfig_3014_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v_manifestFile_3016_);
lean_ctor_set(v_reuseFailAlloc_3050_, 3, v_extraDepTargets_3017_);
lean_ctor_set(v_reuseFailAlloc_3050_, 4, v_moreGlobalServerArgs_3019_);
lean_ctor_set(v_reuseFailAlloc_3050_, 5, v_srcDir_3020_);
lean_ctor_set(v_reuseFailAlloc_3050_, 6, v_buildDir_3021_);
lean_ctor_set(v_reuseFailAlloc_3050_, 7, v_leanLibDir_3022_);
lean_ctor_set(v_reuseFailAlloc_3050_, 8, v_nativeLibDir_3023_);
lean_ctor_set(v_reuseFailAlloc_3050_, 9, v_binDir_3024_);
lean_ctor_set(v_reuseFailAlloc_3050_, 10, v_irDir_3025_);
lean_ctor_set(v_reuseFailAlloc_3050_, 11, v_releaseRepo_3026_);
lean_ctor_set(v_reuseFailAlloc_3050_, 12, v_buildArchive_3027_);
lean_ctor_set(v_reuseFailAlloc_3050_, 13, v_testDriver_3029_);
lean_ctor_set(v_reuseFailAlloc_3050_, 14, v_testDriverArgs_3030_);
lean_ctor_set(v_reuseFailAlloc_3050_, 15, v_lintDriver_3031_);
lean_ctor_set(v_reuseFailAlloc_3050_, 16, v_lintDriverArgs_3032_);
lean_ctor_set(v_reuseFailAlloc_3050_, 17, v_version_3033_);
lean_ctor_set(v_reuseFailAlloc_3050_, 18, v_versionTags_3034_);
lean_ctor_set(v_reuseFailAlloc_3050_, 19, v_description_3035_);
lean_ctor_set(v_reuseFailAlloc_3050_, 20, v_keywords_3036_);
lean_ctor_set(v_reuseFailAlloc_3050_, 21, v_homepage_3037_);
lean_ctor_set(v_reuseFailAlloc_3050_, 22, v_license_3038_);
lean_ctor_set(v_reuseFailAlloc_3050_, 23, v_licenseFiles_3039_);
lean_ctor_set(v_reuseFailAlloc_3050_, 24, v_readmeFile_3040_);
lean_ctor_set(v_reuseFailAlloc_3050_, 25, v_enableArtifactCache_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3050_, 26, v_restoreAllArtifacts_x3f_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*27, v_bootstrap_3015_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*27 + 1, v_precompileModules_3018_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3043_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*27 + 5, v_allowImportAll_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*27 + 3, v_val_3011_);
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* v_val_3052_, lean_object* v_cfg_3053_){
_start:
{
uint8_t v_val_134__boxed_3054_; lean_object* v_res_3055_; 
v_val_134__boxed_3054_ = lean_unbox(v_val_3052_);
v_res_3055_ = l_Lake_PackageConfig_reservoir___proj___lam__1(v_val_134__boxed_3054_, v_cfg_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* v_f_3056_, lean_object* v_cfg_3057_){
_start:
{
lean_object* v_toWorkspaceConfig_3058_; lean_object* v_toLeanConfig_3059_; uint8_t v_bootstrap_3060_; lean_object* v_manifestFile_3061_; lean_object* v_extraDepTargets_3062_; uint8_t v_precompileModules_3063_; lean_object* v_moreGlobalServerArgs_3064_; lean_object* v_srcDir_3065_; lean_object* v_buildDir_3066_; lean_object* v_leanLibDir_3067_; lean_object* v_nativeLibDir_3068_; lean_object* v_binDir_3069_; lean_object* v_irDir_3070_; lean_object* v_releaseRepo_3071_; lean_object* v_buildArchive_3072_; uint8_t v_preferReleaseBuild_3073_; lean_object* v_testDriver_3074_; lean_object* v_testDriverArgs_3075_; lean_object* v_lintDriver_3076_; lean_object* v_lintDriverArgs_3077_; lean_object* v_version_3078_; lean_object* v_versionTags_3079_; lean_object* v_description_3080_; lean_object* v_keywords_3081_; lean_object* v_homepage_3082_; lean_object* v_license_3083_; lean_object* v_licenseFiles_3084_; lean_object* v_readmeFile_3085_; uint8_t v_reservoir_3086_; lean_object* v_enableArtifactCache_x3f_3087_; lean_object* v_restoreAllArtifacts_x3f_3088_; uint8_t v_libPrefixOnWindows_3089_; uint8_t v_allowImportAll_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3100_; 
v_toWorkspaceConfig_3058_ = lean_ctor_get(v_cfg_3057_, 0);
v_toLeanConfig_3059_ = lean_ctor_get(v_cfg_3057_, 1);
v_bootstrap_3060_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*27);
v_manifestFile_3061_ = lean_ctor_get(v_cfg_3057_, 2);
v_extraDepTargets_3062_ = lean_ctor_get(v_cfg_3057_, 3);
v_precompileModules_3063_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3064_ = lean_ctor_get(v_cfg_3057_, 4);
v_srcDir_3065_ = lean_ctor_get(v_cfg_3057_, 5);
v_buildDir_3066_ = lean_ctor_get(v_cfg_3057_, 6);
v_leanLibDir_3067_ = lean_ctor_get(v_cfg_3057_, 7);
v_nativeLibDir_3068_ = lean_ctor_get(v_cfg_3057_, 8);
v_binDir_3069_ = lean_ctor_get(v_cfg_3057_, 9);
v_irDir_3070_ = lean_ctor_get(v_cfg_3057_, 10);
v_releaseRepo_3071_ = lean_ctor_get(v_cfg_3057_, 11);
v_buildArchive_3072_ = lean_ctor_get(v_cfg_3057_, 12);
v_preferReleaseBuild_3073_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*27 + 2);
v_testDriver_3074_ = lean_ctor_get(v_cfg_3057_, 13);
v_testDriverArgs_3075_ = lean_ctor_get(v_cfg_3057_, 14);
v_lintDriver_3076_ = lean_ctor_get(v_cfg_3057_, 15);
v_lintDriverArgs_3077_ = lean_ctor_get(v_cfg_3057_, 16);
v_version_3078_ = lean_ctor_get(v_cfg_3057_, 17);
v_versionTags_3079_ = lean_ctor_get(v_cfg_3057_, 18);
v_description_3080_ = lean_ctor_get(v_cfg_3057_, 19);
v_keywords_3081_ = lean_ctor_get(v_cfg_3057_, 20);
v_homepage_3082_ = lean_ctor_get(v_cfg_3057_, 21);
v_license_3083_ = lean_ctor_get(v_cfg_3057_, 22);
v_licenseFiles_3084_ = lean_ctor_get(v_cfg_3057_, 23);
v_readmeFile_3085_ = lean_ctor_get(v_cfg_3057_, 24);
v_reservoir_3086_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3087_ = lean_ctor_get(v_cfg_3057_, 25);
v_restoreAllArtifacts_x3f_3088_ = lean_ctor_get(v_cfg_3057_, 26);
v_libPrefixOnWindows_3089_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*27 + 4);
v_allowImportAll_3090_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*27 + 5);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_cfg_3057_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3092_ = v_cfg_3057_;
v_isShared_3093_ = v_isSharedCheck_3100_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3088_);
lean_inc(v_enableArtifactCache_x3f_3087_);
lean_inc(v_readmeFile_3085_);
lean_inc(v_licenseFiles_3084_);
lean_inc(v_license_3083_);
lean_inc(v_homepage_3082_);
lean_inc(v_keywords_3081_);
lean_inc(v_description_3080_);
lean_inc(v_versionTags_3079_);
lean_inc(v_version_3078_);
lean_inc(v_lintDriverArgs_3077_);
lean_inc(v_lintDriver_3076_);
lean_inc(v_testDriverArgs_3075_);
lean_inc(v_testDriver_3074_);
lean_inc(v_buildArchive_3072_);
lean_inc(v_releaseRepo_3071_);
lean_inc(v_irDir_3070_);
lean_inc(v_binDir_3069_);
lean_inc(v_nativeLibDir_3068_);
lean_inc(v_leanLibDir_3067_);
lean_inc(v_buildDir_3066_);
lean_inc(v_srcDir_3065_);
lean_inc(v_moreGlobalServerArgs_3064_);
lean_inc(v_extraDepTargets_3062_);
lean_inc(v_manifestFile_3061_);
lean_inc(v_toLeanConfig_3059_);
lean_inc(v_toWorkspaceConfig_3058_);
lean_dec(v_cfg_3057_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3100_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3094_ = lean_box(v_reservoir_3086_);
v___x_3095_ = lean_apply_1(v_f_3056_, v___x_3094_);
if (v_isShared_3093_ == 0)
{
v___x_3097_ = v___x_3092_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_toWorkspaceConfig_3058_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_toLeanConfig_3059_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_manifestFile_3061_);
lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_extraDepTargets_3062_);
lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_moreGlobalServerArgs_3064_);
lean_ctor_set(v_reuseFailAlloc_3099_, 5, v_srcDir_3065_);
lean_ctor_set(v_reuseFailAlloc_3099_, 6, v_buildDir_3066_);
lean_ctor_set(v_reuseFailAlloc_3099_, 7, v_leanLibDir_3067_);
lean_ctor_set(v_reuseFailAlloc_3099_, 8, v_nativeLibDir_3068_);
lean_ctor_set(v_reuseFailAlloc_3099_, 9, v_binDir_3069_);
lean_ctor_set(v_reuseFailAlloc_3099_, 10, v_irDir_3070_);
lean_ctor_set(v_reuseFailAlloc_3099_, 11, v_releaseRepo_3071_);
lean_ctor_set(v_reuseFailAlloc_3099_, 12, v_buildArchive_3072_);
lean_ctor_set(v_reuseFailAlloc_3099_, 13, v_testDriver_3074_);
lean_ctor_set(v_reuseFailAlloc_3099_, 14, v_testDriverArgs_3075_);
lean_ctor_set(v_reuseFailAlloc_3099_, 15, v_lintDriver_3076_);
lean_ctor_set(v_reuseFailAlloc_3099_, 16, v_lintDriverArgs_3077_);
lean_ctor_set(v_reuseFailAlloc_3099_, 17, v_version_3078_);
lean_ctor_set(v_reuseFailAlloc_3099_, 18, v_versionTags_3079_);
lean_ctor_set(v_reuseFailAlloc_3099_, 19, v_description_3080_);
lean_ctor_set(v_reuseFailAlloc_3099_, 20, v_keywords_3081_);
lean_ctor_set(v_reuseFailAlloc_3099_, 21, v_homepage_3082_);
lean_ctor_set(v_reuseFailAlloc_3099_, 22, v_license_3083_);
lean_ctor_set(v_reuseFailAlloc_3099_, 23, v_licenseFiles_3084_);
lean_ctor_set(v_reuseFailAlloc_3099_, 24, v_readmeFile_3085_);
lean_ctor_set(v_reuseFailAlloc_3099_, 25, v_enableArtifactCache_x3f_3087_);
lean_ctor_set(v_reuseFailAlloc_3099_, 26, v_restoreAllArtifacts_x3f_3088_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, sizeof(void*)*27, v_bootstrap_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, sizeof(void*)*27 + 1, v_precompileModules_3063_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3073_);
v___x_3097_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_unbox(v___x_3095_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*27 + 3, v___x_3098_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3089_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*27 + 5, v_allowImportAll_3090_);
return v___x_3097_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* v_x_3101_){
_start:
{
uint8_t v___x_3102_; 
v___x_3102_ = 1;
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* v_x_3103_){
_start:
{
uint8_t v_res_3104_; lean_object* v_r_3105_; 
v_res_3104_ = l_Lake_PackageConfig_reservoir___proj___lam__3(v_x_3103_);
lean_dec_ref(v_x_3103_);
v_r_3105_ = lean_box(v_res_3104_);
return v_r_3105_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3115_, lean_object* v_n_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3118_, lean_object* v_n_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lake_PackageConfig_reservoir___proj(v_p_3118_, v_n_3119_);
lean_dec(v_n_3119_);
lean_dec(v_p_3118_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3121_, lean_object* v_n_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lake_PackageConfig_reservoir___proj(v_p_3121_, v_n_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3124_, lean_object* v_n_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3124_, v_n_3125_);
lean_dec(v_n_3125_);
lean_dec(v_p_3124_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* v_cfg_3127_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3128_; 
v_enableArtifactCache_x3f_3128_ = lean_ctor_get(v_cfg_3127_, 25);
lean_inc(v_enableArtifactCache_x3f_3128_);
return v_enableArtifactCache_x3f_3128_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* v_cfg_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(v_cfg_3129_);
lean_dec_ref(v_cfg_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* v_val_3131_, lean_object* v_cfg_3132_){
_start:
{
lean_object* v_toWorkspaceConfig_3133_; lean_object* v_toLeanConfig_3134_; uint8_t v_bootstrap_3135_; lean_object* v_manifestFile_3136_; lean_object* v_extraDepTargets_3137_; uint8_t v_precompileModules_3138_; lean_object* v_moreGlobalServerArgs_3139_; lean_object* v_srcDir_3140_; lean_object* v_buildDir_3141_; lean_object* v_leanLibDir_3142_; lean_object* v_nativeLibDir_3143_; lean_object* v_binDir_3144_; lean_object* v_irDir_3145_; lean_object* v_releaseRepo_3146_; lean_object* v_buildArchive_3147_; uint8_t v_preferReleaseBuild_3148_; lean_object* v_testDriver_3149_; lean_object* v_testDriverArgs_3150_; lean_object* v_lintDriver_3151_; lean_object* v_lintDriverArgs_3152_; lean_object* v_version_3153_; lean_object* v_versionTags_3154_; lean_object* v_description_3155_; lean_object* v_keywords_3156_; lean_object* v_homepage_3157_; lean_object* v_license_3158_; lean_object* v_licenseFiles_3159_; lean_object* v_readmeFile_3160_; uint8_t v_reservoir_3161_; lean_object* v_restoreAllArtifacts_x3f_3162_; uint8_t v_libPrefixOnWindows_3163_; uint8_t v_allowImportAll_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_toWorkspaceConfig_3133_ = lean_ctor_get(v_cfg_3132_, 0);
v_toLeanConfig_3134_ = lean_ctor_get(v_cfg_3132_, 1);
v_bootstrap_3135_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*27);
v_manifestFile_3136_ = lean_ctor_get(v_cfg_3132_, 2);
v_extraDepTargets_3137_ = lean_ctor_get(v_cfg_3132_, 3);
v_precompileModules_3138_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3139_ = lean_ctor_get(v_cfg_3132_, 4);
v_srcDir_3140_ = lean_ctor_get(v_cfg_3132_, 5);
v_buildDir_3141_ = lean_ctor_get(v_cfg_3132_, 6);
v_leanLibDir_3142_ = lean_ctor_get(v_cfg_3132_, 7);
v_nativeLibDir_3143_ = lean_ctor_get(v_cfg_3132_, 8);
v_binDir_3144_ = lean_ctor_get(v_cfg_3132_, 9);
v_irDir_3145_ = lean_ctor_get(v_cfg_3132_, 10);
v_releaseRepo_3146_ = lean_ctor_get(v_cfg_3132_, 11);
v_buildArchive_3147_ = lean_ctor_get(v_cfg_3132_, 12);
v_preferReleaseBuild_3148_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*27 + 2);
v_testDriver_3149_ = lean_ctor_get(v_cfg_3132_, 13);
v_testDriverArgs_3150_ = lean_ctor_get(v_cfg_3132_, 14);
v_lintDriver_3151_ = lean_ctor_get(v_cfg_3132_, 15);
v_lintDriverArgs_3152_ = lean_ctor_get(v_cfg_3132_, 16);
v_version_3153_ = lean_ctor_get(v_cfg_3132_, 17);
v_versionTags_3154_ = lean_ctor_get(v_cfg_3132_, 18);
v_description_3155_ = lean_ctor_get(v_cfg_3132_, 19);
v_keywords_3156_ = lean_ctor_get(v_cfg_3132_, 20);
v_homepage_3157_ = lean_ctor_get(v_cfg_3132_, 21);
v_license_3158_ = lean_ctor_get(v_cfg_3132_, 22);
v_licenseFiles_3159_ = lean_ctor_get(v_cfg_3132_, 23);
v_readmeFile_3160_ = lean_ctor_get(v_cfg_3132_, 24);
v_reservoir_3161_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*27 + 3);
v_restoreAllArtifacts_x3f_3162_ = lean_ctor_get(v_cfg_3132_, 26);
v_libPrefixOnWindows_3163_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*27 + 4);
v_allowImportAll_3164_ = lean_ctor_get_uint8(v_cfg_3132_, sizeof(void*)*27 + 5);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_cfg_3132_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_cfg_3132_, 25);
lean_dec(v_unused_3172_);
v___x_3166_ = v_cfg_3132_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3162_);
lean_inc(v_readmeFile_3160_);
lean_inc(v_licenseFiles_3159_);
lean_inc(v_license_3158_);
lean_inc(v_homepage_3157_);
lean_inc(v_keywords_3156_);
lean_inc(v_description_3155_);
lean_inc(v_versionTags_3154_);
lean_inc(v_version_3153_);
lean_inc(v_lintDriverArgs_3152_);
lean_inc(v_lintDriver_3151_);
lean_inc(v_testDriverArgs_3150_);
lean_inc(v_testDriver_3149_);
lean_inc(v_buildArchive_3147_);
lean_inc(v_releaseRepo_3146_);
lean_inc(v_irDir_3145_);
lean_inc(v_binDir_3144_);
lean_inc(v_nativeLibDir_3143_);
lean_inc(v_leanLibDir_3142_);
lean_inc(v_buildDir_3141_);
lean_inc(v_srcDir_3140_);
lean_inc(v_moreGlobalServerArgs_3139_);
lean_inc(v_extraDepTargets_3137_);
lean_inc(v_manifestFile_3136_);
lean_inc(v_toLeanConfig_3134_);
lean_inc(v_toWorkspaceConfig_3133_);
lean_dec(v_cfg_3132_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 25, v_val_3131_);
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_toWorkspaceConfig_3133_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_toLeanConfig_3134_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_manifestFile_3136_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_extraDepTargets_3137_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_moreGlobalServerArgs_3139_);
lean_ctor_set(v_reuseFailAlloc_3170_, 5, v_srcDir_3140_);
lean_ctor_set(v_reuseFailAlloc_3170_, 6, v_buildDir_3141_);
lean_ctor_set(v_reuseFailAlloc_3170_, 7, v_leanLibDir_3142_);
lean_ctor_set(v_reuseFailAlloc_3170_, 8, v_nativeLibDir_3143_);
lean_ctor_set(v_reuseFailAlloc_3170_, 9, v_binDir_3144_);
lean_ctor_set(v_reuseFailAlloc_3170_, 10, v_irDir_3145_);
lean_ctor_set(v_reuseFailAlloc_3170_, 11, v_releaseRepo_3146_);
lean_ctor_set(v_reuseFailAlloc_3170_, 12, v_buildArchive_3147_);
lean_ctor_set(v_reuseFailAlloc_3170_, 13, v_testDriver_3149_);
lean_ctor_set(v_reuseFailAlloc_3170_, 14, v_testDriverArgs_3150_);
lean_ctor_set(v_reuseFailAlloc_3170_, 15, v_lintDriver_3151_);
lean_ctor_set(v_reuseFailAlloc_3170_, 16, v_lintDriverArgs_3152_);
lean_ctor_set(v_reuseFailAlloc_3170_, 17, v_version_3153_);
lean_ctor_set(v_reuseFailAlloc_3170_, 18, v_versionTags_3154_);
lean_ctor_set(v_reuseFailAlloc_3170_, 19, v_description_3155_);
lean_ctor_set(v_reuseFailAlloc_3170_, 20, v_keywords_3156_);
lean_ctor_set(v_reuseFailAlloc_3170_, 21, v_homepage_3157_);
lean_ctor_set(v_reuseFailAlloc_3170_, 22, v_license_3158_);
lean_ctor_set(v_reuseFailAlloc_3170_, 23, v_licenseFiles_3159_);
lean_ctor_set(v_reuseFailAlloc_3170_, 24, v_readmeFile_3160_);
lean_ctor_set(v_reuseFailAlloc_3170_, 25, v_val_3131_);
lean_ctor_set(v_reuseFailAlloc_3170_, 26, v_restoreAllArtifacts_x3f_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*27, v_bootstrap_3135_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*27 + 1, v_precompileModules_3138_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3148_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*27 + 3, v_reservoir_3161_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3163_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*27 + 5, v_allowImportAll_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* v_f_3173_, lean_object* v_cfg_3174_){
_start:
{
lean_object* v_toWorkspaceConfig_3175_; lean_object* v_toLeanConfig_3176_; uint8_t v_bootstrap_3177_; lean_object* v_manifestFile_3178_; lean_object* v_extraDepTargets_3179_; uint8_t v_precompileModules_3180_; lean_object* v_moreGlobalServerArgs_3181_; lean_object* v_srcDir_3182_; lean_object* v_buildDir_3183_; lean_object* v_leanLibDir_3184_; lean_object* v_nativeLibDir_3185_; lean_object* v_binDir_3186_; lean_object* v_irDir_3187_; lean_object* v_releaseRepo_3188_; lean_object* v_buildArchive_3189_; uint8_t v_preferReleaseBuild_3190_; lean_object* v_testDriver_3191_; lean_object* v_testDriverArgs_3192_; lean_object* v_lintDriver_3193_; lean_object* v_lintDriverArgs_3194_; lean_object* v_version_3195_; lean_object* v_versionTags_3196_; lean_object* v_description_3197_; lean_object* v_keywords_3198_; lean_object* v_homepage_3199_; lean_object* v_license_3200_; lean_object* v_licenseFiles_3201_; lean_object* v_readmeFile_3202_; uint8_t v_reservoir_3203_; lean_object* v_enableArtifactCache_x3f_3204_; lean_object* v_restoreAllArtifacts_x3f_3205_; uint8_t v_libPrefixOnWindows_3206_; uint8_t v_allowImportAll_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3215_; 
v_toWorkspaceConfig_3175_ = lean_ctor_get(v_cfg_3174_, 0);
v_toLeanConfig_3176_ = lean_ctor_get(v_cfg_3174_, 1);
v_bootstrap_3177_ = lean_ctor_get_uint8(v_cfg_3174_, sizeof(void*)*27);
v_manifestFile_3178_ = lean_ctor_get(v_cfg_3174_, 2);
v_extraDepTargets_3179_ = lean_ctor_get(v_cfg_3174_, 3);
v_precompileModules_3180_ = lean_ctor_get_uint8(v_cfg_3174_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3181_ = lean_ctor_get(v_cfg_3174_, 4);
v_srcDir_3182_ = lean_ctor_get(v_cfg_3174_, 5);
v_buildDir_3183_ = lean_ctor_get(v_cfg_3174_, 6);
v_leanLibDir_3184_ = lean_ctor_get(v_cfg_3174_, 7);
v_nativeLibDir_3185_ = lean_ctor_get(v_cfg_3174_, 8);
v_binDir_3186_ = lean_ctor_get(v_cfg_3174_, 9);
v_irDir_3187_ = lean_ctor_get(v_cfg_3174_, 10);
v_releaseRepo_3188_ = lean_ctor_get(v_cfg_3174_, 11);
v_buildArchive_3189_ = lean_ctor_get(v_cfg_3174_, 12);
v_preferReleaseBuild_3190_ = lean_ctor_get_uint8(v_cfg_3174_, sizeof(void*)*27 + 2);
v_testDriver_3191_ = lean_ctor_get(v_cfg_3174_, 13);
v_testDriverArgs_3192_ = lean_ctor_get(v_cfg_3174_, 14);
v_lintDriver_3193_ = lean_ctor_get(v_cfg_3174_, 15);
v_lintDriverArgs_3194_ = lean_ctor_get(v_cfg_3174_, 16);
v_version_3195_ = lean_ctor_get(v_cfg_3174_, 17);
v_versionTags_3196_ = lean_ctor_get(v_cfg_3174_, 18);
v_description_3197_ = lean_ctor_get(v_cfg_3174_, 19);
v_keywords_3198_ = lean_ctor_get(v_cfg_3174_, 20);
v_homepage_3199_ = lean_ctor_get(v_cfg_3174_, 21);
v_license_3200_ = lean_ctor_get(v_cfg_3174_, 22);
v_licenseFiles_3201_ = lean_ctor_get(v_cfg_3174_, 23);
v_readmeFile_3202_ = lean_ctor_get(v_cfg_3174_, 24);
v_reservoir_3203_ = lean_ctor_get_uint8(v_cfg_3174_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3204_ = lean_ctor_get(v_cfg_3174_, 25);
v_restoreAllArtifacts_x3f_3205_ = lean_ctor_get(v_cfg_3174_, 26);
v_libPrefixOnWindows_3206_ = lean_ctor_get_uint8(v_cfg_3174_, sizeof(void*)*27 + 4);
v_allowImportAll_3207_ = lean_ctor_get_uint8(v_cfg_3174_, sizeof(void*)*27 + 5);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_cfg_3174_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3209_ = v_cfg_3174_;
v_isShared_3210_ = v_isSharedCheck_3215_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3205_);
lean_inc(v_enableArtifactCache_x3f_3204_);
lean_inc(v_readmeFile_3202_);
lean_inc(v_licenseFiles_3201_);
lean_inc(v_license_3200_);
lean_inc(v_homepage_3199_);
lean_inc(v_keywords_3198_);
lean_inc(v_description_3197_);
lean_inc(v_versionTags_3196_);
lean_inc(v_version_3195_);
lean_inc(v_lintDriverArgs_3194_);
lean_inc(v_lintDriver_3193_);
lean_inc(v_testDriverArgs_3192_);
lean_inc(v_testDriver_3191_);
lean_inc(v_buildArchive_3189_);
lean_inc(v_releaseRepo_3188_);
lean_inc(v_irDir_3187_);
lean_inc(v_binDir_3186_);
lean_inc(v_nativeLibDir_3185_);
lean_inc(v_leanLibDir_3184_);
lean_inc(v_buildDir_3183_);
lean_inc(v_srcDir_3182_);
lean_inc(v_moreGlobalServerArgs_3181_);
lean_inc(v_extraDepTargets_3179_);
lean_inc(v_manifestFile_3178_);
lean_inc(v_toLeanConfig_3176_);
lean_inc(v_toWorkspaceConfig_3175_);
lean_dec(v_cfg_3174_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3215_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = lean_apply_1(v_f_3173_, v_enableArtifactCache_x3f_3204_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 25, v___x_3211_);
v___x_3213_ = v___x_3209_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_toWorkspaceConfig_3175_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_toLeanConfig_3176_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_manifestFile_3178_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_extraDepTargets_3179_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v_moreGlobalServerArgs_3181_);
lean_ctor_set(v_reuseFailAlloc_3214_, 5, v_srcDir_3182_);
lean_ctor_set(v_reuseFailAlloc_3214_, 6, v_buildDir_3183_);
lean_ctor_set(v_reuseFailAlloc_3214_, 7, v_leanLibDir_3184_);
lean_ctor_set(v_reuseFailAlloc_3214_, 8, v_nativeLibDir_3185_);
lean_ctor_set(v_reuseFailAlloc_3214_, 9, v_binDir_3186_);
lean_ctor_set(v_reuseFailAlloc_3214_, 10, v_irDir_3187_);
lean_ctor_set(v_reuseFailAlloc_3214_, 11, v_releaseRepo_3188_);
lean_ctor_set(v_reuseFailAlloc_3214_, 12, v_buildArchive_3189_);
lean_ctor_set(v_reuseFailAlloc_3214_, 13, v_testDriver_3191_);
lean_ctor_set(v_reuseFailAlloc_3214_, 14, v_testDriverArgs_3192_);
lean_ctor_set(v_reuseFailAlloc_3214_, 15, v_lintDriver_3193_);
lean_ctor_set(v_reuseFailAlloc_3214_, 16, v_lintDriverArgs_3194_);
lean_ctor_set(v_reuseFailAlloc_3214_, 17, v_version_3195_);
lean_ctor_set(v_reuseFailAlloc_3214_, 18, v_versionTags_3196_);
lean_ctor_set(v_reuseFailAlloc_3214_, 19, v_description_3197_);
lean_ctor_set(v_reuseFailAlloc_3214_, 20, v_keywords_3198_);
lean_ctor_set(v_reuseFailAlloc_3214_, 21, v_homepage_3199_);
lean_ctor_set(v_reuseFailAlloc_3214_, 22, v_license_3200_);
lean_ctor_set(v_reuseFailAlloc_3214_, 23, v_licenseFiles_3201_);
lean_ctor_set(v_reuseFailAlloc_3214_, 24, v_readmeFile_3202_);
lean_ctor_set(v_reuseFailAlloc_3214_, 25, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3214_, 26, v_restoreAllArtifacts_x3f_3205_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*27, v_bootstrap_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*27 + 1, v_precompileModules_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3190_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*27 + 3, v_reservoir_3203_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3206_);
lean_ctor_set_uint8(v_reuseFailAlloc_3214_, sizeof(void*)*27 + 5, v_allowImportAll_3207_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* v_x_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_box(0);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* v_x_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(v_x_3218_);
lean_dec_ref(v_x_3218_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3229_, lean_object* v_n_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3232_, lean_object* v_n_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3232_, v_n_3233_);
lean_dec(v_n_3233_);
lean_dec(v_p_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3235_, lean_object* v_n_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3235_, v_n_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3238_, lean_object* v_n_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3238_, v_n_3239_);
lean_dec(v_n_3239_);
lean_dec(v_p_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3241_, lean_object* v_n_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3241_, v_n_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3244_, lean_object* v_n_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3244_, v_n_3245_);
lean_dec(v_n_3245_);
lean_dec(v_p_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object* v_cfg_3247_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3248_; 
v_restoreAllArtifacts_x3f_3248_ = lean_ctor_get(v_cfg_3247_, 26);
lean_inc(v_restoreAllArtifacts_x3f_3248_);
return v_restoreAllArtifacts_x3f_3248_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object* v_cfg_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(v_cfg_3249_);
lean_dec_ref(v_cfg_3249_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object* v_val_3251_, lean_object* v_cfg_3252_){
_start:
{
lean_object* v_toWorkspaceConfig_3253_; lean_object* v_toLeanConfig_3254_; uint8_t v_bootstrap_3255_; lean_object* v_manifestFile_3256_; lean_object* v_extraDepTargets_3257_; uint8_t v_precompileModules_3258_; lean_object* v_moreGlobalServerArgs_3259_; lean_object* v_srcDir_3260_; lean_object* v_buildDir_3261_; lean_object* v_leanLibDir_3262_; lean_object* v_nativeLibDir_3263_; lean_object* v_binDir_3264_; lean_object* v_irDir_3265_; lean_object* v_releaseRepo_3266_; lean_object* v_buildArchive_3267_; uint8_t v_preferReleaseBuild_3268_; lean_object* v_testDriver_3269_; lean_object* v_testDriverArgs_3270_; lean_object* v_lintDriver_3271_; lean_object* v_lintDriverArgs_3272_; lean_object* v_version_3273_; lean_object* v_versionTags_3274_; lean_object* v_description_3275_; lean_object* v_keywords_3276_; lean_object* v_homepage_3277_; lean_object* v_license_3278_; lean_object* v_licenseFiles_3279_; lean_object* v_readmeFile_3280_; uint8_t v_reservoir_3281_; lean_object* v_enableArtifactCache_x3f_3282_; uint8_t v_libPrefixOnWindows_3283_; uint8_t v_allowImportAll_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
v_toWorkspaceConfig_3253_ = lean_ctor_get(v_cfg_3252_, 0);
v_toLeanConfig_3254_ = lean_ctor_get(v_cfg_3252_, 1);
v_bootstrap_3255_ = lean_ctor_get_uint8(v_cfg_3252_, sizeof(void*)*27);
v_manifestFile_3256_ = lean_ctor_get(v_cfg_3252_, 2);
v_extraDepTargets_3257_ = lean_ctor_get(v_cfg_3252_, 3);
v_precompileModules_3258_ = lean_ctor_get_uint8(v_cfg_3252_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3259_ = lean_ctor_get(v_cfg_3252_, 4);
v_srcDir_3260_ = lean_ctor_get(v_cfg_3252_, 5);
v_buildDir_3261_ = lean_ctor_get(v_cfg_3252_, 6);
v_leanLibDir_3262_ = lean_ctor_get(v_cfg_3252_, 7);
v_nativeLibDir_3263_ = lean_ctor_get(v_cfg_3252_, 8);
v_binDir_3264_ = lean_ctor_get(v_cfg_3252_, 9);
v_irDir_3265_ = lean_ctor_get(v_cfg_3252_, 10);
v_releaseRepo_3266_ = lean_ctor_get(v_cfg_3252_, 11);
v_buildArchive_3267_ = lean_ctor_get(v_cfg_3252_, 12);
v_preferReleaseBuild_3268_ = lean_ctor_get_uint8(v_cfg_3252_, sizeof(void*)*27 + 2);
v_testDriver_3269_ = lean_ctor_get(v_cfg_3252_, 13);
v_testDriverArgs_3270_ = lean_ctor_get(v_cfg_3252_, 14);
v_lintDriver_3271_ = lean_ctor_get(v_cfg_3252_, 15);
v_lintDriverArgs_3272_ = lean_ctor_get(v_cfg_3252_, 16);
v_version_3273_ = lean_ctor_get(v_cfg_3252_, 17);
v_versionTags_3274_ = lean_ctor_get(v_cfg_3252_, 18);
v_description_3275_ = lean_ctor_get(v_cfg_3252_, 19);
v_keywords_3276_ = lean_ctor_get(v_cfg_3252_, 20);
v_homepage_3277_ = lean_ctor_get(v_cfg_3252_, 21);
v_license_3278_ = lean_ctor_get(v_cfg_3252_, 22);
v_licenseFiles_3279_ = lean_ctor_get(v_cfg_3252_, 23);
v_readmeFile_3280_ = lean_ctor_get(v_cfg_3252_, 24);
v_reservoir_3281_ = lean_ctor_get_uint8(v_cfg_3252_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3282_ = lean_ctor_get(v_cfg_3252_, 25);
v_libPrefixOnWindows_3283_ = lean_ctor_get_uint8(v_cfg_3252_, sizeof(void*)*27 + 4);
v_allowImportAll_3284_ = lean_ctor_get_uint8(v_cfg_3252_, sizeof(void*)*27 + 5);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_cfg_3252_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; 
v_unused_3292_ = lean_ctor_get(v_cfg_3252_, 26);
lean_dec(v_unused_3292_);
v___x_3286_ = v_cfg_3252_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_enableArtifactCache_x3f_3282_);
lean_inc(v_readmeFile_3280_);
lean_inc(v_licenseFiles_3279_);
lean_inc(v_license_3278_);
lean_inc(v_homepage_3277_);
lean_inc(v_keywords_3276_);
lean_inc(v_description_3275_);
lean_inc(v_versionTags_3274_);
lean_inc(v_version_3273_);
lean_inc(v_lintDriverArgs_3272_);
lean_inc(v_lintDriver_3271_);
lean_inc(v_testDriverArgs_3270_);
lean_inc(v_testDriver_3269_);
lean_inc(v_buildArchive_3267_);
lean_inc(v_releaseRepo_3266_);
lean_inc(v_irDir_3265_);
lean_inc(v_binDir_3264_);
lean_inc(v_nativeLibDir_3263_);
lean_inc(v_leanLibDir_3262_);
lean_inc(v_buildDir_3261_);
lean_inc(v_srcDir_3260_);
lean_inc(v_moreGlobalServerArgs_3259_);
lean_inc(v_extraDepTargets_3257_);
lean_inc(v_manifestFile_3256_);
lean_inc(v_toLeanConfig_3254_);
lean_inc(v_toWorkspaceConfig_3253_);
lean_dec(v_cfg_3252_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 26, v_val_3251_);
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_toWorkspaceConfig_3253_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_toLeanConfig_3254_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_manifestFile_3256_);
lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_extraDepTargets_3257_);
lean_ctor_set(v_reuseFailAlloc_3290_, 4, v_moreGlobalServerArgs_3259_);
lean_ctor_set(v_reuseFailAlloc_3290_, 5, v_srcDir_3260_);
lean_ctor_set(v_reuseFailAlloc_3290_, 6, v_buildDir_3261_);
lean_ctor_set(v_reuseFailAlloc_3290_, 7, v_leanLibDir_3262_);
lean_ctor_set(v_reuseFailAlloc_3290_, 8, v_nativeLibDir_3263_);
lean_ctor_set(v_reuseFailAlloc_3290_, 9, v_binDir_3264_);
lean_ctor_set(v_reuseFailAlloc_3290_, 10, v_irDir_3265_);
lean_ctor_set(v_reuseFailAlloc_3290_, 11, v_releaseRepo_3266_);
lean_ctor_set(v_reuseFailAlloc_3290_, 12, v_buildArchive_3267_);
lean_ctor_set(v_reuseFailAlloc_3290_, 13, v_testDriver_3269_);
lean_ctor_set(v_reuseFailAlloc_3290_, 14, v_testDriverArgs_3270_);
lean_ctor_set(v_reuseFailAlloc_3290_, 15, v_lintDriver_3271_);
lean_ctor_set(v_reuseFailAlloc_3290_, 16, v_lintDriverArgs_3272_);
lean_ctor_set(v_reuseFailAlloc_3290_, 17, v_version_3273_);
lean_ctor_set(v_reuseFailAlloc_3290_, 18, v_versionTags_3274_);
lean_ctor_set(v_reuseFailAlloc_3290_, 19, v_description_3275_);
lean_ctor_set(v_reuseFailAlloc_3290_, 20, v_keywords_3276_);
lean_ctor_set(v_reuseFailAlloc_3290_, 21, v_homepage_3277_);
lean_ctor_set(v_reuseFailAlloc_3290_, 22, v_license_3278_);
lean_ctor_set(v_reuseFailAlloc_3290_, 23, v_licenseFiles_3279_);
lean_ctor_set(v_reuseFailAlloc_3290_, 24, v_readmeFile_3280_);
lean_ctor_set(v_reuseFailAlloc_3290_, 25, v_enableArtifactCache_x3f_3282_);
lean_ctor_set(v_reuseFailAlloc_3290_, 26, v_val_3251_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*27, v_bootstrap_3255_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*27 + 1, v_precompileModules_3258_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3268_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*27 + 3, v_reservoir_3281_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3283_);
lean_ctor_set_uint8(v_reuseFailAlloc_3290_, sizeof(void*)*27 + 5, v_allowImportAll_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object* v_f_3293_, lean_object* v_cfg_3294_){
_start:
{
lean_object* v_toWorkspaceConfig_3295_; lean_object* v_toLeanConfig_3296_; uint8_t v_bootstrap_3297_; lean_object* v_manifestFile_3298_; lean_object* v_extraDepTargets_3299_; uint8_t v_precompileModules_3300_; lean_object* v_moreGlobalServerArgs_3301_; lean_object* v_srcDir_3302_; lean_object* v_buildDir_3303_; lean_object* v_leanLibDir_3304_; lean_object* v_nativeLibDir_3305_; lean_object* v_binDir_3306_; lean_object* v_irDir_3307_; lean_object* v_releaseRepo_3308_; lean_object* v_buildArchive_3309_; uint8_t v_preferReleaseBuild_3310_; lean_object* v_testDriver_3311_; lean_object* v_testDriverArgs_3312_; lean_object* v_lintDriver_3313_; lean_object* v_lintDriverArgs_3314_; lean_object* v_version_3315_; lean_object* v_versionTags_3316_; lean_object* v_description_3317_; lean_object* v_keywords_3318_; lean_object* v_homepage_3319_; lean_object* v_license_3320_; lean_object* v_licenseFiles_3321_; lean_object* v_readmeFile_3322_; uint8_t v_reservoir_3323_; lean_object* v_enableArtifactCache_x3f_3324_; lean_object* v_restoreAllArtifacts_x3f_3325_; uint8_t v_libPrefixOnWindows_3326_; uint8_t v_allowImportAll_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3335_; 
v_toWorkspaceConfig_3295_ = lean_ctor_get(v_cfg_3294_, 0);
v_toLeanConfig_3296_ = lean_ctor_get(v_cfg_3294_, 1);
v_bootstrap_3297_ = lean_ctor_get_uint8(v_cfg_3294_, sizeof(void*)*27);
v_manifestFile_3298_ = lean_ctor_get(v_cfg_3294_, 2);
v_extraDepTargets_3299_ = lean_ctor_get(v_cfg_3294_, 3);
v_precompileModules_3300_ = lean_ctor_get_uint8(v_cfg_3294_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3301_ = lean_ctor_get(v_cfg_3294_, 4);
v_srcDir_3302_ = lean_ctor_get(v_cfg_3294_, 5);
v_buildDir_3303_ = lean_ctor_get(v_cfg_3294_, 6);
v_leanLibDir_3304_ = lean_ctor_get(v_cfg_3294_, 7);
v_nativeLibDir_3305_ = lean_ctor_get(v_cfg_3294_, 8);
v_binDir_3306_ = lean_ctor_get(v_cfg_3294_, 9);
v_irDir_3307_ = lean_ctor_get(v_cfg_3294_, 10);
v_releaseRepo_3308_ = lean_ctor_get(v_cfg_3294_, 11);
v_buildArchive_3309_ = lean_ctor_get(v_cfg_3294_, 12);
v_preferReleaseBuild_3310_ = lean_ctor_get_uint8(v_cfg_3294_, sizeof(void*)*27 + 2);
v_testDriver_3311_ = lean_ctor_get(v_cfg_3294_, 13);
v_testDriverArgs_3312_ = lean_ctor_get(v_cfg_3294_, 14);
v_lintDriver_3313_ = lean_ctor_get(v_cfg_3294_, 15);
v_lintDriverArgs_3314_ = lean_ctor_get(v_cfg_3294_, 16);
v_version_3315_ = lean_ctor_get(v_cfg_3294_, 17);
v_versionTags_3316_ = lean_ctor_get(v_cfg_3294_, 18);
v_description_3317_ = lean_ctor_get(v_cfg_3294_, 19);
v_keywords_3318_ = lean_ctor_get(v_cfg_3294_, 20);
v_homepage_3319_ = lean_ctor_get(v_cfg_3294_, 21);
v_license_3320_ = lean_ctor_get(v_cfg_3294_, 22);
v_licenseFiles_3321_ = lean_ctor_get(v_cfg_3294_, 23);
v_readmeFile_3322_ = lean_ctor_get(v_cfg_3294_, 24);
v_reservoir_3323_ = lean_ctor_get_uint8(v_cfg_3294_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3324_ = lean_ctor_get(v_cfg_3294_, 25);
v_restoreAllArtifacts_x3f_3325_ = lean_ctor_get(v_cfg_3294_, 26);
v_libPrefixOnWindows_3326_ = lean_ctor_get_uint8(v_cfg_3294_, sizeof(void*)*27 + 4);
v_allowImportAll_3327_ = lean_ctor_get_uint8(v_cfg_3294_, sizeof(void*)*27 + 5);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_cfg_3294_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3329_ = v_cfg_3294_;
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3325_);
lean_inc(v_enableArtifactCache_x3f_3324_);
lean_inc(v_readmeFile_3322_);
lean_inc(v_licenseFiles_3321_);
lean_inc(v_license_3320_);
lean_inc(v_homepage_3319_);
lean_inc(v_keywords_3318_);
lean_inc(v_description_3317_);
lean_inc(v_versionTags_3316_);
lean_inc(v_version_3315_);
lean_inc(v_lintDriverArgs_3314_);
lean_inc(v_lintDriver_3313_);
lean_inc(v_testDriverArgs_3312_);
lean_inc(v_testDriver_3311_);
lean_inc(v_buildArchive_3309_);
lean_inc(v_releaseRepo_3308_);
lean_inc(v_irDir_3307_);
lean_inc(v_binDir_3306_);
lean_inc(v_nativeLibDir_3305_);
lean_inc(v_leanLibDir_3304_);
lean_inc(v_buildDir_3303_);
lean_inc(v_srcDir_3302_);
lean_inc(v_moreGlobalServerArgs_3301_);
lean_inc(v_extraDepTargets_3299_);
lean_inc(v_manifestFile_3298_);
lean_inc(v_toLeanConfig_3296_);
lean_inc(v_toWorkspaceConfig_3295_);
lean_dec(v_cfg_3294_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3331_ = lean_apply_1(v_f_3293_, v_restoreAllArtifacts_x3f_3325_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 26, v___x_3331_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_toWorkspaceConfig_3295_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_toLeanConfig_3296_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_manifestFile_3298_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_extraDepTargets_3299_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_moreGlobalServerArgs_3301_);
lean_ctor_set(v_reuseFailAlloc_3334_, 5, v_srcDir_3302_);
lean_ctor_set(v_reuseFailAlloc_3334_, 6, v_buildDir_3303_);
lean_ctor_set(v_reuseFailAlloc_3334_, 7, v_leanLibDir_3304_);
lean_ctor_set(v_reuseFailAlloc_3334_, 8, v_nativeLibDir_3305_);
lean_ctor_set(v_reuseFailAlloc_3334_, 9, v_binDir_3306_);
lean_ctor_set(v_reuseFailAlloc_3334_, 10, v_irDir_3307_);
lean_ctor_set(v_reuseFailAlloc_3334_, 11, v_releaseRepo_3308_);
lean_ctor_set(v_reuseFailAlloc_3334_, 12, v_buildArchive_3309_);
lean_ctor_set(v_reuseFailAlloc_3334_, 13, v_testDriver_3311_);
lean_ctor_set(v_reuseFailAlloc_3334_, 14, v_testDriverArgs_3312_);
lean_ctor_set(v_reuseFailAlloc_3334_, 15, v_lintDriver_3313_);
lean_ctor_set(v_reuseFailAlloc_3334_, 16, v_lintDriverArgs_3314_);
lean_ctor_set(v_reuseFailAlloc_3334_, 17, v_version_3315_);
lean_ctor_set(v_reuseFailAlloc_3334_, 18, v_versionTags_3316_);
lean_ctor_set(v_reuseFailAlloc_3334_, 19, v_description_3317_);
lean_ctor_set(v_reuseFailAlloc_3334_, 20, v_keywords_3318_);
lean_ctor_set(v_reuseFailAlloc_3334_, 21, v_homepage_3319_);
lean_ctor_set(v_reuseFailAlloc_3334_, 22, v_license_3320_);
lean_ctor_set(v_reuseFailAlloc_3334_, 23, v_licenseFiles_3321_);
lean_ctor_set(v_reuseFailAlloc_3334_, 24, v_readmeFile_3322_);
lean_ctor_set(v_reuseFailAlloc_3334_, 25, v_enableArtifactCache_x3f_3324_);
lean_ctor_set(v_reuseFailAlloc_3334_, 26, v___x_3331_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*27, v_bootstrap_3297_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*27 + 1, v_precompileModules_3300_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*27 + 3, v_reservoir_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*27 + 5, v_allowImportAll_3327_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3344_, lean_object* v_n_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3));
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3347_, lean_object* v_n_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3347_, v_n_3348_);
lean_dec(v_n_3348_);
lean_dec(v_p_3347_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3350_, lean_object* v_n_3351_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3350_, v_n_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3353_, lean_object* v_n_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3353_, v_n_3354_);
lean_dec(v_n_3354_);
lean_dec(v_p_3353_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3356_, lean_object* v_n_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3356_, v_n_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3359_, lean_object* v_n_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3359_, v_n_3360_);
lean_dec(v_n_3360_);
lean_dec(v_p_3359_);
return v_res_3361_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_3362_){
_start:
{
uint8_t v_libPrefixOnWindows_3363_; 
v_libPrefixOnWindows_3363_ = lean_ctor_get_uint8(v_cfg_3362_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_3363_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_3364_){
_start:
{
uint8_t v_res_3365_; lean_object* v_r_3366_; 
v_res_3365_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(v_cfg_3364_);
lean_dec_ref(v_cfg_3364_);
v_r_3366_ = lean_box(v_res_3365_);
return v_r_3366_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_3367_, lean_object* v_cfg_3368_){
_start:
{
lean_object* v_toWorkspaceConfig_3369_; lean_object* v_toLeanConfig_3370_; uint8_t v_bootstrap_3371_; lean_object* v_manifestFile_3372_; lean_object* v_extraDepTargets_3373_; uint8_t v_precompileModules_3374_; lean_object* v_moreGlobalServerArgs_3375_; lean_object* v_srcDir_3376_; lean_object* v_buildDir_3377_; lean_object* v_leanLibDir_3378_; lean_object* v_nativeLibDir_3379_; lean_object* v_binDir_3380_; lean_object* v_irDir_3381_; lean_object* v_releaseRepo_3382_; lean_object* v_buildArchive_3383_; uint8_t v_preferReleaseBuild_3384_; lean_object* v_testDriver_3385_; lean_object* v_testDriverArgs_3386_; lean_object* v_lintDriver_3387_; lean_object* v_lintDriverArgs_3388_; lean_object* v_version_3389_; lean_object* v_versionTags_3390_; lean_object* v_description_3391_; lean_object* v_keywords_3392_; lean_object* v_homepage_3393_; lean_object* v_license_3394_; lean_object* v_licenseFiles_3395_; lean_object* v_readmeFile_3396_; uint8_t v_reservoir_3397_; lean_object* v_enableArtifactCache_x3f_3398_; lean_object* v_restoreAllArtifacts_x3f_3399_; uint8_t v_allowImportAll_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_toWorkspaceConfig_3369_ = lean_ctor_get(v_cfg_3368_, 0);
v_toLeanConfig_3370_ = lean_ctor_get(v_cfg_3368_, 1);
v_bootstrap_3371_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27);
v_manifestFile_3372_ = lean_ctor_get(v_cfg_3368_, 2);
v_extraDepTargets_3373_ = lean_ctor_get(v_cfg_3368_, 3);
v_precompileModules_3374_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3375_ = lean_ctor_get(v_cfg_3368_, 4);
v_srcDir_3376_ = lean_ctor_get(v_cfg_3368_, 5);
v_buildDir_3377_ = lean_ctor_get(v_cfg_3368_, 6);
v_leanLibDir_3378_ = lean_ctor_get(v_cfg_3368_, 7);
v_nativeLibDir_3379_ = lean_ctor_get(v_cfg_3368_, 8);
v_binDir_3380_ = lean_ctor_get(v_cfg_3368_, 9);
v_irDir_3381_ = lean_ctor_get(v_cfg_3368_, 10);
v_releaseRepo_3382_ = lean_ctor_get(v_cfg_3368_, 11);
v_buildArchive_3383_ = lean_ctor_get(v_cfg_3368_, 12);
v_preferReleaseBuild_3384_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 2);
v_testDriver_3385_ = lean_ctor_get(v_cfg_3368_, 13);
v_testDriverArgs_3386_ = lean_ctor_get(v_cfg_3368_, 14);
v_lintDriver_3387_ = lean_ctor_get(v_cfg_3368_, 15);
v_lintDriverArgs_3388_ = lean_ctor_get(v_cfg_3368_, 16);
v_version_3389_ = lean_ctor_get(v_cfg_3368_, 17);
v_versionTags_3390_ = lean_ctor_get(v_cfg_3368_, 18);
v_description_3391_ = lean_ctor_get(v_cfg_3368_, 19);
v_keywords_3392_ = lean_ctor_get(v_cfg_3368_, 20);
v_homepage_3393_ = lean_ctor_get(v_cfg_3368_, 21);
v_license_3394_ = lean_ctor_get(v_cfg_3368_, 22);
v_licenseFiles_3395_ = lean_ctor_get(v_cfg_3368_, 23);
v_readmeFile_3396_ = lean_ctor_get(v_cfg_3368_, 24);
v_reservoir_3397_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3398_ = lean_ctor_get(v_cfg_3368_, 25);
v_restoreAllArtifacts_x3f_3399_ = lean_ctor_get(v_cfg_3368_, 26);
v_allowImportAll_3400_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 5);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_cfg_3368_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v_cfg_3368_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3399_);
lean_inc(v_enableArtifactCache_x3f_3398_);
lean_inc(v_readmeFile_3396_);
lean_inc(v_licenseFiles_3395_);
lean_inc(v_license_3394_);
lean_inc(v_homepage_3393_);
lean_inc(v_keywords_3392_);
lean_inc(v_description_3391_);
lean_inc(v_versionTags_3390_);
lean_inc(v_version_3389_);
lean_inc(v_lintDriverArgs_3388_);
lean_inc(v_lintDriver_3387_);
lean_inc(v_testDriverArgs_3386_);
lean_inc(v_testDriver_3385_);
lean_inc(v_buildArchive_3383_);
lean_inc(v_releaseRepo_3382_);
lean_inc(v_irDir_3381_);
lean_inc(v_binDir_3380_);
lean_inc(v_nativeLibDir_3379_);
lean_inc(v_leanLibDir_3378_);
lean_inc(v_buildDir_3377_);
lean_inc(v_srcDir_3376_);
lean_inc(v_moreGlobalServerArgs_3375_);
lean_inc(v_extraDepTargets_3373_);
lean_inc(v_manifestFile_3372_);
lean_inc(v_toLeanConfig_3370_);
lean_inc(v_toWorkspaceConfig_3369_);
lean_dec(v_cfg_3368_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_toWorkspaceConfig_3369_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_toLeanConfig_3370_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_manifestFile_3372_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v_extraDepTargets_3373_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v_moreGlobalServerArgs_3375_);
lean_ctor_set(v_reuseFailAlloc_3406_, 5, v_srcDir_3376_);
lean_ctor_set(v_reuseFailAlloc_3406_, 6, v_buildDir_3377_);
lean_ctor_set(v_reuseFailAlloc_3406_, 7, v_leanLibDir_3378_);
lean_ctor_set(v_reuseFailAlloc_3406_, 8, v_nativeLibDir_3379_);
lean_ctor_set(v_reuseFailAlloc_3406_, 9, v_binDir_3380_);
lean_ctor_set(v_reuseFailAlloc_3406_, 10, v_irDir_3381_);
lean_ctor_set(v_reuseFailAlloc_3406_, 11, v_releaseRepo_3382_);
lean_ctor_set(v_reuseFailAlloc_3406_, 12, v_buildArchive_3383_);
lean_ctor_set(v_reuseFailAlloc_3406_, 13, v_testDriver_3385_);
lean_ctor_set(v_reuseFailAlloc_3406_, 14, v_testDriverArgs_3386_);
lean_ctor_set(v_reuseFailAlloc_3406_, 15, v_lintDriver_3387_);
lean_ctor_set(v_reuseFailAlloc_3406_, 16, v_lintDriverArgs_3388_);
lean_ctor_set(v_reuseFailAlloc_3406_, 17, v_version_3389_);
lean_ctor_set(v_reuseFailAlloc_3406_, 18, v_versionTags_3390_);
lean_ctor_set(v_reuseFailAlloc_3406_, 19, v_description_3391_);
lean_ctor_set(v_reuseFailAlloc_3406_, 20, v_keywords_3392_);
lean_ctor_set(v_reuseFailAlloc_3406_, 21, v_homepage_3393_);
lean_ctor_set(v_reuseFailAlloc_3406_, 22, v_license_3394_);
lean_ctor_set(v_reuseFailAlloc_3406_, 23, v_licenseFiles_3395_);
lean_ctor_set(v_reuseFailAlloc_3406_, 24, v_readmeFile_3396_);
lean_ctor_set(v_reuseFailAlloc_3406_, 25, v_enableArtifactCache_x3f_3398_);
lean_ctor_set(v_reuseFailAlloc_3406_, 26, v_restoreAllArtifacts_x3f_3399_);
lean_ctor_set_uint8(v_reuseFailAlloc_3406_, sizeof(void*)*27, v_bootstrap_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3406_, sizeof(void*)*27 + 1, v_precompileModules_3374_);
lean_ctor_set_uint8(v_reuseFailAlloc_3406_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3384_);
lean_ctor_set_uint8(v_reuseFailAlloc_3406_, sizeof(void*)*27 + 3, v_reservoir_3397_);
lean_ctor_set_uint8(v_reuseFailAlloc_3406_, sizeof(void*)*27 + 5, v_allowImportAll_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*27 + 4, v_val_3367_);
return v___x_3405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_3408_, lean_object* v_cfg_3409_){
_start:
{
uint8_t v_val_134__boxed_3410_; lean_object* v_res_3411_; 
v_val_134__boxed_3410_ = lean_unbox(v_val_3408_);
v_res_3411_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(v_val_134__boxed_3410_, v_cfg_3409_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_3412_, lean_object* v_cfg_3413_){
_start:
{
lean_object* v_toWorkspaceConfig_3414_; lean_object* v_toLeanConfig_3415_; uint8_t v_bootstrap_3416_; lean_object* v_manifestFile_3417_; lean_object* v_extraDepTargets_3418_; uint8_t v_precompileModules_3419_; lean_object* v_moreGlobalServerArgs_3420_; lean_object* v_srcDir_3421_; lean_object* v_buildDir_3422_; lean_object* v_leanLibDir_3423_; lean_object* v_nativeLibDir_3424_; lean_object* v_binDir_3425_; lean_object* v_irDir_3426_; lean_object* v_releaseRepo_3427_; lean_object* v_buildArchive_3428_; uint8_t v_preferReleaseBuild_3429_; lean_object* v_testDriver_3430_; lean_object* v_testDriverArgs_3431_; lean_object* v_lintDriver_3432_; lean_object* v_lintDriverArgs_3433_; lean_object* v_version_3434_; lean_object* v_versionTags_3435_; lean_object* v_description_3436_; lean_object* v_keywords_3437_; lean_object* v_homepage_3438_; lean_object* v_license_3439_; lean_object* v_licenseFiles_3440_; lean_object* v_readmeFile_3441_; uint8_t v_reservoir_3442_; lean_object* v_enableArtifactCache_x3f_3443_; lean_object* v_restoreAllArtifacts_x3f_3444_; uint8_t v_libPrefixOnWindows_3445_; uint8_t v_allowImportAll_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3456_; 
v_toWorkspaceConfig_3414_ = lean_ctor_get(v_cfg_3413_, 0);
v_toLeanConfig_3415_ = lean_ctor_get(v_cfg_3413_, 1);
v_bootstrap_3416_ = lean_ctor_get_uint8(v_cfg_3413_, sizeof(void*)*27);
v_manifestFile_3417_ = lean_ctor_get(v_cfg_3413_, 2);
v_extraDepTargets_3418_ = lean_ctor_get(v_cfg_3413_, 3);
v_precompileModules_3419_ = lean_ctor_get_uint8(v_cfg_3413_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3420_ = lean_ctor_get(v_cfg_3413_, 4);
v_srcDir_3421_ = lean_ctor_get(v_cfg_3413_, 5);
v_buildDir_3422_ = lean_ctor_get(v_cfg_3413_, 6);
v_leanLibDir_3423_ = lean_ctor_get(v_cfg_3413_, 7);
v_nativeLibDir_3424_ = lean_ctor_get(v_cfg_3413_, 8);
v_binDir_3425_ = lean_ctor_get(v_cfg_3413_, 9);
v_irDir_3426_ = lean_ctor_get(v_cfg_3413_, 10);
v_releaseRepo_3427_ = lean_ctor_get(v_cfg_3413_, 11);
v_buildArchive_3428_ = lean_ctor_get(v_cfg_3413_, 12);
v_preferReleaseBuild_3429_ = lean_ctor_get_uint8(v_cfg_3413_, sizeof(void*)*27 + 2);
v_testDriver_3430_ = lean_ctor_get(v_cfg_3413_, 13);
v_testDriverArgs_3431_ = lean_ctor_get(v_cfg_3413_, 14);
v_lintDriver_3432_ = lean_ctor_get(v_cfg_3413_, 15);
v_lintDriverArgs_3433_ = lean_ctor_get(v_cfg_3413_, 16);
v_version_3434_ = lean_ctor_get(v_cfg_3413_, 17);
v_versionTags_3435_ = lean_ctor_get(v_cfg_3413_, 18);
v_description_3436_ = lean_ctor_get(v_cfg_3413_, 19);
v_keywords_3437_ = lean_ctor_get(v_cfg_3413_, 20);
v_homepage_3438_ = lean_ctor_get(v_cfg_3413_, 21);
v_license_3439_ = lean_ctor_get(v_cfg_3413_, 22);
v_licenseFiles_3440_ = lean_ctor_get(v_cfg_3413_, 23);
v_readmeFile_3441_ = lean_ctor_get(v_cfg_3413_, 24);
v_reservoir_3442_ = lean_ctor_get_uint8(v_cfg_3413_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3443_ = lean_ctor_get(v_cfg_3413_, 25);
v_restoreAllArtifacts_x3f_3444_ = lean_ctor_get(v_cfg_3413_, 26);
v_libPrefixOnWindows_3445_ = lean_ctor_get_uint8(v_cfg_3413_, sizeof(void*)*27 + 4);
v_allowImportAll_3446_ = lean_ctor_get_uint8(v_cfg_3413_, sizeof(void*)*27 + 5);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_cfg_3413_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3448_ = v_cfg_3413_;
v_isShared_3449_ = v_isSharedCheck_3456_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3444_);
lean_inc(v_enableArtifactCache_x3f_3443_);
lean_inc(v_readmeFile_3441_);
lean_inc(v_licenseFiles_3440_);
lean_inc(v_license_3439_);
lean_inc(v_homepage_3438_);
lean_inc(v_keywords_3437_);
lean_inc(v_description_3436_);
lean_inc(v_versionTags_3435_);
lean_inc(v_version_3434_);
lean_inc(v_lintDriverArgs_3433_);
lean_inc(v_lintDriver_3432_);
lean_inc(v_testDriverArgs_3431_);
lean_inc(v_testDriver_3430_);
lean_inc(v_buildArchive_3428_);
lean_inc(v_releaseRepo_3427_);
lean_inc(v_irDir_3426_);
lean_inc(v_binDir_3425_);
lean_inc(v_nativeLibDir_3424_);
lean_inc(v_leanLibDir_3423_);
lean_inc(v_buildDir_3422_);
lean_inc(v_srcDir_3421_);
lean_inc(v_moreGlobalServerArgs_3420_);
lean_inc(v_extraDepTargets_3418_);
lean_inc(v_manifestFile_3417_);
lean_inc(v_toLeanConfig_3415_);
lean_inc(v_toWorkspaceConfig_3414_);
lean_dec(v_cfg_3413_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3456_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3450_ = lean_box(v_libPrefixOnWindows_3445_);
v___x_3451_ = lean_apply_1(v_f_3412_, v___x_3450_);
if (v_isShared_3449_ == 0)
{
v___x_3453_ = v___x_3448_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_toWorkspaceConfig_3414_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_toLeanConfig_3415_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_manifestFile_3417_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_extraDepTargets_3418_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v_moreGlobalServerArgs_3420_);
lean_ctor_set(v_reuseFailAlloc_3455_, 5, v_srcDir_3421_);
lean_ctor_set(v_reuseFailAlloc_3455_, 6, v_buildDir_3422_);
lean_ctor_set(v_reuseFailAlloc_3455_, 7, v_leanLibDir_3423_);
lean_ctor_set(v_reuseFailAlloc_3455_, 8, v_nativeLibDir_3424_);
lean_ctor_set(v_reuseFailAlloc_3455_, 9, v_binDir_3425_);
lean_ctor_set(v_reuseFailAlloc_3455_, 10, v_irDir_3426_);
lean_ctor_set(v_reuseFailAlloc_3455_, 11, v_releaseRepo_3427_);
lean_ctor_set(v_reuseFailAlloc_3455_, 12, v_buildArchive_3428_);
lean_ctor_set(v_reuseFailAlloc_3455_, 13, v_testDriver_3430_);
lean_ctor_set(v_reuseFailAlloc_3455_, 14, v_testDriverArgs_3431_);
lean_ctor_set(v_reuseFailAlloc_3455_, 15, v_lintDriver_3432_);
lean_ctor_set(v_reuseFailAlloc_3455_, 16, v_lintDriverArgs_3433_);
lean_ctor_set(v_reuseFailAlloc_3455_, 17, v_version_3434_);
lean_ctor_set(v_reuseFailAlloc_3455_, 18, v_versionTags_3435_);
lean_ctor_set(v_reuseFailAlloc_3455_, 19, v_description_3436_);
lean_ctor_set(v_reuseFailAlloc_3455_, 20, v_keywords_3437_);
lean_ctor_set(v_reuseFailAlloc_3455_, 21, v_homepage_3438_);
lean_ctor_set(v_reuseFailAlloc_3455_, 22, v_license_3439_);
lean_ctor_set(v_reuseFailAlloc_3455_, 23, v_licenseFiles_3440_);
lean_ctor_set(v_reuseFailAlloc_3455_, 24, v_readmeFile_3441_);
lean_ctor_set(v_reuseFailAlloc_3455_, 25, v_enableArtifactCache_x3f_3443_);
lean_ctor_set(v_reuseFailAlloc_3455_, 26, v_restoreAllArtifacts_x3f_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*27, v_bootstrap_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*27 + 1, v_precompileModules_3419_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3429_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*27 + 3, v_reservoir_3442_);
v___x_3453_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
uint8_t v___x_3454_; 
v___x_3454_ = lean_unbox(v___x_3451_);
lean_ctor_set_uint8(v___x_3453_, sizeof(void*)*27 + 4, v___x_3454_);
lean_ctor_set_uint8(v___x_3453_, sizeof(void*)*27 + 5, v_allowImportAll_3446_);
return v___x_3453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3465_, lean_object* v_n_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3468_, lean_object* v_n_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3468_, v_n_3469_);
lean_dec(v_n_3469_);
lean_dec(v_p_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3471_, lean_object* v_n_3472_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3471_, v_n_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3474_, lean_object* v_n_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3474_, v_n_3475_);
lean_dec(v_n_3475_);
lean_dec(v_p_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_3477_){
_start:
{
uint8_t v_allowImportAll_3478_; 
v_allowImportAll_3478_ = lean_ctor_get_uint8(v_cfg_3477_, sizeof(void*)*27 + 5);
return v_allowImportAll_3478_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_3479_){
_start:
{
uint8_t v_res_3480_; lean_object* v_r_3481_; 
v_res_3480_ = l_Lake_PackageConfig_allowImportAll___proj___lam__0(v_cfg_3479_);
lean_dec_ref(v_cfg_3479_);
v_r_3481_ = lean_box(v_res_3480_);
return v_r_3481_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t v_val_3482_, lean_object* v_cfg_3483_){
_start:
{
lean_object* v_toWorkspaceConfig_3484_; lean_object* v_toLeanConfig_3485_; uint8_t v_bootstrap_3486_; lean_object* v_manifestFile_3487_; lean_object* v_extraDepTargets_3488_; uint8_t v_precompileModules_3489_; lean_object* v_moreGlobalServerArgs_3490_; lean_object* v_srcDir_3491_; lean_object* v_buildDir_3492_; lean_object* v_leanLibDir_3493_; lean_object* v_nativeLibDir_3494_; lean_object* v_binDir_3495_; lean_object* v_irDir_3496_; lean_object* v_releaseRepo_3497_; lean_object* v_buildArchive_3498_; uint8_t v_preferReleaseBuild_3499_; lean_object* v_testDriver_3500_; lean_object* v_testDriverArgs_3501_; lean_object* v_lintDriver_3502_; lean_object* v_lintDriverArgs_3503_; lean_object* v_version_3504_; lean_object* v_versionTags_3505_; lean_object* v_description_3506_; lean_object* v_keywords_3507_; lean_object* v_homepage_3508_; lean_object* v_license_3509_; lean_object* v_licenseFiles_3510_; lean_object* v_readmeFile_3511_; uint8_t v_reservoir_3512_; lean_object* v_enableArtifactCache_x3f_3513_; lean_object* v_restoreAllArtifacts_x3f_3514_; uint8_t v_libPrefixOnWindows_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
v_toWorkspaceConfig_3484_ = lean_ctor_get(v_cfg_3483_, 0);
v_toLeanConfig_3485_ = lean_ctor_get(v_cfg_3483_, 1);
v_bootstrap_3486_ = lean_ctor_get_uint8(v_cfg_3483_, sizeof(void*)*27);
v_manifestFile_3487_ = lean_ctor_get(v_cfg_3483_, 2);
v_extraDepTargets_3488_ = lean_ctor_get(v_cfg_3483_, 3);
v_precompileModules_3489_ = lean_ctor_get_uint8(v_cfg_3483_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3490_ = lean_ctor_get(v_cfg_3483_, 4);
v_srcDir_3491_ = lean_ctor_get(v_cfg_3483_, 5);
v_buildDir_3492_ = lean_ctor_get(v_cfg_3483_, 6);
v_leanLibDir_3493_ = lean_ctor_get(v_cfg_3483_, 7);
v_nativeLibDir_3494_ = lean_ctor_get(v_cfg_3483_, 8);
v_binDir_3495_ = lean_ctor_get(v_cfg_3483_, 9);
v_irDir_3496_ = lean_ctor_get(v_cfg_3483_, 10);
v_releaseRepo_3497_ = lean_ctor_get(v_cfg_3483_, 11);
v_buildArchive_3498_ = lean_ctor_get(v_cfg_3483_, 12);
v_preferReleaseBuild_3499_ = lean_ctor_get_uint8(v_cfg_3483_, sizeof(void*)*27 + 2);
v_testDriver_3500_ = lean_ctor_get(v_cfg_3483_, 13);
v_testDriverArgs_3501_ = lean_ctor_get(v_cfg_3483_, 14);
v_lintDriver_3502_ = lean_ctor_get(v_cfg_3483_, 15);
v_lintDriverArgs_3503_ = lean_ctor_get(v_cfg_3483_, 16);
v_version_3504_ = lean_ctor_get(v_cfg_3483_, 17);
v_versionTags_3505_ = lean_ctor_get(v_cfg_3483_, 18);
v_description_3506_ = lean_ctor_get(v_cfg_3483_, 19);
v_keywords_3507_ = lean_ctor_get(v_cfg_3483_, 20);
v_homepage_3508_ = lean_ctor_get(v_cfg_3483_, 21);
v_license_3509_ = lean_ctor_get(v_cfg_3483_, 22);
v_licenseFiles_3510_ = lean_ctor_get(v_cfg_3483_, 23);
v_readmeFile_3511_ = lean_ctor_get(v_cfg_3483_, 24);
v_reservoir_3512_ = lean_ctor_get_uint8(v_cfg_3483_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3513_ = lean_ctor_get(v_cfg_3483_, 25);
v_restoreAllArtifacts_x3f_3514_ = lean_ctor_get(v_cfg_3483_, 26);
v_libPrefixOnWindows_3515_ = lean_ctor_get_uint8(v_cfg_3483_, sizeof(void*)*27 + 4);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_cfg_3483_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v_cfg_3483_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3514_);
lean_inc(v_enableArtifactCache_x3f_3513_);
lean_inc(v_readmeFile_3511_);
lean_inc(v_licenseFiles_3510_);
lean_inc(v_license_3509_);
lean_inc(v_homepage_3508_);
lean_inc(v_keywords_3507_);
lean_inc(v_description_3506_);
lean_inc(v_versionTags_3505_);
lean_inc(v_version_3504_);
lean_inc(v_lintDriverArgs_3503_);
lean_inc(v_lintDriver_3502_);
lean_inc(v_testDriverArgs_3501_);
lean_inc(v_testDriver_3500_);
lean_inc(v_buildArchive_3498_);
lean_inc(v_releaseRepo_3497_);
lean_inc(v_irDir_3496_);
lean_inc(v_binDir_3495_);
lean_inc(v_nativeLibDir_3494_);
lean_inc(v_leanLibDir_3493_);
lean_inc(v_buildDir_3492_);
lean_inc(v_srcDir_3491_);
lean_inc(v_moreGlobalServerArgs_3490_);
lean_inc(v_extraDepTargets_3488_);
lean_inc(v_manifestFile_3487_);
lean_inc(v_toLeanConfig_3485_);
lean_inc(v_toWorkspaceConfig_3484_);
lean_dec(v_cfg_3483_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_toWorkspaceConfig_3484_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_toLeanConfig_3485_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_manifestFile_3487_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_extraDepTargets_3488_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_moreGlobalServerArgs_3490_);
lean_ctor_set(v_reuseFailAlloc_3521_, 5, v_srcDir_3491_);
lean_ctor_set(v_reuseFailAlloc_3521_, 6, v_buildDir_3492_);
lean_ctor_set(v_reuseFailAlloc_3521_, 7, v_leanLibDir_3493_);
lean_ctor_set(v_reuseFailAlloc_3521_, 8, v_nativeLibDir_3494_);
lean_ctor_set(v_reuseFailAlloc_3521_, 9, v_binDir_3495_);
lean_ctor_set(v_reuseFailAlloc_3521_, 10, v_irDir_3496_);
lean_ctor_set(v_reuseFailAlloc_3521_, 11, v_releaseRepo_3497_);
lean_ctor_set(v_reuseFailAlloc_3521_, 12, v_buildArchive_3498_);
lean_ctor_set(v_reuseFailAlloc_3521_, 13, v_testDriver_3500_);
lean_ctor_set(v_reuseFailAlloc_3521_, 14, v_testDriverArgs_3501_);
lean_ctor_set(v_reuseFailAlloc_3521_, 15, v_lintDriver_3502_);
lean_ctor_set(v_reuseFailAlloc_3521_, 16, v_lintDriverArgs_3503_);
lean_ctor_set(v_reuseFailAlloc_3521_, 17, v_version_3504_);
lean_ctor_set(v_reuseFailAlloc_3521_, 18, v_versionTags_3505_);
lean_ctor_set(v_reuseFailAlloc_3521_, 19, v_description_3506_);
lean_ctor_set(v_reuseFailAlloc_3521_, 20, v_keywords_3507_);
lean_ctor_set(v_reuseFailAlloc_3521_, 21, v_homepage_3508_);
lean_ctor_set(v_reuseFailAlloc_3521_, 22, v_license_3509_);
lean_ctor_set(v_reuseFailAlloc_3521_, 23, v_licenseFiles_3510_);
lean_ctor_set(v_reuseFailAlloc_3521_, 24, v_readmeFile_3511_);
lean_ctor_set(v_reuseFailAlloc_3521_, 25, v_enableArtifactCache_x3f_3513_);
lean_ctor_set(v_reuseFailAlloc_3521_, 26, v_restoreAllArtifacts_x3f_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3521_, sizeof(void*)*27, v_bootstrap_3486_);
lean_ctor_set_uint8(v_reuseFailAlloc_3521_, sizeof(void*)*27 + 1, v_precompileModules_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3521_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3521_, sizeof(void*)*27 + 3, v_reservoir_3512_);
lean_ctor_set_uint8(v_reuseFailAlloc_3521_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*27 + 5, v_val_3482_);
return v___x_3520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_3523_, lean_object* v_cfg_3524_){
_start:
{
uint8_t v_val_134__boxed_3525_; lean_object* v_res_3526_; 
v_val_134__boxed_3525_ = lean_unbox(v_val_3523_);
v_res_3526_ = l_Lake_PackageConfig_allowImportAll___proj___lam__1(v_val_134__boxed_3525_, v_cfg_3524_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* v_f_3527_, lean_object* v_cfg_3528_){
_start:
{
lean_object* v_toWorkspaceConfig_3529_; lean_object* v_toLeanConfig_3530_; uint8_t v_bootstrap_3531_; lean_object* v_manifestFile_3532_; lean_object* v_extraDepTargets_3533_; uint8_t v_precompileModules_3534_; lean_object* v_moreGlobalServerArgs_3535_; lean_object* v_srcDir_3536_; lean_object* v_buildDir_3537_; lean_object* v_leanLibDir_3538_; lean_object* v_nativeLibDir_3539_; lean_object* v_binDir_3540_; lean_object* v_irDir_3541_; lean_object* v_releaseRepo_3542_; lean_object* v_buildArchive_3543_; uint8_t v_preferReleaseBuild_3544_; lean_object* v_testDriver_3545_; lean_object* v_testDriverArgs_3546_; lean_object* v_lintDriver_3547_; lean_object* v_lintDriverArgs_3548_; lean_object* v_version_3549_; lean_object* v_versionTags_3550_; lean_object* v_description_3551_; lean_object* v_keywords_3552_; lean_object* v_homepage_3553_; lean_object* v_license_3554_; lean_object* v_licenseFiles_3555_; lean_object* v_readmeFile_3556_; uint8_t v_reservoir_3557_; lean_object* v_enableArtifactCache_x3f_3558_; lean_object* v_restoreAllArtifacts_x3f_3559_; uint8_t v_libPrefixOnWindows_3560_; uint8_t v_allowImportAll_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3571_; 
v_toWorkspaceConfig_3529_ = lean_ctor_get(v_cfg_3528_, 0);
v_toLeanConfig_3530_ = lean_ctor_get(v_cfg_3528_, 1);
v_bootstrap_3531_ = lean_ctor_get_uint8(v_cfg_3528_, sizeof(void*)*27);
v_manifestFile_3532_ = lean_ctor_get(v_cfg_3528_, 2);
v_extraDepTargets_3533_ = lean_ctor_get(v_cfg_3528_, 3);
v_precompileModules_3534_ = lean_ctor_get_uint8(v_cfg_3528_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3535_ = lean_ctor_get(v_cfg_3528_, 4);
v_srcDir_3536_ = lean_ctor_get(v_cfg_3528_, 5);
v_buildDir_3537_ = lean_ctor_get(v_cfg_3528_, 6);
v_leanLibDir_3538_ = lean_ctor_get(v_cfg_3528_, 7);
v_nativeLibDir_3539_ = lean_ctor_get(v_cfg_3528_, 8);
v_binDir_3540_ = lean_ctor_get(v_cfg_3528_, 9);
v_irDir_3541_ = lean_ctor_get(v_cfg_3528_, 10);
v_releaseRepo_3542_ = lean_ctor_get(v_cfg_3528_, 11);
v_buildArchive_3543_ = lean_ctor_get(v_cfg_3528_, 12);
v_preferReleaseBuild_3544_ = lean_ctor_get_uint8(v_cfg_3528_, sizeof(void*)*27 + 2);
v_testDriver_3545_ = lean_ctor_get(v_cfg_3528_, 13);
v_testDriverArgs_3546_ = lean_ctor_get(v_cfg_3528_, 14);
v_lintDriver_3547_ = lean_ctor_get(v_cfg_3528_, 15);
v_lintDriverArgs_3548_ = lean_ctor_get(v_cfg_3528_, 16);
v_version_3549_ = lean_ctor_get(v_cfg_3528_, 17);
v_versionTags_3550_ = lean_ctor_get(v_cfg_3528_, 18);
v_description_3551_ = lean_ctor_get(v_cfg_3528_, 19);
v_keywords_3552_ = lean_ctor_get(v_cfg_3528_, 20);
v_homepage_3553_ = lean_ctor_get(v_cfg_3528_, 21);
v_license_3554_ = lean_ctor_get(v_cfg_3528_, 22);
v_licenseFiles_3555_ = lean_ctor_get(v_cfg_3528_, 23);
v_readmeFile_3556_ = lean_ctor_get(v_cfg_3528_, 24);
v_reservoir_3557_ = lean_ctor_get_uint8(v_cfg_3528_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3558_ = lean_ctor_get(v_cfg_3528_, 25);
v_restoreAllArtifacts_x3f_3559_ = lean_ctor_get(v_cfg_3528_, 26);
v_libPrefixOnWindows_3560_ = lean_ctor_get_uint8(v_cfg_3528_, sizeof(void*)*27 + 4);
v_allowImportAll_3561_ = lean_ctor_get_uint8(v_cfg_3528_, sizeof(void*)*27 + 5);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_cfg_3528_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3563_ = v_cfg_3528_;
v_isShared_3564_ = v_isSharedCheck_3571_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3559_);
lean_inc(v_enableArtifactCache_x3f_3558_);
lean_inc(v_readmeFile_3556_);
lean_inc(v_licenseFiles_3555_);
lean_inc(v_license_3554_);
lean_inc(v_homepage_3553_);
lean_inc(v_keywords_3552_);
lean_inc(v_description_3551_);
lean_inc(v_versionTags_3550_);
lean_inc(v_version_3549_);
lean_inc(v_lintDriverArgs_3548_);
lean_inc(v_lintDriver_3547_);
lean_inc(v_testDriverArgs_3546_);
lean_inc(v_testDriver_3545_);
lean_inc(v_buildArchive_3543_);
lean_inc(v_releaseRepo_3542_);
lean_inc(v_irDir_3541_);
lean_inc(v_binDir_3540_);
lean_inc(v_nativeLibDir_3539_);
lean_inc(v_leanLibDir_3538_);
lean_inc(v_buildDir_3537_);
lean_inc(v_srcDir_3536_);
lean_inc(v_moreGlobalServerArgs_3535_);
lean_inc(v_extraDepTargets_3533_);
lean_inc(v_manifestFile_3532_);
lean_inc(v_toLeanConfig_3530_);
lean_inc(v_toWorkspaceConfig_3529_);
lean_dec(v_cfg_3528_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3571_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3565_ = lean_box(v_allowImportAll_3561_);
v___x_3566_ = lean_apply_1(v_f_3527_, v___x_3565_);
if (v_isShared_3564_ == 0)
{
v___x_3568_ = v___x_3563_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_toWorkspaceConfig_3529_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_toLeanConfig_3530_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_manifestFile_3532_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_extraDepTargets_3533_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_moreGlobalServerArgs_3535_);
lean_ctor_set(v_reuseFailAlloc_3570_, 5, v_srcDir_3536_);
lean_ctor_set(v_reuseFailAlloc_3570_, 6, v_buildDir_3537_);
lean_ctor_set(v_reuseFailAlloc_3570_, 7, v_leanLibDir_3538_);
lean_ctor_set(v_reuseFailAlloc_3570_, 8, v_nativeLibDir_3539_);
lean_ctor_set(v_reuseFailAlloc_3570_, 9, v_binDir_3540_);
lean_ctor_set(v_reuseFailAlloc_3570_, 10, v_irDir_3541_);
lean_ctor_set(v_reuseFailAlloc_3570_, 11, v_releaseRepo_3542_);
lean_ctor_set(v_reuseFailAlloc_3570_, 12, v_buildArchive_3543_);
lean_ctor_set(v_reuseFailAlloc_3570_, 13, v_testDriver_3545_);
lean_ctor_set(v_reuseFailAlloc_3570_, 14, v_testDriverArgs_3546_);
lean_ctor_set(v_reuseFailAlloc_3570_, 15, v_lintDriver_3547_);
lean_ctor_set(v_reuseFailAlloc_3570_, 16, v_lintDriverArgs_3548_);
lean_ctor_set(v_reuseFailAlloc_3570_, 17, v_version_3549_);
lean_ctor_set(v_reuseFailAlloc_3570_, 18, v_versionTags_3550_);
lean_ctor_set(v_reuseFailAlloc_3570_, 19, v_description_3551_);
lean_ctor_set(v_reuseFailAlloc_3570_, 20, v_keywords_3552_);
lean_ctor_set(v_reuseFailAlloc_3570_, 21, v_homepage_3553_);
lean_ctor_set(v_reuseFailAlloc_3570_, 22, v_license_3554_);
lean_ctor_set(v_reuseFailAlloc_3570_, 23, v_licenseFiles_3555_);
lean_ctor_set(v_reuseFailAlloc_3570_, 24, v_readmeFile_3556_);
lean_ctor_set(v_reuseFailAlloc_3570_, 25, v_enableArtifactCache_x3f_3558_);
lean_ctor_set(v_reuseFailAlloc_3570_, 26, v_restoreAllArtifacts_x3f_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*27, v_bootstrap_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*27 + 1, v_precompileModules_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3544_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*27 + 3, v_reservoir_3557_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3560_);
v___x_3568_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_unbox(v___x_3566_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*27 + 5, v___x_3569_);
return v___x_3568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3580_, lean_object* v_n_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3583_, lean_object* v_n_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3583_, v_n_3584_);
lean_dec(v_n_3584_);
lean_dec(v_p_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3586_, lean_object* v_n_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3586_, v_n_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3589_, lean_object* v_n_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3589_, v_n_3590_);
lean_dec(v_n_3590_);
lean_dec(v_p_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* v_cfg_3592_){
_start:
{
lean_object* v_toWorkspaceConfig_3593_; 
v_toWorkspaceConfig_3593_ = lean_ctor_get(v_cfg_3592_, 0);
lean_inc_ref(v_toWorkspaceConfig_3593_);
return v_toWorkspaceConfig_3593_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* v_cfg_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(v_cfg_3594_);
lean_dec_ref(v_cfg_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* v_val_3596_, lean_object* v_cfg_3597_){
_start:
{
lean_object* v_toLeanConfig_3598_; uint8_t v_bootstrap_3599_; lean_object* v_manifestFile_3600_; lean_object* v_extraDepTargets_3601_; uint8_t v_precompileModules_3602_; lean_object* v_moreGlobalServerArgs_3603_; lean_object* v_srcDir_3604_; lean_object* v_buildDir_3605_; lean_object* v_leanLibDir_3606_; lean_object* v_nativeLibDir_3607_; lean_object* v_binDir_3608_; lean_object* v_irDir_3609_; lean_object* v_releaseRepo_3610_; lean_object* v_buildArchive_3611_; uint8_t v_preferReleaseBuild_3612_; lean_object* v_testDriver_3613_; lean_object* v_testDriverArgs_3614_; lean_object* v_lintDriver_3615_; lean_object* v_lintDriverArgs_3616_; lean_object* v_version_3617_; lean_object* v_versionTags_3618_; lean_object* v_description_3619_; lean_object* v_keywords_3620_; lean_object* v_homepage_3621_; lean_object* v_license_3622_; lean_object* v_licenseFiles_3623_; lean_object* v_readmeFile_3624_; uint8_t v_reservoir_3625_; lean_object* v_enableArtifactCache_x3f_3626_; lean_object* v_restoreAllArtifacts_x3f_3627_; uint8_t v_libPrefixOnWindows_3628_; uint8_t v_allowImportAll_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v_toLeanConfig_3598_ = lean_ctor_get(v_cfg_3597_, 1);
v_bootstrap_3599_ = lean_ctor_get_uint8(v_cfg_3597_, sizeof(void*)*27);
v_manifestFile_3600_ = lean_ctor_get(v_cfg_3597_, 2);
v_extraDepTargets_3601_ = lean_ctor_get(v_cfg_3597_, 3);
v_precompileModules_3602_ = lean_ctor_get_uint8(v_cfg_3597_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3603_ = lean_ctor_get(v_cfg_3597_, 4);
v_srcDir_3604_ = lean_ctor_get(v_cfg_3597_, 5);
v_buildDir_3605_ = lean_ctor_get(v_cfg_3597_, 6);
v_leanLibDir_3606_ = lean_ctor_get(v_cfg_3597_, 7);
v_nativeLibDir_3607_ = lean_ctor_get(v_cfg_3597_, 8);
v_binDir_3608_ = lean_ctor_get(v_cfg_3597_, 9);
v_irDir_3609_ = lean_ctor_get(v_cfg_3597_, 10);
v_releaseRepo_3610_ = lean_ctor_get(v_cfg_3597_, 11);
v_buildArchive_3611_ = lean_ctor_get(v_cfg_3597_, 12);
v_preferReleaseBuild_3612_ = lean_ctor_get_uint8(v_cfg_3597_, sizeof(void*)*27 + 2);
v_testDriver_3613_ = lean_ctor_get(v_cfg_3597_, 13);
v_testDriverArgs_3614_ = lean_ctor_get(v_cfg_3597_, 14);
v_lintDriver_3615_ = lean_ctor_get(v_cfg_3597_, 15);
v_lintDriverArgs_3616_ = lean_ctor_get(v_cfg_3597_, 16);
v_version_3617_ = lean_ctor_get(v_cfg_3597_, 17);
v_versionTags_3618_ = lean_ctor_get(v_cfg_3597_, 18);
v_description_3619_ = lean_ctor_get(v_cfg_3597_, 19);
v_keywords_3620_ = lean_ctor_get(v_cfg_3597_, 20);
v_homepage_3621_ = lean_ctor_get(v_cfg_3597_, 21);
v_license_3622_ = lean_ctor_get(v_cfg_3597_, 22);
v_licenseFiles_3623_ = lean_ctor_get(v_cfg_3597_, 23);
v_readmeFile_3624_ = lean_ctor_get(v_cfg_3597_, 24);
v_reservoir_3625_ = lean_ctor_get_uint8(v_cfg_3597_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3626_ = lean_ctor_get(v_cfg_3597_, 25);
v_restoreAllArtifacts_x3f_3627_ = lean_ctor_get(v_cfg_3597_, 26);
v_libPrefixOnWindows_3628_ = lean_ctor_get_uint8(v_cfg_3597_, sizeof(void*)*27 + 4);
v_allowImportAll_3629_ = lean_ctor_get_uint8(v_cfg_3597_, sizeof(void*)*27 + 5);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_cfg_3597_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v_cfg_3597_, 0);
lean_dec(v_unused_3637_);
v___x_3631_ = v_cfg_3597_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3627_);
lean_inc(v_enableArtifactCache_x3f_3626_);
lean_inc(v_readmeFile_3624_);
lean_inc(v_licenseFiles_3623_);
lean_inc(v_license_3622_);
lean_inc(v_homepage_3621_);
lean_inc(v_keywords_3620_);
lean_inc(v_description_3619_);
lean_inc(v_versionTags_3618_);
lean_inc(v_version_3617_);
lean_inc(v_lintDriverArgs_3616_);
lean_inc(v_lintDriver_3615_);
lean_inc(v_testDriverArgs_3614_);
lean_inc(v_testDriver_3613_);
lean_inc(v_buildArchive_3611_);
lean_inc(v_releaseRepo_3610_);
lean_inc(v_irDir_3609_);
lean_inc(v_binDir_3608_);
lean_inc(v_nativeLibDir_3607_);
lean_inc(v_leanLibDir_3606_);
lean_inc(v_buildDir_3605_);
lean_inc(v_srcDir_3604_);
lean_inc(v_moreGlobalServerArgs_3603_);
lean_inc(v_extraDepTargets_3601_);
lean_inc(v_manifestFile_3600_);
lean_inc(v_toLeanConfig_3598_);
lean_dec(v_cfg_3597_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v_val_3596_);
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_val_3596_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_toLeanConfig_3598_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_manifestFile_3600_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_extraDepTargets_3601_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_moreGlobalServerArgs_3603_);
lean_ctor_set(v_reuseFailAlloc_3635_, 5, v_srcDir_3604_);
lean_ctor_set(v_reuseFailAlloc_3635_, 6, v_buildDir_3605_);
lean_ctor_set(v_reuseFailAlloc_3635_, 7, v_leanLibDir_3606_);
lean_ctor_set(v_reuseFailAlloc_3635_, 8, v_nativeLibDir_3607_);
lean_ctor_set(v_reuseFailAlloc_3635_, 9, v_binDir_3608_);
lean_ctor_set(v_reuseFailAlloc_3635_, 10, v_irDir_3609_);
lean_ctor_set(v_reuseFailAlloc_3635_, 11, v_releaseRepo_3610_);
lean_ctor_set(v_reuseFailAlloc_3635_, 12, v_buildArchive_3611_);
lean_ctor_set(v_reuseFailAlloc_3635_, 13, v_testDriver_3613_);
lean_ctor_set(v_reuseFailAlloc_3635_, 14, v_testDriverArgs_3614_);
lean_ctor_set(v_reuseFailAlloc_3635_, 15, v_lintDriver_3615_);
lean_ctor_set(v_reuseFailAlloc_3635_, 16, v_lintDriverArgs_3616_);
lean_ctor_set(v_reuseFailAlloc_3635_, 17, v_version_3617_);
lean_ctor_set(v_reuseFailAlloc_3635_, 18, v_versionTags_3618_);
lean_ctor_set(v_reuseFailAlloc_3635_, 19, v_description_3619_);
lean_ctor_set(v_reuseFailAlloc_3635_, 20, v_keywords_3620_);
lean_ctor_set(v_reuseFailAlloc_3635_, 21, v_homepage_3621_);
lean_ctor_set(v_reuseFailAlloc_3635_, 22, v_license_3622_);
lean_ctor_set(v_reuseFailAlloc_3635_, 23, v_licenseFiles_3623_);
lean_ctor_set(v_reuseFailAlloc_3635_, 24, v_readmeFile_3624_);
lean_ctor_set(v_reuseFailAlloc_3635_, 25, v_enableArtifactCache_x3f_3626_);
lean_ctor_set(v_reuseFailAlloc_3635_, 26, v_restoreAllArtifacts_x3f_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*27, v_bootstrap_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*27 + 1, v_precompileModules_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*27 + 3, v_reservoir_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, sizeof(void*)*27 + 5, v_allowImportAll_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* v_f_3638_, lean_object* v_cfg_3639_){
_start:
{
lean_object* v_toWorkspaceConfig_3640_; lean_object* v_toLeanConfig_3641_; uint8_t v_bootstrap_3642_; lean_object* v_manifestFile_3643_; lean_object* v_extraDepTargets_3644_; uint8_t v_precompileModules_3645_; lean_object* v_moreGlobalServerArgs_3646_; lean_object* v_srcDir_3647_; lean_object* v_buildDir_3648_; lean_object* v_leanLibDir_3649_; lean_object* v_nativeLibDir_3650_; lean_object* v_binDir_3651_; lean_object* v_irDir_3652_; lean_object* v_releaseRepo_3653_; lean_object* v_buildArchive_3654_; uint8_t v_preferReleaseBuild_3655_; lean_object* v_testDriver_3656_; lean_object* v_testDriverArgs_3657_; lean_object* v_lintDriver_3658_; lean_object* v_lintDriverArgs_3659_; lean_object* v_version_3660_; lean_object* v_versionTags_3661_; lean_object* v_description_3662_; lean_object* v_keywords_3663_; lean_object* v_homepage_3664_; lean_object* v_license_3665_; lean_object* v_licenseFiles_3666_; lean_object* v_readmeFile_3667_; uint8_t v_reservoir_3668_; lean_object* v_enableArtifactCache_x3f_3669_; lean_object* v_restoreAllArtifacts_x3f_3670_; uint8_t v_libPrefixOnWindows_3671_; uint8_t v_allowImportAll_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3680_; 
v_toWorkspaceConfig_3640_ = lean_ctor_get(v_cfg_3639_, 0);
v_toLeanConfig_3641_ = lean_ctor_get(v_cfg_3639_, 1);
v_bootstrap_3642_ = lean_ctor_get_uint8(v_cfg_3639_, sizeof(void*)*27);
v_manifestFile_3643_ = lean_ctor_get(v_cfg_3639_, 2);
v_extraDepTargets_3644_ = lean_ctor_get(v_cfg_3639_, 3);
v_precompileModules_3645_ = lean_ctor_get_uint8(v_cfg_3639_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3646_ = lean_ctor_get(v_cfg_3639_, 4);
v_srcDir_3647_ = lean_ctor_get(v_cfg_3639_, 5);
v_buildDir_3648_ = lean_ctor_get(v_cfg_3639_, 6);
v_leanLibDir_3649_ = lean_ctor_get(v_cfg_3639_, 7);
v_nativeLibDir_3650_ = lean_ctor_get(v_cfg_3639_, 8);
v_binDir_3651_ = lean_ctor_get(v_cfg_3639_, 9);
v_irDir_3652_ = lean_ctor_get(v_cfg_3639_, 10);
v_releaseRepo_3653_ = lean_ctor_get(v_cfg_3639_, 11);
v_buildArchive_3654_ = lean_ctor_get(v_cfg_3639_, 12);
v_preferReleaseBuild_3655_ = lean_ctor_get_uint8(v_cfg_3639_, sizeof(void*)*27 + 2);
v_testDriver_3656_ = lean_ctor_get(v_cfg_3639_, 13);
v_testDriverArgs_3657_ = lean_ctor_get(v_cfg_3639_, 14);
v_lintDriver_3658_ = lean_ctor_get(v_cfg_3639_, 15);
v_lintDriverArgs_3659_ = lean_ctor_get(v_cfg_3639_, 16);
v_version_3660_ = lean_ctor_get(v_cfg_3639_, 17);
v_versionTags_3661_ = lean_ctor_get(v_cfg_3639_, 18);
v_description_3662_ = lean_ctor_get(v_cfg_3639_, 19);
v_keywords_3663_ = lean_ctor_get(v_cfg_3639_, 20);
v_homepage_3664_ = lean_ctor_get(v_cfg_3639_, 21);
v_license_3665_ = lean_ctor_get(v_cfg_3639_, 22);
v_licenseFiles_3666_ = lean_ctor_get(v_cfg_3639_, 23);
v_readmeFile_3667_ = lean_ctor_get(v_cfg_3639_, 24);
v_reservoir_3668_ = lean_ctor_get_uint8(v_cfg_3639_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3669_ = lean_ctor_get(v_cfg_3639_, 25);
v_restoreAllArtifacts_x3f_3670_ = lean_ctor_get(v_cfg_3639_, 26);
v_libPrefixOnWindows_3671_ = lean_ctor_get_uint8(v_cfg_3639_, sizeof(void*)*27 + 4);
v_allowImportAll_3672_ = lean_ctor_get_uint8(v_cfg_3639_, sizeof(void*)*27 + 5);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_cfg_3639_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3674_ = v_cfg_3639_;
v_isShared_3675_ = v_isSharedCheck_3680_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3670_);
lean_inc(v_enableArtifactCache_x3f_3669_);
lean_inc(v_readmeFile_3667_);
lean_inc(v_licenseFiles_3666_);
lean_inc(v_license_3665_);
lean_inc(v_homepage_3664_);
lean_inc(v_keywords_3663_);
lean_inc(v_description_3662_);
lean_inc(v_versionTags_3661_);
lean_inc(v_version_3660_);
lean_inc(v_lintDriverArgs_3659_);
lean_inc(v_lintDriver_3658_);
lean_inc(v_testDriverArgs_3657_);
lean_inc(v_testDriver_3656_);
lean_inc(v_buildArchive_3654_);
lean_inc(v_releaseRepo_3653_);
lean_inc(v_irDir_3652_);
lean_inc(v_binDir_3651_);
lean_inc(v_nativeLibDir_3650_);
lean_inc(v_leanLibDir_3649_);
lean_inc(v_buildDir_3648_);
lean_inc(v_srcDir_3647_);
lean_inc(v_moreGlobalServerArgs_3646_);
lean_inc(v_extraDepTargets_3644_);
lean_inc(v_manifestFile_3643_);
lean_inc(v_toLeanConfig_3641_);
lean_inc(v_toWorkspaceConfig_3640_);
lean_dec(v_cfg_3639_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3680_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = lean_apply_1(v_f_3638_, v_toWorkspaceConfig_3640_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3676_);
v___x_3678_ = v___x_3674_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_toLeanConfig_3641_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_manifestFile_3643_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_extraDepTargets_3644_);
lean_ctor_set(v_reuseFailAlloc_3679_, 4, v_moreGlobalServerArgs_3646_);
lean_ctor_set(v_reuseFailAlloc_3679_, 5, v_srcDir_3647_);
lean_ctor_set(v_reuseFailAlloc_3679_, 6, v_buildDir_3648_);
lean_ctor_set(v_reuseFailAlloc_3679_, 7, v_leanLibDir_3649_);
lean_ctor_set(v_reuseFailAlloc_3679_, 8, v_nativeLibDir_3650_);
lean_ctor_set(v_reuseFailAlloc_3679_, 9, v_binDir_3651_);
lean_ctor_set(v_reuseFailAlloc_3679_, 10, v_irDir_3652_);
lean_ctor_set(v_reuseFailAlloc_3679_, 11, v_releaseRepo_3653_);
lean_ctor_set(v_reuseFailAlloc_3679_, 12, v_buildArchive_3654_);
lean_ctor_set(v_reuseFailAlloc_3679_, 13, v_testDriver_3656_);
lean_ctor_set(v_reuseFailAlloc_3679_, 14, v_testDriverArgs_3657_);
lean_ctor_set(v_reuseFailAlloc_3679_, 15, v_lintDriver_3658_);
lean_ctor_set(v_reuseFailAlloc_3679_, 16, v_lintDriverArgs_3659_);
lean_ctor_set(v_reuseFailAlloc_3679_, 17, v_version_3660_);
lean_ctor_set(v_reuseFailAlloc_3679_, 18, v_versionTags_3661_);
lean_ctor_set(v_reuseFailAlloc_3679_, 19, v_description_3662_);
lean_ctor_set(v_reuseFailAlloc_3679_, 20, v_keywords_3663_);
lean_ctor_set(v_reuseFailAlloc_3679_, 21, v_homepage_3664_);
lean_ctor_set(v_reuseFailAlloc_3679_, 22, v_license_3665_);
lean_ctor_set(v_reuseFailAlloc_3679_, 23, v_licenseFiles_3666_);
lean_ctor_set(v_reuseFailAlloc_3679_, 24, v_readmeFile_3667_);
lean_ctor_set(v_reuseFailAlloc_3679_, 25, v_enableArtifactCache_x3f_3669_);
lean_ctor_set(v_reuseFailAlloc_3679_, 26, v_restoreAllArtifacts_x3f_3670_);
lean_ctor_set_uint8(v_reuseFailAlloc_3679_, sizeof(void*)*27, v_bootstrap_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3679_, sizeof(void*)*27 + 1, v_precompileModules_3645_);
lean_ctor_set_uint8(v_reuseFailAlloc_3679_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3679_, sizeof(void*)*27 + 3, v_reservoir_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3679_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3679_, sizeof(void*)*27 + 5, v_allowImportAll_3672_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* v_x_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lake_defaultPackagesDir;
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* v_x_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(v_x_3683_);
lean_dec_ref(v_x_3683_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_3694_, lean_object* v_n_3695_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_3697_, lean_object* v_n_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3697_, v_n_3698_);
lean_dec(v_n_3698_);
lean_dec(v_p_3697_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_3700_, lean_object* v_n_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3700_, v_n_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_3703_, lean_object* v_n_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_3703_, v_n_3704_);
lean_dec(v_n_3704_);
lean_dec(v_p_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_3706_){
_start:
{
lean_object* v_toLeanConfig_3707_; 
v_toLeanConfig_3707_ = lean_ctor_get(v_cfg_3706_, 1);
lean_inc_ref(v_toLeanConfig_3707_);
return v_toLeanConfig_3707_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(v_cfg_3708_);
lean_dec_ref(v_cfg_3708_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* v_val_3710_, lean_object* v_cfg_3711_){
_start:
{
lean_object* v_toWorkspaceConfig_3712_; uint8_t v_bootstrap_3713_; lean_object* v_manifestFile_3714_; lean_object* v_extraDepTargets_3715_; uint8_t v_precompileModules_3716_; lean_object* v_moreGlobalServerArgs_3717_; lean_object* v_srcDir_3718_; lean_object* v_buildDir_3719_; lean_object* v_leanLibDir_3720_; lean_object* v_nativeLibDir_3721_; lean_object* v_binDir_3722_; lean_object* v_irDir_3723_; lean_object* v_releaseRepo_3724_; lean_object* v_buildArchive_3725_; uint8_t v_preferReleaseBuild_3726_; lean_object* v_testDriver_3727_; lean_object* v_testDriverArgs_3728_; lean_object* v_lintDriver_3729_; lean_object* v_lintDriverArgs_3730_; lean_object* v_version_3731_; lean_object* v_versionTags_3732_; lean_object* v_description_3733_; lean_object* v_keywords_3734_; lean_object* v_homepage_3735_; lean_object* v_license_3736_; lean_object* v_licenseFiles_3737_; lean_object* v_readmeFile_3738_; uint8_t v_reservoir_3739_; lean_object* v_enableArtifactCache_x3f_3740_; lean_object* v_restoreAllArtifacts_x3f_3741_; uint8_t v_libPrefixOnWindows_3742_; uint8_t v_allowImportAll_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
v_toWorkspaceConfig_3712_ = lean_ctor_get(v_cfg_3711_, 0);
v_bootstrap_3713_ = lean_ctor_get_uint8(v_cfg_3711_, sizeof(void*)*27);
v_manifestFile_3714_ = lean_ctor_get(v_cfg_3711_, 2);
v_extraDepTargets_3715_ = lean_ctor_get(v_cfg_3711_, 3);
v_precompileModules_3716_ = lean_ctor_get_uint8(v_cfg_3711_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3717_ = lean_ctor_get(v_cfg_3711_, 4);
v_srcDir_3718_ = lean_ctor_get(v_cfg_3711_, 5);
v_buildDir_3719_ = lean_ctor_get(v_cfg_3711_, 6);
v_leanLibDir_3720_ = lean_ctor_get(v_cfg_3711_, 7);
v_nativeLibDir_3721_ = lean_ctor_get(v_cfg_3711_, 8);
v_binDir_3722_ = lean_ctor_get(v_cfg_3711_, 9);
v_irDir_3723_ = lean_ctor_get(v_cfg_3711_, 10);
v_releaseRepo_3724_ = lean_ctor_get(v_cfg_3711_, 11);
v_buildArchive_3725_ = lean_ctor_get(v_cfg_3711_, 12);
v_preferReleaseBuild_3726_ = lean_ctor_get_uint8(v_cfg_3711_, sizeof(void*)*27 + 2);
v_testDriver_3727_ = lean_ctor_get(v_cfg_3711_, 13);
v_testDriverArgs_3728_ = lean_ctor_get(v_cfg_3711_, 14);
v_lintDriver_3729_ = lean_ctor_get(v_cfg_3711_, 15);
v_lintDriverArgs_3730_ = lean_ctor_get(v_cfg_3711_, 16);
v_version_3731_ = lean_ctor_get(v_cfg_3711_, 17);
v_versionTags_3732_ = lean_ctor_get(v_cfg_3711_, 18);
v_description_3733_ = lean_ctor_get(v_cfg_3711_, 19);
v_keywords_3734_ = lean_ctor_get(v_cfg_3711_, 20);
v_homepage_3735_ = lean_ctor_get(v_cfg_3711_, 21);
v_license_3736_ = lean_ctor_get(v_cfg_3711_, 22);
v_licenseFiles_3737_ = lean_ctor_get(v_cfg_3711_, 23);
v_readmeFile_3738_ = lean_ctor_get(v_cfg_3711_, 24);
v_reservoir_3739_ = lean_ctor_get_uint8(v_cfg_3711_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3740_ = lean_ctor_get(v_cfg_3711_, 25);
v_restoreAllArtifacts_x3f_3741_ = lean_ctor_get(v_cfg_3711_, 26);
v_libPrefixOnWindows_3742_ = lean_ctor_get_uint8(v_cfg_3711_, sizeof(void*)*27 + 4);
v_allowImportAll_3743_ = lean_ctor_get_uint8(v_cfg_3711_, sizeof(void*)*27 + 5);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_cfg_3711_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; 
v_unused_3751_ = lean_ctor_get(v_cfg_3711_, 1);
lean_dec(v_unused_3751_);
v___x_3745_ = v_cfg_3711_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3741_);
lean_inc(v_enableArtifactCache_x3f_3740_);
lean_inc(v_readmeFile_3738_);
lean_inc(v_licenseFiles_3737_);
lean_inc(v_license_3736_);
lean_inc(v_homepage_3735_);
lean_inc(v_keywords_3734_);
lean_inc(v_description_3733_);
lean_inc(v_versionTags_3732_);
lean_inc(v_version_3731_);
lean_inc(v_lintDriverArgs_3730_);
lean_inc(v_lintDriver_3729_);
lean_inc(v_testDriverArgs_3728_);
lean_inc(v_testDriver_3727_);
lean_inc(v_buildArchive_3725_);
lean_inc(v_releaseRepo_3724_);
lean_inc(v_irDir_3723_);
lean_inc(v_binDir_3722_);
lean_inc(v_nativeLibDir_3721_);
lean_inc(v_leanLibDir_3720_);
lean_inc(v_buildDir_3719_);
lean_inc(v_srcDir_3718_);
lean_inc(v_moreGlobalServerArgs_3717_);
lean_inc(v_extraDepTargets_3715_);
lean_inc(v_manifestFile_3714_);
lean_inc(v_toWorkspaceConfig_3712_);
lean_dec(v_cfg_3711_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 1, v_val_3710_);
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_toWorkspaceConfig_3712_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_val_3710_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_manifestFile_3714_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v_extraDepTargets_3715_);
lean_ctor_set(v_reuseFailAlloc_3749_, 4, v_moreGlobalServerArgs_3717_);
lean_ctor_set(v_reuseFailAlloc_3749_, 5, v_srcDir_3718_);
lean_ctor_set(v_reuseFailAlloc_3749_, 6, v_buildDir_3719_);
lean_ctor_set(v_reuseFailAlloc_3749_, 7, v_leanLibDir_3720_);
lean_ctor_set(v_reuseFailAlloc_3749_, 8, v_nativeLibDir_3721_);
lean_ctor_set(v_reuseFailAlloc_3749_, 9, v_binDir_3722_);
lean_ctor_set(v_reuseFailAlloc_3749_, 10, v_irDir_3723_);
lean_ctor_set(v_reuseFailAlloc_3749_, 11, v_releaseRepo_3724_);
lean_ctor_set(v_reuseFailAlloc_3749_, 12, v_buildArchive_3725_);
lean_ctor_set(v_reuseFailAlloc_3749_, 13, v_testDriver_3727_);
lean_ctor_set(v_reuseFailAlloc_3749_, 14, v_testDriverArgs_3728_);
lean_ctor_set(v_reuseFailAlloc_3749_, 15, v_lintDriver_3729_);
lean_ctor_set(v_reuseFailAlloc_3749_, 16, v_lintDriverArgs_3730_);
lean_ctor_set(v_reuseFailAlloc_3749_, 17, v_version_3731_);
lean_ctor_set(v_reuseFailAlloc_3749_, 18, v_versionTags_3732_);
lean_ctor_set(v_reuseFailAlloc_3749_, 19, v_description_3733_);
lean_ctor_set(v_reuseFailAlloc_3749_, 20, v_keywords_3734_);
lean_ctor_set(v_reuseFailAlloc_3749_, 21, v_homepage_3735_);
lean_ctor_set(v_reuseFailAlloc_3749_, 22, v_license_3736_);
lean_ctor_set(v_reuseFailAlloc_3749_, 23, v_licenseFiles_3737_);
lean_ctor_set(v_reuseFailAlloc_3749_, 24, v_readmeFile_3738_);
lean_ctor_set(v_reuseFailAlloc_3749_, 25, v_enableArtifactCache_x3f_3740_);
lean_ctor_set(v_reuseFailAlloc_3749_, 26, v_restoreAllArtifacts_x3f_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3749_, sizeof(void*)*27, v_bootstrap_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3749_, sizeof(void*)*27 + 1, v_precompileModules_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3749_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3749_, sizeof(void*)*27 + 3, v_reservoir_3739_);
lean_ctor_set_uint8(v_reuseFailAlloc_3749_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3742_);
lean_ctor_set_uint8(v_reuseFailAlloc_3749_, sizeof(void*)*27 + 5, v_allowImportAll_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* v_f_3752_, lean_object* v_cfg_3753_){
_start:
{
lean_object* v_toWorkspaceConfig_3754_; lean_object* v_toLeanConfig_3755_; uint8_t v_bootstrap_3756_; lean_object* v_manifestFile_3757_; lean_object* v_extraDepTargets_3758_; uint8_t v_precompileModules_3759_; lean_object* v_moreGlobalServerArgs_3760_; lean_object* v_srcDir_3761_; lean_object* v_buildDir_3762_; lean_object* v_leanLibDir_3763_; lean_object* v_nativeLibDir_3764_; lean_object* v_binDir_3765_; lean_object* v_irDir_3766_; lean_object* v_releaseRepo_3767_; lean_object* v_buildArchive_3768_; uint8_t v_preferReleaseBuild_3769_; lean_object* v_testDriver_3770_; lean_object* v_testDriverArgs_3771_; lean_object* v_lintDriver_3772_; lean_object* v_lintDriverArgs_3773_; lean_object* v_version_3774_; lean_object* v_versionTags_3775_; lean_object* v_description_3776_; lean_object* v_keywords_3777_; lean_object* v_homepage_3778_; lean_object* v_license_3779_; lean_object* v_licenseFiles_3780_; lean_object* v_readmeFile_3781_; uint8_t v_reservoir_3782_; lean_object* v_enableArtifactCache_x3f_3783_; lean_object* v_restoreAllArtifacts_x3f_3784_; uint8_t v_libPrefixOnWindows_3785_; uint8_t v_allowImportAll_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3794_; 
v_toWorkspaceConfig_3754_ = lean_ctor_get(v_cfg_3753_, 0);
v_toLeanConfig_3755_ = lean_ctor_get(v_cfg_3753_, 1);
v_bootstrap_3756_ = lean_ctor_get_uint8(v_cfg_3753_, sizeof(void*)*27);
v_manifestFile_3757_ = lean_ctor_get(v_cfg_3753_, 2);
v_extraDepTargets_3758_ = lean_ctor_get(v_cfg_3753_, 3);
v_precompileModules_3759_ = lean_ctor_get_uint8(v_cfg_3753_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3760_ = lean_ctor_get(v_cfg_3753_, 4);
v_srcDir_3761_ = lean_ctor_get(v_cfg_3753_, 5);
v_buildDir_3762_ = lean_ctor_get(v_cfg_3753_, 6);
v_leanLibDir_3763_ = lean_ctor_get(v_cfg_3753_, 7);
v_nativeLibDir_3764_ = lean_ctor_get(v_cfg_3753_, 8);
v_binDir_3765_ = lean_ctor_get(v_cfg_3753_, 9);
v_irDir_3766_ = lean_ctor_get(v_cfg_3753_, 10);
v_releaseRepo_3767_ = lean_ctor_get(v_cfg_3753_, 11);
v_buildArchive_3768_ = lean_ctor_get(v_cfg_3753_, 12);
v_preferReleaseBuild_3769_ = lean_ctor_get_uint8(v_cfg_3753_, sizeof(void*)*27 + 2);
v_testDriver_3770_ = lean_ctor_get(v_cfg_3753_, 13);
v_testDriverArgs_3771_ = lean_ctor_get(v_cfg_3753_, 14);
v_lintDriver_3772_ = lean_ctor_get(v_cfg_3753_, 15);
v_lintDriverArgs_3773_ = lean_ctor_get(v_cfg_3753_, 16);
v_version_3774_ = lean_ctor_get(v_cfg_3753_, 17);
v_versionTags_3775_ = lean_ctor_get(v_cfg_3753_, 18);
v_description_3776_ = lean_ctor_get(v_cfg_3753_, 19);
v_keywords_3777_ = lean_ctor_get(v_cfg_3753_, 20);
v_homepage_3778_ = lean_ctor_get(v_cfg_3753_, 21);
v_license_3779_ = lean_ctor_get(v_cfg_3753_, 22);
v_licenseFiles_3780_ = lean_ctor_get(v_cfg_3753_, 23);
v_readmeFile_3781_ = lean_ctor_get(v_cfg_3753_, 24);
v_reservoir_3782_ = lean_ctor_get_uint8(v_cfg_3753_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3783_ = lean_ctor_get(v_cfg_3753_, 25);
v_restoreAllArtifacts_x3f_3784_ = lean_ctor_get(v_cfg_3753_, 26);
v_libPrefixOnWindows_3785_ = lean_ctor_get_uint8(v_cfg_3753_, sizeof(void*)*27 + 4);
v_allowImportAll_3786_ = lean_ctor_get_uint8(v_cfg_3753_, sizeof(void*)*27 + 5);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_cfg_3753_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3788_ = v_cfg_3753_;
v_isShared_3789_ = v_isSharedCheck_3794_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3784_);
lean_inc(v_enableArtifactCache_x3f_3783_);
lean_inc(v_readmeFile_3781_);
lean_inc(v_licenseFiles_3780_);
lean_inc(v_license_3779_);
lean_inc(v_homepage_3778_);
lean_inc(v_keywords_3777_);
lean_inc(v_description_3776_);
lean_inc(v_versionTags_3775_);
lean_inc(v_version_3774_);
lean_inc(v_lintDriverArgs_3773_);
lean_inc(v_lintDriver_3772_);
lean_inc(v_testDriverArgs_3771_);
lean_inc(v_testDriver_3770_);
lean_inc(v_buildArchive_3768_);
lean_inc(v_releaseRepo_3767_);
lean_inc(v_irDir_3766_);
lean_inc(v_binDir_3765_);
lean_inc(v_nativeLibDir_3764_);
lean_inc(v_leanLibDir_3763_);
lean_inc(v_buildDir_3762_);
lean_inc(v_srcDir_3761_);
lean_inc(v_moreGlobalServerArgs_3760_);
lean_inc(v_extraDepTargets_3758_);
lean_inc(v_manifestFile_3757_);
lean_inc(v_toLeanConfig_3755_);
lean_inc(v_toWorkspaceConfig_3754_);
lean_dec(v_cfg_3753_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3794_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = lean_apply_1(v_f_3752_, v_toLeanConfig_3755_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___x_3790_);
v___x_3792_ = v___x_3788_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_toWorkspaceConfig_3754_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_manifestFile_3757_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_extraDepTargets_3758_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v_moreGlobalServerArgs_3760_);
lean_ctor_set(v_reuseFailAlloc_3793_, 5, v_srcDir_3761_);
lean_ctor_set(v_reuseFailAlloc_3793_, 6, v_buildDir_3762_);
lean_ctor_set(v_reuseFailAlloc_3793_, 7, v_leanLibDir_3763_);
lean_ctor_set(v_reuseFailAlloc_3793_, 8, v_nativeLibDir_3764_);
lean_ctor_set(v_reuseFailAlloc_3793_, 9, v_binDir_3765_);
lean_ctor_set(v_reuseFailAlloc_3793_, 10, v_irDir_3766_);
lean_ctor_set(v_reuseFailAlloc_3793_, 11, v_releaseRepo_3767_);
lean_ctor_set(v_reuseFailAlloc_3793_, 12, v_buildArchive_3768_);
lean_ctor_set(v_reuseFailAlloc_3793_, 13, v_testDriver_3770_);
lean_ctor_set(v_reuseFailAlloc_3793_, 14, v_testDriverArgs_3771_);
lean_ctor_set(v_reuseFailAlloc_3793_, 15, v_lintDriver_3772_);
lean_ctor_set(v_reuseFailAlloc_3793_, 16, v_lintDriverArgs_3773_);
lean_ctor_set(v_reuseFailAlloc_3793_, 17, v_version_3774_);
lean_ctor_set(v_reuseFailAlloc_3793_, 18, v_versionTags_3775_);
lean_ctor_set(v_reuseFailAlloc_3793_, 19, v_description_3776_);
lean_ctor_set(v_reuseFailAlloc_3793_, 20, v_keywords_3777_);
lean_ctor_set(v_reuseFailAlloc_3793_, 21, v_homepage_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 22, v_license_3779_);
lean_ctor_set(v_reuseFailAlloc_3793_, 23, v_licenseFiles_3780_);
lean_ctor_set(v_reuseFailAlloc_3793_, 24, v_readmeFile_3781_);
lean_ctor_set(v_reuseFailAlloc_3793_, 25, v_enableArtifactCache_x3f_3783_);
lean_ctor_set(v_reuseFailAlloc_3793_, 26, v_restoreAllArtifacts_x3f_3784_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*27, v_bootstrap_3756_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*27 + 1, v_precompileModules_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*27 + 3, v_reservoir_3782_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3785_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*27 + 5, v_allowImportAll_3786_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
static lean_object* _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1(void){
_start:
{
lean_object* v___x_3797_; uint8_t v___x_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; 
v___x_3797_ = lean_box(0);
v___x_3798_ = 2;
v___x_3799_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_3800_ = 3;
v___x_3801_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3799_);
lean_ctor_set(v___x_3801_, 2, v___x_3799_);
lean_ctor_set(v___x_3801_, 3, v___x_3799_);
lean_ctor_set(v___x_3801_, 4, v___x_3799_);
lean_ctor_set(v___x_3801_, 5, v___x_3799_);
lean_ctor_set(v___x_3801_, 6, v___x_3799_);
lean_ctor_set(v___x_3801_, 7, v___x_3799_);
lean_ctor_set(v___x_3801_, 8, v___x_3799_);
lean_ctor_set(v___x_3801_, 9, v___x_3799_);
lean_ctor_set(v___x_3801_, 10, v___x_3797_);
lean_ctor_set(v___x_3801_, 11, v___x_3799_);
lean_ctor_set(v___x_3801_, 12, v___x_3799_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*13, v___x_3800_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*13 + 1, v___x_3798_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* v_x_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1, &l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__3(v_x_3804_);
lean_dec_ref(v_x_3804_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_3815_, lean_object* v_n_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___closed__4));
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_3818_, lean_object* v_n_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_3818_, v_n_3819_);
lean_dec(v_n_3819_);
lean_dec(v_p_3818_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_3821_, lean_object* v_n_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_3821_, v_n_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_3824_, lean_object* v_n_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_3824_, v_n_3825_);
lean_dec(v_n_3825_);
lean_dec(v_p_3824_);
return v_res_3826_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__3(void){
_start:
{
uint8_t v___x_3832_; uint8_t v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3832_ = 0;
v___x_3833_ = 1;
v___x_3834_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__2));
v___x_3835_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
lean_ctor_set_uint8(v___x_3835_, sizeof(void*)*2, v___x_3833_);
lean_ctor_set_uint8(v___x_3835_, sizeof(void*)*2 + 1, v___x_3832_);
return v___x_3835_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__3, &l_Lake_PackageConfig___fields___closed__3_once, _init_l_Lake_PackageConfig___fields___closed__3);
v___x_3837_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_3838_ = lean_array_push(v___x_3837_, v___x_3836_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__7(void){
_start:
{
uint8_t v___x_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3842_ = 0;
v___x_3843_ = 1;
v___x_3844_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__6));
v___x_3845_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*2, v___x_3843_);
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*2 + 1, v___x_3842_);
return v___x_3845_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__7, &l_Lake_PackageConfig___fields___closed__7_once, _init_l_Lake_PackageConfig___fields___closed__7);
v___x_3847_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_3848_ = lean_array_push(v___x_3847_, v___x_3846_);
return v___x_3848_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__11(void){
_start:
{
uint8_t v___x_3852_; uint8_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3852_ = 0;
v___x_3853_ = 1;
v___x_3854_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__10));
v___x_3855_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*2, v___x_3853_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*2 + 1, v___x_3852_);
return v___x_3855_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__11, &l_Lake_PackageConfig___fields___closed__11_once, _init_l_Lake_PackageConfig___fields___closed__11);
v___x_3857_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_3858_ = lean_array_push(v___x_3857_, v___x_3856_);
return v___x_3858_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__15(void){
_start:
{
uint8_t v___x_3862_; uint8_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3862_ = 0;
v___x_3863_ = 1;
v___x_3864_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__14));
v___x_3865_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*2, v___x_3863_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*2 + 1, v___x_3862_);
return v___x_3865_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__15, &l_Lake_PackageConfig___fields___closed__15_once, _init_l_Lake_PackageConfig___fields___closed__15);
v___x_3867_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_3868_ = lean_array_push(v___x_3867_, v___x_3866_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__19(void){
_start:
{
uint8_t v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3872_ = 0;
v___x_3873_ = 1;
v___x_3874_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__18));
v___x_3875_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*2, v___x_3873_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*2 + 1, v___x_3872_);
return v___x_3875_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__19, &l_Lake_PackageConfig___fields___closed__19_once, _init_l_Lake_PackageConfig___fields___closed__19);
v___x_3877_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_3878_ = lean_array_push(v___x_3877_, v___x_3876_);
return v___x_3878_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_3887_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_3888_ = lean_array_push(v___x_3887_, v___x_3886_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__27(void){
_start:
{
uint8_t v___x_3892_; uint8_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3892_ = 0;
v___x_3893_ = 1;
v___x_3894_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__26));
v___x_3895_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
lean_ctor_set_uint8(v___x_3895_, sizeof(void*)*2, v___x_3893_);
lean_ctor_set_uint8(v___x_3895_, sizeof(void*)*2 + 1, v___x_3892_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__27, &l_Lake_PackageConfig___fields___closed__27_once, _init_l_Lake_PackageConfig___fields___closed__27);
v___x_3897_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_3898_ = lean_array_push(v___x_3897_, v___x_3896_);
return v___x_3898_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__31(void){
_start:
{
uint8_t v___x_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3902_ = 0;
v___x_3903_ = 1;
v___x_3904_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__30));
v___x_3905_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
lean_ctor_set_uint8(v___x_3905_, sizeof(void*)*2, v___x_3903_);
lean_ctor_set_uint8(v___x_3905_, sizeof(void*)*2 + 1, v___x_3902_);
return v___x_3905_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3906_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__31, &l_Lake_PackageConfig___fields___closed__31_once, _init_l_Lake_PackageConfig___fields___closed__31);
v___x_3907_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_3908_ = lean_array_push(v___x_3907_, v___x_3906_);
return v___x_3908_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__35(void){
_start:
{
uint8_t v___x_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3912_ = 0;
v___x_3913_ = 1;
v___x_3914_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__34));
v___x_3915_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
lean_ctor_set_uint8(v___x_3915_, sizeof(void*)*2, v___x_3913_);
lean_ctor_set_uint8(v___x_3915_, sizeof(void*)*2 + 1, v___x_3912_);
return v___x_3915_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__35, &l_Lake_PackageConfig___fields___closed__35_once, _init_l_Lake_PackageConfig___fields___closed__35);
v___x_3917_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_3918_ = lean_array_push(v___x_3917_, v___x_3916_);
return v___x_3918_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__39(void){
_start:
{
uint8_t v___x_3922_; uint8_t v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3922_ = 0;
v___x_3923_ = 1;
v___x_3924_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__38));
v___x_3925_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*2, v___x_3923_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*2 + 1, v___x_3922_);
return v___x_3925_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__39, &l_Lake_PackageConfig___fields___closed__39_once, _init_l_Lake_PackageConfig___fields___closed__39);
v___x_3927_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_3928_ = lean_array_push(v___x_3927_, v___x_3926_);
return v___x_3928_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__43(void){
_start:
{
uint8_t v___x_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3932_ = 0;
v___x_3933_ = 1;
v___x_3934_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__42));
v___x_3935_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*2, v___x_3933_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*2 + 1, v___x_3932_);
return v___x_3935_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__43, &l_Lake_PackageConfig___fields___closed__43_once, _init_l_Lake_PackageConfig___fields___closed__43);
v___x_3937_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_3938_ = lean_array_push(v___x_3937_, v___x_3936_);
return v___x_3938_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__47(void){
_start:
{
uint8_t v___x_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3942_ = 0;
v___x_3943_ = 1;
v___x_3944_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__46));
v___x_3945_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
lean_ctor_set_uint8(v___x_3945_, sizeof(void*)*2, v___x_3943_);
lean_ctor_set_uint8(v___x_3945_, sizeof(void*)*2 + 1, v___x_3942_);
return v___x_3945_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3946_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__47, &l_Lake_PackageConfig___fields___closed__47_once, _init_l_Lake_PackageConfig___fields___closed__47);
v___x_3947_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_3948_ = lean_array_push(v___x_3947_, v___x_3946_);
return v___x_3948_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__51(void){
_start:
{
uint8_t v___x_3952_; uint8_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3952_ = 0;
v___x_3953_ = 1;
v___x_3954_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__50));
v___x_3955_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
lean_ctor_set_uint8(v___x_3955_, sizeof(void*)*2, v___x_3953_);
lean_ctor_set_uint8(v___x_3955_, sizeof(void*)*2 + 1, v___x_3952_);
return v___x_3955_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__51, &l_Lake_PackageConfig___fields___closed__51_once, _init_l_Lake_PackageConfig___fields___closed__51);
v___x_3957_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_3958_ = lean_array_push(v___x_3957_, v___x_3956_);
return v___x_3958_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_3967_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_3968_ = lean_array_push(v___x_3967_, v___x_3966_);
return v___x_3968_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__59(void){
_start:
{
uint8_t v___x_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3972_ = 0;
v___x_3973_ = 1;
v___x_3974_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__58));
v___x_3975_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
lean_ctor_set_uint8(v___x_3975_, sizeof(void*)*2, v___x_3973_);
lean_ctor_set_uint8(v___x_3975_, sizeof(void*)*2 + 1, v___x_3972_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__59, &l_Lake_PackageConfig___fields___closed__59_once, _init_l_Lake_PackageConfig___fields___closed__59);
v___x_3977_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_3978_ = lean_array_push(v___x_3977_, v___x_3976_);
return v___x_3978_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_3987_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_3988_ = lean_array_push(v___x_3987_, v___x_3986_);
return v___x_3988_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__67(void){
_start:
{
uint8_t v___x_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3992_ = 0;
v___x_3993_ = 1;
v___x_3994_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__66));
v___x_3995_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*2, v___x_3993_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*2 + 1, v___x_3992_);
return v___x_3995_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__67, &l_Lake_PackageConfig___fields___closed__67_once, _init_l_Lake_PackageConfig___fields___closed__67);
v___x_3997_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_3998_ = lean_array_push(v___x_3997_, v___x_3996_);
return v___x_3998_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__71(void){
_start:
{
uint8_t v___x_4002_; uint8_t v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4002_ = 0;
v___x_4003_ = 1;
v___x_4004_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__70));
v___x_4005_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
lean_ctor_set_uint8(v___x_4005_, sizeof(void*)*2, v___x_4003_);
lean_ctor_set_uint8(v___x_4005_, sizeof(void*)*2 + 1, v___x_4002_);
return v___x_4005_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__71, &l_Lake_PackageConfig___fields___closed__71_once, _init_l_Lake_PackageConfig___fields___closed__71);
v___x_4007_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4008_ = lean_array_push(v___x_4007_, v___x_4006_);
return v___x_4008_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4017_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4018_ = lean_array_push(v___x_4017_, v___x_4016_);
return v___x_4018_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__79(void){
_start:
{
uint8_t v___x_4022_; uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4022_ = 0;
v___x_4023_ = 1;
v___x_4024_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__78));
v___x_4025_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*2, v___x_4023_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*2 + 1, v___x_4022_);
return v___x_4025_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__79, &l_Lake_PackageConfig___fields___closed__79_once, _init_l_Lake_PackageConfig___fields___closed__79);
v___x_4027_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4028_ = lean_array_push(v___x_4027_, v___x_4026_);
return v___x_4028_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__83(void){
_start:
{
uint8_t v___x_4032_; uint8_t v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4032_ = 0;
v___x_4033_ = 1;
v___x_4034_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__82));
v___x_4035_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
lean_ctor_set_uint8(v___x_4035_, sizeof(void*)*2, v___x_4033_);
lean_ctor_set_uint8(v___x_4035_, sizeof(void*)*2 + 1, v___x_4032_);
return v___x_4035_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4036_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__83, &l_Lake_PackageConfig___fields___closed__83_once, _init_l_Lake_PackageConfig___fields___closed__83);
v___x_4037_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4038_ = lean_array_push(v___x_4037_, v___x_4036_);
return v___x_4038_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__87(void){
_start:
{
uint8_t v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4042_ = 0;
v___x_4043_ = 1;
v___x_4044_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__86));
v___x_4045_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
lean_ctor_set_uint8(v___x_4045_, sizeof(void*)*2, v___x_4043_);
lean_ctor_set_uint8(v___x_4045_, sizeof(void*)*2 + 1, v___x_4042_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__87, &l_Lake_PackageConfig___fields___closed__87_once, _init_l_Lake_PackageConfig___fields___closed__87);
v___x_4047_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4048_ = lean_array_push(v___x_4047_, v___x_4046_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__91(void){
_start:
{
uint8_t v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4052_ = 0;
v___x_4053_ = 1;
v___x_4054_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__90));
v___x_4055_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
lean_ctor_set_uint8(v___x_4055_, sizeof(void*)*2, v___x_4053_);
lean_ctor_set_uint8(v___x_4055_, sizeof(void*)*2 + 1, v___x_4052_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__91, &l_Lake_PackageConfig___fields___closed__91_once, _init_l_Lake_PackageConfig___fields___closed__91);
v___x_4057_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4058_ = lean_array_push(v___x_4057_, v___x_4056_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__95(void){
_start:
{
uint8_t v___x_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4062_ = 0;
v___x_4063_ = 1;
v___x_4064_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__94));
v___x_4065_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
lean_ctor_set_uint8(v___x_4065_, sizeof(void*)*2, v___x_4063_);
lean_ctor_set_uint8(v___x_4065_, sizeof(void*)*2 + 1, v___x_4062_);
return v___x_4065_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__95, &l_Lake_PackageConfig___fields___closed__95_once, _init_l_Lake_PackageConfig___fields___closed__95);
v___x_4067_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4068_ = lean_array_push(v___x_4067_, v___x_4066_);
return v___x_4068_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__99(void){
_start:
{
uint8_t v___x_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4072_ = 0;
v___x_4073_ = 1;
v___x_4074_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__98));
v___x_4075_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
lean_ctor_set_uint8(v___x_4075_, sizeof(void*)*2, v___x_4073_);
lean_ctor_set_uint8(v___x_4075_, sizeof(void*)*2 + 1, v___x_4072_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__99, &l_Lake_PackageConfig___fields___closed__99_once, _init_l_Lake_PackageConfig___fields___closed__99);
v___x_4077_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4078_ = lean_array_push(v___x_4077_, v___x_4076_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__103(void){
_start:
{
uint8_t v___x_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4082_ = 0;
v___x_4083_ = 1;
v___x_4084_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__102));
v___x_4085_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
lean_ctor_set_uint8(v___x_4085_, sizeof(void*)*2, v___x_4083_);
lean_ctor_set_uint8(v___x_4085_, sizeof(void*)*2 + 1, v___x_4082_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__103, &l_Lake_PackageConfig___fields___closed__103_once, _init_l_Lake_PackageConfig___fields___closed__103);
v___x_4087_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4088_ = lean_array_push(v___x_4087_, v___x_4086_);
return v___x_4088_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__107(void){
_start:
{
uint8_t v___x_4092_; uint8_t v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4092_ = 0;
v___x_4093_ = 1;
v___x_4094_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__106));
v___x_4095_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*2, v___x_4093_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*2 + 1, v___x_4092_);
return v___x_4095_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__107, &l_Lake_PackageConfig___fields___closed__107_once, _init_l_Lake_PackageConfig___fields___closed__107);
v___x_4097_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4098_ = lean_array_push(v___x_4097_, v___x_4096_);
return v___x_4098_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__111(void){
_start:
{
uint8_t v___x_4102_; uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4102_ = 0;
v___x_4103_ = 1;
v___x_4104_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__110));
v___x_4105_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
lean_ctor_set_uint8(v___x_4105_, sizeof(void*)*2, v___x_4103_);
lean_ctor_set_uint8(v___x_4105_, sizeof(void*)*2 + 1, v___x_4102_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__111, &l_Lake_PackageConfig___fields___closed__111_once, _init_l_Lake_PackageConfig___fields___closed__111);
v___x_4107_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4108_ = lean_array_push(v___x_4107_, v___x_4106_);
return v___x_4108_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__115(void){
_start:
{
uint8_t v___x_4112_; uint8_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4112_ = 0;
v___x_4113_ = 1;
v___x_4114_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__114));
v___x_4115_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
lean_ctor_set_uint8(v___x_4115_, sizeof(void*)*2, v___x_4113_);
lean_ctor_set_uint8(v___x_4115_, sizeof(void*)*2 + 1, v___x_4112_);
return v___x_4115_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__115, &l_Lake_PackageConfig___fields___closed__115_once, _init_l_Lake_PackageConfig___fields___closed__115);
v___x_4117_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4118_ = lean_array_push(v___x_4117_, v___x_4116_);
return v___x_4118_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__119(void){
_start:
{
uint8_t v___x_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4122_ = 0;
v___x_4123_ = 1;
v___x_4124_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__118));
v___x_4125_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*2, v___x_4123_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*2 + 1, v___x_4122_);
return v___x_4125_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4126_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__119, &l_Lake_PackageConfig___fields___closed__119_once, _init_l_Lake_PackageConfig___fields___closed__119);
v___x_4127_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4128_ = lean_array_push(v___x_4127_, v___x_4126_);
return v___x_4128_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__123(void){
_start:
{
uint8_t v___x_4132_; uint8_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4132_ = 0;
v___x_4133_ = 1;
v___x_4134_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__122));
v___x_4135_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
lean_ctor_set_uint8(v___x_4135_, sizeof(void*)*2, v___x_4133_);
lean_ctor_set_uint8(v___x_4135_, sizeof(void*)*2 + 1, v___x_4132_);
return v___x_4135_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__123, &l_Lake_PackageConfig___fields___closed__123_once, _init_l_Lake_PackageConfig___fields___closed__123);
v___x_4137_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4138_ = lean_array_push(v___x_4137_, v___x_4136_);
return v___x_4138_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__127(void){
_start:
{
uint8_t v___x_4142_; uint8_t v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4142_ = 0;
v___x_4143_ = 1;
v___x_4144_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__126));
v___x_4145_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
lean_ctor_set_uint8(v___x_4145_, sizeof(void*)*2, v___x_4143_);
lean_ctor_set_uint8(v___x_4145_, sizeof(void*)*2 + 1, v___x_4142_);
return v___x_4145_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__127, &l_Lake_PackageConfig___fields___closed__127_once, _init_l_Lake_PackageConfig___fields___closed__127);
v___x_4147_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4148_ = lean_array_push(v___x_4147_, v___x_4146_);
return v___x_4148_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4156_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4157_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4158_ = lean_array_push(v___x_4157_, v___x_4156_);
return v___x_4158_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__135(void){
_start:
{
uint8_t v___x_4162_; uint8_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4162_ = 0;
v___x_4163_ = 1;
v___x_4164_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__134));
v___x_4165_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
lean_ctor_set_uint8(v___x_4165_, sizeof(void*)*2, v___x_4163_);
lean_ctor_set_uint8(v___x_4165_, sizeof(void*)*2 + 1, v___x_4162_);
return v___x_4165_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__135, &l_Lake_PackageConfig___fields___closed__135_once, _init_l_Lake_PackageConfig___fields___closed__135);
v___x_4167_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4168_ = lean_array_push(v___x_4167_, v___x_4166_);
return v___x_4168_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4176_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_4177_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_4178_ = lean_array_push(v___x_4177_, v___x_4176_);
return v___x_4178_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__143(void){
_start:
{
uint8_t v___x_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4182_ = 0;
v___x_4183_ = 1;
v___x_4184_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__142));
v___x_4185_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
lean_ctor_set_uint8(v___x_4185_, sizeof(void*)*2, v___x_4183_);
lean_ctor_set_uint8(v___x_4185_, sizeof(void*)*2 + 1, v___x_4182_);
return v___x_4185_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4186_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__143, &l_Lake_PackageConfig___fields___closed__143_once, _init_l_Lake_PackageConfig___fields___closed__143);
v___x_4187_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_4188_ = lean_array_push(v___x_4187_, v___x_4186_);
return v___x_4188_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__147(void){
_start:
{
uint8_t v___x_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4192_ = 0;
v___x_4193_ = 1;
v___x_4194_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__146));
v___x_4195_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
lean_ctor_set_uint8(v___x_4195_, sizeof(void*)*2, v___x_4193_);
lean_ctor_set_uint8(v___x_4195_, sizeof(void*)*2 + 1, v___x_4192_);
return v___x_4195_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4196_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__147, &l_Lake_PackageConfig___fields___closed__147_once, _init_l_Lake_PackageConfig___fields___closed__147);
v___x_4197_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_4198_ = lean_array_push(v___x_4197_, v___x_4196_);
return v___x_4198_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__149(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = l_Lake_WorkspaceConfig___fields;
v___x_4200_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_4201_ = l_Array_append___redArg(v___x_4200_, v___x_4199_);
return v___x_4201_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__152(void){
_start:
{
uint8_t v___x_4205_; uint8_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4205_ = 1;
v___x_4206_ = 0;
v___x_4207_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__151));
v___x_4208_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
lean_ctor_set_uint8(v___x_4208_, sizeof(void*)*2, v___x_4206_);
lean_ctor_set_uint8(v___x_4208_, sizeof(void*)*2 + 1, v___x_4205_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__153(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__152, &l_Lake_PackageConfig___fields___closed__152_once, _init_l_Lake_PackageConfig___fields___closed__152);
v___x_4210_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__149, &l_Lake_PackageConfig___fields___closed__149_once, _init_l_Lake_PackageConfig___fields___closed__149);
v___x_4211_ = lean_array_push(v___x_4210_, v___x_4209_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__154(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = l_Lake_LeanConfig___fields;
v___x_4213_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__153, &l_Lake_PackageConfig___fields___closed__153_once, _init_l_Lake_PackageConfig___fields___closed__153);
v___x_4214_ = l_Array_append___redArg(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__157(void){
_start:
{
uint8_t v___x_4218_; uint8_t v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4218_ = 1;
v___x_4219_ = 0;
v___x_4220_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__156));
v___x_4221_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
lean_ctor_set_uint8(v___x_4221_, sizeof(void*)*2, v___x_4219_);
lean_ctor_set_uint8(v___x_4221_, sizeof(void*)*2 + 1, v___x_4218_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__158(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4222_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__157, &l_Lake_PackageConfig___fields___closed__157_once, _init_l_Lake_PackageConfig___fields___closed__157);
v___x_4223_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__154, &l_Lake_PackageConfig___fields___closed__154_once, _init_l_Lake_PackageConfig___fields___closed__154);
v___x_4224_ = lean_array_push(v___x_4223_, v___x_4222_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__158, &l_Lake_PackageConfig___fields___closed__158_once, _init_l_Lake_PackageConfig___fields___closed__158);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_4226_, lean_object* v_n_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lake_PackageConfig___fields;
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_4229_, lean_object* v_n_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lake_PackageConfig_instConfigFields(v_p_4229_, v_n_4230_);
lean_dec(v_n_4230_);
lean_dec(v_p_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_4232_, lean_object* v_x2_4233_){
_start:
{
lean_object* v_name_4234_; lean_object* v___x_4235_; 
v_name_4234_ = lean_ctor_get(v_x2_4233_, 0);
lean_inc(v_name_4234_);
v___x_4235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_4234_, v_x2_4233_, v_x1_4232_);
return v___x_4235_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = l_Lake_PackageConfig___fields;
v___x_4237_ = lean_array_get_size(v___x_4236_);
return v___x_4237_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v___x_4257_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = lean_nat_dec_lt(v___x_4258_, v___x_4257_);
return v___x_4259_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4261_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4262_ = lean_nat_dec_le(v___x_4261_, v___x_4261_);
return v___x_4262_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_4263_; size_t v___x_4264_; 
v___x_4263_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4264_ = lean_usize_of_nat(v___x_4263_);
return v___x_4264_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_4265_; size_t v___x_4266_; size_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___f_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4265_ = lean_box(1);
v___x_4266_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_4267_ = ((size_t)0ULL);
v___x_4268_ = l_Lake_PackageConfig___fields;
v___f_4269_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_4270_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_4271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4270_, v___f_4269_, v___x_4268_, v___x_4267_, v___x_4266_, v___x_4265_);
return v___x_4271_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___y_4274_; lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4272_ = l_Lake_PackageConfig___fields;
v___x_4277_ = lean_box(1);
v___x_4278_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_4278_ == 0)
{
v___y_4274_ = v___x_4277_;
goto v___jp_4273_;
}
else
{
uint8_t v___x_4279_; 
v___x_4279_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_4279_ == 0)
{
if (v___x_4278_ == 0)
{
v___y_4274_ = v___x_4277_;
goto v___jp_4273_;
}
else
{
lean_object* v___x_4280_; 
v___x_4280_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4274_ = v___x_4280_;
goto v___jp_4273_;
}
}
else
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4274_ = v___x_4281_;
goto v___jp_4273_;
}
}
v___jp_4273_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4275_ = lean_unsigned_to_nat(2u);
v___x_4276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4272_);
lean_ctor_set(v___x_4276_, 1, v___y_4274_);
lean_ctor_set(v___x_4276_, 2, v___x_4275_);
return v___x_4276_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
uint8_t v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4282_ = 1;
v___x_4283_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___lam__3___closed__0));
v___x_4284_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___lam__3___closed__1));
v___x_4285_ = l_Lake_defaultVersionTags;
v___x_4286_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___lam__3___closed__1));
v___x_4287_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_4288_ = l_Lake_defaultIrDir;
v___x_4289_ = l_Lake_defaultBinDir;
v___x_4290_ = l_Lake_defaultNativeLibDir;
v___x_4291_ = l_Lake_defaultLeanLibDir;
v___x_4292_ = l_Lake_defaultBuildDir;
v___x_4293_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___lam__3___closed__0));
v___x_4294_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_4295_ = lean_box(0);
v___x_4296_ = 0;
v___x_4297_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1, &l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1);
v___x_4298_ = l_Lake_defaultPackagesDir;
v___x_4299_ = lean_alloc_ctor(0, 27, 6);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
lean_ctor_set(v___x_4299_, 1, v___x_4297_);
lean_ctor_set(v___x_4299_, 2, v___x_4295_);
lean_ctor_set(v___x_4299_, 3, v___x_4294_);
lean_ctor_set(v___x_4299_, 4, v___x_4294_);
lean_ctor_set(v___x_4299_, 5, v___x_4293_);
lean_ctor_set(v___x_4299_, 6, v___x_4292_);
lean_ctor_set(v___x_4299_, 7, v___x_4291_);
lean_ctor_set(v___x_4299_, 8, v___x_4290_);
lean_ctor_set(v___x_4299_, 9, v___x_4289_);
lean_ctor_set(v___x_4299_, 10, v___x_4288_);
lean_ctor_set(v___x_4299_, 11, v___x_4295_);
lean_ctor_set(v___x_4299_, 12, v___x_4295_);
lean_ctor_set(v___x_4299_, 13, v___x_4287_);
lean_ctor_set(v___x_4299_, 14, v___x_4294_);
lean_ctor_set(v___x_4299_, 15, v___x_4287_);
lean_ctor_set(v___x_4299_, 16, v___x_4294_);
lean_ctor_set(v___x_4299_, 17, v___x_4286_);
lean_ctor_set(v___x_4299_, 18, v___x_4285_);
lean_ctor_set(v___x_4299_, 19, v___x_4287_);
lean_ctor_set(v___x_4299_, 20, v___x_4294_);
lean_ctor_set(v___x_4299_, 21, v___x_4287_);
lean_ctor_set(v___x_4299_, 22, v___x_4287_);
lean_ctor_set(v___x_4299_, 23, v___x_4284_);
lean_ctor_set(v___x_4299_, 24, v___x_4283_);
lean_ctor_set(v___x_4299_, 25, v___x_4295_);
lean_ctor_set(v___x_4299_, 26, v___x_4295_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*27, v___x_4296_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*27 + 1, v___x_4296_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*27 + 2, v___x_4296_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*27 + 3, v___x_4282_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*27 + 4, v___x_4296_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*27 + 5, v___x_4296_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_4300_, lean_object* v_n_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_4303_, lean_object* v_n_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lake_PackageConfig_instEmptyCollection(v_p_4303_, v_n_4304_);
lean_dec(v_n_4304_);
lean_dec(v_p_4303_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_4306_){
_start:
{
lean_inc(v_n_4306_);
return v_n_4306_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Lake_PackageConfig_origName___redArg(v_n_4307_);
lean_dec(v_n_4307_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_4309_, lean_object* v_n_4310_, lean_object* v_x_4311_){
_start:
{
lean_inc(v_n_4310_);
return v_n_4310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_4312_, lean_object* v_n_4313_, lean_object* v_x_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lake_PackageConfig_origName(v_p_4312_, v_n_4313_, v_x_4314_);
lean_dec_ref(v_x_4314_);
lean_dec(v_n_4313_);
lean_dec(v_p_4312_);
return v_res_4315_;
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
