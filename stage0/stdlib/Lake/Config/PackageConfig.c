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
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanConfig___fields;
extern lean_object* l_Lake_WorkspaceConfig___fields;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__1_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__2_value;
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__3_value;
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__3_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__2_value)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__4 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__4_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LICENSE"};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__5 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__5_value;
static const lean_array_object l_Lake_instInhabitedPackageConfig_default___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__5_value)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__6 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__6_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___closed__7 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___closed__7_value;
static lean_once_cell_t l_Lake_instInhabitedPackageConfig_default___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__8;
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_builtinLint_x3f___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_builtinLint_x3f___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_builtinLint_x3f___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_builtinLint_x3f___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_builtinLint_x3f___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_PackageConfig___fields___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "builtinLint\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__145 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__145_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__145_value),LEAN_SCALAR_PTR_LITERAL(97, 5, 46, 89, 142, 210, 136, 240)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__146 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__146_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__147 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__147_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__148;
static const lean_string_object l_Lake_PackageConfig___fields___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "builtinLint"};
static const lean_object* l_Lake_PackageConfig___fields___closed__149 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__149_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__149_value),LEAN_SCALAR_PTR_LITERAL(188, 180, 184, 187, 78, 165, 206, 169)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__150 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__150_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__150_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__151 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__151_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__152_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__152;
static const lean_string_object l_Lake_PackageConfig___fields___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fixedToolchain"};
static const lean_object* l_Lake_PackageConfig___fields___closed__153 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__153_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__153_value),LEAN_SCALAR_PTR_LITERAL(248, 4, 88, 39, 97, 195, 130, 156)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__154 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__154_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__154_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__154_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__155 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__155_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__156;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__157;
static const lean_string_object l_Lake_PackageConfig___fields___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toWorkspaceConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__158 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__158_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__158_value),LEAN_SCALAR_PTR_LITERAL(135, 228, 155, 156, 156, 252, 46, 118)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__159 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__159_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__159_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__159_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__160 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__160_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__161_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__161;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__162_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__162;
static const lean_string_object l_Lake_PackageConfig___fields___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__163 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__163_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__163_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__164 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__164_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__164_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__164_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__165 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__165_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__166_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__166;
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
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PackageDecl"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value;
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(253, 117, 189, 141, 218, 132, 90, 198)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNamePackageDecl = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_18__value;
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object*);
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
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__8(void){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_27_ = 1;
v___x_28_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
v___x_29_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
v___x_30_ = l_Lake_defaultVersionTags;
v___x_31_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
v___x_32_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
v___x_33_ = lean_box(0);
v___x_34_ = l_Lake_defaultIrDir;
v___x_35_ = l_Lake_defaultBinDir;
v___x_36_ = l_Lake_defaultNativeLibDir;
v___x_37_ = l_Lake_defaultLeanLibDir;
v___x_38_ = l_Lake_defaultBuildDir;
v___x_39_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_40_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
v___x_41_ = 0;
v___x_42_ = l_Lake_instInhabitedLeanConfig_default;
v___x_43_ = l_Lake_defaultPackagesDir;
v___x_44_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_40_);
lean_ctor_set(v___x_44_, 3, v___x_40_);
lean_ctor_set(v___x_44_, 4, v___x_39_);
lean_ctor_set(v___x_44_, 5, v___x_38_);
lean_ctor_set(v___x_44_, 6, v___x_37_);
lean_ctor_set(v___x_44_, 7, v___x_36_);
lean_ctor_set(v___x_44_, 8, v___x_35_);
lean_ctor_set(v___x_44_, 9, v___x_34_);
lean_ctor_set(v___x_44_, 10, v___x_33_);
lean_ctor_set(v___x_44_, 11, v___x_33_);
lean_ctor_set(v___x_44_, 12, v___x_32_);
lean_ctor_set(v___x_44_, 13, v___x_40_);
lean_ctor_set(v___x_44_, 14, v___x_32_);
lean_ctor_set(v___x_44_, 15, v___x_40_);
lean_ctor_set(v___x_44_, 16, v___x_31_);
lean_ctor_set(v___x_44_, 17, v___x_30_);
lean_ctor_set(v___x_44_, 18, v___x_32_);
lean_ctor_set(v___x_44_, 19, v___x_40_);
lean_ctor_set(v___x_44_, 20, v___x_32_);
lean_ctor_set(v___x_44_, 21, v___x_32_);
lean_ctor_set(v___x_44_, 22, v___x_29_);
lean_ctor_set(v___x_44_, 23, v___x_28_);
lean_ctor_set(v___x_44_, 24, v___x_33_);
lean_ctor_set(v___x_44_, 25, v___x_33_);
lean_ctor_set(v___x_44_, 26, v___x_33_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27 + 1, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27 + 2, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27 + 3, v___x_27_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27 + 4, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27 + 5, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*27 + 6, v___x_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object* v_p_45_, lean_object* v_n_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__8, &l_Lake_instInhabitedPackageConfig_default___closed__8_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__8);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object* v_p_48_, lean_object* v_n_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_instInhabitedPackageConfig_default(v_p_48_, v_n_49_);
lean_dec(v_n_49_);
lean_dec(v_p_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lake_instInhabitedPackageConfig_default(v_a_51_, v_a_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_instInhabitedPackageConfig(v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec(v_a_54_);
return v_res_56_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__0(lean_object* v_cfg_57_){
_start:
{
uint8_t v_bootstrap_58_; 
v_bootstrap_58_ = lean_ctor_get_uint8(v_cfg_57_, sizeof(void*)*27);
return v_bootstrap_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__0___boxed(lean_object* v_cfg_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Lake_PackageConfig_bootstrap___proj___lam__0(v_cfg_59_);
lean_dec_ref(v_cfg_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1(uint8_t v_val_62_, lean_object* v_cfg_63_){
_start:
{
lean_object* v_toWorkspaceConfig_64_; lean_object* v_toLeanConfig_65_; lean_object* v_extraDepTargets_66_; uint8_t v_precompileModules_67_; lean_object* v_moreGlobalServerArgs_68_; lean_object* v_srcDir_69_; lean_object* v_buildDir_70_; lean_object* v_leanLibDir_71_; lean_object* v_nativeLibDir_72_; lean_object* v_binDir_73_; lean_object* v_irDir_74_; lean_object* v_releaseRepo_75_; lean_object* v_buildArchive_76_; uint8_t v_preferReleaseBuild_77_; lean_object* v_testDriver_78_; lean_object* v_testDriverArgs_79_; lean_object* v_lintDriver_80_; lean_object* v_lintDriverArgs_81_; lean_object* v_version_82_; lean_object* v_versionTags_83_; lean_object* v_description_84_; lean_object* v_keywords_85_; lean_object* v_homepage_86_; lean_object* v_license_87_; lean_object* v_licenseFiles_88_; lean_object* v_readmeFile_89_; uint8_t v_reservoir_90_; lean_object* v_enableArtifactCache_x3f_91_; lean_object* v_restoreAllArtifacts_x3f_92_; uint8_t v_libPrefixOnWindows_93_; uint8_t v_allowImportAll_94_; lean_object* v_builtinLint_x3f_95_; uint8_t v_fixedToolchain_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_toWorkspaceConfig_64_ = lean_ctor_get(v_cfg_63_, 0);
v_toLeanConfig_65_ = lean_ctor_get(v_cfg_63_, 1);
v_extraDepTargets_66_ = lean_ctor_get(v_cfg_63_, 2);
v_precompileModules_67_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_68_ = lean_ctor_get(v_cfg_63_, 3);
v_srcDir_69_ = lean_ctor_get(v_cfg_63_, 4);
v_buildDir_70_ = lean_ctor_get(v_cfg_63_, 5);
v_leanLibDir_71_ = lean_ctor_get(v_cfg_63_, 6);
v_nativeLibDir_72_ = lean_ctor_get(v_cfg_63_, 7);
v_binDir_73_ = lean_ctor_get(v_cfg_63_, 8);
v_irDir_74_ = lean_ctor_get(v_cfg_63_, 9);
v_releaseRepo_75_ = lean_ctor_get(v_cfg_63_, 10);
v_buildArchive_76_ = lean_ctor_get(v_cfg_63_, 11);
v_preferReleaseBuild_77_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*27 + 2);
v_testDriver_78_ = lean_ctor_get(v_cfg_63_, 12);
v_testDriverArgs_79_ = lean_ctor_get(v_cfg_63_, 13);
v_lintDriver_80_ = lean_ctor_get(v_cfg_63_, 14);
v_lintDriverArgs_81_ = lean_ctor_get(v_cfg_63_, 15);
v_version_82_ = lean_ctor_get(v_cfg_63_, 16);
v_versionTags_83_ = lean_ctor_get(v_cfg_63_, 17);
v_description_84_ = lean_ctor_get(v_cfg_63_, 18);
v_keywords_85_ = lean_ctor_get(v_cfg_63_, 19);
v_homepage_86_ = lean_ctor_get(v_cfg_63_, 20);
v_license_87_ = lean_ctor_get(v_cfg_63_, 21);
v_licenseFiles_88_ = lean_ctor_get(v_cfg_63_, 22);
v_readmeFile_89_ = lean_ctor_get(v_cfg_63_, 23);
v_reservoir_90_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_91_ = lean_ctor_get(v_cfg_63_, 24);
v_restoreAllArtifacts_x3f_92_ = lean_ctor_get(v_cfg_63_, 25);
v_libPrefixOnWindows_93_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*27 + 4);
v_allowImportAll_94_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_95_ = lean_ctor_get(v_cfg_63_, 26);
v_fixedToolchain_96_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*27 + 6);
v_isSharedCheck_103_ = !lean_is_exclusive(v_cfg_63_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v_cfg_63_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_builtinLint_x3f_95_);
lean_inc(v_restoreAllArtifacts_x3f_92_);
lean_inc(v_enableArtifactCache_x3f_91_);
lean_inc(v_readmeFile_89_);
lean_inc(v_licenseFiles_88_);
lean_inc(v_license_87_);
lean_inc(v_homepage_86_);
lean_inc(v_keywords_85_);
lean_inc(v_description_84_);
lean_inc(v_versionTags_83_);
lean_inc(v_version_82_);
lean_inc(v_lintDriverArgs_81_);
lean_inc(v_lintDriver_80_);
lean_inc(v_testDriverArgs_79_);
lean_inc(v_testDriver_78_);
lean_inc(v_buildArchive_76_);
lean_inc(v_releaseRepo_75_);
lean_inc(v_irDir_74_);
lean_inc(v_binDir_73_);
lean_inc(v_nativeLibDir_72_);
lean_inc(v_leanLibDir_71_);
lean_inc(v_buildDir_70_);
lean_inc(v_srcDir_69_);
lean_inc(v_moreGlobalServerArgs_68_);
lean_inc(v_extraDepTargets_66_);
lean_inc(v_toLeanConfig_65_);
lean_inc(v_toWorkspaceConfig_64_);
lean_dec(v_cfg_63_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_toWorkspaceConfig_64_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_toLeanConfig_65_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_extraDepTargets_66_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v_moreGlobalServerArgs_68_);
lean_ctor_set(v_reuseFailAlloc_102_, 4, v_srcDir_69_);
lean_ctor_set(v_reuseFailAlloc_102_, 5, v_buildDir_70_);
lean_ctor_set(v_reuseFailAlloc_102_, 6, v_leanLibDir_71_);
lean_ctor_set(v_reuseFailAlloc_102_, 7, v_nativeLibDir_72_);
lean_ctor_set(v_reuseFailAlloc_102_, 8, v_binDir_73_);
lean_ctor_set(v_reuseFailAlloc_102_, 9, v_irDir_74_);
lean_ctor_set(v_reuseFailAlloc_102_, 10, v_releaseRepo_75_);
lean_ctor_set(v_reuseFailAlloc_102_, 11, v_buildArchive_76_);
lean_ctor_set(v_reuseFailAlloc_102_, 12, v_testDriver_78_);
lean_ctor_set(v_reuseFailAlloc_102_, 13, v_testDriverArgs_79_);
lean_ctor_set(v_reuseFailAlloc_102_, 14, v_lintDriver_80_);
lean_ctor_set(v_reuseFailAlloc_102_, 15, v_lintDriverArgs_81_);
lean_ctor_set(v_reuseFailAlloc_102_, 16, v_version_82_);
lean_ctor_set(v_reuseFailAlloc_102_, 17, v_versionTags_83_);
lean_ctor_set(v_reuseFailAlloc_102_, 18, v_description_84_);
lean_ctor_set(v_reuseFailAlloc_102_, 19, v_keywords_85_);
lean_ctor_set(v_reuseFailAlloc_102_, 20, v_homepage_86_);
lean_ctor_set(v_reuseFailAlloc_102_, 21, v_license_87_);
lean_ctor_set(v_reuseFailAlloc_102_, 22, v_licenseFiles_88_);
lean_ctor_set(v_reuseFailAlloc_102_, 23, v_readmeFile_89_);
lean_ctor_set(v_reuseFailAlloc_102_, 24, v_enableArtifactCache_x3f_91_);
lean_ctor_set(v_reuseFailAlloc_102_, 25, v_restoreAllArtifacts_x3f_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 26, v_builtinLint_x3f_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*27 + 1, v_precompileModules_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*27 + 2, v_preferReleaseBuild_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*27 + 3, v_reservoir_90_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*27 + 5, v_allowImportAll_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*27 + 6, v_fixedToolchain_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*27, v_val_62_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object* v_val_104_, lean_object* v_cfg_105_){
_start:
{
uint8_t v_val_137__boxed_106_; lean_object* v_res_107_; 
v_val_137__boxed_106_ = lean_unbox(v_val_104_);
v_res_107_ = l_Lake_PackageConfig_bootstrap___proj___lam__1(v_val_137__boxed_106_, v_cfg_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object* v_f_108_, lean_object* v_cfg_109_){
_start:
{
lean_object* v_toWorkspaceConfig_110_; lean_object* v_toLeanConfig_111_; uint8_t v_bootstrap_112_; lean_object* v_extraDepTargets_113_; uint8_t v_precompileModules_114_; lean_object* v_moreGlobalServerArgs_115_; lean_object* v_srcDir_116_; lean_object* v_buildDir_117_; lean_object* v_leanLibDir_118_; lean_object* v_nativeLibDir_119_; lean_object* v_binDir_120_; lean_object* v_irDir_121_; lean_object* v_releaseRepo_122_; lean_object* v_buildArchive_123_; uint8_t v_preferReleaseBuild_124_; lean_object* v_testDriver_125_; lean_object* v_testDriverArgs_126_; lean_object* v_lintDriver_127_; lean_object* v_lintDriverArgs_128_; lean_object* v_version_129_; lean_object* v_versionTags_130_; lean_object* v_description_131_; lean_object* v_keywords_132_; lean_object* v_homepage_133_; lean_object* v_license_134_; lean_object* v_licenseFiles_135_; lean_object* v_readmeFile_136_; uint8_t v_reservoir_137_; lean_object* v_enableArtifactCache_x3f_138_; lean_object* v_restoreAllArtifacts_x3f_139_; uint8_t v_libPrefixOnWindows_140_; uint8_t v_allowImportAll_141_; lean_object* v_builtinLint_x3f_142_; uint8_t v_fixedToolchain_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_toWorkspaceConfig_110_ = lean_ctor_get(v_cfg_109_, 0);
v_toLeanConfig_111_ = lean_ctor_get(v_cfg_109_, 1);
v_bootstrap_112_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27);
v_extraDepTargets_113_ = lean_ctor_get(v_cfg_109_, 2);
v_precompileModules_114_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_115_ = lean_ctor_get(v_cfg_109_, 3);
v_srcDir_116_ = lean_ctor_get(v_cfg_109_, 4);
v_buildDir_117_ = lean_ctor_get(v_cfg_109_, 5);
v_leanLibDir_118_ = lean_ctor_get(v_cfg_109_, 6);
v_nativeLibDir_119_ = lean_ctor_get(v_cfg_109_, 7);
v_binDir_120_ = lean_ctor_get(v_cfg_109_, 8);
v_irDir_121_ = lean_ctor_get(v_cfg_109_, 9);
v_releaseRepo_122_ = lean_ctor_get(v_cfg_109_, 10);
v_buildArchive_123_ = lean_ctor_get(v_cfg_109_, 11);
v_preferReleaseBuild_124_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27 + 2);
v_testDriver_125_ = lean_ctor_get(v_cfg_109_, 12);
v_testDriverArgs_126_ = lean_ctor_get(v_cfg_109_, 13);
v_lintDriver_127_ = lean_ctor_get(v_cfg_109_, 14);
v_lintDriverArgs_128_ = lean_ctor_get(v_cfg_109_, 15);
v_version_129_ = lean_ctor_get(v_cfg_109_, 16);
v_versionTags_130_ = lean_ctor_get(v_cfg_109_, 17);
v_description_131_ = lean_ctor_get(v_cfg_109_, 18);
v_keywords_132_ = lean_ctor_get(v_cfg_109_, 19);
v_homepage_133_ = lean_ctor_get(v_cfg_109_, 20);
v_license_134_ = lean_ctor_get(v_cfg_109_, 21);
v_licenseFiles_135_ = lean_ctor_get(v_cfg_109_, 22);
v_readmeFile_136_ = lean_ctor_get(v_cfg_109_, 23);
v_reservoir_137_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_138_ = lean_ctor_get(v_cfg_109_, 24);
v_restoreAllArtifacts_x3f_139_ = lean_ctor_get(v_cfg_109_, 25);
v_libPrefixOnWindows_140_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27 + 4);
v_allowImportAll_141_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_142_ = lean_ctor_get(v_cfg_109_, 26);
v_fixedToolchain_143_ = lean_ctor_get_uint8(v_cfg_109_, sizeof(void*)*27 + 6);
v_isSharedCheck_153_ = !lean_is_exclusive(v_cfg_109_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v_cfg_109_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_builtinLint_x3f_142_);
lean_inc(v_restoreAllArtifacts_x3f_139_);
lean_inc(v_enableArtifactCache_x3f_138_);
lean_inc(v_readmeFile_136_);
lean_inc(v_licenseFiles_135_);
lean_inc(v_license_134_);
lean_inc(v_homepage_133_);
lean_inc(v_keywords_132_);
lean_inc(v_description_131_);
lean_inc(v_versionTags_130_);
lean_inc(v_version_129_);
lean_inc(v_lintDriverArgs_128_);
lean_inc(v_lintDriver_127_);
lean_inc(v_testDriverArgs_126_);
lean_inc(v_testDriver_125_);
lean_inc(v_buildArchive_123_);
lean_inc(v_releaseRepo_122_);
lean_inc(v_irDir_121_);
lean_inc(v_binDir_120_);
lean_inc(v_nativeLibDir_119_);
lean_inc(v_leanLibDir_118_);
lean_inc(v_buildDir_117_);
lean_inc(v_srcDir_116_);
lean_inc(v_moreGlobalServerArgs_115_);
lean_inc(v_extraDepTargets_113_);
lean_inc(v_toLeanConfig_111_);
lean_inc(v_toWorkspaceConfig_110_);
lean_dec(v_cfg_109_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = lean_box(v_bootstrap_112_);
v___x_148_ = lean_apply_1(v_f_108_, v___x_147_);
if (v_isShared_146_ == 0)
{
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_toWorkspaceConfig_110_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_toLeanConfig_111_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_extraDepTargets_113_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_moreGlobalServerArgs_115_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_srcDir_116_);
lean_ctor_set(v_reuseFailAlloc_152_, 5, v_buildDir_117_);
lean_ctor_set(v_reuseFailAlloc_152_, 6, v_leanLibDir_118_);
lean_ctor_set(v_reuseFailAlloc_152_, 7, v_nativeLibDir_119_);
lean_ctor_set(v_reuseFailAlloc_152_, 8, v_binDir_120_);
lean_ctor_set(v_reuseFailAlloc_152_, 9, v_irDir_121_);
lean_ctor_set(v_reuseFailAlloc_152_, 10, v_releaseRepo_122_);
lean_ctor_set(v_reuseFailAlloc_152_, 11, v_buildArchive_123_);
lean_ctor_set(v_reuseFailAlloc_152_, 12, v_testDriver_125_);
lean_ctor_set(v_reuseFailAlloc_152_, 13, v_testDriverArgs_126_);
lean_ctor_set(v_reuseFailAlloc_152_, 14, v_lintDriver_127_);
lean_ctor_set(v_reuseFailAlloc_152_, 15, v_lintDriverArgs_128_);
lean_ctor_set(v_reuseFailAlloc_152_, 16, v_version_129_);
lean_ctor_set(v_reuseFailAlloc_152_, 17, v_versionTags_130_);
lean_ctor_set(v_reuseFailAlloc_152_, 18, v_description_131_);
lean_ctor_set(v_reuseFailAlloc_152_, 19, v_keywords_132_);
lean_ctor_set(v_reuseFailAlloc_152_, 20, v_homepage_133_);
lean_ctor_set(v_reuseFailAlloc_152_, 21, v_license_134_);
lean_ctor_set(v_reuseFailAlloc_152_, 22, v_licenseFiles_135_);
lean_ctor_set(v_reuseFailAlloc_152_, 23, v_readmeFile_136_);
lean_ctor_set(v_reuseFailAlloc_152_, 24, v_enableArtifactCache_x3f_138_);
lean_ctor_set(v_reuseFailAlloc_152_, 25, v_restoreAllArtifacts_x3f_139_);
lean_ctor_set(v_reuseFailAlloc_152_, 26, v_builtinLint_x3f_142_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27, v___x_151_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27 + 1, v_precompileModules_114_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27 + 2, v_preferReleaseBuild_124_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27 + 3, v_reservoir_137_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_140_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27 + 5, v_allowImportAll_141_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*27 + 6, v_fixedToolchain_143_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object* v_x_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lake_PackageConfig_bootstrap___proj___lam__3(v_x_156_);
lean_dec_ref(v_x_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_168_, lean_object* v_n_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___closed__4));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_171_, lean_object* v_n_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lake_PackageConfig_bootstrap___proj(v_p_171_, v_n_172_);
lean_dec(v_n_172_);
lean_dec(v_p_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_174_, lean_object* v_n_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lake_PackageConfig_bootstrap___proj(v_p_174_, v_n_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_177_, lean_object* v_n_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_177_, v_n_178_);
lean_dec(v_n_178_);
lean_dec(v_p_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_180_){
_start:
{
lean_object* v_extraDepTargets_181_; 
v_extraDepTargets_181_ = lean_ctor_get(v_cfg_180_, 2);
lean_inc_ref(v_extraDepTargets_181_);
return v_extraDepTargets_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(v_cfg_182_);
lean_dec_ref(v_cfg_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* v_val_184_, lean_object* v_cfg_185_){
_start:
{
lean_object* v_toWorkspaceConfig_186_; lean_object* v_toLeanConfig_187_; uint8_t v_bootstrap_188_; uint8_t v_precompileModules_189_; lean_object* v_moreGlobalServerArgs_190_; lean_object* v_srcDir_191_; lean_object* v_buildDir_192_; lean_object* v_leanLibDir_193_; lean_object* v_nativeLibDir_194_; lean_object* v_binDir_195_; lean_object* v_irDir_196_; lean_object* v_releaseRepo_197_; lean_object* v_buildArchive_198_; uint8_t v_preferReleaseBuild_199_; lean_object* v_testDriver_200_; lean_object* v_testDriverArgs_201_; lean_object* v_lintDriver_202_; lean_object* v_lintDriverArgs_203_; lean_object* v_version_204_; lean_object* v_versionTags_205_; lean_object* v_description_206_; lean_object* v_keywords_207_; lean_object* v_homepage_208_; lean_object* v_license_209_; lean_object* v_licenseFiles_210_; lean_object* v_readmeFile_211_; uint8_t v_reservoir_212_; lean_object* v_enableArtifactCache_x3f_213_; lean_object* v_restoreAllArtifacts_x3f_214_; uint8_t v_libPrefixOnWindows_215_; uint8_t v_allowImportAll_216_; lean_object* v_builtinLint_x3f_217_; uint8_t v_fixedToolchain_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_toWorkspaceConfig_186_ = lean_ctor_get(v_cfg_185_, 0);
v_toLeanConfig_187_ = lean_ctor_get(v_cfg_185_, 1);
v_bootstrap_188_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27);
v_precompileModules_189_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_190_ = lean_ctor_get(v_cfg_185_, 3);
v_srcDir_191_ = lean_ctor_get(v_cfg_185_, 4);
v_buildDir_192_ = lean_ctor_get(v_cfg_185_, 5);
v_leanLibDir_193_ = lean_ctor_get(v_cfg_185_, 6);
v_nativeLibDir_194_ = lean_ctor_get(v_cfg_185_, 7);
v_binDir_195_ = lean_ctor_get(v_cfg_185_, 8);
v_irDir_196_ = lean_ctor_get(v_cfg_185_, 9);
v_releaseRepo_197_ = lean_ctor_get(v_cfg_185_, 10);
v_buildArchive_198_ = lean_ctor_get(v_cfg_185_, 11);
v_preferReleaseBuild_199_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27 + 2);
v_testDriver_200_ = lean_ctor_get(v_cfg_185_, 12);
v_testDriverArgs_201_ = lean_ctor_get(v_cfg_185_, 13);
v_lintDriver_202_ = lean_ctor_get(v_cfg_185_, 14);
v_lintDriverArgs_203_ = lean_ctor_get(v_cfg_185_, 15);
v_version_204_ = lean_ctor_get(v_cfg_185_, 16);
v_versionTags_205_ = lean_ctor_get(v_cfg_185_, 17);
v_description_206_ = lean_ctor_get(v_cfg_185_, 18);
v_keywords_207_ = lean_ctor_get(v_cfg_185_, 19);
v_homepage_208_ = lean_ctor_get(v_cfg_185_, 20);
v_license_209_ = lean_ctor_get(v_cfg_185_, 21);
v_licenseFiles_210_ = lean_ctor_get(v_cfg_185_, 22);
v_readmeFile_211_ = lean_ctor_get(v_cfg_185_, 23);
v_reservoir_212_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_213_ = lean_ctor_get(v_cfg_185_, 24);
v_restoreAllArtifacts_x3f_214_ = lean_ctor_get(v_cfg_185_, 25);
v_libPrefixOnWindows_215_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27 + 4);
v_allowImportAll_216_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_217_ = lean_ctor_get(v_cfg_185_, 26);
v_fixedToolchain_218_ = lean_ctor_get_uint8(v_cfg_185_, sizeof(void*)*27 + 6);
v_isSharedCheck_225_ = !lean_is_exclusive(v_cfg_185_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; 
v_unused_226_ = lean_ctor_get(v_cfg_185_, 2);
lean_dec(v_unused_226_);
v___x_220_ = v_cfg_185_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_builtinLint_x3f_217_);
lean_inc(v_restoreAllArtifacts_x3f_214_);
lean_inc(v_enableArtifactCache_x3f_213_);
lean_inc(v_readmeFile_211_);
lean_inc(v_licenseFiles_210_);
lean_inc(v_license_209_);
lean_inc(v_homepage_208_);
lean_inc(v_keywords_207_);
lean_inc(v_description_206_);
lean_inc(v_versionTags_205_);
lean_inc(v_version_204_);
lean_inc(v_lintDriverArgs_203_);
lean_inc(v_lintDriver_202_);
lean_inc(v_testDriverArgs_201_);
lean_inc(v_testDriver_200_);
lean_inc(v_buildArchive_198_);
lean_inc(v_releaseRepo_197_);
lean_inc(v_irDir_196_);
lean_inc(v_binDir_195_);
lean_inc(v_nativeLibDir_194_);
lean_inc(v_leanLibDir_193_);
lean_inc(v_buildDir_192_);
lean_inc(v_srcDir_191_);
lean_inc(v_moreGlobalServerArgs_190_);
lean_inc(v_toLeanConfig_187_);
lean_inc(v_toWorkspaceConfig_186_);
lean_dec(v_cfg_185_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 2, v_val_184_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_toWorkspaceConfig_186_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_toLeanConfig_187_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_val_184_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_moreGlobalServerArgs_190_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_srcDir_191_);
lean_ctor_set(v_reuseFailAlloc_224_, 5, v_buildDir_192_);
lean_ctor_set(v_reuseFailAlloc_224_, 6, v_leanLibDir_193_);
lean_ctor_set(v_reuseFailAlloc_224_, 7, v_nativeLibDir_194_);
lean_ctor_set(v_reuseFailAlloc_224_, 8, v_binDir_195_);
lean_ctor_set(v_reuseFailAlloc_224_, 9, v_irDir_196_);
lean_ctor_set(v_reuseFailAlloc_224_, 10, v_releaseRepo_197_);
lean_ctor_set(v_reuseFailAlloc_224_, 11, v_buildArchive_198_);
lean_ctor_set(v_reuseFailAlloc_224_, 12, v_testDriver_200_);
lean_ctor_set(v_reuseFailAlloc_224_, 13, v_testDriverArgs_201_);
lean_ctor_set(v_reuseFailAlloc_224_, 14, v_lintDriver_202_);
lean_ctor_set(v_reuseFailAlloc_224_, 15, v_lintDriverArgs_203_);
lean_ctor_set(v_reuseFailAlloc_224_, 16, v_version_204_);
lean_ctor_set(v_reuseFailAlloc_224_, 17, v_versionTags_205_);
lean_ctor_set(v_reuseFailAlloc_224_, 18, v_description_206_);
lean_ctor_set(v_reuseFailAlloc_224_, 19, v_keywords_207_);
lean_ctor_set(v_reuseFailAlloc_224_, 20, v_homepage_208_);
lean_ctor_set(v_reuseFailAlloc_224_, 21, v_license_209_);
lean_ctor_set(v_reuseFailAlloc_224_, 22, v_licenseFiles_210_);
lean_ctor_set(v_reuseFailAlloc_224_, 23, v_readmeFile_211_);
lean_ctor_set(v_reuseFailAlloc_224_, 24, v_enableArtifactCache_x3f_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 25, v_restoreAllArtifacts_x3f_214_);
lean_ctor_set(v_reuseFailAlloc_224_, 26, v_builtinLint_x3f_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27, v_bootstrap_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27 + 1, v_precompileModules_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27 + 2, v_preferReleaseBuild_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27 + 3, v_reservoir_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27 + 5, v_allowImportAll_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*27 + 6, v_fixedToolchain_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* v_f_227_, lean_object* v_cfg_228_){
_start:
{
lean_object* v_toWorkspaceConfig_229_; lean_object* v_toLeanConfig_230_; uint8_t v_bootstrap_231_; lean_object* v_extraDepTargets_232_; uint8_t v_precompileModules_233_; lean_object* v_moreGlobalServerArgs_234_; lean_object* v_srcDir_235_; lean_object* v_buildDir_236_; lean_object* v_leanLibDir_237_; lean_object* v_nativeLibDir_238_; lean_object* v_binDir_239_; lean_object* v_irDir_240_; lean_object* v_releaseRepo_241_; lean_object* v_buildArchive_242_; uint8_t v_preferReleaseBuild_243_; lean_object* v_testDriver_244_; lean_object* v_testDriverArgs_245_; lean_object* v_lintDriver_246_; lean_object* v_lintDriverArgs_247_; lean_object* v_version_248_; lean_object* v_versionTags_249_; lean_object* v_description_250_; lean_object* v_keywords_251_; lean_object* v_homepage_252_; lean_object* v_license_253_; lean_object* v_licenseFiles_254_; lean_object* v_readmeFile_255_; uint8_t v_reservoir_256_; lean_object* v_enableArtifactCache_x3f_257_; lean_object* v_restoreAllArtifacts_x3f_258_; uint8_t v_libPrefixOnWindows_259_; uint8_t v_allowImportAll_260_; lean_object* v_builtinLint_x3f_261_; uint8_t v_fixedToolchain_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
v_toWorkspaceConfig_229_ = lean_ctor_get(v_cfg_228_, 0);
v_toLeanConfig_230_ = lean_ctor_get(v_cfg_228_, 1);
v_bootstrap_231_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27);
v_extraDepTargets_232_ = lean_ctor_get(v_cfg_228_, 2);
v_precompileModules_233_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_234_ = lean_ctor_get(v_cfg_228_, 3);
v_srcDir_235_ = lean_ctor_get(v_cfg_228_, 4);
v_buildDir_236_ = lean_ctor_get(v_cfg_228_, 5);
v_leanLibDir_237_ = lean_ctor_get(v_cfg_228_, 6);
v_nativeLibDir_238_ = lean_ctor_get(v_cfg_228_, 7);
v_binDir_239_ = lean_ctor_get(v_cfg_228_, 8);
v_irDir_240_ = lean_ctor_get(v_cfg_228_, 9);
v_releaseRepo_241_ = lean_ctor_get(v_cfg_228_, 10);
v_buildArchive_242_ = lean_ctor_get(v_cfg_228_, 11);
v_preferReleaseBuild_243_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27 + 2);
v_testDriver_244_ = lean_ctor_get(v_cfg_228_, 12);
v_testDriverArgs_245_ = lean_ctor_get(v_cfg_228_, 13);
v_lintDriver_246_ = lean_ctor_get(v_cfg_228_, 14);
v_lintDriverArgs_247_ = lean_ctor_get(v_cfg_228_, 15);
v_version_248_ = lean_ctor_get(v_cfg_228_, 16);
v_versionTags_249_ = lean_ctor_get(v_cfg_228_, 17);
v_description_250_ = lean_ctor_get(v_cfg_228_, 18);
v_keywords_251_ = lean_ctor_get(v_cfg_228_, 19);
v_homepage_252_ = lean_ctor_get(v_cfg_228_, 20);
v_license_253_ = lean_ctor_get(v_cfg_228_, 21);
v_licenseFiles_254_ = lean_ctor_get(v_cfg_228_, 22);
v_readmeFile_255_ = lean_ctor_get(v_cfg_228_, 23);
v_reservoir_256_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_257_ = lean_ctor_get(v_cfg_228_, 24);
v_restoreAllArtifacts_x3f_258_ = lean_ctor_get(v_cfg_228_, 25);
v_libPrefixOnWindows_259_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27 + 4);
v_allowImportAll_260_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_261_ = lean_ctor_get(v_cfg_228_, 26);
v_fixedToolchain_262_ = lean_ctor_get_uint8(v_cfg_228_, sizeof(void*)*27 + 6);
v_isSharedCheck_270_ = !lean_is_exclusive(v_cfg_228_);
if (v_isSharedCheck_270_ == 0)
{
v___x_264_ = v_cfg_228_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_builtinLint_x3f_261_);
lean_inc(v_restoreAllArtifacts_x3f_258_);
lean_inc(v_enableArtifactCache_x3f_257_);
lean_inc(v_readmeFile_255_);
lean_inc(v_licenseFiles_254_);
lean_inc(v_license_253_);
lean_inc(v_homepage_252_);
lean_inc(v_keywords_251_);
lean_inc(v_description_250_);
lean_inc(v_versionTags_249_);
lean_inc(v_version_248_);
lean_inc(v_lintDriverArgs_247_);
lean_inc(v_lintDriver_246_);
lean_inc(v_testDriverArgs_245_);
lean_inc(v_testDriver_244_);
lean_inc(v_buildArchive_242_);
lean_inc(v_releaseRepo_241_);
lean_inc(v_irDir_240_);
lean_inc(v_binDir_239_);
lean_inc(v_nativeLibDir_238_);
lean_inc(v_leanLibDir_237_);
lean_inc(v_buildDir_236_);
lean_inc(v_srcDir_235_);
lean_inc(v_moreGlobalServerArgs_234_);
lean_inc(v_extraDepTargets_232_);
lean_inc(v_toLeanConfig_230_);
lean_inc(v_toWorkspaceConfig_229_);
lean_dec(v_cfg_228_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_apply_1(v_f_227_, v_extraDepTargets_232_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 2, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_toWorkspaceConfig_229_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_toLeanConfig_230_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_moreGlobalServerArgs_234_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_srcDir_235_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_buildDir_236_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_leanLibDir_237_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_nativeLibDir_238_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_binDir_239_);
lean_ctor_set(v_reuseFailAlloc_269_, 9, v_irDir_240_);
lean_ctor_set(v_reuseFailAlloc_269_, 10, v_releaseRepo_241_);
lean_ctor_set(v_reuseFailAlloc_269_, 11, v_buildArchive_242_);
lean_ctor_set(v_reuseFailAlloc_269_, 12, v_testDriver_244_);
lean_ctor_set(v_reuseFailAlloc_269_, 13, v_testDriverArgs_245_);
lean_ctor_set(v_reuseFailAlloc_269_, 14, v_lintDriver_246_);
lean_ctor_set(v_reuseFailAlloc_269_, 15, v_lintDriverArgs_247_);
lean_ctor_set(v_reuseFailAlloc_269_, 16, v_version_248_);
lean_ctor_set(v_reuseFailAlloc_269_, 17, v_versionTags_249_);
lean_ctor_set(v_reuseFailAlloc_269_, 18, v_description_250_);
lean_ctor_set(v_reuseFailAlloc_269_, 19, v_keywords_251_);
lean_ctor_set(v_reuseFailAlloc_269_, 20, v_homepage_252_);
lean_ctor_set(v_reuseFailAlloc_269_, 21, v_license_253_);
lean_ctor_set(v_reuseFailAlloc_269_, 22, v_licenseFiles_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 23, v_readmeFile_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 24, v_enableArtifactCache_x3f_257_);
lean_ctor_set(v_reuseFailAlloc_269_, 25, v_restoreAllArtifacts_x3f_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 26, v_builtinLint_x3f_261_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27, v_bootstrap_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27 + 1, v_precompileModules_233_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27 + 2, v_preferReleaseBuild_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27 + 3, v_reservoir_256_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_259_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27 + 5, v_allowImportAll_260_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, sizeof(void*)*27 + 6, v_fixedToolchain_262_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(v_x_273_);
lean_dec_ref(v_x_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_284_, lean_object* v_n_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_287_, lean_object* v_n_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_287_, v_n_288_);
lean_dec(v_n_288_);
lean_dec(v_p_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_290_, lean_object* v_n_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_290_, v_n_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_293_, lean_object* v_n_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_293_, v_n_294_);
lean_dec(v_n_294_);
lean_dec(v_p_293_);
return v_res_295_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* v_cfg_296_){
_start:
{
uint8_t v_precompileModules_297_; 
v_precompileModules_297_ = lean_ctor_get_uint8(v_cfg_296_, sizeof(void*)*27 + 1);
return v_precompileModules_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Lake_PackageConfig_precompileModules___proj___lam__0(v_cfg_298_);
lean_dec_ref(v_cfg_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t v_val_301_, lean_object* v_cfg_302_){
_start:
{
lean_object* v_toWorkspaceConfig_303_; lean_object* v_toLeanConfig_304_; uint8_t v_bootstrap_305_; lean_object* v_extraDepTargets_306_; lean_object* v_moreGlobalServerArgs_307_; lean_object* v_srcDir_308_; lean_object* v_buildDir_309_; lean_object* v_leanLibDir_310_; lean_object* v_nativeLibDir_311_; lean_object* v_binDir_312_; lean_object* v_irDir_313_; lean_object* v_releaseRepo_314_; lean_object* v_buildArchive_315_; uint8_t v_preferReleaseBuild_316_; lean_object* v_testDriver_317_; lean_object* v_testDriverArgs_318_; lean_object* v_lintDriver_319_; lean_object* v_lintDriverArgs_320_; lean_object* v_version_321_; lean_object* v_versionTags_322_; lean_object* v_description_323_; lean_object* v_keywords_324_; lean_object* v_homepage_325_; lean_object* v_license_326_; lean_object* v_licenseFiles_327_; lean_object* v_readmeFile_328_; uint8_t v_reservoir_329_; lean_object* v_enableArtifactCache_x3f_330_; lean_object* v_restoreAllArtifacts_x3f_331_; uint8_t v_libPrefixOnWindows_332_; uint8_t v_allowImportAll_333_; lean_object* v_builtinLint_x3f_334_; uint8_t v_fixedToolchain_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_toWorkspaceConfig_303_ = lean_ctor_get(v_cfg_302_, 0);
v_toLeanConfig_304_ = lean_ctor_get(v_cfg_302_, 1);
v_bootstrap_305_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*27);
v_extraDepTargets_306_ = lean_ctor_get(v_cfg_302_, 2);
v_moreGlobalServerArgs_307_ = lean_ctor_get(v_cfg_302_, 3);
v_srcDir_308_ = lean_ctor_get(v_cfg_302_, 4);
v_buildDir_309_ = lean_ctor_get(v_cfg_302_, 5);
v_leanLibDir_310_ = lean_ctor_get(v_cfg_302_, 6);
v_nativeLibDir_311_ = lean_ctor_get(v_cfg_302_, 7);
v_binDir_312_ = lean_ctor_get(v_cfg_302_, 8);
v_irDir_313_ = lean_ctor_get(v_cfg_302_, 9);
v_releaseRepo_314_ = lean_ctor_get(v_cfg_302_, 10);
v_buildArchive_315_ = lean_ctor_get(v_cfg_302_, 11);
v_preferReleaseBuild_316_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*27 + 2);
v_testDriver_317_ = lean_ctor_get(v_cfg_302_, 12);
v_testDriverArgs_318_ = lean_ctor_get(v_cfg_302_, 13);
v_lintDriver_319_ = lean_ctor_get(v_cfg_302_, 14);
v_lintDriverArgs_320_ = lean_ctor_get(v_cfg_302_, 15);
v_version_321_ = lean_ctor_get(v_cfg_302_, 16);
v_versionTags_322_ = lean_ctor_get(v_cfg_302_, 17);
v_description_323_ = lean_ctor_get(v_cfg_302_, 18);
v_keywords_324_ = lean_ctor_get(v_cfg_302_, 19);
v_homepage_325_ = lean_ctor_get(v_cfg_302_, 20);
v_license_326_ = lean_ctor_get(v_cfg_302_, 21);
v_licenseFiles_327_ = lean_ctor_get(v_cfg_302_, 22);
v_readmeFile_328_ = lean_ctor_get(v_cfg_302_, 23);
v_reservoir_329_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_330_ = lean_ctor_get(v_cfg_302_, 24);
v_restoreAllArtifacts_x3f_331_ = lean_ctor_get(v_cfg_302_, 25);
v_libPrefixOnWindows_332_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*27 + 4);
v_allowImportAll_333_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_334_ = lean_ctor_get(v_cfg_302_, 26);
v_fixedToolchain_335_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*27 + 6);
v_isSharedCheck_342_ = !lean_is_exclusive(v_cfg_302_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v_cfg_302_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_builtinLint_x3f_334_);
lean_inc(v_restoreAllArtifacts_x3f_331_);
lean_inc(v_enableArtifactCache_x3f_330_);
lean_inc(v_readmeFile_328_);
lean_inc(v_licenseFiles_327_);
lean_inc(v_license_326_);
lean_inc(v_homepage_325_);
lean_inc(v_keywords_324_);
lean_inc(v_description_323_);
lean_inc(v_versionTags_322_);
lean_inc(v_version_321_);
lean_inc(v_lintDriverArgs_320_);
lean_inc(v_lintDriver_319_);
lean_inc(v_testDriverArgs_318_);
lean_inc(v_testDriver_317_);
lean_inc(v_buildArchive_315_);
lean_inc(v_releaseRepo_314_);
lean_inc(v_irDir_313_);
lean_inc(v_binDir_312_);
lean_inc(v_nativeLibDir_311_);
lean_inc(v_leanLibDir_310_);
lean_inc(v_buildDir_309_);
lean_inc(v_srcDir_308_);
lean_inc(v_moreGlobalServerArgs_307_);
lean_inc(v_extraDepTargets_306_);
lean_inc(v_toLeanConfig_304_);
lean_inc(v_toWorkspaceConfig_303_);
lean_dec(v_cfg_302_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_toWorkspaceConfig_303_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_toLeanConfig_304_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_extraDepTargets_306_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_moreGlobalServerArgs_307_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_srcDir_308_);
lean_ctor_set(v_reuseFailAlloc_341_, 5, v_buildDir_309_);
lean_ctor_set(v_reuseFailAlloc_341_, 6, v_leanLibDir_310_);
lean_ctor_set(v_reuseFailAlloc_341_, 7, v_nativeLibDir_311_);
lean_ctor_set(v_reuseFailAlloc_341_, 8, v_binDir_312_);
lean_ctor_set(v_reuseFailAlloc_341_, 9, v_irDir_313_);
lean_ctor_set(v_reuseFailAlloc_341_, 10, v_releaseRepo_314_);
lean_ctor_set(v_reuseFailAlloc_341_, 11, v_buildArchive_315_);
lean_ctor_set(v_reuseFailAlloc_341_, 12, v_testDriver_317_);
lean_ctor_set(v_reuseFailAlloc_341_, 13, v_testDriverArgs_318_);
lean_ctor_set(v_reuseFailAlloc_341_, 14, v_lintDriver_319_);
lean_ctor_set(v_reuseFailAlloc_341_, 15, v_lintDriverArgs_320_);
lean_ctor_set(v_reuseFailAlloc_341_, 16, v_version_321_);
lean_ctor_set(v_reuseFailAlloc_341_, 17, v_versionTags_322_);
lean_ctor_set(v_reuseFailAlloc_341_, 18, v_description_323_);
lean_ctor_set(v_reuseFailAlloc_341_, 19, v_keywords_324_);
lean_ctor_set(v_reuseFailAlloc_341_, 20, v_homepage_325_);
lean_ctor_set(v_reuseFailAlloc_341_, 21, v_license_326_);
lean_ctor_set(v_reuseFailAlloc_341_, 22, v_licenseFiles_327_);
lean_ctor_set(v_reuseFailAlloc_341_, 23, v_readmeFile_328_);
lean_ctor_set(v_reuseFailAlloc_341_, 24, v_enableArtifactCache_x3f_330_);
lean_ctor_set(v_reuseFailAlloc_341_, 25, v_restoreAllArtifacts_x3f_331_);
lean_ctor_set(v_reuseFailAlloc_341_, 26, v_builtinLint_x3f_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*27, v_bootstrap_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*27 + 2, v_preferReleaseBuild_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*27 + 3, v_reservoir_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*27 + 5, v_allowImportAll_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_341_, sizeof(void*)*27 + 6, v_fixedToolchain_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*27 + 1, v_val_301_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_343_, lean_object* v_cfg_344_){
_start:
{
uint8_t v_val_137__boxed_345_; lean_object* v_res_346_; 
v_val_137__boxed_345_ = lean_unbox(v_val_343_);
v_res_346_ = l_Lake_PackageConfig_precompileModules___proj___lam__1(v_val_137__boxed_345_, v_cfg_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* v_f_347_, lean_object* v_cfg_348_){
_start:
{
lean_object* v_toWorkspaceConfig_349_; lean_object* v_toLeanConfig_350_; uint8_t v_bootstrap_351_; lean_object* v_extraDepTargets_352_; uint8_t v_precompileModules_353_; lean_object* v_moreGlobalServerArgs_354_; lean_object* v_srcDir_355_; lean_object* v_buildDir_356_; lean_object* v_leanLibDir_357_; lean_object* v_nativeLibDir_358_; lean_object* v_binDir_359_; lean_object* v_irDir_360_; lean_object* v_releaseRepo_361_; lean_object* v_buildArchive_362_; uint8_t v_preferReleaseBuild_363_; lean_object* v_testDriver_364_; lean_object* v_testDriverArgs_365_; lean_object* v_lintDriver_366_; lean_object* v_lintDriverArgs_367_; lean_object* v_version_368_; lean_object* v_versionTags_369_; lean_object* v_description_370_; lean_object* v_keywords_371_; lean_object* v_homepage_372_; lean_object* v_license_373_; lean_object* v_licenseFiles_374_; lean_object* v_readmeFile_375_; uint8_t v_reservoir_376_; lean_object* v_enableArtifactCache_x3f_377_; lean_object* v_restoreAllArtifacts_x3f_378_; uint8_t v_libPrefixOnWindows_379_; uint8_t v_allowImportAll_380_; lean_object* v_builtinLint_x3f_381_; uint8_t v_fixedToolchain_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_392_; 
v_toWorkspaceConfig_349_ = lean_ctor_get(v_cfg_348_, 0);
v_toLeanConfig_350_ = lean_ctor_get(v_cfg_348_, 1);
v_bootstrap_351_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27);
v_extraDepTargets_352_ = lean_ctor_get(v_cfg_348_, 2);
v_precompileModules_353_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_354_ = lean_ctor_get(v_cfg_348_, 3);
v_srcDir_355_ = lean_ctor_get(v_cfg_348_, 4);
v_buildDir_356_ = lean_ctor_get(v_cfg_348_, 5);
v_leanLibDir_357_ = lean_ctor_get(v_cfg_348_, 6);
v_nativeLibDir_358_ = lean_ctor_get(v_cfg_348_, 7);
v_binDir_359_ = lean_ctor_get(v_cfg_348_, 8);
v_irDir_360_ = lean_ctor_get(v_cfg_348_, 9);
v_releaseRepo_361_ = lean_ctor_get(v_cfg_348_, 10);
v_buildArchive_362_ = lean_ctor_get(v_cfg_348_, 11);
v_preferReleaseBuild_363_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27 + 2);
v_testDriver_364_ = lean_ctor_get(v_cfg_348_, 12);
v_testDriverArgs_365_ = lean_ctor_get(v_cfg_348_, 13);
v_lintDriver_366_ = lean_ctor_get(v_cfg_348_, 14);
v_lintDriverArgs_367_ = lean_ctor_get(v_cfg_348_, 15);
v_version_368_ = lean_ctor_get(v_cfg_348_, 16);
v_versionTags_369_ = lean_ctor_get(v_cfg_348_, 17);
v_description_370_ = lean_ctor_get(v_cfg_348_, 18);
v_keywords_371_ = lean_ctor_get(v_cfg_348_, 19);
v_homepage_372_ = lean_ctor_get(v_cfg_348_, 20);
v_license_373_ = lean_ctor_get(v_cfg_348_, 21);
v_licenseFiles_374_ = lean_ctor_get(v_cfg_348_, 22);
v_readmeFile_375_ = lean_ctor_get(v_cfg_348_, 23);
v_reservoir_376_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_377_ = lean_ctor_get(v_cfg_348_, 24);
v_restoreAllArtifacts_x3f_378_ = lean_ctor_get(v_cfg_348_, 25);
v_libPrefixOnWindows_379_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27 + 4);
v_allowImportAll_380_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_381_ = lean_ctor_get(v_cfg_348_, 26);
v_fixedToolchain_382_ = lean_ctor_get_uint8(v_cfg_348_, sizeof(void*)*27 + 6);
v_isSharedCheck_392_ = !lean_is_exclusive(v_cfg_348_);
if (v_isSharedCheck_392_ == 0)
{
v___x_384_ = v_cfg_348_;
v_isShared_385_ = v_isSharedCheck_392_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_builtinLint_x3f_381_);
lean_inc(v_restoreAllArtifacts_x3f_378_);
lean_inc(v_enableArtifactCache_x3f_377_);
lean_inc(v_readmeFile_375_);
lean_inc(v_licenseFiles_374_);
lean_inc(v_license_373_);
lean_inc(v_homepage_372_);
lean_inc(v_keywords_371_);
lean_inc(v_description_370_);
lean_inc(v_versionTags_369_);
lean_inc(v_version_368_);
lean_inc(v_lintDriverArgs_367_);
lean_inc(v_lintDriver_366_);
lean_inc(v_testDriverArgs_365_);
lean_inc(v_testDriver_364_);
lean_inc(v_buildArchive_362_);
lean_inc(v_releaseRepo_361_);
lean_inc(v_irDir_360_);
lean_inc(v_binDir_359_);
lean_inc(v_nativeLibDir_358_);
lean_inc(v_leanLibDir_357_);
lean_inc(v_buildDir_356_);
lean_inc(v_srcDir_355_);
lean_inc(v_moreGlobalServerArgs_354_);
lean_inc(v_extraDepTargets_352_);
lean_inc(v_toLeanConfig_350_);
lean_inc(v_toWorkspaceConfig_349_);
lean_dec(v_cfg_348_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_392_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = lean_box(v_precompileModules_353_);
v___x_387_ = lean_apply_1(v_f_347_, v___x_386_);
if (v_isShared_385_ == 0)
{
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_toWorkspaceConfig_349_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_toLeanConfig_350_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_extraDepTargets_352_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_moreGlobalServerArgs_354_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_srcDir_355_);
lean_ctor_set(v_reuseFailAlloc_391_, 5, v_buildDir_356_);
lean_ctor_set(v_reuseFailAlloc_391_, 6, v_leanLibDir_357_);
lean_ctor_set(v_reuseFailAlloc_391_, 7, v_nativeLibDir_358_);
lean_ctor_set(v_reuseFailAlloc_391_, 8, v_binDir_359_);
lean_ctor_set(v_reuseFailAlloc_391_, 9, v_irDir_360_);
lean_ctor_set(v_reuseFailAlloc_391_, 10, v_releaseRepo_361_);
lean_ctor_set(v_reuseFailAlloc_391_, 11, v_buildArchive_362_);
lean_ctor_set(v_reuseFailAlloc_391_, 12, v_testDriver_364_);
lean_ctor_set(v_reuseFailAlloc_391_, 13, v_testDriverArgs_365_);
lean_ctor_set(v_reuseFailAlloc_391_, 14, v_lintDriver_366_);
lean_ctor_set(v_reuseFailAlloc_391_, 15, v_lintDriverArgs_367_);
lean_ctor_set(v_reuseFailAlloc_391_, 16, v_version_368_);
lean_ctor_set(v_reuseFailAlloc_391_, 17, v_versionTags_369_);
lean_ctor_set(v_reuseFailAlloc_391_, 18, v_description_370_);
lean_ctor_set(v_reuseFailAlloc_391_, 19, v_keywords_371_);
lean_ctor_set(v_reuseFailAlloc_391_, 20, v_homepage_372_);
lean_ctor_set(v_reuseFailAlloc_391_, 21, v_license_373_);
lean_ctor_set(v_reuseFailAlloc_391_, 22, v_licenseFiles_374_);
lean_ctor_set(v_reuseFailAlloc_391_, 23, v_readmeFile_375_);
lean_ctor_set(v_reuseFailAlloc_391_, 24, v_enableArtifactCache_x3f_377_);
lean_ctor_set(v_reuseFailAlloc_391_, 25, v_restoreAllArtifacts_x3f_378_);
lean_ctor_set(v_reuseFailAlloc_391_, 26, v_builtinLint_x3f_381_);
lean_ctor_set_uint8(v_reuseFailAlloc_391_, sizeof(void*)*27, v_bootstrap_351_);
v___x_389_ = v_reuseFailAlloc_391_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
uint8_t v___x_390_; 
v___x_390_ = lean_unbox(v___x_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*27 + 1, v___x_390_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*27 + 2, v_preferReleaseBuild_363_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*27 + 3, v_reservoir_376_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_379_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*27 + 5, v_allowImportAll_380_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*27 + 6, v_fixedToolchain_382_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_401_, lean_object* v_n_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_404_, lean_object* v_n_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lake_PackageConfig_precompileModules___proj(v_p_404_, v_n_405_);
lean_dec(v_n_405_);
lean_dec(v_p_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_407_, lean_object* v_n_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lake_PackageConfig_precompileModules___proj(v_p_407_, v_n_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_410_, lean_object* v_n_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_410_, v_n_411_);
lean_dec(v_n_411_);
lean_dec(v_p_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* v_cfg_413_){
_start:
{
lean_object* v_moreGlobalServerArgs_414_; 
v_moreGlobalServerArgs_414_ = lean_ctor_get(v_cfg_413_, 3);
lean_inc_ref(v_moreGlobalServerArgs_414_);
return v_moreGlobalServerArgs_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* v_cfg_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(v_cfg_415_);
lean_dec_ref(v_cfg_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* v_val_417_, lean_object* v_cfg_418_){
_start:
{
lean_object* v_toWorkspaceConfig_419_; lean_object* v_toLeanConfig_420_; uint8_t v_bootstrap_421_; lean_object* v_extraDepTargets_422_; uint8_t v_precompileModules_423_; lean_object* v_srcDir_424_; lean_object* v_buildDir_425_; lean_object* v_leanLibDir_426_; lean_object* v_nativeLibDir_427_; lean_object* v_binDir_428_; lean_object* v_irDir_429_; lean_object* v_releaseRepo_430_; lean_object* v_buildArchive_431_; uint8_t v_preferReleaseBuild_432_; lean_object* v_testDriver_433_; lean_object* v_testDriverArgs_434_; lean_object* v_lintDriver_435_; lean_object* v_lintDriverArgs_436_; lean_object* v_version_437_; lean_object* v_versionTags_438_; lean_object* v_description_439_; lean_object* v_keywords_440_; lean_object* v_homepage_441_; lean_object* v_license_442_; lean_object* v_licenseFiles_443_; lean_object* v_readmeFile_444_; uint8_t v_reservoir_445_; lean_object* v_enableArtifactCache_x3f_446_; lean_object* v_restoreAllArtifacts_x3f_447_; uint8_t v_libPrefixOnWindows_448_; uint8_t v_allowImportAll_449_; lean_object* v_builtinLint_x3f_450_; uint8_t v_fixedToolchain_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_toWorkspaceConfig_419_ = lean_ctor_get(v_cfg_418_, 0);
v_toLeanConfig_420_ = lean_ctor_get(v_cfg_418_, 1);
v_bootstrap_421_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27);
v_extraDepTargets_422_ = lean_ctor_get(v_cfg_418_, 2);
v_precompileModules_423_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27 + 1);
v_srcDir_424_ = lean_ctor_get(v_cfg_418_, 4);
v_buildDir_425_ = lean_ctor_get(v_cfg_418_, 5);
v_leanLibDir_426_ = lean_ctor_get(v_cfg_418_, 6);
v_nativeLibDir_427_ = lean_ctor_get(v_cfg_418_, 7);
v_binDir_428_ = lean_ctor_get(v_cfg_418_, 8);
v_irDir_429_ = lean_ctor_get(v_cfg_418_, 9);
v_releaseRepo_430_ = lean_ctor_get(v_cfg_418_, 10);
v_buildArchive_431_ = lean_ctor_get(v_cfg_418_, 11);
v_preferReleaseBuild_432_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27 + 2);
v_testDriver_433_ = lean_ctor_get(v_cfg_418_, 12);
v_testDriverArgs_434_ = lean_ctor_get(v_cfg_418_, 13);
v_lintDriver_435_ = lean_ctor_get(v_cfg_418_, 14);
v_lintDriverArgs_436_ = lean_ctor_get(v_cfg_418_, 15);
v_version_437_ = lean_ctor_get(v_cfg_418_, 16);
v_versionTags_438_ = lean_ctor_get(v_cfg_418_, 17);
v_description_439_ = lean_ctor_get(v_cfg_418_, 18);
v_keywords_440_ = lean_ctor_get(v_cfg_418_, 19);
v_homepage_441_ = lean_ctor_get(v_cfg_418_, 20);
v_license_442_ = lean_ctor_get(v_cfg_418_, 21);
v_licenseFiles_443_ = lean_ctor_get(v_cfg_418_, 22);
v_readmeFile_444_ = lean_ctor_get(v_cfg_418_, 23);
v_reservoir_445_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_446_ = lean_ctor_get(v_cfg_418_, 24);
v_restoreAllArtifacts_x3f_447_ = lean_ctor_get(v_cfg_418_, 25);
v_libPrefixOnWindows_448_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27 + 4);
v_allowImportAll_449_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_450_ = lean_ctor_get(v_cfg_418_, 26);
v_fixedToolchain_451_ = lean_ctor_get_uint8(v_cfg_418_, sizeof(void*)*27 + 6);
v_isSharedCheck_458_ = !lean_is_exclusive(v_cfg_418_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v_cfg_418_, 3);
lean_dec(v_unused_459_);
v___x_453_ = v_cfg_418_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_builtinLint_x3f_450_);
lean_inc(v_restoreAllArtifacts_x3f_447_);
lean_inc(v_enableArtifactCache_x3f_446_);
lean_inc(v_readmeFile_444_);
lean_inc(v_licenseFiles_443_);
lean_inc(v_license_442_);
lean_inc(v_homepage_441_);
lean_inc(v_keywords_440_);
lean_inc(v_description_439_);
lean_inc(v_versionTags_438_);
lean_inc(v_version_437_);
lean_inc(v_lintDriverArgs_436_);
lean_inc(v_lintDriver_435_);
lean_inc(v_testDriverArgs_434_);
lean_inc(v_testDriver_433_);
lean_inc(v_buildArchive_431_);
lean_inc(v_releaseRepo_430_);
lean_inc(v_irDir_429_);
lean_inc(v_binDir_428_);
lean_inc(v_nativeLibDir_427_);
lean_inc(v_leanLibDir_426_);
lean_inc(v_buildDir_425_);
lean_inc(v_srcDir_424_);
lean_inc(v_extraDepTargets_422_);
lean_inc(v_toLeanConfig_420_);
lean_inc(v_toWorkspaceConfig_419_);
lean_dec(v_cfg_418_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 3, v_val_417_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_toWorkspaceConfig_419_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_toLeanConfig_420_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_extraDepTargets_422_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_val_417_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_srcDir_424_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_buildDir_425_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_leanLibDir_426_);
lean_ctor_set(v_reuseFailAlloc_457_, 7, v_nativeLibDir_427_);
lean_ctor_set(v_reuseFailAlloc_457_, 8, v_binDir_428_);
lean_ctor_set(v_reuseFailAlloc_457_, 9, v_irDir_429_);
lean_ctor_set(v_reuseFailAlloc_457_, 10, v_releaseRepo_430_);
lean_ctor_set(v_reuseFailAlloc_457_, 11, v_buildArchive_431_);
lean_ctor_set(v_reuseFailAlloc_457_, 12, v_testDriver_433_);
lean_ctor_set(v_reuseFailAlloc_457_, 13, v_testDriverArgs_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 14, v_lintDriver_435_);
lean_ctor_set(v_reuseFailAlloc_457_, 15, v_lintDriverArgs_436_);
lean_ctor_set(v_reuseFailAlloc_457_, 16, v_version_437_);
lean_ctor_set(v_reuseFailAlloc_457_, 17, v_versionTags_438_);
lean_ctor_set(v_reuseFailAlloc_457_, 18, v_description_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 19, v_keywords_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 20, v_homepage_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 21, v_license_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 22, v_licenseFiles_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 23, v_readmeFile_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 24, v_enableArtifactCache_x3f_446_);
lean_ctor_set(v_reuseFailAlloc_457_, 25, v_restoreAllArtifacts_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_457_, 26, v_builtinLint_x3f_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27, v_bootstrap_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27 + 1, v_precompileModules_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27 + 2, v_preferReleaseBuild_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27 + 3, v_reservoir_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27 + 5, v_allowImportAll_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*27 + 6, v_fixedToolchain_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object* v_f_460_, lean_object* v_cfg_461_){
_start:
{
lean_object* v_toWorkspaceConfig_462_; lean_object* v_toLeanConfig_463_; uint8_t v_bootstrap_464_; lean_object* v_extraDepTargets_465_; uint8_t v_precompileModules_466_; lean_object* v_moreGlobalServerArgs_467_; lean_object* v_srcDir_468_; lean_object* v_buildDir_469_; lean_object* v_leanLibDir_470_; lean_object* v_nativeLibDir_471_; lean_object* v_binDir_472_; lean_object* v_irDir_473_; lean_object* v_releaseRepo_474_; lean_object* v_buildArchive_475_; uint8_t v_preferReleaseBuild_476_; lean_object* v_testDriver_477_; lean_object* v_testDriverArgs_478_; lean_object* v_lintDriver_479_; lean_object* v_lintDriverArgs_480_; lean_object* v_version_481_; lean_object* v_versionTags_482_; lean_object* v_description_483_; lean_object* v_keywords_484_; lean_object* v_homepage_485_; lean_object* v_license_486_; lean_object* v_licenseFiles_487_; lean_object* v_readmeFile_488_; uint8_t v_reservoir_489_; lean_object* v_enableArtifactCache_x3f_490_; lean_object* v_restoreAllArtifacts_x3f_491_; uint8_t v_libPrefixOnWindows_492_; uint8_t v_allowImportAll_493_; lean_object* v_builtinLint_x3f_494_; uint8_t v_fixedToolchain_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_toWorkspaceConfig_462_ = lean_ctor_get(v_cfg_461_, 0);
v_toLeanConfig_463_ = lean_ctor_get(v_cfg_461_, 1);
v_bootstrap_464_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27);
v_extraDepTargets_465_ = lean_ctor_get(v_cfg_461_, 2);
v_precompileModules_466_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_467_ = lean_ctor_get(v_cfg_461_, 3);
v_srcDir_468_ = lean_ctor_get(v_cfg_461_, 4);
v_buildDir_469_ = lean_ctor_get(v_cfg_461_, 5);
v_leanLibDir_470_ = lean_ctor_get(v_cfg_461_, 6);
v_nativeLibDir_471_ = lean_ctor_get(v_cfg_461_, 7);
v_binDir_472_ = lean_ctor_get(v_cfg_461_, 8);
v_irDir_473_ = lean_ctor_get(v_cfg_461_, 9);
v_releaseRepo_474_ = lean_ctor_get(v_cfg_461_, 10);
v_buildArchive_475_ = lean_ctor_get(v_cfg_461_, 11);
v_preferReleaseBuild_476_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27 + 2);
v_testDriver_477_ = lean_ctor_get(v_cfg_461_, 12);
v_testDriverArgs_478_ = lean_ctor_get(v_cfg_461_, 13);
v_lintDriver_479_ = lean_ctor_get(v_cfg_461_, 14);
v_lintDriverArgs_480_ = lean_ctor_get(v_cfg_461_, 15);
v_version_481_ = lean_ctor_get(v_cfg_461_, 16);
v_versionTags_482_ = lean_ctor_get(v_cfg_461_, 17);
v_description_483_ = lean_ctor_get(v_cfg_461_, 18);
v_keywords_484_ = lean_ctor_get(v_cfg_461_, 19);
v_homepage_485_ = lean_ctor_get(v_cfg_461_, 20);
v_license_486_ = lean_ctor_get(v_cfg_461_, 21);
v_licenseFiles_487_ = lean_ctor_get(v_cfg_461_, 22);
v_readmeFile_488_ = lean_ctor_get(v_cfg_461_, 23);
v_reservoir_489_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_490_ = lean_ctor_get(v_cfg_461_, 24);
v_restoreAllArtifacts_x3f_491_ = lean_ctor_get(v_cfg_461_, 25);
v_libPrefixOnWindows_492_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27 + 4);
v_allowImportAll_493_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_494_ = lean_ctor_get(v_cfg_461_, 26);
v_fixedToolchain_495_ = lean_ctor_get_uint8(v_cfg_461_, sizeof(void*)*27 + 6);
v_isSharedCheck_503_ = !lean_is_exclusive(v_cfg_461_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v_cfg_461_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_builtinLint_x3f_494_);
lean_inc(v_restoreAllArtifacts_x3f_491_);
lean_inc(v_enableArtifactCache_x3f_490_);
lean_inc(v_readmeFile_488_);
lean_inc(v_licenseFiles_487_);
lean_inc(v_license_486_);
lean_inc(v_homepage_485_);
lean_inc(v_keywords_484_);
lean_inc(v_description_483_);
lean_inc(v_versionTags_482_);
lean_inc(v_version_481_);
lean_inc(v_lintDriverArgs_480_);
lean_inc(v_lintDriver_479_);
lean_inc(v_testDriverArgs_478_);
lean_inc(v_testDriver_477_);
lean_inc(v_buildArchive_475_);
lean_inc(v_releaseRepo_474_);
lean_inc(v_irDir_473_);
lean_inc(v_binDir_472_);
lean_inc(v_nativeLibDir_471_);
lean_inc(v_leanLibDir_470_);
lean_inc(v_buildDir_469_);
lean_inc(v_srcDir_468_);
lean_inc(v_moreGlobalServerArgs_467_);
lean_inc(v_extraDepTargets_465_);
lean_inc(v_toLeanConfig_463_);
lean_inc(v_toWorkspaceConfig_462_);
lean_dec(v_cfg_461_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_apply_1(v_f_460_, v_moreGlobalServerArgs_467_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_toWorkspaceConfig_462_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_toLeanConfig_463_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_extraDepTargets_465_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_srcDir_468_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_buildDir_469_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_leanLibDir_470_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_nativeLibDir_471_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_binDir_472_);
lean_ctor_set(v_reuseFailAlloc_502_, 9, v_irDir_473_);
lean_ctor_set(v_reuseFailAlloc_502_, 10, v_releaseRepo_474_);
lean_ctor_set(v_reuseFailAlloc_502_, 11, v_buildArchive_475_);
lean_ctor_set(v_reuseFailAlloc_502_, 12, v_testDriver_477_);
lean_ctor_set(v_reuseFailAlloc_502_, 13, v_testDriverArgs_478_);
lean_ctor_set(v_reuseFailAlloc_502_, 14, v_lintDriver_479_);
lean_ctor_set(v_reuseFailAlloc_502_, 15, v_lintDriverArgs_480_);
lean_ctor_set(v_reuseFailAlloc_502_, 16, v_version_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 17, v_versionTags_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 18, v_description_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 19, v_keywords_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 20, v_homepage_485_);
lean_ctor_set(v_reuseFailAlloc_502_, 21, v_license_486_);
lean_ctor_set(v_reuseFailAlloc_502_, 22, v_licenseFiles_487_);
lean_ctor_set(v_reuseFailAlloc_502_, 23, v_readmeFile_488_);
lean_ctor_set(v_reuseFailAlloc_502_, 24, v_enableArtifactCache_x3f_490_);
lean_ctor_set(v_reuseFailAlloc_502_, 25, v_restoreAllArtifacts_x3f_491_);
lean_ctor_set(v_reuseFailAlloc_502_, 26, v_builtinLint_x3f_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27, v_bootstrap_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27 + 1, v_precompileModules_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27 + 2, v_preferReleaseBuild_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27 + 3, v_reservoir_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27 + 5, v_allowImportAll_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*27 + 6, v_fixedToolchain_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0));
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* v_x_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(v_x_508_);
lean_dec_ref(v_x_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_519_, lean_object* v_n_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_522_, lean_object* v_n_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_522_, v_n_523_);
lean_dec(v_n_523_);
lean_dec(v_p_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_525_, lean_object* v_n_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_525_, v_n_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_528_, lean_object* v_n_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_528_, v_n_529_);
lean_dec(v_n_529_);
lean_dec(v_p_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_531_, lean_object* v_n_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_531_, v_n_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_534_, lean_object* v_n_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_534_, v_n_535_);
lean_dec(v_n_535_);
lean_dec(v_p_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* v_cfg_537_){
_start:
{
lean_object* v_srcDir_538_; 
v_srcDir_538_ = lean_ctor_get(v_cfg_537_, 4);
lean_inc_ref(v_srcDir_538_);
return v_srcDir_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lake_PackageConfig_srcDir___proj___lam__0(v_cfg_539_);
lean_dec_ref(v_cfg_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* v_val_541_, lean_object* v_cfg_542_){
_start:
{
lean_object* v_toWorkspaceConfig_543_; lean_object* v_toLeanConfig_544_; uint8_t v_bootstrap_545_; lean_object* v_extraDepTargets_546_; uint8_t v_precompileModules_547_; lean_object* v_moreGlobalServerArgs_548_; lean_object* v_buildDir_549_; lean_object* v_leanLibDir_550_; lean_object* v_nativeLibDir_551_; lean_object* v_binDir_552_; lean_object* v_irDir_553_; lean_object* v_releaseRepo_554_; lean_object* v_buildArchive_555_; uint8_t v_preferReleaseBuild_556_; lean_object* v_testDriver_557_; lean_object* v_testDriverArgs_558_; lean_object* v_lintDriver_559_; lean_object* v_lintDriverArgs_560_; lean_object* v_version_561_; lean_object* v_versionTags_562_; lean_object* v_description_563_; lean_object* v_keywords_564_; lean_object* v_homepage_565_; lean_object* v_license_566_; lean_object* v_licenseFiles_567_; lean_object* v_readmeFile_568_; uint8_t v_reservoir_569_; lean_object* v_enableArtifactCache_x3f_570_; lean_object* v_restoreAllArtifacts_x3f_571_; uint8_t v_libPrefixOnWindows_572_; uint8_t v_allowImportAll_573_; lean_object* v_builtinLint_x3f_574_; uint8_t v_fixedToolchain_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_toWorkspaceConfig_543_ = lean_ctor_get(v_cfg_542_, 0);
v_toLeanConfig_544_ = lean_ctor_get(v_cfg_542_, 1);
v_bootstrap_545_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27);
v_extraDepTargets_546_ = lean_ctor_get(v_cfg_542_, 2);
v_precompileModules_547_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_548_ = lean_ctor_get(v_cfg_542_, 3);
v_buildDir_549_ = lean_ctor_get(v_cfg_542_, 5);
v_leanLibDir_550_ = lean_ctor_get(v_cfg_542_, 6);
v_nativeLibDir_551_ = lean_ctor_get(v_cfg_542_, 7);
v_binDir_552_ = lean_ctor_get(v_cfg_542_, 8);
v_irDir_553_ = lean_ctor_get(v_cfg_542_, 9);
v_releaseRepo_554_ = lean_ctor_get(v_cfg_542_, 10);
v_buildArchive_555_ = lean_ctor_get(v_cfg_542_, 11);
v_preferReleaseBuild_556_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27 + 2);
v_testDriver_557_ = lean_ctor_get(v_cfg_542_, 12);
v_testDriverArgs_558_ = lean_ctor_get(v_cfg_542_, 13);
v_lintDriver_559_ = lean_ctor_get(v_cfg_542_, 14);
v_lintDriverArgs_560_ = lean_ctor_get(v_cfg_542_, 15);
v_version_561_ = lean_ctor_get(v_cfg_542_, 16);
v_versionTags_562_ = lean_ctor_get(v_cfg_542_, 17);
v_description_563_ = lean_ctor_get(v_cfg_542_, 18);
v_keywords_564_ = lean_ctor_get(v_cfg_542_, 19);
v_homepage_565_ = lean_ctor_get(v_cfg_542_, 20);
v_license_566_ = lean_ctor_get(v_cfg_542_, 21);
v_licenseFiles_567_ = lean_ctor_get(v_cfg_542_, 22);
v_readmeFile_568_ = lean_ctor_get(v_cfg_542_, 23);
v_reservoir_569_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_570_ = lean_ctor_get(v_cfg_542_, 24);
v_restoreAllArtifacts_x3f_571_ = lean_ctor_get(v_cfg_542_, 25);
v_libPrefixOnWindows_572_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27 + 4);
v_allowImportAll_573_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_574_ = lean_ctor_get(v_cfg_542_, 26);
v_fixedToolchain_575_ = lean_ctor_get_uint8(v_cfg_542_, sizeof(void*)*27 + 6);
v_isSharedCheck_582_ = !lean_is_exclusive(v_cfg_542_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v_cfg_542_, 4);
lean_dec(v_unused_583_);
v___x_577_ = v_cfg_542_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_builtinLint_x3f_574_);
lean_inc(v_restoreAllArtifacts_x3f_571_);
lean_inc(v_enableArtifactCache_x3f_570_);
lean_inc(v_readmeFile_568_);
lean_inc(v_licenseFiles_567_);
lean_inc(v_license_566_);
lean_inc(v_homepage_565_);
lean_inc(v_keywords_564_);
lean_inc(v_description_563_);
lean_inc(v_versionTags_562_);
lean_inc(v_version_561_);
lean_inc(v_lintDriverArgs_560_);
lean_inc(v_lintDriver_559_);
lean_inc(v_testDriverArgs_558_);
lean_inc(v_testDriver_557_);
lean_inc(v_buildArchive_555_);
lean_inc(v_releaseRepo_554_);
lean_inc(v_irDir_553_);
lean_inc(v_binDir_552_);
lean_inc(v_nativeLibDir_551_);
lean_inc(v_leanLibDir_550_);
lean_inc(v_buildDir_549_);
lean_inc(v_moreGlobalServerArgs_548_);
lean_inc(v_extraDepTargets_546_);
lean_inc(v_toLeanConfig_544_);
lean_inc(v_toWorkspaceConfig_543_);
lean_dec(v_cfg_542_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 4, v_val_541_);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_toWorkspaceConfig_543_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_toLeanConfig_544_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_extraDepTargets_546_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_moreGlobalServerArgs_548_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_val_541_);
lean_ctor_set(v_reuseFailAlloc_581_, 5, v_buildDir_549_);
lean_ctor_set(v_reuseFailAlloc_581_, 6, v_leanLibDir_550_);
lean_ctor_set(v_reuseFailAlloc_581_, 7, v_nativeLibDir_551_);
lean_ctor_set(v_reuseFailAlloc_581_, 8, v_binDir_552_);
lean_ctor_set(v_reuseFailAlloc_581_, 9, v_irDir_553_);
lean_ctor_set(v_reuseFailAlloc_581_, 10, v_releaseRepo_554_);
lean_ctor_set(v_reuseFailAlloc_581_, 11, v_buildArchive_555_);
lean_ctor_set(v_reuseFailAlloc_581_, 12, v_testDriver_557_);
lean_ctor_set(v_reuseFailAlloc_581_, 13, v_testDriverArgs_558_);
lean_ctor_set(v_reuseFailAlloc_581_, 14, v_lintDriver_559_);
lean_ctor_set(v_reuseFailAlloc_581_, 15, v_lintDriverArgs_560_);
lean_ctor_set(v_reuseFailAlloc_581_, 16, v_version_561_);
lean_ctor_set(v_reuseFailAlloc_581_, 17, v_versionTags_562_);
lean_ctor_set(v_reuseFailAlloc_581_, 18, v_description_563_);
lean_ctor_set(v_reuseFailAlloc_581_, 19, v_keywords_564_);
lean_ctor_set(v_reuseFailAlloc_581_, 20, v_homepage_565_);
lean_ctor_set(v_reuseFailAlloc_581_, 21, v_license_566_);
lean_ctor_set(v_reuseFailAlloc_581_, 22, v_licenseFiles_567_);
lean_ctor_set(v_reuseFailAlloc_581_, 23, v_readmeFile_568_);
lean_ctor_set(v_reuseFailAlloc_581_, 24, v_enableArtifactCache_x3f_570_);
lean_ctor_set(v_reuseFailAlloc_581_, 25, v_restoreAllArtifacts_x3f_571_);
lean_ctor_set(v_reuseFailAlloc_581_, 26, v_builtinLint_x3f_574_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27, v_bootstrap_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27 + 1, v_precompileModules_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27 + 2, v_preferReleaseBuild_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27 + 3, v_reservoir_569_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_572_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27 + 5, v_allowImportAll_573_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*27 + 6, v_fixedToolchain_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* v_f_584_, lean_object* v_cfg_585_){
_start:
{
lean_object* v_toWorkspaceConfig_586_; lean_object* v_toLeanConfig_587_; uint8_t v_bootstrap_588_; lean_object* v_extraDepTargets_589_; uint8_t v_precompileModules_590_; lean_object* v_moreGlobalServerArgs_591_; lean_object* v_srcDir_592_; lean_object* v_buildDir_593_; lean_object* v_leanLibDir_594_; lean_object* v_nativeLibDir_595_; lean_object* v_binDir_596_; lean_object* v_irDir_597_; lean_object* v_releaseRepo_598_; lean_object* v_buildArchive_599_; uint8_t v_preferReleaseBuild_600_; lean_object* v_testDriver_601_; lean_object* v_testDriverArgs_602_; lean_object* v_lintDriver_603_; lean_object* v_lintDriverArgs_604_; lean_object* v_version_605_; lean_object* v_versionTags_606_; lean_object* v_description_607_; lean_object* v_keywords_608_; lean_object* v_homepage_609_; lean_object* v_license_610_; lean_object* v_licenseFiles_611_; lean_object* v_readmeFile_612_; uint8_t v_reservoir_613_; lean_object* v_enableArtifactCache_x3f_614_; lean_object* v_restoreAllArtifacts_x3f_615_; uint8_t v_libPrefixOnWindows_616_; uint8_t v_allowImportAll_617_; lean_object* v_builtinLint_x3f_618_; uint8_t v_fixedToolchain_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
v_toWorkspaceConfig_586_ = lean_ctor_get(v_cfg_585_, 0);
v_toLeanConfig_587_ = lean_ctor_get(v_cfg_585_, 1);
v_bootstrap_588_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27);
v_extraDepTargets_589_ = lean_ctor_get(v_cfg_585_, 2);
v_precompileModules_590_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_591_ = lean_ctor_get(v_cfg_585_, 3);
v_srcDir_592_ = lean_ctor_get(v_cfg_585_, 4);
v_buildDir_593_ = lean_ctor_get(v_cfg_585_, 5);
v_leanLibDir_594_ = lean_ctor_get(v_cfg_585_, 6);
v_nativeLibDir_595_ = lean_ctor_get(v_cfg_585_, 7);
v_binDir_596_ = lean_ctor_get(v_cfg_585_, 8);
v_irDir_597_ = lean_ctor_get(v_cfg_585_, 9);
v_releaseRepo_598_ = lean_ctor_get(v_cfg_585_, 10);
v_buildArchive_599_ = lean_ctor_get(v_cfg_585_, 11);
v_preferReleaseBuild_600_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27 + 2);
v_testDriver_601_ = lean_ctor_get(v_cfg_585_, 12);
v_testDriverArgs_602_ = lean_ctor_get(v_cfg_585_, 13);
v_lintDriver_603_ = lean_ctor_get(v_cfg_585_, 14);
v_lintDriverArgs_604_ = lean_ctor_get(v_cfg_585_, 15);
v_version_605_ = lean_ctor_get(v_cfg_585_, 16);
v_versionTags_606_ = lean_ctor_get(v_cfg_585_, 17);
v_description_607_ = lean_ctor_get(v_cfg_585_, 18);
v_keywords_608_ = lean_ctor_get(v_cfg_585_, 19);
v_homepage_609_ = lean_ctor_get(v_cfg_585_, 20);
v_license_610_ = lean_ctor_get(v_cfg_585_, 21);
v_licenseFiles_611_ = lean_ctor_get(v_cfg_585_, 22);
v_readmeFile_612_ = lean_ctor_get(v_cfg_585_, 23);
v_reservoir_613_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_614_ = lean_ctor_get(v_cfg_585_, 24);
v_restoreAllArtifacts_x3f_615_ = lean_ctor_get(v_cfg_585_, 25);
v_libPrefixOnWindows_616_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27 + 4);
v_allowImportAll_617_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_618_ = lean_ctor_get(v_cfg_585_, 26);
v_fixedToolchain_619_ = lean_ctor_get_uint8(v_cfg_585_, sizeof(void*)*27 + 6);
v_isSharedCheck_627_ = !lean_is_exclusive(v_cfg_585_);
if (v_isSharedCheck_627_ == 0)
{
v___x_621_ = v_cfg_585_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_builtinLint_x3f_618_);
lean_inc(v_restoreAllArtifacts_x3f_615_);
lean_inc(v_enableArtifactCache_x3f_614_);
lean_inc(v_readmeFile_612_);
lean_inc(v_licenseFiles_611_);
lean_inc(v_license_610_);
lean_inc(v_homepage_609_);
lean_inc(v_keywords_608_);
lean_inc(v_description_607_);
lean_inc(v_versionTags_606_);
lean_inc(v_version_605_);
lean_inc(v_lintDriverArgs_604_);
lean_inc(v_lintDriver_603_);
lean_inc(v_testDriverArgs_602_);
lean_inc(v_testDriver_601_);
lean_inc(v_buildArchive_599_);
lean_inc(v_releaseRepo_598_);
lean_inc(v_irDir_597_);
lean_inc(v_binDir_596_);
lean_inc(v_nativeLibDir_595_);
lean_inc(v_leanLibDir_594_);
lean_inc(v_buildDir_593_);
lean_inc(v_srcDir_592_);
lean_inc(v_moreGlobalServerArgs_591_);
lean_inc(v_extraDepTargets_589_);
lean_inc(v_toLeanConfig_587_);
lean_inc(v_toWorkspaceConfig_586_);
lean_dec(v_cfg_585_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_apply_1(v_f_584_, v_srcDir_592_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_toWorkspaceConfig_586_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_toLeanConfig_587_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_extraDepTargets_589_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_moreGlobalServerArgs_591_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_buildDir_593_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_leanLibDir_594_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_nativeLibDir_595_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_binDir_596_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_irDir_597_);
lean_ctor_set(v_reuseFailAlloc_626_, 10, v_releaseRepo_598_);
lean_ctor_set(v_reuseFailAlloc_626_, 11, v_buildArchive_599_);
lean_ctor_set(v_reuseFailAlloc_626_, 12, v_testDriver_601_);
lean_ctor_set(v_reuseFailAlloc_626_, 13, v_testDriverArgs_602_);
lean_ctor_set(v_reuseFailAlloc_626_, 14, v_lintDriver_603_);
lean_ctor_set(v_reuseFailAlloc_626_, 15, v_lintDriverArgs_604_);
lean_ctor_set(v_reuseFailAlloc_626_, 16, v_version_605_);
lean_ctor_set(v_reuseFailAlloc_626_, 17, v_versionTags_606_);
lean_ctor_set(v_reuseFailAlloc_626_, 18, v_description_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 19, v_keywords_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 20, v_homepage_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 21, v_license_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 22, v_licenseFiles_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 23, v_readmeFile_612_);
lean_ctor_set(v_reuseFailAlloc_626_, 24, v_enableArtifactCache_x3f_614_);
lean_ctor_set(v_reuseFailAlloc_626_, 25, v_restoreAllArtifacts_x3f_615_);
lean_ctor_set(v_reuseFailAlloc_626_, 26, v_builtinLint_x3f_618_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27, v_bootstrap_588_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27 + 1, v_precompileModules_590_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27 + 2, v_preferReleaseBuild_600_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27 + 3, v_reservoir_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_616_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27 + 5, v_allowImportAll_617_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*27 + 6, v_fixedToolchain_619_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* v_x_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lake_PackageConfig_srcDir___proj___lam__3(v_x_630_);
lean_dec_ref(v_x_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_641_, lean_object* v_n_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_644_, lean_object* v_n_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lake_PackageConfig_srcDir___proj(v_p_644_, v_n_645_);
lean_dec(v_n_645_);
lean_dec(v_p_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_647_, lean_object* v_n_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lake_PackageConfig_srcDir___proj(v_p_647_, v_n_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_650_, lean_object* v_n_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_650_, v_n_651_);
lean_dec(v_n_651_);
lean_dec(v_p_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* v_cfg_653_){
_start:
{
lean_object* v_buildDir_654_; 
v_buildDir_654_ = lean_ctor_get(v_cfg_653_, 5);
lean_inc_ref(v_buildDir_654_);
return v_buildDir_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* v_cfg_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lake_PackageConfig_buildDir___proj___lam__0(v_cfg_655_);
lean_dec_ref(v_cfg_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* v_val_657_, lean_object* v_cfg_658_){
_start:
{
lean_object* v_toWorkspaceConfig_659_; lean_object* v_toLeanConfig_660_; uint8_t v_bootstrap_661_; lean_object* v_extraDepTargets_662_; uint8_t v_precompileModules_663_; lean_object* v_moreGlobalServerArgs_664_; lean_object* v_srcDir_665_; lean_object* v_leanLibDir_666_; lean_object* v_nativeLibDir_667_; lean_object* v_binDir_668_; lean_object* v_irDir_669_; lean_object* v_releaseRepo_670_; lean_object* v_buildArchive_671_; uint8_t v_preferReleaseBuild_672_; lean_object* v_testDriver_673_; lean_object* v_testDriverArgs_674_; lean_object* v_lintDriver_675_; lean_object* v_lintDriverArgs_676_; lean_object* v_version_677_; lean_object* v_versionTags_678_; lean_object* v_description_679_; lean_object* v_keywords_680_; lean_object* v_homepage_681_; lean_object* v_license_682_; lean_object* v_licenseFiles_683_; lean_object* v_readmeFile_684_; uint8_t v_reservoir_685_; lean_object* v_enableArtifactCache_x3f_686_; lean_object* v_restoreAllArtifacts_x3f_687_; uint8_t v_libPrefixOnWindows_688_; uint8_t v_allowImportAll_689_; lean_object* v_builtinLint_x3f_690_; uint8_t v_fixedToolchain_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_toWorkspaceConfig_659_ = lean_ctor_get(v_cfg_658_, 0);
v_toLeanConfig_660_ = lean_ctor_get(v_cfg_658_, 1);
v_bootstrap_661_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27);
v_extraDepTargets_662_ = lean_ctor_get(v_cfg_658_, 2);
v_precompileModules_663_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_664_ = lean_ctor_get(v_cfg_658_, 3);
v_srcDir_665_ = lean_ctor_get(v_cfg_658_, 4);
v_leanLibDir_666_ = lean_ctor_get(v_cfg_658_, 6);
v_nativeLibDir_667_ = lean_ctor_get(v_cfg_658_, 7);
v_binDir_668_ = lean_ctor_get(v_cfg_658_, 8);
v_irDir_669_ = lean_ctor_get(v_cfg_658_, 9);
v_releaseRepo_670_ = lean_ctor_get(v_cfg_658_, 10);
v_buildArchive_671_ = lean_ctor_get(v_cfg_658_, 11);
v_preferReleaseBuild_672_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27 + 2);
v_testDriver_673_ = lean_ctor_get(v_cfg_658_, 12);
v_testDriverArgs_674_ = lean_ctor_get(v_cfg_658_, 13);
v_lintDriver_675_ = lean_ctor_get(v_cfg_658_, 14);
v_lintDriverArgs_676_ = lean_ctor_get(v_cfg_658_, 15);
v_version_677_ = lean_ctor_get(v_cfg_658_, 16);
v_versionTags_678_ = lean_ctor_get(v_cfg_658_, 17);
v_description_679_ = lean_ctor_get(v_cfg_658_, 18);
v_keywords_680_ = lean_ctor_get(v_cfg_658_, 19);
v_homepage_681_ = lean_ctor_get(v_cfg_658_, 20);
v_license_682_ = lean_ctor_get(v_cfg_658_, 21);
v_licenseFiles_683_ = lean_ctor_get(v_cfg_658_, 22);
v_readmeFile_684_ = lean_ctor_get(v_cfg_658_, 23);
v_reservoir_685_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_686_ = lean_ctor_get(v_cfg_658_, 24);
v_restoreAllArtifacts_x3f_687_ = lean_ctor_get(v_cfg_658_, 25);
v_libPrefixOnWindows_688_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27 + 4);
v_allowImportAll_689_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_690_ = lean_ctor_get(v_cfg_658_, 26);
v_fixedToolchain_691_ = lean_ctor_get_uint8(v_cfg_658_, sizeof(void*)*27 + 6);
v_isSharedCheck_698_ = !lean_is_exclusive(v_cfg_658_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_cfg_658_, 5);
lean_dec(v_unused_699_);
v___x_693_ = v_cfg_658_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_builtinLint_x3f_690_);
lean_inc(v_restoreAllArtifacts_x3f_687_);
lean_inc(v_enableArtifactCache_x3f_686_);
lean_inc(v_readmeFile_684_);
lean_inc(v_licenseFiles_683_);
lean_inc(v_license_682_);
lean_inc(v_homepage_681_);
lean_inc(v_keywords_680_);
lean_inc(v_description_679_);
lean_inc(v_versionTags_678_);
lean_inc(v_version_677_);
lean_inc(v_lintDriverArgs_676_);
lean_inc(v_lintDriver_675_);
lean_inc(v_testDriverArgs_674_);
lean_inc(v_testDriver_673_);
lean_inc(v_buildArchive_671_);
lean_inc(v_releaseRepo_670_);
lean_inc(v_irDir_669_);
lean_inc(v_binDir_668_);
lean_inc(v_nativeLibDir_667_);
lean_inc(v_leanLibDir_666_);
lean_inc(v_srcDir_665_);
lean_inc(v_moreGlobalServerArgs_664_);
lean_inc(v_extraDepTargets_662_);
lean_inc(v_toLeanConfig_660_);
lean_inc(v_toWorkspaceConfig_659_);
lean_dec(v_cfg_658_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 5, v_val_657_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_toWorkspaceConfig_659_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_toLeanConfig_660_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_extraDepTargets_662_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_moreGlobalServerArgs_664_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_srcDir_665_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v_val_657_);
lean_ctor_set(v_reuseFailAlloc_697_, 6, v_leanLibDir_666_);
lean_ctor_set(v_reuseFailAlloc_697_, 7, v_nativeLibDir_667_);
lean_ctor_set(v_reuseFailAlloc_697_, 8, v_binDir_668_);
lean_ctor_set(v_reuseFailAlloc_697_, 9, v_irDir_669_);
lean_ctor_set(v_reuseFailAlloc_697_, 10, v_releaseRepo_670_);
lean_ctor_set(v_reuseFailAlloc_697_, 11, v_buildArchive_671_);
lean_ctor_set(v_reuseFailAlloc_697_, 12, v_testDriver_673_);
lean_ctor_set(v_reuseFailAlloc_697_, 13, v_testDriverArgs_674_);
lean_ctor_set(v_reuseFailAlloc_697_, 14, v_lintDriver_675_);
lean_ctor_set(v_reuseFailAlloc_697_, 15, v_lintDriverArgs_676_);
lean_ctor_set(v_reuseFailAlloc_697_, 16, v_version_677_);
lean_ctor_set(v_reuseFailAlloc_697_, 17, v_versionTags_678_);
lean_ctor_set(v_reuseFailAlloc_697_, 18, v_description_679_);
lean_ctor_set(v_reuseFailAlloc_697_, 19, v_keywords_680_);
lean_ctor_set(v_reuseFailAlloc_697_, 20, v_homepage_681_);
lean_ctor_set(v_reuseFailAlloc_697_, 21, v_license_682_);
lean_ctor_set(v_reuseFailAlloc_697_, 22, v_licenseFiles_683_);
lean_ctor_set(v_reuseFailAlloc_697_, 23, v_readmeFile_684_);
lean_ctor_set(v_reuseFailAlloc_697_, 24, v_enableArtifactCache_x3f_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 25, v_restoreAllArtifacts_x3f_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 26, v_builtinLint_x3f_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27, v_bootstrap_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27 + 1, v_precompileModules_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27 + 2, v_preferReleaseBuild_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27 + 3, v_reservoir_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_688_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27 + 5, v_allowImportAll_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*27 + 6, v_fixedToolchain_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* v_f_700_, lean_object* v_cfg_701_){
_start:
{
lean_object* v_toWorkspaceConfig_702_; lean_object* v_toLeanConfig_703_; uint8_t v_bootstrap_704_; lean_object* v_extraDepTargets_705_; uint8_t v_precompileModules_706_; lean_object* v_moreGlobalServerArgs_707_; lean_object* v_srcDir_708_; lean_object* v_buildDir_709_; lean_object* v_leanLibDir_710_; lean_object* v_nativeLibDir_711_; lean_object* v_binDir_712_; lean_object* v_irDir_713_; lean_object* v_releaseRepo_714_; lean_object* v_buildArchive_715_; uint8_t v_preferReleaseBuild_716_; lean_object* v_testDriver_717_; lean_object* v_testDriverArgs_718_; lean_object* v_lintDriver_719_; lean_object* v_lintDriverArgs_720_; lean_object* v_version_721_; lean_object* v_versionTags_722_; lean_object* v_description_723_; lean_object* v_keywords_724_; lean_object* v_homepage_725_; lean_object* v_license_726_; lean_object* v_licenseFiles_727_; lean_object* v_readmeFile_728_; uint8_t v_reservoir_729_; lean_object* v_enableArtifactCache_x3f_730_; lean_object* v_restoreAllArtifacts_x3f_731_; uint8_t v_libPrefixOnWindows_732_; uint8_t v_allowImportAll_733_; lean_object* v_builtinLint_x3f_734_; uint8_t v_fixedToolchain_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_toWorkspaceConfig_702_ = lean_ctor_get(v_cfg_701_, 0);
v_toLeanConfig_703_ = lean_ctor_get(v_cfg_701_, 1);
v_bootstrap_704_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27);
v_extraDepTargets_705_ = lean_ctor_get(v_cfg_701_, 2);
v_precompileModules_706_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_707_ = lean_ctor_get(v_cfg_701_, 3);
v_srcDir_708_ = lean_ctor_get(v_cfg_701_, 4);
v_buildDir_709_ = lean_ctor_get(v_cfg_701_, 5);
v_leanLibDir_710_ = lean_ctor_get(v_cfg_701_, 6);
v_nativeLibDir_711_ = lean_ctor_get(v_cfg_701_, 7);
v_binDir_712_ = lean_ctor_get(v_cfg_701_, 8);
v_irDir_713_ = lean_ctor_get(v_cfg_701_, 9);
v_releaseRepo_714_ = lean_ctor_get(v_cfg_701_, 10);
v_buildArchive_715_ = lean_ctor_get(v_cfg_701_, 11);
v_preferReleaseBuild_716_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27 + 2);
v_testDriver_717_ = lean_ctor_get(v_cfg_701_, 12);
v_testDriverArgs_718_ = lean_ctor_get(v_cfg_701_, 13);
v_lintDriver_719_ = lean_ctor_get(v_cfg_701_, 14);
v_lintDriverArgs_720_ = lean_ctor_get(v_cfg_701_, 15);
v_version_721_ = lean_ctor_get(v_cfg_701_, 16);
v_versionTags_722_ = lean_ctor_get(v_cfg_701_, 17);
v_description_723_ = lean_ctor_get(v_cfg_701_, 18);
v_keywords_724_ = lean_ctor_get(v_cfg_701_, 19);
v_homepage_725_ = lean_ctor_get(v_cfg_701_, 20);
v_license_726_ = lean_ctor_get(v_cfg_701_, 21);
v_licenseFiles_727_ = lean_ctor_get(v_cfg_701_, 22);
v_readmeFile_728_ = lean_ctor_get(v_cfg_701_, 23);
v_reservoir_729_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_730_ = lean_ctor_get(v_cfg_701_, 24);
v_restoreAllArtifacts_x3f_731_ = lean_ctor_get(v_cfg_701_, 25);
v_libPrefixOnWindows_732_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27 + 4);
v_allowImportAll_733_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_734_ = lean_ctor_get(v_cfg_701_, 26);
v_fixedToolchain_735_ = lean_ctor_get_uint8(v_cfg_701_, sizeof(void*)*27 + 6);
v_isSharedCheck_743_ = !lean_is_exclusive(v_cfg_701_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v_cfg_701_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_builtinLint_x3f_734_);
lean_inc(v_restoreAllArtifacts_x3f_731_);
lean_inc(v_enableArtifactCache_x3f_730_);
lean_inc(v_readmeFile_728_);
lean_inc(v_licenseFiles_727_);
lean_inc(v_license_726_);
lean_inc(v_homepage_725_);
lean_inc(v_keywords_724_);
lean_inc(v_description_723_);
lean_inc(v_versionTags_722_);
lean_inc(v_version_721_);
lean_inc(v_lintDriverArgs_720_);
lean_inc(v_lintDriver_719_);
lean_inc(v_testDriverArgs_718_);
lean_inc(v_testDriver_717_);
lean_inc(v_buildArchive_715_);
lean_inc(v_releaseRepo_714_);
lean_inc(v_irDir_713_);
lean_inc(v_binDir_712_);
lean_inc(v_nativeLibDir_711_);
lean_inc(v_leanLibDir_710_);
lean_inc(v_buildDir_709_);
lean_inc(v_srcDir_708_);
lean_inc(v_moreGlobalServerArgs_707_);
lean_inc(v_extraDepTargets_705_);
lean_inc(v_toLeanConfig_703_);
lean_inc(v_toWorkspaceConfig_702_);
lean_dec(v_cfg_701_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_apply_1(v_f_700_, v_buildDir_709_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 5, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_toWorkspaceConfig_702_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_toLeanConfig_703_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_extraDepTargets_705_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_moreGlobalServerArgs_707_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_srcDir_708_);
lean_ctor_set(v_reuseFailAlloc_742_, 5, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 6, v_leanLibDir_710_);
lean_ctor_set(v_reuseFailAlloc_742_, 7, v_nativeLibDir_711_);
lean_ctor_set(v_reuseFailAlloc_742_, 8, v_binDir_712_);
lean_ctor_set(v_reuseFailAlloc_742_, 9, v_irDir_713_);
lean_ctor_set(v_reuseFailAlloc_742_, 10, v_releaseRepo_714_);
lean_ctor_set(v_reuseFailAlloc_742_, 11, v_buildArchive_715_);
lean_ctor_set(v_reuseFailAlloc_742_, 12, v_testDriver_717_);
lean_ctor_set(v_reuseFailAlloc_742_, 13, v_testDriverArgs_718_);
lean_ctor_set(v_reuseFailAlloc_742_, 14, v_lintDriver_719_);
lean_ctor_set(v_reuseFailAlloc_742_, 15, v_lintDriverArgs_720_);
lean_ctor_set(v_reuseFailAlloc_742_, 16, v_version_721_);
lean_ctor_set(v_reuseFailAlloc_742_, 17, v_versionTags_722_);
lean_ctor_set(v_reuseFailAlloc_742_, 18, v_description_723_);
lean_ctor_set(v_reuseFailAlloc_742_, 19, v_keywords_724_);
lean_ctor_set(v_reuseFailAlloc_742_, 20, v_homepage_725_);
lean_ctor_set(v_reuseFailAlloc_742_, 21, v_license_726_);
lean_ctor_set(v_reuseFailAlloc_742_, 22, v_licenseFiles_727_);
lean_ctor_set(v_reuseFailAlloc_742_, 23, v_readmeFile_728_);
lean_ctor_set(v_reuseFailAlloc_742_, 24, v_enableArtifactCache_x3f_730_);
lean_ctor_set(v_reuseFailAlloc_742_, 25, v_restoreAllArtifacts_x3f_731_);
lean_ctor_set(v_reuseFailAlloc_742_, 26, v_builtinLint_x3f_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27, v_bootstrap_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27 + 1, v_precompileModules_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27 + 2, v_preferReleaseBuild_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27 + 3, v_reservoir_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27 + 5, v_allowImportAll_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_742_, sizeof(void*)*27 + 6, v_fixedToolchain_735_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lake_defaultBuildDir;
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* v_x_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lake_PackageConfig_buildDir___proj___lam__3(v_x_746_);
lean_dec_ref(v_x_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_757_, lean_object* v_n_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_760_, lean_object* v_n_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lake_PackageConfig_buildDir___proj(v_p_760_, v_n_761_);
lean_dec(v_n_761_);
lean_dec(v_p_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_763_, lean_object* v_n_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lake_PackageConfig_buildDir___proj(v_p_763_, v_n_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_766_, lean_object* v_n_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_766_, v_n_767_);
lean_dec(v_n_767_);
lean_dec(v_p_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* v_cfg_769_){
_start:
{
lean_object* v_leanLibDir_770_; 
v_leanLibDir_770_ = lean_ctor_get(v_cfg_769_, 6);
lean_inc_ref(v_leanLibDir_770_);
return v_leanLibDir_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* v_cfg_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lake_PackageConfig_leanLibDir___proj___lam__0(v_cfg_771_);
lean_dec_ref(v_cfg_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* v_val_773_, lean_object* v_cfg_774_){
_start:
{
lean_object* v_toWorkspaceConfig_775_; lean_object* v_toLeanConfig_776_; uint8_t v_bootstrap_777_; lean_object* v_extraDepTargets_778_; uint8_t v_precompileModules_779_; lean_object* v_moreGlobalServerArgs_780_; lean_object* v_srcDir_781_; lean_object* v_buildDir_782_; lean_object* v_nativeLibDir_783_; lean_object* v_binDir_784_; lean_object* v_irDir_785_; lean_object* v_releaseRepo_786_; lean_object* v_buildArchive_787_; uint8_t v_preferReleaseBuild_788_; lean_object* v_testDriver_789_; lean_object* v_testDriverArgs_790_; lean_object* v_lintDriver_791_; lean_object* v_lintDriverArgs_792_; lean_object* v_version_793_; lean_object* v_versionTags_794_; lean_object* v_description_795_; lean_object* v_keywords_796_; lean_object* v_homepage_797_; lean_object* v_license_798_; lean_object* v_licenseFiles_799_; lean_object* v_readmeFile_800_; uint8_t v_reservoir_801_; lean_object* v_enableArtifactCache_x3f_802_; lean_object* v_restoreAllArtifacts_x3f_803_; uint8_t v_libPrefixOnWindows_804_; uint8_t v_allowImportAll_805_; lean_object* v_builtinLint_x3f_806_; uint8_t v_fixedToolchain_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
v_toWorkspaceConfig_775_ = lean_ctor_get(v_cfg_774_, 0);
v_toLeanConfig_776_ = lean_ctor_get(v_cfg_774_, 1);
v_bootstrap_777_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27);
v_extraDepTargets_778_ = lean_ctor_get(v_cfg_774_, 2);
v_precompileModules_779_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_780_ = lean_ctor_get(v_cfg_774_, 3);
v_srcDir_781_ = lean_ctor_get(v_cfg_774_, 4);
v_buildDir_782_ = lean_ctor_get(v_cfg_774_, 5);
v_nativeLibDir_783_ = lean_ctor_get(v_cfg_774_, 7);
v_binDir_784_ = lean_ctor_get(v_cfg_774_, 8);
v_irDir_785_ = lean_ctor_get(v_cfg_774_, 9);
v_releaseRepo_786_ = lean_ctor_get(v_cfg_774_, 10);
v_buildArchive_787_ = lean_ctor_get(v_cfg_774_, 11);
v_preferReleaseBuild_788_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27 + 2);
v_testDriver_789_ = lean_ctor_get(v_cfg_774_, 12);
v_testDriverArgs_790_ = lean_ctor_get(v_cfg_774_, 13);
v_lintDriver_791_ = lean_ctor_get(v_cfg_774_, 14);
v_lintDriverArgs_792_ = lean_ctor_get(v_cfg_774_, 15);
v_version_793_ = lean_ctor_get(v_cfg_774_, 16);
v_versionTags_794_ = lean_ctor_get(v_cfg_774_, 17);
v_description_795_ = lean_ctor_get(v_cfg_774_, 18);
v_keywords_796_ = lean_ctor_get(v_cfg_774_, 19);
v_homepage_797_ = lean_ctor_get(v_cfg_774_, 20);
v_license_798_ = lean_ctor_get(v_cfg_774_, 21);
v_licenseFiles_799_ = lean_ctor_get(v_cfg_774_, 22);
v_readmeFile_800_ = lean_ctor_get(v_cfg_774_, 23);
v_reservoir_801_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_802_ = lean_ctor_get(v_cfg_774_, 24);
v_restoreAllArtifacts_x3f_803_ = lean_ctor_get(v_cfg_774_, 25);
v_libPrefixOnWindows_804_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27 + 4);
v_allowImportAll_805_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_806_ = lean_ctor_get(v_cfg_774_, 26);
v_fixedToolchain_807_ = lean_ctor_get_uint8(v_cfg_774_, sizeof(void*)*27 + 6);
v_isSharedCheck_814_ = !lean_is_exclusive(v_cfg_774_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_cfg_774_, 6);
lean_dec(v_unused_815_);
v___x_809_ = v_cfg_774_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_builtinLint_x3f_806_);
lean_inc(v_restoreAllArtifacts_x3f_803_);
lean_inc(v_enableArtifactCache_x3f_802_);
lean_inc(v_readmeFile_800_);
lean_inc(v_licenseFiles_799_);
lean_inc(v_license_798_);
lean_inc(v_homepage_797_);
lean_inc(v_keywords_796_);
lean_inc(v_description_795_);
lean_inc(v_versionTags_794_);
lean_inc(v_version_793_);
lean_inc(v_lintDriverArgs_792_);
lean_inc(v_lintDriver_791_);
lean_inc(v_testDriverArgs_790_);
lean_inc(v_testDriver_789_);
lean_inc(v_buildArchive_787_);
lean_inc(v_releaseRepo_786_);
lean_inc(v_irDir_785_);
lean_inc(v_binDir_784_);
lean_inc(v_nativeLibDir_783_);
lean_inc(v_buildDir_782_);
lean_inc(v_srcDir_781_);
lean_inc(v_moreGlobalServerArgs_780_);
lean_inc(v_extraDepTargets_778_);
lean_inc(v_toLeanConfig_776_);
lean_inc(v_toWorkspaceConfig_775_);
lean_dec(v_cfg_774_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 6, v_val_773_);
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_toWorkspaceConfig_775_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_toLeanConfig_776_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_extraDepTargets_778_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_moreGlobalServerArgs_780_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_srcDir_781_);
lean_ctor_set(v_reuseFailAlloc_813_, 5, v_buildDir_782_);
lean_ctor_set(v_reuseFailAlloc_813_, 6, v_val_773_);
lean_ctor_set(v_reuseFailAlloc_813_, 7, v_nativeLibDir_783_);
lean_ctor_set(v_reuseFailAlloc_813_, 8, v_binDir_784_);
lean_ctor_set(v_reuseFailAlloc_813_, 9, v_irDir_785_);
lean_ctor_set(v_reuseFailAlloc_813_, 10, v_releaseRepo_786_);
lean_ctor_set(v_reuseFailAlloc_813_, 11, v_buildArchive_787_);
lean_ctor_set(v_reuseFailAlloc_813_, 12, v_testDriver_789_);
lean_ctor_set(v_reuseFailAlloc_813_, 13, v_testDriverArgs_790_);
lean_ctor_set(v_reuseFailAlloc_813_, 14, v_lintDriver_791_);
lean_ctor_set(v_reuseFailAlloc_813_, 15, v_lintDriverArgs_792_);
lean_ctor_set(v_reuseFailAlloc_813_, 16, v_version_793_);
lean_ctor_set(v_reuseFailAlloc_813_, 17, v_versionTags_794_);
lean_ctor_set(v_reuseFailAlloc_813_, 18, v_description_795_);
lean_ctor_set(v_reuseFailAlloc_813_, 19, v_keywords_796_);
lean_ctor_set(v_reuseFailAlloc_813_, 20, v_homepage_797_);
lean_ctor_set(v_reuseFailAlloc_813_, 21, v_license_798_);
lean_ctor_set(v_reuseFailAlloc_813_, 22, v_licenseFiles_799_);
lean_ctor_set(v_reuseFailAlloc_813_, 23, v_readmeFile_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 24, v_enableArtifactCache_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 25, v_restoreAllArtifacts_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 26, v_builtinLint_x3f_806_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27, v_bootstrap_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27 + 1, v_precompileModules_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27 + 2, v_preferReleaseBuild_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27 + 3, v_reservoir_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27 + 5, v_allowImportAll_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*27 + 6, v_fixedToolchain_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* v_f_816_, lean_object* v_cfg_817_){
_start:
{
lean_object* v_toWorkspaceConfig_818_; lean_object* v_toLeanConfig_819_; uint8_t v_bootstrap_820_; lean_object* v_extraDepTargets_821_; uint8_t v_precompileModules_822_; lean_object* v_moreGlobalServerArgs_823_; lean_object* v_srcDir_824_; lean_object* v_buildDir_825_; lean_object* v_leanLibDir_826_; lean_object* v_nativeLibDir_827_; lean_object* v_binDir_828_; lean_object* v_irDir_829_; lean_object* v_releaseRepo_830_; lean_object* v_buildArchive_831_; uint8_t v_preferReleaseBuild_832_; lean_object* v_testDriver_833_; lean_object* v_testDriverArgs_834_; lean_object* v_lintDriver_835_; lean_object* v_lintDriverArgs_836_; lean_object* v_version_837_; lean_object* v_versionTags_838_; lean_object* v_description_839_; lean_object* v_keywords_840_; lean_object* v_homepage_841_; lean_object* v_license_842_; lean_object* v_licenseFiles_843_; lean_object* v_readmeFile_844_; uint8_t v_reservoir_845_; lean_object* v_enableArtifactCache_x3f_846_; lean_object* v_restoreAllArtifacts_x3f_847_; uint8_t v_libPrefixOnWindows_848_; uint8_t v_allowImportAll_849_; lean_object* v_builtinLint_x3f_850_; uint8_t v_fixedToolchain_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_toWorkspaceConfig_818_ = lean_ctor_get(v_cfg_817_, 0);
v_toLeanConfig_819_ = lean_ctor_get(v_cfg_817_, 1);
v_bootstrap_820_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27);
v_extraDepTargets_821_ = lean_ctor_get(v_cfg_817_, 2);
v_precompileModules_822_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_823_ = lean_ctor_get(v_cfg_817_, 3);
v_srcDir_824_ = lean_ctor_get(v_cfg_817_, 4);
v_buildDir_825_ = lean_ctor_get(v_cfg_817_, 5);
v_leanLibDir_826_ = lean_ctor_get(v_cfg_817_, 6);
v_nativeLibDir_827_ = lean_ctor_get(v_cfg_817_, 7);
v_binDir_828_ = lean_ctor_get(v_cfg_817_, 8);
v_irDir_829_ = lean_ctor_get(v_cfg_817_, 9);
v_releaseRepo_830_ = lean_ctor_get(v_cfg_817_, 10);
v_buildArchive_831_ = lean_ctor_get(v_cfg_817_, 11);
v_preferReleaseBuild_832_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27 + 2);
v_testDriver_833_ = lean_ctor_get(v_cfg_817_, 12);
v_testDriverArgs_834_ = lean_ctor_get(v_cfg_817_, 13);
v_lintDriver_835_ = lean_ctor_get(v_cfg_817_, 14);
v_lintDriverArgs_836_ = lean_ctor_get(v_cfg_817_, 15);
v_version_837_ = lean_ctor_get(v_cfg_817_, 16);
v_versionTags_838_ = lean_ctor_get(v_cfg_817_, 17);
v_description_839_ = lean_ctor_get(v_cfg_817_, 18);
v_keywords_840_ = lean_ctor_get(v_cfg_817_, 19);
v_homepage_841_ = lean_ctor_get(v_cfg_817_, 20);
v_license_842_ = lean_ctor_get(v_cfg_817_, 21);
v_licenseFiles_843_ = lean_ctor_get(v_cfg_817_, 22);
v_readmeFile_844_ = lean_ctor_get(v_cfg_817_, 23);
v_reservoir_845_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_846_ = lean_ctor_get(v_cfg_817_, 24);
v_restoreAllArtifacts_x3f_847_ = lean_ctor_get(v_cfg_817_, 25);
v_libPrefixOnWindows_848_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27 + 4);
v_allowImportAll_849_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_850_ = lean_ctor_get(v_cfg_817_, 26);
v_fixedToolchain_851_ = lean_ctor_get_uint8(v_cfg_817_, sizeof(void*)*27 + 6);
v_isSharedCheck_859_ = !lean_is_exclusive(v_cfg_817_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_cfg_817_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_builtinLint_x3f_850_);
lean_inc(v_restoreAllArtifacts_x3f_847_);
lean_inc(v_enableArtifactCache_x3f_846_);
lean_inc(v_readmeFile_844_);
lean_inc(v_licenseFiles_843_);
lean_inc(v_license_842_);
lean_inc(v_homepage_841_);
lean_inc(v_keywords_840_);
lean_inc(v_description_839_);
lean_inc(v_versionTags_838_);
lean_inc(v_version_837_);
lean_inc(v_lintDriverArgs_836_);
lean_inc(v_lintDriver_835_);
lean_inc(v_testDriverArgs_834_);
lean_inc(v_testDriver_833_);
lean_inc(v_buildArchive_831_);
lean_inc(v_releaseRepo_830_);
lean_inc(v_irDir_829_);
lean_inc(v_binDir_828_);
lean_inc(v_nativeLibDir_827_);
lean_inc(v_leanLibDir_826_);
lean_inc(v_buildDir_825_);
lean_inc(v_srcDir_824_);
lean_inc(v_moreGlobalServerArgs_823_);
lean_inc(v_extraDepTargets_821_);
lean_inc(v_toLeanConfig_819_);
lean_inc(v_toWorkspaceConfig_818_);
lean_dec(v_cfg_817_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_apply_1(v_f_816_, v_leanLibDir_826_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 6, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_toWorkspaceConfig_818_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_toLeanConfig_819_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_extraDepTargets_821_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_moreGlobalServerArgs_823_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_srcDir_824_);
lean_ctor_set(v_reuseFailAlloc_858_, 5, v_buildDir_825_);
lean_ctor_set(v_reuseFailAlloc_858_, 6, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 7, v_nativeLibDir_827_);
lean_ctor_set(v_reuseFailAlloc_858_, 8, v_binDir_828_);
lean_ctor_set(v_reuseFailAlloc_858_, 9, v_irDir_829_);
lean_ctor_set(v_reuseFailAlloc_858_, 10, v_releaseRepo_830_);
lean_ctor_set(v_reuseFailAlloc_858_, 11, v_buildArchive_831_);
lean_ctor_set(v_reuseFailAlloc_858_, 12, v_testDriver_833_);
lean_ctor_set(v_reuseFailAlloc_858_, 13, v_testDriverArgs_834_);
lean_ctor_set(v_reuseFailAlloc_858_, 14, v_lintDriver_835_);
lean_ctor_set(v_reuseFailAlloc_858_, 15, v_lintDriverArgs_836_);
lean_ctor_set(v_reuseFailAlloc_858_, 16, v_version_837_);
lean_ctor_set(v_reuseFailAlloc_858_, 17, v_versionTags_838_);
lean_ctor_set(v_reuseFailAlloc_858_, 18, v_description_839_);
lean_ctor_set(v_reuseFailAlloc_858_, 19, v_keywords_840_);
lean_ctor_set(v_reuseFailAlloc_858_, 20, v_homepage_841_);
lean_ctor_set(v_reuseFailAlloc_858_, 21, v_license_842_);
lean_ctor_set(v_reuseFailAlloc_858_, 22, v_licenseFiles_843_);
lean_ctor_set(v_reuseFailAlloc_858_, 23, v_readmeFile_844_);
lean_ctor_set(v_reuseFailAlloc_858_, 24, v_enableArtifactCache_x3f_846_);
lean_ctor_set(v_reuseFailAlloc_858_, 25, v_restoreAllArtifacts_x3f_847_);
lean_ctor_set(v_reuseFailAlloc_858_, 26, v_builtinLint_x3f_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27, v_bootstrap_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27 + 1, v_precompileModules_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27 + 2, v_preferReleaseBuild_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27 + 3, v_reservoir_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27 + 5, v_allowImportAll_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*27 + 6, v_fixedToolchain_851_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lake_defaultLeanLibDir;
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lake_PackageConfig_leanLibDir___proj___lam__3(v_x_862_);
lean_dec_ref(v_x_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_873_, lean_object* v_n_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_876_, lean_object* v_n_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_876_, v_n_877_);
lean_dec(v_n_877_);
lean_dec(v_p_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_879_, lean_object* v_n_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_879_, v_n_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_882_, lean_object* v_n_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_882_, v_n_883_);
lean_dec(v_n_883_);
lean_dec(v_p_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* v_cfg_885_){
_start:
{
lean_object* v_nativeLibDir_886_; 
v_nativeLibDir_886_ = lean_ctor_get(v_cfg_885_, 7);
lean_inc_ref(v_nativeLibDir_886_);
return v_nativeLibDir_886_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* v_cfg_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(v_cfg_887_);
lean_dec_ref(v_cfg_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* v_val_889_, lean_object* v_cfg_890_){
_start:
{
lean_object* v_toWorkspaceConfig_891_; lean_object* v_toLeanConfig_892_; uint8_t v_bootstrap_893_; lean_object* v_extraDepTargets_894_; uint8_t v_precompileModules_895_; lean_object* v_moreGlobalServerArgs_896_; lean_object* v_srcDir_897_; lean_object* v_buildDir_898_; lean_object* v_leanLibDir_899_; lean_object* v_binDir_900_; lean_object* v_irDir_901_; lean_object* v_releaseRepo_902_; lean_object* v_buildArchive_903_; uint8_t v_preferReleaseBuild_904_; lean_object* v_testDriver_905_; lean_object* v_testDriverArgs_906_; lean_object* v_lintDriver_907_; lean_object* v_lintDriverArgs_908_; lean_object* v_version_909_; lean_object* v_versionTags_910_; lean_object* v_description_911_; lean_object* v_keywords_912_; lean_object* v_homepage_913_; lean_object* v_license_914_; lean_object* v_licenseFiles_915_; lean_object* v_readmeFile_916_; uint8_t v_reservoir_917_; lean_object* v_enableArtifactCache_x3f_918_; lean_object* v_restoreAllArtifacts_x3f_919_; uint8_t v_libPrefixOnWindows_920_; uint8_t v_allowImportAll_921_; lean_object* v_builtinLint_x3f_922_; uint8_t v_fixedToolchain_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_toWorkspaceConfig_891_ = lean_ctor_get(v_cfg_890_, 0);
v_toLeanConfig_892_ = lean_ctor_get(v_cfg_890_, 1);
v_bootstrap_893_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27);
v_extraDepTargets_894_ = lean_ctor_get(v_cfg_890_, 2);
v_precompileModules_895_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_896_ = lean_ctor_get(v_cfg_890_, 3);
v_srcDir_897_ = lean_ctor_get(v_cfg_890_, 4);
v_buildDir_898_ = lean_ctor_get(v_cfg_890_, 5);
v_leanLibDir_899_ = lean_ctor_get(v_cfg_890_, 6);
v_binDir_900_ = lean_ctor_get(v_cfg_890_, 8);
v_irDir_901_ = lean_ctor_get(v_cfg_890_, 9);
v_releaseRepo_902_ = lean_ctor_get(v_cfg_890_, 10);
v_buildArchive_903_ = lean_ctor_get(v_cfg_890_, 11);
v_preferReleaseBuild_904_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27 + 2);
v_testDriver_905_ = lean_ctor_get(v_cfg_890_, 12);
v_testDriverArgs_906_ = lean_ctor_get(v_cfg_890_, 13);
v_lintDriver_907_ = lean_ctor_get(v_cfg_890_, 14);
v_lintDriverArgs_908_ = lean_ctor_get(v_cfg_890_, 15);
v_version_909_ = lean_ctor_get(v_cfg_890_, 16);
v_versionTags_910_ = lean_ctor_get(v_cfg_890_, 17);
v_description_911_ = lean_ctor_get(v_cfg_890_, 18);
v_keywords_912_ = lean_ctor_get(v_cfg_890_, 19);
v_homepage_913_ = lean_ctor_get(v_cfg_890_, 20);
v_license_914_ = lean_ctor_get(v_cfg_890_, 21);
v_licenseFiles_915_ = lean_ctor_get(v_cfg_890_, 22);
v_readmeFile_916_ = lean_ctor_get(v_cfg_890_, 23);
v_reservoir_917_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_918_ = lean_ctor_get(v_cfg_890_, 24);
v_restoreAllArtifacts_x3f_919_ = lean_ctor_get(v_cfg_890_, 25);
v_libPrefixOnWindows_920_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27 + 4);
v_allowImportAll_921_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_922_ = lean_ctor_get(v_cfg_890_, 26);
v_fixedToolchain_923_ = lean_ctor_get_uint8(v_cfg_890_, sizeof(void*)*27 + 6);
v_isSharedCheck_930_ = !lean_is_exclusive(v_cfg_890_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_cfg_890_, 7);
lean_dec(v_unused_931_);
v___x_925_ = v_cfg_890_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_builtinLint_x3f_922_);
lean_inc(v_restoreAllArtifacts_x3f_919_);
lean_inc(v_enableArtifactCache_x3f_918_);
lean_inc(v_readmeFile_916_);
lean_inc(v_licenseFiles_915_);
lean_inc(v_license_914_);
lean_inc(v_homepage_913_);
lean_inc(v_keywords_912_);
lean_inc(v_description_911_);
lean_inc(v_versionTags_910_);
lean_inc(v_version_909_);
lean_inc(v_lintDriverArgs_908_);
lean_inc(v_lintDriver_907_);
lean_inc(v_testDriverArgs_906_);
lean_inc(v_testDriver_905_);
lean_inc(v_buildArchive_903_);
lean_inc(v_releaseRepo_902_);
lean_inc(v_irDir_901_);
lean_inc(v_binDir_900_);
lean_inc(v_leanLibDir_899_);
lean_inc(v_buildDir_898_);
lean_inc(v_srcDir_897_);
lean_inc(v_moreGlobalServerArgs_896_);
lean_inc(v_extraDepTargets_894_);
lean_inc(v_toLeanConfig_892_);
lean_inc(v_toWorkspaceConfig_891_);
lean_dec(v_cfg_890_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 7, v_val_889_);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_toWorkspaceConfig_891_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_toLeanConfig_892_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_extraDepTargets_894_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_moreGlobalServerArgs_896_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_srcDir_897_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_buildDir_898_);
lean_ctor_set(v_reuseFailAlloc_929_, 6, v_leanLibDir_899_);
lean_ctor_set(v_reuseFailAlloc_929_, 7, v_val_889_);
lean_ctor_set(v_reuseFailAlloc_929_, 8, v_binDir_900_);
lean_ctor_set(v_reuseFailAlloc_929_, 9, v_irDir_901_);
lean_ctor_set(v_reuseFailAlloc_929_, 10, v_releaseRepo_902_);
lean_ctor_set(v_reuseFailAlloc_929_, 11, v_buildArchive_903_);
lean_ctor_set(v_reuseFailAlloc_929_, 12, v_testDriver_905_);
lean_ctor_set(v_reuseFailAlloc_929_, 13, v_testDriverArgs_906_);
lean_ctor_set(v_reuseFailAlloc_929_, 14, v_lintDriver_907_);
lean_ctor_set(v_reuseFailAlloc_929_, 15, v_lintDriverArgs_908_);
lean_ctor_set(v_reuseFailAlloc_929_, 16, v_version_909_);
lean_ctor_set(v_reuseFailAlloc_929_, 17, v_versionTags_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 18, v_description_911_);
lean_ctor_set(v_reuseFailAlloc_929_, 19, v_keywords_912_);
lean_ctor_set(v_reuseFailAlloc_929_, 20, v_homepage_913_);
lean_ctor_set(v_reuseFailAlloc_929_, 21, v_license_914_);
lean_ctor_set(v_reuseFailAlloc_929_, 22, v_licenseFiles_915_);
lean_ctor_set(v_reuseFailAlloc_929_, 23, v_readmeFile_916_);
lean_ctor_set(v_reuseFailAlloc_929_, 24, v_enableArtifactCache_x3f_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 25, v_restoreAllArtifacts_x3f_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 26, v_builtinLint_x3f_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27, v_bootstrap_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27 + 1, v_precompileModules_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27 + 2, v_preferReleaseBuild_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27 + 3, v_reservoir_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27 + 5, v_allowImportAll_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*27 + 6, v_fixedToolchain_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* v_f_932_, lean_object* v_cfg_933_){
_start:
{
lean_object* v_toWorkspaceConfig_934_; lean_object* v_toLeanConfig_935_; uint8_t v_bootstrap_936_; lean_object* v_extraDepTargets_937_; uint8_t v_precompileModules_938_; lean_object* v_moreGlobalServerArgs_939_; lean_object* v_srcDir_940_; lean_object* v_buildDir_941_; lean_object* v_leanLibDir_942_; lean_object* v_nativeLibDir_943_; lean_object* v_binDir_944_; lean_object* v_irDir_945_; lean_object* v_releaseRepo_946_; lean_object* v_buildArchive_947_; uint8_t v_preferReleaseBuild_948_; lean_object* v_testDriver_949_; lean_object* v_testDriverArgs_950_; lean_object* v_lintDriver_951_; lean_object* v_lintDriverArgs_952_; lean_object* v_version_953_; lean_object* v_versionTags_954_; lean_object* v_description_955_; lean_object* v_keywords_956_; lean_object* v_homepage_957_; lean_object* v_license_958_; lean_object* v_licenseFiles_959_; lean_object* v_readmeFile_960_; uint8_t v_reservoir_961_; lean_object* v_enableArtifactCache_x3f_962_; lean_object* v_restoreAllArtifacts_x3f_963_; uint8_t v_libPrefixOnWindows_964_; uint8_t v_allowImportAll_965_; lean_object* v_builtinLint_x3f_966_; uint8_t v_fixedToolchain_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_toWorkspaceConfig_934_ = lean_ctor_get(v_cfg_933_, 0);
v_toLeanConfig_935_ = lean_ctor_get(v_cfg_933_, 1);
v_bootstrap_936_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27);
v_extraDepTargets_937_ = lean_ctor_get(v_cfg_933_, 2);
v_precompileModules_938_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_939_ = lean_ctor_get(v_cfg_933_, 3);
v_srcDir_940_ = lean_ctor_get(v_cfg_933_, 4);
v_buildDir_941_ = lean_ctor_get(v_cfg_933_, 5);
v_leanLibDir_942_ = lean_ctor_get(v_cfg_933_, 6);
v_nativeLibDir_943_ = lean_ctor_get(v_cfg_933_, 7);
v_binDir_944_ = lean_ctor_get(v_cfg_933_, 8);
v_irDir_945_ = lean_ctor_get(v_cfg_933_, 9);
v_releaseRepo_946_ = lean_ctor_get(v_cfg_933_, 10);
v_buildArchive_947_ = lean_ctor_get(v_cfg_933_, 11);
v_preferReleaseBuild_948_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27 + 2);
v_testDriver_949_ = lean_ctor_get(v_cfg_933_, 12);
v_testDriverArgs_950_ = lean_ctor_get(v_cfg_933_, 13);
v_lintDriver_951_ = lean_ctor_get(v_cfg_933_, 14);
v_lintDriverArgs_952_ = lean_ctor_get(v_cfg_933_, 15);
v_version_953_ = lean_ctor_get(v_cfg_933_, 16);
v_versionTags_954_ = lean_ctor_get(v_cfg_933_, 17);
v_description_955_ = lean_ctor_get(v_cfg_933_, 18);
v_keywords_956_ = lean_ctor_get(v_cfg_933_, 19);
v_homepage_957_ = lean_ctor_get(v_cfg_933_, 20);
v_license_958_ = lean_ctor_get(v_cfg_933_, 21);
v_licenseFiles_959_ = lean_ctor_get(v_cfg_933_, 22);
v_readmeFile_960_ = lean_ctor_get(v_cfg_933_, 23);
v_reservoir_961_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_962_ = lean_ctor_get(v_cfg_933_, 24);
v_restoreAllArtifacts_x3f_963_ = lean_ctor_get(v_cfg_933_, 25);
v_libPrefixOnWindows_964_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27 + 4);
v_allowImportAll_965_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_966_ = lean_ctor_get(v_cfg_933_, 26);
v_fixedToolchain_967_ = lean_ctor_get_uint8(v_cfg_933_, sizeof(void*)*27 + 6);
v_isSharedCheck_975_ = !lean_is_exclusive(v_cfg_933_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v_cfg_933_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_builtinLint_x3f_966_);
lean_inc(v_restoreAllArtifacts_x3f_963_);
lean_inc(v_enableArtifactCache_x3f_962_);
lean_inc(v_readmeFile_960_);
lean_inc(v_licenseFiles_959_);
lean_inc(v_license_958_);
lean_inc(v_homepage_957_);
lean_inc(v_keywords_956_);
lean_inc(v_description_955_);
lean_inc(v_versionTags_954_);
lean_inc(v_version_953_);
lean_inc(v_lintDriverArgs_952_);
lean_inc(v_lintDriver_951_);
lean_inc(v_testDriverArgs_950_);
lean_inc(v_testDriver_949_);
lean_inc(v_buildArchive_947_);
lean_inc(v_releaseRepo_946_);
lean_inc(v_irDir_945_);
lean_inc(v_binDir_944_);
lean_inc(v_nativeLibDir_943_);
lean_inc(v_leanLibDir_942_);
lean_inc(v_buildDir_941_);
lean_inc(v_srcDir_940_);
lean_inc(v_moreGlobalServerArgs_939_);
lean_inc(v_extraDepTargets_937_);
lean_inc(v_toLeanConfig_935_);
lean_inc(v_toWorkspaceConfig_934_);
lean_dec(v_cfg_933_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_apply_1(v_f_932_, v_nativeLibDir_943_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 7, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_toWorkspaceConfig_934_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_toLeanConfig_935_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_extraDepTargets_937_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_moreGlobalServerArgs_939_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_srcDir_940_);
lean_ctor_set(v_reuseFailAlloc_974_, 5, v_buildDir_941_);
lean_ctor_set(v_reuseFailAlloc_974_, 6, v_leanLibDir_942_);
lean_ctor_set(v_reuseFailAlloc_974_, 7, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_974_, 8, v_binDir_944_);
lean_ctor_set(v_reuseFailAlloc_974_, 9, v_irDir_945_);
lean_ctor_set(v_reuseFailAlloc_974_, 10, v_releaseRepo_946_);
lean_ctor_set(v_reuseFailAlloc_974_, 11, v_buildArchive_947_);
lean_ctor_set(v_reuseFailAlloc_974_, 12, v_testDriver_949_);
lean_ctor_set(v_reuseFailAlloc_974_, 13, v_testDriverArgs_950_);
lean_ctor_set(v_reuseFailAlloc_974_, 14, v_lintDriver_951_);
lean_ctor_set(v_reuseFailAlloc_974_, 15, v_lintDriverArgs_952_);
lean_ctor_set(v_reuseFailAlloc_974_, 16, v_version_953_);
lean_ctor_set(v_reuseFailAlloc_974_, 17, v_versionTags_954_);
lean_ctor_set(v_reuseFailAlloc_974_, 18, v_description_955_);
lean_ctor_set(v_reuseFailAlloc_974_, 19, v_keywords_956_);
lean_ctor_set(v_reuseFailAlloc_974_, 20, v_homepage_957_);
lean_ctor_set(v_reuseFailAlloc_974_, 21, v_license_958_);
lean_ctor_set(v_reuseFailAlloc_974_, 22, v_licenseFiles_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 23, v_readmeFile_960_);
lean_ctor_set(v_reuseFailAlloc_974_, 24, v_enableArtifactCache_x3f_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 25, v_restoreAllArtifacts_x3f_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 26, v_builtinLint_x3f_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27, v_bootstrap_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27 + 1, v_precompileModules_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27 + 2, v_preferReleaseBuild_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27 + 3, v_reservoir_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27 + 5, v_allowImportAll_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*27 + 6, v_fixedToolchain_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lake_defaultNativeLibDir;
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* v_x_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(v_x_978_);
lean_dec_ref(v_x_978_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_989_, lean_object* v_n_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_992_, lean_object* v_n_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_992_, v_n_993_);
lean_dec(v_n_993_);
lean_dec(v_p_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_995_, lean_object* v_n_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_995_, v_n_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_998_, lean_object* v_n_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_998_, v_n_999_);
lean_dec(v_n_999_);
lean_dec(v_p_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* v_cfg_1001_){
_start:
{
lean_object* v_binDir_1002_; 
v_binDir_1002_ = lean_ctor_get(v_cfg_1001_, 8);
lean_inc_ref(v_binDir_1002_);
return v_binDir_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* v_cfg_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lake_PackageConfig_binDir___proj___lam__0(v_cfg_1003_);
lean_dec_ref(v_cfg_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* v_val_1005_, lean_object* v_cfg_1006_){
_start:
{
lean_object* v_toWorkspaceConfig_1007_; lean_object* v_toLeanConfig_1008_; uint8_t v_bootstrap_1009_; lean_object* v_extraDepTargets_1010_; uint8_t v_precompileModules_1011_; lean_object* v_moreGlobalServerArgs_1012_; lean_object* v_srcDir_1013_; lean_object* v_buildDir_1014_; lean_object* v_leanLibDir_1015_; lean_object* v_nativeLibDir_1016_; lean_object* v_irDir_1017_; lean_object* v_releaseRepo_1018_; lean_object* v_buildArchive_1019_; uint8_t v_preferReleaseBuild_1020_; lean_object* v_testDriver_1021_; lean_object* v_testDriverArgs_1022_; lean_object* v_lintDriver_1023_; lean_object* v_lintDriverArgs_1024_; lean_object* v_version_1025_; lean_object* v_versionTags_1026_; lean_object* v_description_1027_; lean_object* v_keywords_1028_; lean_object* v_homepage_1029_; lean_object* v_license_1030_; lean_object* v_licenseFiles_1031_; lean_object* v_readmeFile_1032_; uint8_t v_reservoir_1033_; lean_object* v_enableArtifactCache_x3f_1034_; lean_object* v_restoreAllArtifacts_x3f_1035_; uint8_t v_libPrefixOnWindows_1036_; uint8_t v_allowImportAll_1037_; lean_object* v_builtinLint_x3f_1038_; uint8_t v_fixedToolchain_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_toWorkspaceConfig_1007_ = lean_ctor_get(v_cfg_1006_, 0);
v_toLeanConfig_1008_ = lean_ctor_get(v_cfg_1006_, 1);
v_bootstrap_1009_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27);
v_extraDepTargets_1010_ = lean_ctor_get(v_cfg_1006_, 2);
v_precompileModules_1011_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1012_ = lean_ctor_get(v_cfg_1006_, 3);
v_srcDir_1013_ = lean_ctor_get(v_cfg_1006_, 4);
v_buildDir_1014_ = lean_ctor_get(v_cfg_1006_, 5);
v_leanLibDir_1015_ = lean_ctor_get(v_cfg_1006_, 6);
v_nativeLibDir_1016_ = lean_ctor_get(v_cfg_1006_, 7);
v_irDir_1017_ = lean_ctor_get(v_cfg_1006_, 9);
v_releaseRepo_1018_ = lean_ctor_get(v_cfg_1006_, 10);
v_buildArchive_1019_ = lean_ctor_get(v_cfg_1006_, 11);
v_preferReleaseBuild_1020_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27 + 2);
v_testDriver_1021_ = lean_ctor_get(v_cfg_1006_, 12);
v_testDriverArgs_1022_ = lean_ctor_get(v_cfg_1006_, 13);
v_lintDriver_1023_ = lean_ctor_get(v_cfg_1006_, 14);
v_lintDriverArgs_1024_ = lean_ctor_get(v_cfg_1006_, 15);
v_version_1025_ = lean_ctor_get(v_cfg_1006_, 16);
v_versionTags_1026_ = lean_ctor_get(v_cfg_1006_, 17);
v_description_1027_ = lean_ctor_get(v_cfg_1006_, 18);
v_keywords_1028_ = lean_ctor_get(v_cfg_1006_, 19);
v_homepage_1029_ = lean_ctor_get(v_cfg_1006_, 20);
v_license_1030_ = lean_ctor_get(v_cfg_1006_, 21);
v_licenseFiles_1031_ = lean_ctor_get(v_cfg_1006_, 22);
v_readmeFile_1032_ = lean_ctor_get(v_cfg_1006_, 23);
v_reservoir_1033_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1034_ = lean_ctor_get(v_cfg_1006_, 24);
v_restoreAllArtifacts_x3f_1035_ = lean_ctor_get(v_cfg_1006_, 25);
v_libPrefixOnWindows_1036_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27 + 4);
v_allowImportAll_1037_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1038_ = lean_ctor_get(v_cfg_1006_, 26);
v_fixedToolchain_1039_ = lean_ctor_get_uint8(v_cfg_1006_, sizeof(void*)*27 + 6);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_cfg_1006_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_cfg_1006_, 8);
lean_dec(v_unused_1047_);
v___x_1041_ = v_cfg_1006_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_builtinLint_x3f_1038_);
lean_inc(v_restoreAllArtifacts_x3f_1035_);
lean_inc(v_enableArtifactCache_x3f_1034_);
lean_inc(v_readmeFile_1032_);
lean_inc(v_licenseFiles_1031_);
lean_inc(v_license_1030_);
lean_inc(v_homepage_1029_);
lean_inc(v_keywords_1028_);
lean_inc(v_description_1027_);
lean_inc(v_versionTags_1026_);
lean_inc(v_version_1025_);
lean_inc(v_lintDriverArgs_1024_);
lean_inc(v_lintDriver_1023_);
lean_inc(v_testDriverArgs_1022_);
lean_inc(v_testDriver_1021_);
lean_inc(v_buildArchive_1019_);
lean_inc(v_releaseRepo_1018_);
lean_inc(v_irDir_1017_);
lean_inc(v_nativeLibDir_1016_);
lean_inc(v_leanLibDir_1015_);
lean_inc(v_buildDir_1014_);
lean_inc(v_srcDir_1013_);
lean_inc(v_moreGlobalServerArgs_1012_);
lean_inc(v_extraDepTargets_1010_);
lean_inc(v_toLeanConfig_1008_);
lean_inc(v_toWorkspaceConfig_1007_);
lean_dec(v_cfg_1006_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 8, v_val_1005_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_toWorkspaceConfig_1007_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_toLeanConfig_1008_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_extraDepTargets_1010_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_moreGlobalServerArgs_1012_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_srcDir_1013_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_buildDir_1014_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_leanLibDir_1015_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_nativeLibDir_1016_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_val_1005_);
lean_ctor_set(v_reuseFailAlloc_1045_, 9, v_irDir_1017_);
lean_ctor_set(v_reuseFailAlloc_1045_, 10, v_releaseRepo_1018_);
lean_ctor_set(v_reuseFailAlloc_1045_, 11, v_buildArchive_1019_);
lean_ctor_set(v_reuseFailAlloc_1045_, 12, v_testDriver_1021_);
lean_ctor_set(v_reuseFailAlloc_1045_, 13, v_testDriverArgs_1022_);
lean_ctor_set(v_reuseFailAlloc_1045_, 14, v_lintDriver_1023_);
lean_ctor_set(v_reuseFailAlloc_1045_, 15, v_lintDriverArgs_1024_);
lean_ctor_set(v_reuseFailAlloc_1045_, 16, v_version_1025_);
lean_ctor_set(v_reuseFailAlloc_1045_, 17, v_versionTags_1026_);
lean_ctor_set(v_reuseFailAlloc_1045_, 18, v_description_1027_);
lean_ctor_set(v_reuseFailAlloc_1045_, 19, v_keywords_1028_);
lean_ctor_set(v_reuseFailAlloc_1045_, 20, v_homepage_1029_);
lean_ctor_set(v_reuseFailAlloc_1045_, 21, v_license_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 22, v_licenseFiles_1031_);
lean_ctor_set(v_reuseFailAlloc_1045_, 23, v_readmeFile_1032_);
lean_ctor_set(v_reuseFailAlloc_1045_, 24, v_enableArtifactCache_x3f_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 25, v_restoreAllArtifacts_x3f_1035_);
lean_ctor_set(v_reuseFailAlloc_1045_, 26, v_builtinLint_x3f_1038_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27, v_bootstrap_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27 + 1, v_precompileModules_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27 + 3, v_reservoir_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1036_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27 + 5, v_allowImportAll_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*27 + 6, v_fixedToolchain_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* v_f_1048_, lean_object* v_cfg_1049_){
_start:
{
lean_object* v_toWorkspaceConfig_1050_; lean_object* v_toLeanConfig_1051_; uint8_t v_bootstrap_1052_; lean_object* v_extraDepTargets_1053_; uint8_t v_precompileModules_1054_; lean_object* v_moreGlobalServerArgs_1055_; lean_object* v_srcDir_1056_; lean_object* v_buildDir_1057_; lean_object* v_leanLibDir_1058_; lean_object* v_nativeLibDir_1059_; lean_object* v_binDir_1060_; lean_object* v_irDir_1061_; lean_object* v_releaseRepo_1062_; lean_object* v_buildArchive_1063_; uint8_t v_preferReleaseBuild_1064_; lean_object* v_testDriver_1065_; lean_object* v_testDriverArgs_1066_; lean_object* v_lintDriver_1067_; lean_object* v_lintDriverArgs_1068_; lean_object* v_version_1069_; lean_object* v_versionTags_1070_; lean_object* v_description_1071_; lean_object* v_keywords_1072_; lean_object* v_homepage_1073_; lean_object* v_license_1074_; lean_object* v_licenseFiles_1075_; lean_object* v_readmeFile_1076_; uint8_t v_reservoir_1077_; lean_object* v_enableArtifactCache_x3f_1078_; lean_object* v_restoreAllArtifacts_x3f_1079_; uint8_t v_libPrefixOnWindows_1080_; uint8_t v_allowImportAll_1081_; lean_object* v_builtinLint_x3f_1082_; uint8_t v_fixedToolchain_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_toWorkspaceConfig_1050_ = lean_ctor_get(v_cfg_1049_, 0);
v_toLeanConfig_1051_ = lean_ctor_get(v_cfg_1049_, 1);
v_bootstrap_1052_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27);
v_extraDepTargets_1053_ = lean_ctor_get(v_cfg_1049_, 2);
v_precompileModules_1054_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1055_ = lean_ctor_get(v_cfg_1049_, 3);
v_srcDir_1056_ = lean_ctor_get(v_cfg_1049_, 4);
v_buildDir_1057_ = lean_ctor_get(v_cfg_1049_, 5);
v_leanLibDir_1058_ = lean_ctor_get(v_cfg_1049_, 6);
v_nativeLibDir_1059_ = lean_ctor_get(v_cfg_1049_, 7);
v_binDir_1060_ = lean_ctor_get(v_cfg_1049_, 8);
v_irDir_1061_ = lean_ctor_get(v_cfg_1049_, 9);
v_releaseRepo_1062_ = lean_ctor_get(v_cfg_1049_, 10);
v_buildArchive_1063_ = lean_ctor_get(v_cfg_1049_, 11);
v_preferReleaseBuild_1064_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27 + 2);
v_testDriver_1065_ = lean_ctor_get(v_cfg_1049_, 12);
v_testDriverArgs_1066_ = lean_ctor_get(v_cfg_1049_, 13);
v_lintDriver_1067_ = lean_ctor_get(v_cfg_1049_, 14);
v_lintDriverArgs_1068_ = lean_ctor_get(v_cfg_1049_, 15);
v_version_1069_ = lean_ctor_get(v_cfg_1049_, 16);
v_versionTags_1070_ = lean_ctor_get(v_cfg_1049_, 17);
v_description_1071_ = lean_ctor_get(v_cfg_1049_, 18);
v_keywords_1072_ = lean_ctor_get(v_cfg_1049_, 19);
v_homepage_1073_ = lean_ctor_get(v_cfg_1049_, 20);
v_license_1074_ = lean_ctor_get(v_cfg_1049_, 21);
v_licenseFiles_1075_ = lean_ctor_get(v_cfg_1049_, 22);
v_readmeFile_1076_ = lean_ctor_get(v_cfg_1049_, 23);
v_reservoir_1077_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1078_ = lean_ctor_get(v_cfg_1049_, 24);
v_restoreAllArtifacts_x3f_1079_ = lean_ctor_get(v_cfg_1049_, 25);
v_libPrefixOnWindows_1080_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27 + 4);
v_allowImportAll_1081_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1082_ = lean_ctor_get(v_cfg_1049_, 26);
v_fixedToolchain_1083_ = lean_ctor_get_uint8(v_cfg_1049_, sizeof(void*)*27 + 6);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_cfg_1049_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1085_ = v_cfg_1049_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_builtinLint_x3f_1082_);
lean_inc(v_restoreAllArtifacts_x3f_1079_);
lean_inc(v_enableArtifactCache_x3f_1078_);
lean_inc(v_readmeFile_1076_);
lean_inc(v_licenseFiles_1075_);
lean_inc(v_license_1074_);
lean_inc(v_homepage_1073_);
lean_inc(v_keywords_1072_);
lean_inc(v_description_1071_);
lean_inc(v_versionTags_1070_);
lean_inc(v_version_1069_);
lean_inc(v_lintDriverArgs_1068_);
lean_inc(v_lintDriver_1067_);
lean_inc(v_testDriverArgs_1066_);
lean_inc(v_testDriver_1065_);
lean_inc(v_buildArchive_1063_);
lean_inc(v_releaseRepo_1062_);
lean_inc(v_irDir_1061_);
lean_inc(v_binDir_1060_);
lean_inc(v_nativeLibDir_1059_);
lean_inc(v_leanLibDir_1058_);
lean_inc(v_buildDir_1057_);
lean_inc(v_srcDir_1056_);
lean_inc(v_moreGlobalServerArgs_1055_);
lean_inc(v_extraDepTargets_1053_);
lean_inc(v_toLeanConfig_1051_);
lean_inc(v_toWorkspaceConfig_1050_);
lean_dec(v_cfg_1049_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_apply_1(v_f_1048_, v_binDir_1060_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 8, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_toWorkspaceConfig_1050_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_toLeanConfig_1051_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_extraDepTargets_1053_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_moreGlobalServerArgs_1055_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_srcDir_1056_);
lean_ctor_set(v_reuseFailAlloc_1090_, 5, v_buildDir_1057_);
lean_ctor_set(v_reuseFailAlloc_1090_, 6, v_leanLibDir_1058_);
lean_ctor_set(v_reuseFailAlloc_1090_, 7, v_nativeLibDir_1059_);
lean_ctor_set(v_reuseFailAlloc_1090_, 8, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 9, v_irDir_1061_);
lean_ctor_set(v_reuseFailAlloc_1090_, 10, v_releaseRepo_1062_);
lean_ctor_set(v_reuseFailAlloc_1090_, 11, v_buildArchive_1063_);
lean_ctor_set(v_reuseFailAlloc_1090_, 12, v_testDriver_1065_);
lean_ctor_set(v_reuseFailAlloc_1090_, 13, v_testDriverArgs_1066_);
lean_ctor_set(v_reuseFailAlloc_1090_, 14, v_lintDriver_1067_);
lean_ctor_set(v_reuseFailAlloc_1090_, 15, v_lintDriverArgs_1068_);
lean_ctor_set(v_reuseFailAlloc_1090_, 16, v_version_1069_);
lean_ctor_set(v_reuseFailAlloc_1090_, 17, v_versionTags_1070_);
lean_ctor_set(v_reuseFailAlloc_1090_, 18, v_description_1071_);
lean_ctor_set(v_reuseFailAlloc_1090_, 19, v_keywords_1072_);
lean_ctor_set(v_reuseFailAlloc_1090_, 20, v_homepage_1073_);
lean_ctor_set(v_reuseFailAlloc_1090_, 21, v_license_1074_);
lean_ctor_set(v_reuseFailAlloc_1090_, 22, v_licenseFiles_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 23, v_readmeFile_1076_);
lean_ctor_set(v_reuseFailAlloc_1090_, 24, v_enableArtifactCache_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 25, v_restoreAllArtifacts_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1090_, 26, v_builtinLint_x3f_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27, v_bootstrap_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27 + 1, v_precompileModules_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27 + 3, v_reservoir_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27 + 5, v_allowImportAll_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*27 + 6, v_fixedToolchain_1083_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lake_defaultBinDir;
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* v_x_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_PackageConfig_binDir___proj___lam__3(v_x_1094_);
lean_dec_ref(v_x_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1105_, lean_object* v_n_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1108_, lean_object* v_n_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lake_PackageConfig_binDir___proj(v_p_1108_, v_n_1109_);
lean_dec(v_n_1109_);
lean_dec(v_p_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1111_, lean_object* v_n_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lake_PackageConfig_binDir___proj(v_p_1111_, v_n_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1114_, lean_object* v_n_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1114_, v_n_1115_);
lean_dec(v_n_1115_);
lean_dec(v_p_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* v_cfg_1117_){
_start:
{
lean_object* v_irDir_1118_; 
v_irDir_1118_ = lean_ctor_get(v_cfg_1117_, 9);
lean_inc_ref(v_irDir_1118_);
return v_irDir_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* v_cfg_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lake_PackageConfig_irDir___proj___lam__0(v_cfg_1119_);
lean_dec_ref(v_cfg_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* v_val_1121_, lean_object* v_cfg_1122_){
_start:
{
lean_object* v_toWorkspaceConfig_1123_; lean_object* v_toLeanConfig_1124_; uint8_t v_bootstrap_1125_; lean_object* v_extraDepTargets_1126_; uint8_t v_precompileModules_1127_; lean_object* v_moreGlobalServerArgs_1128_; lean_object* v_srcDir_1129_; lean_object* v_buildDir_1130_; lean_object* v_leanLibDir_1131_; lean_object* v_nativeLibDir_1132_; lean_object* v_binDir_1133_; lean_object* v_releaseRepo_1134_; lean_object* v_buildArchive_1135_; uint8_t v_preferReleaseBuild_1136_; lean_object* v_testDriver_1137_; lean_object* v_testDriverArgs_1138_; lean_object* v_lintDriver_1139_; lean_object* v_lintDriverArgs_1140_; lean_object* v_version_1141_; lean_object* v_versionTags_1142_; lean_object* v_description_1143_; lean_object* v_keywords_1144_; lean_object* v_homepage_1145_; lean_object* v_license_1146_; lean_object* v_licenseFiles_1147_; lean_object* v_readmeFile_1148_; uint8_t v_reservoir_1149_; lean_object* v_enableArtifactCache_x3f_1150_; lean_object* v_restoreAllArtifacts_x3f_1151_; uint8_t v_libPrefixOnWindows_1152_; uint8_t v_allowImportAll_1153_; lean_object* v_builtinLint_x3f_1154_; uint8_t v_fixedToolchain_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_toWorkspaceConfig_1123_ = lean_ctor_get(v_cfg_1122_, 0);
v_toLeanConfig_1124_ = lean_ctor_get(v_cfg_1122_, 1);
v_bootstrap_1125_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27);
v_extraDepTargets_1126_ = lean_ctor_get(v_cfg_1122_, 2);
v_precompileModules_1127_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1128_ = lean_ctor_get(v_cfg_1122_, 3);
v_srcDir_1129_ = lean_ctor_get(v_cfg_1122_, 4);
v_buildDir_1130_ = lean_ctor_get(v_cfg_1122_, 5);
v_leanLibDir_1131_ = lean_ctor_get(v_cfg_1122_, 6);
v_nativeLibDir_1132_ = lean_ctor_get(v_cfg_1122_, 7);
v_binDir_1133_ = lean_ctor_get(v_cfg_1122_, 8);
v_releaseRepo_1134_ = lean_ctor_get(v_cfg_1122_, 10);
v_buildArchive_1135_ = lean_ctor_get(v_cfg_1122_, 11);
v_preferReleaseBuild_1136_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27 + 2);
v_testDriver_1137_ = lean_ctor_get(v_cfg_1122_, 12);
v_testDriverArgs_1138_ = lean_ctor_get(v_cfg_1122_, 13);
v_lintDriver_1139_ = lean_ctor_get(v_cfg_1122_, 14);
v_lintDriverArgs_1140_ = lean_ctor_get(v_cfg_1122_, 15);
v_version_1141_ = lean_ctor_get(v_cfg_1122_, 16);
v_versionTags_1142_ = lean_ctor_get(v_cfg_1122_, 17);
v_description_1143_ = lean_ctor_get(v_cfg_1122_, 18);
v_keywords_1144_ = lean_ctor_get(v_cfg_1122_, 19);
v_homepage_1145_ = lean_ctor_get(v_cfg_1122_, 20);
v_license_1146_ = lean_ctor_get(v_cfg_1122_, 21);
v_licenseFiles_1147_ = lean_ctor_get(v_cfg_1122_, 22);
v_readmeFile_1148_ = lean_ctor_get(v_cfg_1122_, 23);
v_reservoir_1149_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1150_ = lean_ctor_get(v_cfg_1122_, 24);
v_restoreAllArtifacts_x3f_1151_ = lean_ctor_get(v_cfg_1122_, 25);
v_libPrefixOnWindows_1152_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27 + 4);
v_allowImportAll_1153_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1154_ = lean_ctor_get(v_cfg_1122_, 26);
v_fixedToolchain_1155_ = lean_ctor_get_uint8(v_cfg_1122_, sizeof(void*)*27 + 6);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_cfg_1122_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_cfg_1122_, 9);
lean_dec(v_unused_1163_);
v___x_1157_ = v_cfg_1122_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_builtinLint_x3f_1154_);
lean_inc(v_restoreAllArtifacts_x3f_1151_);
lean_inc(v_enableArtifactCache_x3f_1150_);
lean_inc(v_readmeFile_1148_);
lean_inc(v_licenseFiles_1147_);
lean_inc(v_license_1146_);
lean_inc(v_homepage_1145_);
lean_inc(v_keywords_1144_);
lean_inc(v_description_1143_);
lean_inc(v_versionTags_1142_);
lean_inc(v_version_1141_);
lean_inc(v_lintDriverArgs_1140_);
lean_inc(v_lintDriver_1139_);
lean_inc(v_testDriverArgs_1138_);
lean_inc(v_testDriver_1137_);
lean_inc(v_buildArchive_1135_);
lean_inc(v_releaseRepo_1134_);
lean_inc(v_binDir_1133_);
lean_inc(v_nativeLibDir_1132_);
lean_inc(v_leanLibDir_1131_);
lean_inc(v_buildDir_1130_);
lean_inc(v_srcDir_1129_);
lean_inc(v_moreGlobalServerArgs_1128_);
lean_inc(v_extraDepTargets_1126_);
lean_inc(v_toLeanConfig_1124_);
lean_inc(v_toWorkspaceConfig_1123_);
lean_dec(v_cfg_1122_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 9, v_val_1121_);
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_toWorkspaceConfig_1123_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_toLeanConfig_1124_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_extraDepTargets_1126_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_moreGlobalServerArgs_1128_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_srcDir_1129_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_buildDir_1130_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_leanLibDir_1131_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v_nativeLibDir_1132_);
lean_ctor_set(v_reuseFailAlloc_1161_, 8, v_binDir_1133_);
lean_ctor_set(v_reuseFailAlloc_1161_, 9, v_val_1121_);
lean_ctor_set(v_reuseFailAlloc_1161_, 10, v_releaseRepo_1134_);
lean_ctor_set(v_reuseFailAlloc_1161_, 11, v_buildArchive_1135_);
lean_ctor_set(v_reuseFailAlloc_1161_, 12, v_testDriver_1137_);
lean_ctor_set(v_reuseFailAlloc_1161_, 13, v_testDriverArgs_1138_);
lean_ctor_set(v_reuseFailAlloc_1161_, 14, v_lintDriver_1139_);
lean_ctor_set(v_reuseFailAlloc_1161_, 15, v_lintDriverArgs_1140_);
lean_ctor_set(v_reuseFailAlloc_1161_, 16, v_version_1141_);
lean_ctor_set(v_reuseFailAlloc_1161_, 17, v_versionTags_1142_);
lean_ctor_set(v_reuseFailAlloc_1161_, 18, v_description_1143_);
lean_ctor_set(v_reuseFailAlloc_1161_, 19, v_keywords_1144_);
lean_ctor_set(v_reuseFailAlloc_1161_, 20, v_homepage_1145_);
lean_ctor_set(v_reuseFailAlloc_1161_, 21, v_license_1146_);
lean_ctor_set(v_reuseFailAlloc_1161_, 22, v_licenseFiles_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 23, v_readmeFile_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 24, v_enableArtifactCache_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 25, v_restoreAllArtifacts_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 26, v_builtinLint_x3f_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27, v_bootstrap_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27 + 1, v_precompileModules_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27 + 3, v_reservoir_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27 + 5, v_allowImportAll_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*27 + 6, v_fixedToolchain_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* v_f_1164_, lean_object* v_cfg_1165_){
_start:
{
lean_object* v_toWorkspaceConfig_1166_; lean_object* v_toLeanConfig_1167_; uint8_t v_bootstrap_1168_; lean_object* v_extraDepTargets_1169_; uint8_t v_precompileModules_1170_; lean_object* v_moreGlobalServerArgs_1171_; lean_object* v_srcDir_1172_; lean_object* v_buildDir_1173_; lean_object* v_leanLibDir_1174_; lean_object* v_nativeLibDir_1175_; lean_object* v_binDir_1176_; lean_object* v_irDir_1177_; lean_object* v_releaseRepo_1178_; lean_object* v_buildArchive_1179_; uint8_t v_preferReleaseBuild_1180_; lean_object* v_testDriver_1181_; lean_object* v_testDriverArgs_1182_; lean_object* v_lintDriver_1183_; lean_object* v_lintDriverArgs_1184_; lean_object* v_version_1185_; lean_object* v_versionTags_1186_; lean_object* v_description_1187_; lean_object* v_keywords_1188_; lean_object* v_homepage_1189_; lean_object* v_license_1190_; lean_object* v_licenseFiles_1191_; lean_object* v_readmeFile_1192_; uint8_t v_reservoir_1193_; lean_object* v_enableArtifactCache_x3f_1194_; lean_object* v_restoreAllArtifacts_x3f_1195_; uint8_t v_libPrefixOnWindows_1196_; uint8_t v_allowImportAll_1197_; lean_object* v_builtinLint_x3f_1198_; uint8_t v_fixedToolchain_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_toWorkspaceConfig_1166_ = lean_ctor_get(v_cfg_1165_, 0);
v_toLeanConfig_1167_ = lean_ctor_get(v_cfg_1165_, 1);
v_bootstrap_1168_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27);
v_extraDepTargets_1169_ = lean_ctor_get(v_cfg_1165_, 2);
v_precompileModules_1170_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1171_ = lean_ctor_get(v_cfg_1165_, 3);
v_srcDir_1172_ = lean_ctor_get(v_cfg_1165_, 4);
v_buildDir_1173_ = lean_ctor_get(v_cfg_1165_, 5);
v_leanLibDir_1174_ = lean_ctor_get(v_cfg_1165_, 6);
v_nativeLibDir_1175_ = lean_ctor_get(v_cfg_1165_, 7);
v_binDir_1176_ = lean_ctor_get(v_cfg_1165_, 8);
v_irDir_1177_ = lean_ctor_get(v_cfg_1165_, 9);
v_releaseRepo_1178_ = lean_ctor_get(v_cfg_1165_, 10);
v_buildArchive_1179_ = lean_ctor_get(v_cfg_1165_, 11);
v_preferReleaseBuild_1180_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27 + 2);
v_testDriver_1181_ = lean_ctor_get(v_cfg_1165_, 12);
v_testDriverArgs_1182_ = lean_ctor_get(v_cfg_1165_, 13);
v_lintDriver_1183_ = lean_ctor_get(v_cfg_1165_, 14);
v_lintDriverArgs_1184_ = lean_ctor_get(v_cfg_1165_, 15);
v_version_1185_ = lean_ctor_get(v_cfg_1165_, 16);
v_versionTags_1186_ = lean_ctor_get(v_cfg_1165_, 17);
v_description_1187_ = lean_ctor_get(v_cfg_1165_, 18);
v_keywords_1188_ = lean_ctor_get(v_cfg_1165_, 19);
v_homepage_1189_ = lean_ctor_get(v_cfg_1165_, 20);
v_license_1190_ = lean_ctor_get(v_cfg_1165_, 21);
v_licenseFiles_1191_ = lean_ctor_get(v_cfg_1165_, 22);
v_readmeFile_1192_ = lean_ctor_get(v_cfg_1165_, 23);
v_reservoir_1193_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1194_ = lean_ctor_get(v_cfg_1165_, 24);
v_restoreAllArtifacts_x3f_1195_ = lean_ctor_get(v_cfg_1165_, 25);
v_libPrefixOnWindows_1196_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27 + 4);
v_allowImportAll_1197_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1198_ = lean_ctor_get(v_cfg_1165_, 26);
v_fixedToolchain_1199_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*27 + 6);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_cfg_1165_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v_cfg_1165_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_builtinLint_x3f_1198_);
lean_inc(v_restoreAllArtifacts_x3f_1195_);
lean_inc(v_enableArtifactCache_x3f_1194_);
lean_inc(v_readmeFile_1192_);
lean_inc(v_licenseFiles_1191_);
lean_inc(v_license_1190_);
lean_inc(v_homepage_1189_);
lean_inc(v_keywords_1188_);
lean_inc(v_description_1187_);
lean_inc(v_versionTags_1186_);
lean_inc(v_version_1185_);
lean_inc(v_lintDriverArgs_1184_);
lean_inc(v_lintDriver_1183_);
lean_inc(v_testDriverArgs_1182_);
lean_inc(v_testDriver_1181_);
lean_inc(v_buildArchive_1179_);
lean_inc(v_releaseRepo_1178_);
lean_inc(v_irDir_1177_);
lean_inc(v_binDir_1176_);
lean_inc(v_nativeLibDir_1175_);
lean_inc(v_leanLibDir_1174_);
lean_inc(v_buildDir_1173_);
lean_inc(v_srcDir_1172_);
lean_inc(v_moreGlobalServerArgs_1171_);
lean_inc(v_extraDepTargets_1169_);
lean_inc(v_toLeanConfig_1167_);
lean_inc(v_toWorkspaceConfig_1166_);
lean_dec(v_cfg_1165_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_apply_1(v_f_1164_, v_irDir_1177_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 9, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_toWorkspaceConfig_1166_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_toLeanConfig_1167_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_extraDepTargets_1169_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_moreGlobalServerArgs_1171_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_srcDir_1172_);
lean_ctor_set(v_reuseFailAlloc_1206_, 5, v_buildDir_1173_);
lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_leanLibDir_1174_);
lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_nativeLibDir_1175_);
lean_ctor_set(v_reuseFailAlloc_1206_, 8, v_binDir_1176_);
lean_ctor_set(v_reuseFailAlloc_1206_, 9, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1206_, 10, v_releaseRepo_1178_);
lean_ctor_set(v_reuseFailAlloc_1206_, 11, v_buildArchive_1179_);
lean_ctor_set(v_reuseFailAlloc_1206_, 12, v_testDriver_1181_);
lean_ctor_set(v_reuseFailAlloc_1206_, 13, v_testDriverArgs_1182_);
lean_ctor_set(v_reuseFailAlloc_1206_, 14, v_lintDriver_1183_);
lean_ctor_set(v_reuseFailAlloc_1206_, 15, v_lintDriverArgs_1184_);
lean_ctor_set(v_reuseFailAlloc_1206_, 16, v_version_1185_);
lean_ctor_set(v_reuseFailAlloc_1206_, 17, v_versionTags_1186_);
lean_ctor_set(v_reuseFailAlloc_1206_, 18, v_description_1187_);
lean_ctor_set(v_reuseFailAlloc_1206_, 19, v_keywords_1188_);
lean_ctor_set(v_reuseFailAlloc_1206_, 20, v_homepage_1189_);
lean_ctor_set(v_reuseFailAlloc_1206_, 21, v_license_1190_);
lean_ctor_set(v_reuseFailAlloc_1206_, 22, v_licenseFiles_1191_);
lean_ctor_set(v_reuseFailAlloc_1206_, 23, v_readmeFile_1192_);
lean_ctor_set(v_reuseFailAlloc_1206_, 24, v_enableArtifactCache_x3f_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 25, v_restoreAllArtifacts_x3f_1195_);
lean_ctor_set(v_reuseFailAlloc_1206_, 26, v_builtinLint_x3f_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27, v_bootstrap_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27 + 1, v_precompileModules_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27 + 3, v_reservoir_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27 + 5, v_allowImportAll_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*27 + 6, v_fixedToolchain_1199_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* v_x_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lake_defaultIrDir;
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lake_PackageConfig_irDir___proj___lam__3(v_x_1210_);
lean_dec_ref(v_x_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1221_, lean_object* v_n_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1224_, lean_object* v_n_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lake_PackageConfig_irDir___proj(v_p_1224_, v_n_1225_);
lean_dec(v_n_1225_);
lean_dec(v_p_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1227_, lean_object* v_n_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lake_PackageConfig_irDir___proj(v_p_1227_, v_n_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1230_, lean_object* v_n_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1230_, v_n_1231_);
lean_dec(v_n_1231_);
lean_dec(v_p_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* v_cfg_1233_){
_start:
{
lean_object* v_releaseRepo_1234_; 
v_releaseRepo_1234_ = lean_ctor_get(v_cfg_1233_, 10);
lean_inc(v_releaseRepo_1234_);
return v_releaseRepo_1234_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* v_cfg_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lake_PackageConfig_releaseRepo___proj___lam__0(v_cfg_1235_);
lean_dec_ref(v_cfg_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* v_val_1237_, lean_object* v_cfg_1238_){
_start:
{
lean_object* v_toWorkspaceConfig_1239_; lean_object* v_toLeanConfig_1240_; uint8_t v_bootstrap_1241_; lean_object* v_extraDepTargets_1242_; uint8_t v_precompileModules_1243_; lean_object* v_moreGlobalServerArgs_1244_; lean_object* v_srcDir_1245_; lean_object* v_buildDir_1246_; lean_object* v_leanLibDir_1247_; lean_object* v_nativeLibDir_1248_; lean_object* v_binDir_1249_; lean_object* v_irDir_1250_; lean_object* v_buildArchive_1251_; uint8_t v_preferReleaseBuild_1252_; lean_object* v_testDriver_1253_; lean_object* v_testDriverArgs_1254_; lean_object* v_lintDriver_1255_; lean_object* v_lintDriverArgs_1256_; lean_object* v_version_1257_; lean_object* v_versionTags_1258_; lean_object* v_description_1259_; lean_object* v_keywords_1260_; lean_object* v_homepage_1261_; lean_object* v_license_1262_; lean_object* v_licenseFiles_1263_; lean_object* v_readmeFile_1264_; uint8_t v_reservoir_1265_; lean_object* v_enableArtifactCache_x3f_1266_; lean_object* v_restoreAllArtifacts_x3f_1267_; uint8_t v_libPrefixOnWindows_1268_; uint8_t v_allowImportAll_1269_; lean_object* v_builtinLint_x3f_1270_; uint8_t v_fixedToolchain_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_toWorkspaceConfig_1239_ = lean_ctor_get(v_cfg_1238_, 0);
v_toLeanConfig_1240_ = lean_ctor_get(v_cfg_1238_, 1);
v_bootstrap_1241_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27);
v_extraDepTargets_1242_ = lean_ctor_get(v_cfg_1238_, 2);
v_precompileModules_1243_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1244_ = lean_ctor_get(v_cfg_1238_, 3);
v_srcDir_1245_ = lean_ctor_get(v_cfg_1238_, 4);
v_buildDir_1246_ = lean_ctor_get(v_cfg_1238_, 5);
v_leanLibDir_1247_ = lean_ctor_get(v_cfg_1238_, 6);
v_nativeLibDir_1248_ = lean_ctor_get(v_cfg_1238_, 7);
v_binDir_1249_ = lean_ctor_get(v_cfg_1238_, 8);
v_irDir_1250_ = lean_ctor_get(v_cfg_1238_, 9);
v_buildArchive_1251_ = lean_ctor_get(v_cfg_1238_, 11);
v_preferReleaseBuild_1252_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27 + 2);
v_testDriver_1253_ = lean_ctor_get(v_cfg_1238_, 12);
v_testDriverArgs_1254_ = lean_ctor_get(v_cfg_1238_, 13);
v_lintDriver_1255_ = lean_ctor_get(v_cfg_1238_, 14);
v_lintDriverArgs_1256_ = lean_ctor_get(v_cfg_1238_, 15);
v_version_1257_ = lean_ctor_get(v_cfg_1238_, 16);
v_versionTags_1258_ = lean_ctor_get(v_cfg_1238_, 17);
v_description_1259_ = lean_ctor_get(v_cfg_1238_, 18);
v_keywords_1260_ = lean_ctor_get(v_cfg_1238_, 19);
v_homepage_1261_ = lean_ctor_get(v_cfg_1238_, 20);
v_license_1262_ = lean_ctor_get(v_cfg_1238_, 21);
v_licenseFiles_1263_ = lean_ctor_get(v_cfg_1238_, 22);
v_readmeFile_1264_ = lean_ctor_get(v_cfg_1238_, 23);
v_reservoir_1265_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1266_ = lean_ctor_get(v_cfg_1238_, 24);
v_restoreAllArtifacts_x3f_1267_ = lean_ctor_get(v_cfg_1238_, 25);
v_libPrefixOnWindows_1268_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27 + 4);
v_allowImportAll_1269_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1270_ = lean_ctor_get(v_cfg_1238_, 26);
v_fixedToolchain_1271_ = lean_ctor_get_uint8(v_cfg_1238_, sizeof(void*)*27 + 6);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_cfg_1238_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v_cfg_1238_, 10);
lean_dec(v_unused_1279_);
v___x_1273_ = v_cfg_1238_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_builtinLint_x3f_1270_);
lean_inc(v_restoreAllArtifacts_x3f_1267_);
lean_inc(v_enableArtifactCache_x3f_1266_);
lean_inc(v_readmeFile_1264_);
lean_inc(v_licenseFiles_1263_);
lean_inc(v_license_1262_);
lean_inc(v_homepage_1261_);
lean_inc(v_keywords_1260_);
lean_inc(v_description_1259_);
lean_inc(v_versionTags_1258_);
lean_inc(v_version_1257_);
lean_inc(v_lintDriverArgs_1256_);
lean_inc(v_lintDriver_1255_);
lean_inc(v_testDriverArgs_1254_);
lean_inc(v_testDriver_1253_);
lean_inc(v_buildArchive_1251_);
lean_inc(v_irDir_1250_);
lean_inc(v_binDir_1249_);
lean_inc(v_nativeLibDir_1248_);
lean_inc(v_leanLibDir_1247_);
lean_inc(v_buildDir_1246_);
lean_inc(v_srcDir_1245_);
lean_inc(v_moreGlobalServerArgs_1244_);
lean_inc(v_extraDepTargets_1242_);
lean_inc(v_toLeanConfig_1240_);
lean_inc(v_toWorkspaceConfig_1239_);
lean_dec(v_cfg_1238_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 10, v_val_1237_);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_toWorkspaceConfig_1239_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_toLeanConfig_1240_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_extraDepTargets_1242_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_moreGlobalServerArgs_1244_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_srcDir_1245_);
lean_ctor_set(v_reuseFailAlloc_1277_, 5, v_buildDir_1246_);
lean_ctor_set(v_reuseFailAlloc_1277_, 6, v_leanLibDir_1247_);
lean_ctor_set(v_reuseFailAlloc_1277_, 7, v_nativeLibDir_1248_);
lean_ctor_set(v_reuseFailAlloc_1277_, 8, v_binDir_1249_);
lean_ctor_set(v_reuseFailAlloc_1277_, 9, v_irDir_1250_);
lean_ctor_set(v_reuseFailAlloc_1277_, 10, v_val_1237_);
lean_ctor_set(v_reuseFailAlloc_1277_, 11, v_buildArchive_1251_);
lean_ctor_set(v_reuseFailAlloc_1277_, 12, v_testDriver_1253_);
lean_ctor_set(v_reuseFailAlloc_1277_, 13, v_testDriverArgs_1254_);
lean_ctor_set(v_reuseFailAlloc_1277_, 14, v_lintDriver_1255_);
lean_ctor_set(v_reuseFailAlloc_1277_, 15, v_lintDriverArgs_1256_);
lean_ctor_set(v_reuseFailAlloc_1277_, 16, v_version_1257_);
lean_ctor_set(v_reuseFailAlloc_1277_, 17, v_versionTags_1258_);
lean_ctor_set(v_reuseFailAlloc_1277_, 18, v_description_1259_);
lean_ctor_set(v_reuseFailAlloc_1277_, 19, v_keywords_1260_);
lean_ctor_set(v_reuseFailAlloc_1277_, 20, v_homepage_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 21, v_license_1262_);
lean_ctor_set(v_reuseFailAlloc_1277_, 22, v_licenseFiles_1263_);
lean_ctor_set(v_reuseFailAlloc_1277_, 23, v_readmeFile_1264_);
lean_ctor_set(v_reuseFailAlloc_1277_, 24, v_enableArtifactCache_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1277_, 25, v_restoreAllArtifacts_x3f_1267_);
lean_ctor_set(v_reuseFailAlloc_1277_, 26, v_builtinLint_x3f_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27, v_bootstrap_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27 + 1, v_precompileModules_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27 + 3, v_reservoir_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27 + 5, v_allowImportAll_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*27 + 6, v_fixedToolchain_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* v_f_1280_, lean_object* v_cfg_1281_){
_start:
{
lean_object* v_toWorkspaceConfig_1282_; lean_object* v_toLeanConfig_1283_; uint8_t v_bootstrap_1284_; lean_object* v_extraDepTargets_1285_; uint8_t v_precompileModules_1286_; lean_object* v_moreGlobalServerArgs_1287_; lean_object* v_srcDir_1288_; lean_object* v_buildDir_1289_; lean_object* v_leanLibDir_1290_; lean_object* v_nativeLibDir_1291_; lean_object* v_binDir_1292_; lean_object* v_irDir_1293_; lean_object* v_releaseRepo_1294_; lean_object* v_buildArchive_1295_; uint8_t v_preferReleaseBuild_1296_; lean_object* v_testDriver_1297_; lean_object* v_testDriverArgs_1298_; lean_object* v_lintDriver_1299_; lean_object* v_lintDriverArgs_1300_; lean_object* v_version_1301_; lean_object* v_versionTags_1302_; lean_object* v_description_1303_; lean_object* v_keywords_1304_; lean_object* v_homepage_1305_; lean_object* v_license_1306_; lean_object* v_licenseFiles_1307_; lean_object* v_readmeFile_1308_; uint8_t v_reservoir_1309_; lean_object* v_enableArtifactCache_x3f_1310_; lean_object* v_restoreAllArtifacts_x3f_1311_; uint8_t v_libPrefixOnWindows_1312_; uint8_t v_allowImportAll_1313_; lean_object* v_builtinLint_x3f_1314_; uint8_t v_fixedToolchain_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
v_toWorkspaceConfig_1282_ = lean_ctor_get(v_cfg_1281_, 0);
v_toLeanConfig_1283_ = lean_ctor_get(v_cfg_1281_, 1);
v_bootstrap_1284_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27);
v_extraDepTargets_1285_ = lean_ctor_get(v_cfg_1281_, 2);
v_precompileModules_1286_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1287_ = lean_ctor_get(v_cfg_1281_, 3);
v_srcDir_1288_ = lean_ctor_get(v_cfg_1281_, 4);
v_buildDir_1289_ = lean_ctor_get(v_cfg_1281_, 5);
v_leanLibDir_1290_ = lean_ctor_get(v_cfg_1281_, 6);
v_nativeLibDir_1291_ = lean_ctor_get(v_cfg_1281_, 7);
v_binDir_1292_ = lean_ctor_get(v_cfg_1281_, 8);
v_irDir_1293_ = lean_ctor_get(v_cfg_1281_, 9);
v_releaseRepo_1294_ = lean_ctor_get(v_cfg_1281_, 10);
v_buildArchive_1295_ = lean_ctor_get(v_cfg_1281_, 11);
v_preferReleaseBuild_1296_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27 + 2);
v_testDriver_1297_ = lean_ctor_get(v_cfg_1281_, 12);
v_testDriverArgs_1298_ = lean_ctor_get(v_cfg_1281_, 13);
v_lintDriver_1299_ = lean_ctor_get(v_cfg_1281_, 14);
v_lintDriverArgs_1300_ = lean_ctor_get(v_cfg_1281_, 15);
v_version_1301_ = lean_ctor_get(v_cfg_1281_, 16);
v_versionTags_1302_ = lean_ctor_get(v_cfg_1281_, 17);
v_description_1303_ = lean_ctor_get(v_cfg_1281_, 18);
v_keywords_1304_ = lean_ctor_get(v_cfg_1281_, 19);
v_homepage_1305_ = lean_ctor_get(v_cfg_1281_, 20);
v_license_1306_ = lean_ctor_get(v_cfg_1281_, 21);
v_licenseFiles_1307_ = lean_ctor_get(v_cfg_1281_, 22);
v_readmeFile_1308_ = lean_ctor_get(v_cfg_1281_, 23);
v_reservoir_1309_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1310_ = lean_ctor_get(v_cfg_1281_, 24);
v_restoreAllArtifacts_x3f_1311_ = lean_ctor_get(v_cfg_1281_, 25);
v_libPrefixOnWindows_1312_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27 + 4);
v_allowImportAll_1313_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1314_ = lean_ctor_get(v_cfg_1281_, 26);
v_fixedToolchain_1315_ = lean_ctor_get_uint8(v_cfg_1281_, sizeof(void*)*27 + 6);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_cfg_1281_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1317_ = v_cfg_1281_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_builtinLint_x3f_1314_);
lean_inc(v_restoreAllArtifacts_x3f_1311_);
lean_inc(v_enableArtifactCache_x3f_1310_);
lean_inc(v_readmeFile_1308_);
lean_inc(v_licenseFiles_1307_);
lean_inc(v_license_1306_);
lean_inc(v_homepage_1305_);
lean_inc(v_keywords_1304_);
lean_inc(v_description_1303_);
lean_inc(v_versionTags_1302_);
lean_inc(v_version_1301_);
lean_inc(v_lintDriverArgs_1300_);
lean_inc(v_lintDriver_1299_);
lean_inc(v_testDriverArgs_1298_);
lean_inc(v_testDriver_1297_);
lean_inc(v_buildArchive_1295_);
lean_inc(v_releaseRepo_1294_);
lean_inc(v_irDir_1293_);
lean_inc(v_binDir_1292_);
lean_inc(v_nativeLibDir_1291_);
lean_inc(v_leanLibDir_1290_);
lean_inc(v_buildDir_1289_);
lean_inc(v_srcDir_1288_);
lean_inc(v_moreGlobalServerArgs_1287_);
lean_inc(v_extraDepTargets_1285_);
lean_inc(v_toLeanConfig_1283_);
lean_inc(v_toWorkspaceConfig_1282_);
lean_dec(v_cfg_1281_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_apply_1(v_f_1280_, v_releaseRepo_1294_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 10, v___x_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_toWorkspaceConfig_1282_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_toLeanConfig_1283_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_extraDepTargets_1285_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_moreGlobalServerArgs_1287_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_srcDir_1288_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v_buildDir_1289_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v_leanLibDir_1290_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_nativeLibDir_1291_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v_binDir_1292_);
lean_ctor_set(v_reuseFailAlloc_1322_, 9, v_irDir_1293_);
lean_ctor_set(v_reuseFailAlloc_1322_, 10, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 11, v_buildArchive_1295_);
lean_ctor_set(v_reuseFailAlloc_1322_, 12, v_testDriver_1297_);
lean_ctor_set(v_reuseFailAlloc_1322_, 13, v_testDriverArgs_1298_);
lean_ctor_set(v_reuseFailAlloc_1322_, 14, v_lintDriver_1299_);
lean_ctor_set(v_reuseFailAlloc_1322_, 15, v_lintDriverArgs_1300_);
lean_ctor_set(v_reuseFailAlloc_1322_, 16, v_version_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 17, v_versionTags_1302_);
lean_ctor_set(v_reuseFailAlloc_1322_, 18, v_description_1303_);
lean_ctor_set(v_reuseFailAlloc_1322_, 19, v_keywords_1304_);
lean_ctor_set(v_reuseFailAlloc_1322_, 20, v_homepage_1305_);
lean_ctor_set(v_reuseFailAlloc_1322_, 21, v_license_1306_);
lean_ctor_set(v_reuseFailAlloc_1322_, 22, v_licenseFiles_1307_);
lean_ctor_set(v_reuseFailAlloc_1322_, 23, v_readmeFile_1308_);
lean_ctor_set(v_reuseFailAlloc_1322_, 24, v_enableArtifactCache_x3f_1310_);
lean_ctor_set(v_reuseFailAlloc_1322_, 25, v_restoreAllArtifacts_x3f_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 26, v_builtinLint_x3f_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27, v_bootstrap_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27 + 1, v_precompileModules_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27 + 3, v_reservoir_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27 + 5, v_allowImportAll_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*27 + 6, v_fixedToolchain_1315_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3(lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_box(0);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed(lean_object* v_x_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_PackageConfig_releaseRepo___proj___lam__3(v_x_1326_);
lean_dec_ref(v_x_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1337_, lean_object* v_n_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__4));
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1340_, lean_object* v_n_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1340_, v_n_1341_);
lean_dec(v_n_1341_);
lean_dec(v_p_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1343_, lean_object* v_n_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1343_, v_n_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1346_, lean_object* v_n_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1346_, v_n_1347_);
lean_dec(v_n_1347_);
lean_dec(v_p_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1349_, lean_object* v_n_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1349_, v_n_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1352_, lean_object* v_n_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1352_, v_n_1353_);
lean_dec(v_n_1353_);
lean_dec(v_p_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* v_cfg_1355_){
_start:
{
lean_object* v_buildArchive_1356_; 
v_buildArchive_1356_ = lean_ctor_get(v_cfg_1355_, 11);
lean_inc(v_buildArchive_1356_);
return v_buildArchive_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* v_cfg_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lake_PackageConfig_buildArchive___proj___lam__0(v_cfg_1357_);
lean_dec_ref(v_cfg_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* v_val_1359_, lean_object* v_cfg_1360_){
_start:
{
lean_object* v_toWorkspaceConfig_1361_; lean_object* v_toLeanConfig_1362_; uint8_t v_bootstrap_1363_; lean_object* v_extraDepTargets_1364_; uint8_t v_precompileModules_1365_; lean_object* v_moreGlobalServerArgs_1366_; lean_object* v_srcDir_1367_; lean_object* v_buildDir_1368_; lean_object* v_leanLibDir_1369_; lean_object* v_nativeLibDir_1370_; lean_object* v_binDir_1371_; lean_object* v_irDir_1372_; lean_object* v_releaseRepo_1373_; uint8_t v_preferReleaseBuild_1374_; lean_object* v_testDriver_1375_; lean_object* v_testDriverArgs_1376_; lean_object* v_lintDriver_1377_; lean_object* v_lintDriverArgs_1378_; lean_object* v_version_1379_; lean_object* v_versionTags_1380_; lean_object* v_description_1381_; lean_object* v_keywords_1382_; lean_object* v_homepage_1383_; lean_object* v_license_1384_; lean_object* v_licenseFiles_1385_; lean_object* v_readmeFile_1386_; uint8_t v_reservoir_1387_; lean_object* v_enableArtifactCache_x3f_1388_; lean_object* v_restoreAllArtifacts_x3f_1389_; uint8_t v_libPrefixOnWindows_1390_; uint8_t v_allowImportAll_1391_; lean_object* v_builtinLint_x3f_1392_; uint8_t v_fixedToolchain_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_toWorkspaceConfig_1361_ = lean_ctor_get(v_cfg_1360_, 0);
v_toLeanConfig_1362_ = lean_ctor_get(v_cfg_1360_, 1);
v_bootstrap_1363_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27);
v_extraDepTargets_1364_ = lean_ctor_get(v_cfg_1360_, 2);
v_precompileModules_1365_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1366_ = lean_ctor_get(v_cfg_1360_, 3);
v_srcDir_1367_ = lean_ctor_get(v_cfg_1360_, 4);
v_buildDir_1368_ = lean_ctor_get(v_cfg_1360_, 5);
v_leanLibDir_1369_ = lean_ctor_get(v_cfg_1360_, 6);
v_nativeLibDir_1370_ = lean_ctor_get(v_cfg_1360_, 7);
v_binDir_1371_ = lean_ctor_get(v_cfg_1360_, 8);
v_irDir_1372_ = lean_ctor_get(v_cfg_1360_, 9);
v_releaseRepo_1373_ = lean_ctor_get(v_cfg_1360_, 10);
v_preferReleaseBuild_1374_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27 + 2);
v_testDriver_1375_ = lean_ctor_get(v_cfg_1360_, 12);
v_testDriverArgs_1376_ = lean_ctor_get(v_cfg_1360_, 13);
v_lintDriver_1377_ = lean_ctor_get(v_cfg_1360_, 14);
v_lintDriverArgs_1378_ = lean_ctor_get(v_cfg_1360_, 15);
v_version_1379_ = lean_ctor_get(v_cfg_1360_, 16);
v_versionTags_1380_ = lean_ctor_get(v_cfg_1360_, 17);
v_description_1381_ = lean_ctor_get(v_cfg_1360_, 18);
v_keywords_1382_ = lean_ctor_get(v_cfg_1360_, 19);
v_homepage_1383_ = lean_ctor_get(v_cfg_1360_, 20);
v_license_1384_ = lean_ctor_get(v_cfg_1360_, 21);
v_licenseFiles_1385_ = lean_ctor_get(v_cfg_1360_, 22);
v_readmeFile_1386_ = lean_ctor_get(v_cfg_1360_, 23);
v_reservoir_1387_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1388_ = lean_ctor_get(v_cfg_1360_, 24);
v_restoreAllArtifacts_x3f_1389_ = lean_ctor_get(v_cfg_1360_, 25);
v_libPrefixOnWindows_1390_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27 + 4);
v_allowImportAll_1391_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1392_ = lean_ctor_get(v_cfg_1360_, 26);
v_fixedToolchain_1393_ = lean_ctor_get_uint8(v_cfg_1360_, sizeof(void*)*27 + 6);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_cfg_1360_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_cfg_1360_, 11);
lean_dec(v_unused_1401_);
v___x_1395_ = v_cfg_1360_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_builtinLint_x3f_1392_);
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
lean_inc(v_releaseRepo_1373_);
lean_inc(v_irDir_1372_);
lean_inc(v_binDir_1371_);
lean_inc(v_nativeLibDir_1370_);
lean_inc(v_leanLibDir_1369_);
lean_inc(v_buildDir_1368_);
lean_inc(v_srcDir_1367_);
lean_inc(v_moreGlobalServerArgs_1366_);
lean_inc(v_extraDepTargets_1364_);
lean_inc(v_toLeanConfig_1362_);
lean_inc(v_toWorkspaceConfig_1361_);
lean_dec(v_cfg_1360_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 11, v_val_1359_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_toWorkspaceConfig_1361_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_toLeanConfig_1362_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_extraDepTargets_1364_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_moreGlobalServerArgs_1366_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_srcDir_1367_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_buildDir_1368_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_leanLibDir_1369_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_nativeLibDir_1370_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_binDir_1371_);
lean_ctor_set(v_reuseFailAlloc_1399_, 9, v_irDir_1372_);
lean_ctor_set(v_reuseFailAlloc_1399_, 10, v_releaseRepo_1373_);
lean_ctor_set(v_reuseFailAlloc_1399_, 11, v_val_1359_);
lean_ctor_set(v_reuseFailAlloc_1399_, 12, v_testDriver_1375_);
lean_ctor_set(v_reuseFailAlloc_1399_, 13, v_testDriverArgs_1376_);
lean_ctor_set(v_reuseFailAlloc_1399_, 14, v_lintDriver_1377_);
lean_ctor_set(v_reuseFailAlloc_1399_, 15, v_lintDriverArgs_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 16, v_version_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 17, v_versionTags_1380_);
lean_ctor_set(v_reuseFailAlloc_1399_, 18, v_description_1381_);
lean_ctor_set(v_reuseFailAlloc_1399_, 19, v_keywords_1382_);
lean_ctor_set(v_reuseFailAlloc_1399_, 20, v_homepage_1383_);
lean_ctor_set(v_reuseFailAlloc_1399_, 21, v_license_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 22, v_licenseFiles_1385_);
lean_ctor_set(v_reuseFailAlloc_1399_, 23, v_readmeFile_1386_);
lean_ctor_set(v_reuseFailAlloc_1399_, 24, v_enableArtifactCache_x3f_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 25, v_restoreAllArtifacts_x3f_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 26, v_builtinLint_x3f_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27, v_bootstrap_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27 + 1, v_precompileModules_1365_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27 + 3, v_reservoir_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27 + 5, v_allowImportAll_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1399_, sizeof(void*)*27 + 6, v_fixedToolchain_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* v_f_1402_, lean_object* v_cfg_1403_){
_start:
{
lean_object* v_toWorkspaceConfig_1404_; lean_object* v_toLeanConfig_1405_; uint8_t v_bootstrap_1406_; lean_object* v_extraDepTargets_1407_; uint8_t v_precompileModules_1408_; lean_object* v_moreGlobalServerArgs_1409_; lean_object* v_srcDir_1410_; lean_object* v_buildDir_1411_; lean_object* v_leanLibDir_1412_; lean_object* v_nativeLibDir_1413_; lean_object* v_binDir_1414_; lean_object* v_irDir_1415_; lean_object* v_releaseRepo_1416_; lean_object* v_buildArchive_1417_; uint8_t v_preferReleaseBuild_1418_; lean_object* v_testDriver_1419_; lean_object* v_testDriverArgs_1420_; lean_object* v_lintDriver_1421_; lean_object* v_lintDriverArgs_1422_; lean_object* v_version_1423_; lean_object* v_versionTags_1424_; lean_object* v_description_1425_; lean_object* v_keywords_1426_; lean_object* v_homepage_1427_; lean_object* v_license_1428_; lean_object* v_licenseFiles_1429_; lean_object* v_readmeFile_1430_; uint8_t v_reservoir_1431_; lean_object* v_enableArtifactCache_x3f_1432_; lean_object* v_restoreAllArtifacts_x3f_1433_; uint8_t v_libPrefixOnWindows_1434_; uint8_t v_allowImportAll_1435_; lean_object* v_builtinLint_x3f_1436_; uint8_t v_fixedToolchain_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_toWorkspaceConfig_1404_ = lean_ctor_get(v_cfg_1403_, 0);
v_toLeanConfig_1405_ = lean_ctor_get(v_cfg_1403_, 1);
v_bootstrap_1406_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27);
v_extraDepTargets_1407_ = lean_ctor_get(v_cfg_1403_, 2);
v_precompileModules_1408_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1409_ = lean_ctor_get(v_cfg_1403_, 3);
v_srcDir_1410_ = lean_ctor_get(v_cfg_1403_, 4);
v_buildDir_1411_ = lean_ctor_get(v_cfg_1403_, 5);
v_leanLibDir_1412_ = lean_ctor_get(v_cfg_1403_, 6);
v_nativeLibDir_1413_ = lean_ctor_get(v_cfg_1403_, 7);
v_binDir_1414_ = lean_ctor_get(v_cfg_1403_, 8);
v_irDir_1415_ = lean_ctor_get(v_cfg_1403_, 9);
v_releaseRepo_1416_ = lean_ctor_get(v_cfg_1403_, 10);
v_buildArchive_1417_ = lean_ctor_get(v_cfg_1403_, 11);
v_preferReleaseBuild_1418_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27 + 2);
v_testDriver_1419_ = lean_ctor_get(v_cfg_1403_, 12);
v_testDriverArgs_1420_ = lean_ctor_get(v_cfg_1403_, 13);
v_lintDriver_1421_ = lean_ctor_get(v_cfg_1403_, 14);
v_lintDriverArgs_1422_ = lean_ctor_get(v_cfg_1403_, 15);
v_version_1423_ = lean_ctor_get(v_cfg_1403_, 16);
v_versionTags_1424_ = lean_ctor_get(v_cfg_1403_, 17);
v_description_1425_ = lean_ctor_get(v_cfg_1403_, 18);
v_keywords_1426_ = lean_ctor_get(v_cfg_1403_, 19);
v_homepage_1427_ = lean_ctor_get(v_cfg_1403_, 20);
v_license_1428_ = lean_ctor_get(v_cfg_1403_, 21);
v_licenseFiles_1429_ = lean_ctor_get(v_cfg_1403_, 22);
v_readmeFile_1430_ = lean_ctor_get(v_cfg_1403_, 23);
v_reservoir_1431_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1432_ = lean_ctor_get(v_cfg_1403_, 24);
v_restoreAllArtifacts_x3f_1433_ = lean_ctor_get(v_cfg_1403_, 25);
v_libPrefixOnWindows_1434_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27 + 4);
v_allowImportAll_1435_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1436_ = lean_ctor_get(v_cfg_1403_, 26);
v_fixedToolchain_1437_ = lean_ctor_get_uint8(v_cfg_1403_, sizeof(void*)*27 + 6);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_cfg_1403_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v_cfg_1403_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_builtinLint_x3f_1436_);
lean_inc(v_restoreAllArtifacts_x3f_1433_);
lean_inc(v_enableArtifactCache_x3f_1432_);
lean_inc(v_readmeFile_1430_);
lean_inc(v_licenseFiles_1429_);
lean_inc(v_license_1428_);
lean_inc(v_homepage_1427_);
lean_inc(v_keywords_1426_);
lean_inc(v_description_1425_);
lean_inc(v_versionTags_1424_);
lean_inc(v_version_1423_);
lean_inc(v_lintDriverArgs_1422_);
lean_inc(v_lintDriver_1421_);
lean_inc(v_testDriverArgs_1420_);
lean_inc(v_testDriver_1419_);
lean_inc(v_buildArchive_1417_);
lean_inc(v_releaseRepo_1416_);
lean_inc(v_irDir_1415_);
lean_inc(v_binDir_1414_);
lean_inc(v_nativeLibDir_1413_);
lean_inc(v_leanLibDir_1412_);
lean_inc(v_buildDir_1411_);
lean_inc(v_srcDir_1410_);
lean_inc(v_moreGlobalServerArgs_1409_);
lean_inc(v_extraDepTargets_1407_);
lean_inc(v_toLeanConfig_1405_);
lean_inc(v_toWorkspaceConfig_1404_);
lean_dec(v_cfg_1403_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_apply_1(v_f_1402_, v_buildArchive_1417_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 11, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_toWorkspaceConfig_1404_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_toLeanConfig_1405_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_extraDepTargets_1407_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_moreGlobalServerArgs_1409_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_srcDir_1410_);
lean_ctor_set(v_reuseFailAlloc_1444_, 5, v_buildDir_1411_);
lean_ctor_set(v_reuseFailAlloc_1444_, 6, v_leanLibDir_1412_);
lean_ctor_set(v_reuseFailAlloc_1444_, 7, v_nativeLibDir_1413_);
lean_ctor_set(v_reuseFailAlloc_1444_, 8, v_binDir_1414_);
lean_ctor_set(v_reuseFailAlloc_1444_, 9, v_irDir_1415_);
lean_ctor_set(v_reuseFailAlloc_1444_, 10, v_releaseRepo_1416_);
lean_ctor_set(v_reuseFailAlloc_1444_, 11, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1444_, 12, v_testDriver_1419_);
lean_ctor_set(v_reuseFailAlloc_1444_, 13, v_testDriverArgs_1420_);
lean_ctor_set(v_reuseFailAlloc_1444_, 14, v_lintDriver_1421_);
lean_ctor_set(v_reuseFailAlloc_1444_, 15, v_lintDriverArgs_1422_);
lean_ctor_set(v_reuseFailAlloc_1444_, 16, v_version_1423_);
lean_ctor_set(v_reuseFailAlloc_1444_, 17, v_versionTags_1424_);
lean_ctor_set(v_reuseFailAlloc_1444_, 18, v_description_1425_);
lean_ctor_set(v_reuseFailAlloc_1444_, 19, v_keywords_1426_);
lean_ctor_set(v_reuseFailAlloc_1444_, 20, v_homepage_1427_);
lean_ctor_set(v_reuseFailAlloc_1444_, 21, v_license_1428_);
lean_ctor_set(v_reuseFailAlloc_1444_, 22, v_licenseFiles_1429_);
lean_ctor_set(v_reuseFailAlloc_1444_, 23, v_readmeFile_1430_);
lean_ctor_set(v_reuseFailAlloc_1444_, 24, v_enableArtifactCache_x3f_1432_);
lean_ctor_set(v_reuseFailAlloc_1444_, 25, v_restoreAllArtifacts_x3f_1433_);
lean_ctor_set(v_reuseFailAlloc_1444_, 26, v_builtinLint_x3f_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27, v_bootstrap_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27 + 1, v_precompileModules_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27 + 3, v_reservoir_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27 + 5, v_allowImportAll_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*27 + 6, v_fixedToolchain_1437_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1454_, lean_object* v_n_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1457_, lean_object* v_n_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1457_, v_n_1458_);
lean_dec(v_n_1458_);
lean_dec(v_p_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1460_, lean_object* v_n_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1460_, v_n_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1463_, lean_object* v_n_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1463_, v_n_1464_);
lean_dec(v_n_1464_);
lean_dec(v_p_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1466_, lean_object* v_n_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1466_, v_n_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1469_, lean_object* v_n_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1469_, v_n_1470_);
lean_dec(v_n_1470_);
lean_dec(v_p_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* v_cfg_1472_){
_start:
{
uint8_t v_preferReleaseBuild_1473_; 
v_preferReleaseBuild_1473_ = lean_ctor_get_uint8(v_cfg_1472_, sizeof(void*)*27 + 2);
return v_preferReleaseBuild_1473_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* v_cfg_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(v_cfg_1474_);
lean_dec_ref(v_cfg_1474_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t v_val_1477_, lean_object* v_cfg_1478_){
_start:
{
lean_object* v_toWorkspaceConfig_1479_; lean_object* v_toLeanConfig_1480_; uint8_t v_bootstrap_1481_; lean_object* v_extraDepTargets_1482_; uint8_t v_precompileModules_1483_; lean_object* v_moreGlobalServerArgs_1484_; lean_object* v_srcDir_1485_; lean_object* v_buildDir_1486_; lean_object* v_leanLibDir_1487_; lean_object* v_nativeLibDir_1488_; lean_object* v_binDir_1489_; lean_object* v_irDir_1490_; lean_object* v_releaseRepo_1491_; lean_object* v_buildArchive_1492_; lean_object* v_testDriver_1493_; lean_object* v_testDriverArgs_1494_; lean_object* v_lintDriver_1495_; lean_object* v_lintDriverArgs_1496_; lean_object* v_version_1497_; lean_object* v_versionTags_1498_; lean_object* v_description_1499_; lean_object* v_keywords_1500_; lean_object* v_homepage_1501_; lean_object* v_license_1502_; lean_object* v_licenseFiles_1503_; lean_object* v_readmeFile_1504_; uint8_t v_reservoir_1505_; lean_object* v_enableArtifactCache_x3f_1506_; lean_object* v_restoreAllArtifacts_x3f_1507_; uint8_t v_libPrefixOnWindows_1508_; uint8_t v_allowImportAll_1509_; lean_object* v_builtinLint_x3f_1510_; uint8_t v_fixedToolchain_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_toWorkspaceConfig_1479_ = lean_ctor_get(v_cfg_1478_, 0);
v_toLeanConfig_1480_ = lean_ctor_get(v_cfg_1478_, 1);
v_bootstrap_1481_ = lean_ctor_get_uint8(v_cfg_1478_, sizeof(void*)*27);
v_extraDepTargets_1482_ = lean_ctor_get(v_cfg_1478_, 2);
v_precompileModules_1483_ = lean_ctor_get_uint8(v_cfg_1478_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1484_ = lean_ctor_get(v_cfg_1478_, 3);
v_srcDir_1485_ = lean_ctor_get(v_cfg_1478_, 4);
v_buildDir_1486_ = lean_ctor_get(v_cfg_1478_, 5);
v_leanLibDir_1487_ = lean_ctor_get(v_cfg_1478_, 6);
v_nativeLibDir_1488_ = lean_ctor_get(v_cfg_1478_, 7);
v_binDir_1489_ = lean_ctor_get(v_cfg_1478_, 8);
v_irDir_1490_ = lean_ctor_get(v_cfg_1478_, 9);
v_releaseRepo_1491_ = lean_ctor_get(v_cfg_1478_, 10);
v_buildArchive_1492_ = lean_ctor_get(v_cfg_1478_, 11);
v_testDriver_1493_ = lean_ctor_get(v_cfg_1478_, 12);
v_testDriverArgs_1494_ = lean_ctor_get(v_cfg_1478_, 13);
v_lintDriver_1495_ = lean_ctor_get(v_cfg_1478_, 14);
v_lintDriverArgs_1496_ = lean_ctor_get(v_cfg_1478_, 15);
v_version_1497_ = lean_ctor_get(v_cfg_1478_, 16);
v_versionTags_1498_ = lean_ctor_get(v_cfg_1478_, 17);
v_description_1499_ = lean_ctor_get(v_cfg_1478_, 18);
v_keywords_1500_ = lean_ctor_get(v_cfg_1478_, 19);
v_homepage_1501_ = lean_ctor_get(v_cfg_1478_, 20);
v_license_1502_ = lean_ctor_get(v_cfg_1478_, 21);
v_licenseFiles_1503_ = lean_ctor_get(v_cfg_1478_, 22);
v_readmeFile_1504_ = lean_ctor_get(v_cfg_1478_, 23);
v_reservoir_1505_ = lean_ctor_get_uint8(v_cfg_1478_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1506_ = lean_ctor_get(v_cfg_1478_, 24);
v_restoreAllArtifacts_x3f_1507_ = lean_ctor_get(v_cfg_1478_, 25);
v_libPrefixOnWindows_1508_ = lean_ctor_get_uint8(v_cfg_1478_, sizeof(void*)*27 + 4);
v_allowImportAll_1509_ = lean_ctor_get_uint8(v_cfg_1478_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1510_ = lean_ctor_get(v_cfg_1478_, 26);
v_fixedToolchain_1511_ = lean_ctor_get_uint8(v_cfg_1478_, sizeof(void*)*27 + 6);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_cfg_1478_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v_cfg_1478_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_builtinLint_x3f_1510_);
lean_inc(v_restoreAllArtifacts_x3f_1507_);
lean_inc(v_enableArtifactCache_x3f_1506_);
lean_inc(v_readmeFile_1504_);
lean_inc(v_licenseFiles_1503_);
lean_inc(v_license_1502_);
lean_inc(v_homepage_1501_);
lean_inc(v_keywords_1500_);
lean_inc(v_description_1499_);
lean_inc(v_versionTags_1498_);
lean_inc(v_version_1497_);
lean_inc(v_lintDriverArgs_1496_);
lean_inc(v_lintDriver_1495_);
lean_inc(v_testDriverArgs_1494_);
lean_inc(v_testDriver_1493_);
lean_inc(v_buildArchive_1492_);
lean_inc(v_releaseRepo_1491_);
lean_inc(v_irDir_1490_);
lean_inc(v_binDir_1489_);
lean_inc(v_nativeLibDir_1488_);
lean_inc(v_leanLibDir_1487_);
lean_inc(v_buildDir_1486_);
lean_inc(v_srcDir_1485_);
lean_inc(v_moreGlobalServerArgs_1484_);
lean_inc(v_extraDepTargets_1482_);
lean_inc(v_toLeanConfig_1480_);
lean_inc(v_toWorkspaceConfig_1479_);
lean_dec(v_cfg_1478_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_toWorkspaceConfig_1479_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_toLeanConfig_1480_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_extraDepTargets_1482_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_moreGlobalServerArgs_1484_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_srcDir_1485_);
lean_ctor_set(v_reuseFailAlloc_1517_, 5, v_buildDir_1486_);
lean_ctor_set(v_reuseFailAlloc_1517_, 6, v_leanLibDir_1487_);
lean_ctor_set(v_reuseFailAlloc_1517_, 7, v_nativeLibDir_1488_);
lean_ctor_set(v_reuseFailAlloc_1517_, 8, v_binDir_1489_);
lean_ctor_set(v_reuseFailAlloc_1517_, 9, v_irDir_1490_);
lean_ctor_set(v_reuseFailAlloc_1517_, 10, v_releaseRepo_1491_);
lean_ctor_set(v_reuseFailAlloc_1517_, 11, v_buildArchive_1492_);
lean_ctor_set(v_reuseFailAlloc_1517_, 12, v_testDriver_1493_);
lean_ctor_set(v_reuseFailAlloc_1517_, 13, v_testDriverArgs_1494_);
lean_ctor_set(v_reuseFailAlloc_1517_, 14, v_lintDriver_1495_);
lean_ctor_set(v_reuseFailAlloc_1517_, 15, v_lintDriverArgs_1496_);
lean_ctor_set(v_reuseFailAlloc_1517_, 16, v_version_1497_);
lean_ctor_set(v_reuseFailAlloc_1517_, 17, v_versionTags_1498_);
lean_ctor_set(v_reuseFailAlloc_1517_, 18, v_description_1499_);
lean_ctor_set(v_reuseFailAlloc_1517_, 19, v_keywords_1500_);
lean_ctor_set(v_reuseFailAlloc_1517_, 20, v_homepage_1501_);
lean_ctor_set(v_reuseFailAlloc_1517_, 21, v_license_1502_);
lean_ctor_set(v_reuseFailAlloc_1517_, 22, v_licenseFiles_1503_);
lean_ctor_set(v_reuseFailAlloc_1517_, 23, v_readmeFile_1504_);
lean_ctor_set(v_reuseFailAlloc_1517_, 24, v_enableArtifactCache_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1517_, 25, v_restoreAllArtifacts_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1517_, 26, v_builtinLint_x3f_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*27, v_bootstrap_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*27 + 1, v_precompileModules_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*27 + 3, v_reservoir_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*27 + 5, v_allowImportAll_1509_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*27 + 6, v_fixedToolchain_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*27 + 2, v_val_1477_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* v_val_1519_, lean_object* v_cfg_1520_){
_start:
{
uint8_t v_val_137__boxed_1521_; lean_object* v_res_1522_; 
v_val_137__boxed_1521_ = lean_unbox(v_val_1519_);
v_res_1522_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(v_val_137__boxed_1521_, v_cfg_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* v_f_1523_, lean_object* v_cfg_1524_){
_start:
{
lean_object* v_toWorkspaceConfig_1525_; lean_object* v_toLeanConfig_1526_; uint8_t v_bootstrap_1527_; lean_object* v_extraDepTargets_1528_; uint8_t v_precompileModules_1529_; lean_object* v_moreGlobalServerArgs_1530_; lean_object* v_srcDir_1531_; lean_object* v_buildDir_1532_; lean_object* v_leanLibDir_1533_; lean_object* v_nativeLibDir_1534_; lean_object* v_binDir_1535_; lean_object* v_irDir_1536_; lean_object* v_releaseRepo_1537_; lean_object* v_buildArchive_1538_; uint8_t v_preferReleaseBuild_1539_; lean_object* v_testDriver_1540_; lean_object* v_testDriverArgs_1541_; lean_object* v_lintDriver_1542_; lean_object* v_lintDriverArgs_1543_; lean_object* v_version_1544_; lean_object* v_versionTags_1545_; lean_object* v_description_1546_; lean_object* v_keywords_1547_; lean_object* v_homepage_1548_; lean_object* v_license_1549_; lean_object* v_licenseFiles_1550_; lean_object* v_readmeFile_1551_; uint8_t v_reservoir_1552_; lean_object* v_enableArtifactCache_x3f_1553_; lean_object* v_restoreAllArtifacts_x3f_1554_; uint8_t v_libPrefixOnWindows_1555_; uint8_t v_allowImportAll_1556_; lean_object* v_builtinLint_x3f_1557_; uint8_t v_fixedToolchain_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1568_; 
v_toWorkspaceConfig_1525_ = lean_ctor_get(v_cfg_1524_, 0);
v_toLeanConfig_1526_ = lean_ctor_get(v_cfg_1524_, 1);
v_bootstrap_1527_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27);
v_extraDepTargets_1528_ = lean_ctor_get(v_cfg_1524_, 2);
v_precompileModules_1529_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1530_ = lean_ctor_get(v_cfg_1524_, 3);
v_srcDir_1531_ = lean_ctor_get(v_cfg_1524_, 4);
v_buildDir_1532_ = lean_ctor_get(v_cfg_1524_, 5);
v_leanLibDir_1533_ = lean_ctor_get(v_cfg_1524_, 6);
v_nativeLibDir_1534_ = lean_ctor_get(v_cfg_1524_, 7);
v_binDir_1535_ = lean_ctor_get(v_cfg_1524_, 8);
v_irDir_1536_ = lean_ctor_get(v_cfg_1524_, 9);
v_releaseRepo_1537_ = lean_ctor_get(v_cfg_1524_, 10);
v_buildArchive_1538_ = lean_ctor_get(v_cfg_1524_, 11);
v_preferReleaseBuild_1539_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27 + 2);
v_testDriver_1540_ = lean_ctor_get(v_cfg_1524_, 12);
v_testDriverArgs_1541_ = lean_ctor_get(v_cfg_1524_, 13);
v_lintDriver_1542_ = lean_ctor_get(v_cfg_1524_, 14);
v_lintDriverArgs_1543_ = lean_ctor_get(v_cfg_1524_, 15);
v_version_1544_ = lean_ctor_get(v_cfg_1524_, 16);
v_versionTags_1545_ = lean_ctor_get(v_cfg_1524_, 17);
v_description_1546_ = lean_ctor_get(v_cfg_1524_, 18);
v_keywords_1547_ = lean_ctor_get(v_cfg_1524_, 19);
v_homepage_1548_ = lean_ctor_get(v_cfg_1524_, 20);
v_license_1549_ = lean_ctor_get(v_cfg_1524_, 21);
v_licenseFiles_1550_ = lean_ctor_get(v_cfg_1524_, 22);
v_readmeFile_1551_ = lean_ctor_get(v_cfg_1524_, 23);
v_reservoir_1552_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1553_ = lean_ctor_get(v_cfg_1524_, 24);
v_restoreAllArtifacts_x3f_1554_ = lean_ctor_get(v_cfg_1524_, 25);
v_libPrefixOnWindows_1555_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27 + 4);
v_allowImportAll_1556_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1557_ = lean_ctor_get(v_cfg_1524_, 26);
v_fixedToolchain_1558_ = lean_ctor_get_uint8(v_cfg_1524_, sizeof(void*)*27 + 6);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_cfg_1524_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1560_ = v_cfg_1524_;
v_isShared_1561_ = v_isSharedCheck_1568_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_builtinLint_x3f_1557_);
lean_inc(v_restoreAllArtifacts_x3f_1554_);
lean_inc(v_enableArtifactCache_x3f_1553_);
lean_inc(v_readmeFile_1551_);
lean_inc(v_licenseFiles_1550_);
lean_inc(v_license_1549_);
lean_inc(v_homepage_1548_);
lean_inc(v_keywords_1547_);
lean_inc(v_description_1546_);
lean_inc(v_versionTags_1545_);
lean_inc(v_version_1544_);
lean_inc(v_lintDriverArgs_1543_);
lean_inc(v_lintDriver_1542_);
lean_inc(v_testDriverArgs_1541_);
lean_inc(v_testDriver_1540_);
lean_inc(v_buildArchive_1538_);
lean_inc(v_releaseRepo_1537_);
lean_inc(v_irDir_1536_);
lean_inc(v_binDir_1535_);
lean_inc(v_nativeLibDir_1534_);
lean_inc(v_leanLibDir_1533_);
lean_inc(v_buildDir_1532_);
lean_inc(v_srcDir_1531_);
lean_inc(v_moreGlobalServerArgs_1530_);
lean_inc(v_extraDepTargets_1528_);
lean_inc(v_toLeanConfig_1526_);
lean_inc(v_toWorkspaceConfig_1525_);
lean_dec(v_cfg_1524_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1568_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1562_ = lean_box(v_preferReleaseBuild_1539_);
v___x_1563_ = lean_apply_1(v_f_1523_, v___x_1562_);
if (v_isShared_1561_ == 0)
{
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_toWorkspaceConfig_1525_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_toLeanConfig_1526_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_extraDepTargets_1528_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_moreGlobalServerArgs_1530_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_srcDir_1531_);
lean_ctor_set(v_reuseFailAlloc_1567_, 5, v_buildDir_1532_);
lean_ctor_set(v_reuseFailAlloc_1567_, 6, v_leanLibDir_1533_);
lean_ctor_set(v_reuseFailAlloc_1567_, 7, v_nativeLibDir_1534_);
lean_ctor_set(v_reuseFailAlloc_1567_, 8, v_binDir_1535_);
lean_ctor_set(v_reuseFailAlloc_1567_, 9, v_irDir_1536_);
lean_ctor_set(v_reuseFailAlloc_1567_, 10, v_releaseRepo_1537_);
lean_ctor_set(v_reuseFailAlloc_1567_, 11, v_buildArchive_1538_);
lean_ctor_set(v_reuseFailAlloc_1567_, 12, v_testDriver_1540_);
lean_ctor_set(v_reuseFailAlloc_1567_, 13, v_testDriverArgs_1541_);
lean_ctor_set(v_reuseFailAlloc_1567_, 14, v_lintDriver_1542_);
lean_ctor_set(v_reuseFailAlloc_1567_, 15, v_lintDriverArgs_1543_);
lean_ctor_set(v_reuseFailAlloc_1567_, 16, v_version_1544_);
lean_ctor_set(v_reuseFailAlloc_1567_, 17, v_versionTags_1545_);
lean_ctor_set(v_reuseFailAlloc_1567_, 18, v_description_1546_);
lean_ctor_set(v_reuseFailAlloc_1567_, 19, v_keywords_1547_);
lean_ctor_set(v_reuseFailAlloc_1567_, 20, v_homepage_1548_);
lean_ctor_set(v_reuseFailAlloc_1567_, 21, v_license_1549_);
lean_ctor_set(v_reuseFailAlloc_1567_, 22, v_licenseFiles_1550_);
lean_ctor_set(v_reuseFailAlloc_1567_, 23, v_readmeFile_1551_);
lean_ctor_set(v_reuseFailAlloc_1567_, 24, v_enableArtifactCache_x3f_1553_);
lean_ctor_set(v_reuseFailAlloc_1567_, 25, v_restoreAllArtifacts_x3f_1554_);
lean_ctor_set(v_reuseFailAlloc_1567_, 26, v_builtinLint_x3f_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*27, v_bootstrap_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*27 + 1, v_precompileModules_1529_);
v___x_1565_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_unbox(v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*27 + 2, v___x_1566_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*27 + 3, v_reservoir_1552_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1555_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*27 + 5, v_allowImportAll_1556_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*27 + 6, v_fixedToolchain_1558_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1577_, lean_object* v_n_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1580_, lean_object* v_n_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1580_, v_n_1581_);
lean_dec(v_n_1581_);
lean_dec(v_p_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1583_, lean_object* v_n_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1583_, v_n_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1586_, lean_object* v_n_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1586_, v_n_1587_);
lean_dec(v_n_1587_);
lean_dec(v_p_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* v_cfg_1589_){
_start:
{
lean_object* v_testDriver_1590_; 
v_testDriver_1590_ = lean_ctor_get(v_cfg_1589_, 12);
lean_inc_ref(v_testDriver_1590_);
return v_testDriver_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* v_cfg_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lake_PackageConfig_testDriver___proj___lam__0(v_cfg_1591_);
lean_dec_ref(v_cfg_1591_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* v_val_1593_, lean_object* v_cfg_1594_){
_start:
{
lean_object* v_toWorkspaceConfig_1595_; lean_object* v_toLeanConfig_1596_; uint8_t v_bootstrap_1597_; lean_object* v_extraDepTargets_1598_; uint8_t v_precompileModules_1599_; lean_object* v_moreGlobalServerArgs_1600_; lean_object* v_srcDir_1601_; lean_object* v_buildDir_1602_; lean_object* v_leanLibDir_1603_; lean_object* v_nativeLibDir_1604_; lean_object* v_binDir_1605_; lean_object* v_irDir_1606_; lean_object* v_releaseRepo_1607_; lean_object* v_buildArchive_1608_; uint8_t v_preferReleaseBuild_1609_; lean_object* v_testDriverArgs_1610_; lean_object* v_lintDriver_1611_; lean_object* v_lintDriverArgs_1612_; lean_object* v_version_1613_; lean_object* v_versionTags_1614_; lean_object* v_description_1615_; lean_object* v_keywords_1616_; lean_object* v_homepage_1617_; lean_object* v_license_1618_; lean_object* v_licenseFiles_1619_; lean_object* v_readmeFile_1620_; uint8_t v_reservoir_1621_; lean_object* v_enableArtifactCache_x3f_1622_; lean_object* v_restoreAllArtifacts_x3f_1623_; uint8_t v_libPrefixOnWindows_1624_; uint8_t v_allowImportAll_1625_; lean_object* v_builtinLint_x3f_1626_; uint8_t v_fixedToolchain_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_toWorkspaceConfig_1595_ = lean_ctor_get(v_cfg_1594_, 0);
v_toLeanConfig_1596_ = lean_ctor_get(v_cfg_1594_, 1);
v_bootstrap_1597_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27);
v_extraDepTargets_1598_ = lean_ctor_get(v_cfg_1594_, 2);
v_precompileModules_1599_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1600_ = lean_ctor_get(v_cfg_1594_, 3);
v_srcDir_1601_ = lean_ctor_get(v_cfg_1594_, 4);
v_buildDir_1602_ = lean_ctor_get(v_cfg_1594_, 5);
v_leanLibDir_1603_ = lean_ctor_get(v_cfg_1594_, 6);
v_nativeLibDir_1604_ = lean_ctor_get(v_cfg_1594_, 7);
v_binDir_1605_ = lean_ctor_get(v_cfg_1594_, 8);
v_irDir_1606_ = lean_ctor_get(v_cfg_1594_, 9);
v_releaseRepo_1607_ = lean_ctor_get(v_cfg_1594_, 10);
v_buildArchive_1608_ = lean_ctor_get(v_cfg_1594_, 11);
v_preferReleaseBuild_1609_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27 + 2);
v_testDriverArgs_1610_ = lean_ctor_get(v_cfg_1594_, 13);
v_lintDriver_1611_ = lean_ctor_get(v_cfg_1594_, 14);
v_lintDriverArgs_1612_ = lean_ctor_get(v_cfg_1594_, 15);
v_version_1613_ = lean_ctor_get(v_cfg_1594_, 16);
v_versionTags_1614_ = lean_ctor_get(v_cfg_1594_, 17);
v_description_1615_ = lean_ctor_get(v_cfg_1594_, 18);
v_keywords_1616_ = lean_ctor_get(v_cfg_1594_, 19);
v_homepage_1617_ = lean_ctor_get(v_cfg_1594_, 20);
v_license_1618_ = lean_ctor_get(v_cfg_1594_, 21);
v_licenseFiles_1619_ = lean_ctor_get(v_cfg_1594_, 22);
v_readmeFile_1620_ = lean_ctor_get(v_cfg_1594_, 23);
v_reservoir_1621_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1622_ = lean_ctor_get(v_cfg_1594_, 24);
v_restoreAllArtifacts_x3f_1623_ = lean_ctor_get(v_cfg_1594_, 25);
v_libPrefixOnWindows_1624_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27 + 4);
v_allowImportAll_1625_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1626_ = lean_ctor_get(v_cfg_1594_, 26);
v_fixedToolchain_1627_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*27 + 6);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_cfg_1594_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_cfg_1594_, 12);
lean_dec(v_unused_1635_);
v___x_1629_ = v_cfg_1594_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_builtinLint_x3f_1626_);
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
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 12, v_val_1593_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_toWorkspaceConfig_1595_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_toLeanConfig_1596_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_extraDepTargets_1598_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_moreGlobalServerArgs_1600_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v_srcDir_1601_);
lean_ctor_set(v_reuseFailAlloc_1633_, 5, v_buildDir_1602_);
lean_ctor_set(v_reuseFailAlloc_1633_, 6, v_leanLibDir_1603_);
lean_ctor_set(v_reuseFailAlloc_1633_, 7, v_nativeLibDir_1604_);
lean_ctor_set(v_reuseFailAlloc_1633_, 8, v_binDir_1605_);
lean_ctor_set(v_reuseFailAlloc_1633_, 9, v_irDir_1606_);
lean_ctor_set(v_reuseFailAlloc_1633_, 10, v_releaseRepo_1607_);
lean_ctor_set(v_reuseFailAlloc_1633_, 11, v_buildArchive_1608_);
lean_ctor_set(v_reuseFailAlloc_1633_, 12, v_val_1593_);
lean_ctor_set(v_reuseFailAlloc_1633_, 13, v_testDriverArgs_1610_);
lean_ctor_set(v_reuseFailAlloc_1633_, 14, v_lintDriver_1611_);
lean_ctor_set(v_reuseFailAlloc_1633_, 15, v_lintDriverArgs_1612_);
lean_ctor_set(v_reuseFailAlloc_1633_, 16, v_version_1613_);
lean_ctor_set(v_reuseFailAlloc_1633_, 17, v_versionTags_1614_);
lean_ctor_set(v_reuseFailAlloc_1633_, 18, v_description_1615_);
lean_ctor_set(v_reuseFailAlloc_1633_, 19, v_keywords_1616_);
lean_ctor_set(v_reuseFailAlloc_1633_, 20, v_homepage_1617_);
lean_ctor_set(v_reuseFailAlloc_1633_, 21, v_license_1618_);
lean_ctor_set(v_reuseFailAlloc_1633_, 22, v_licenseFiles_1619_);
lean_ctor_set(v_reuseFailAlloc_1633_, 23, v_readmeFile_1620_);
lean_ctor_set(v_reuseFailAlloc_1633_, 24, v_enableArtifactCache_x3f_1622_);
lean_ctor_set(v_reuseFailAlloc_1633_, 25, v_restoreAllArtifacts_x3f_1623_);
lean_ctor_set(v_reuseFailAlloc_1633_, 26, v_builtinLint_x3f_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27, v_bootstrap_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27 + 1, v_precompileModules_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27 + 3, v_reservoir_1621_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27 + 5, v_allowImportAll_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*27 + 6, v_fixedToolchain_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* v_f_1636_, lean_object* v_cfg_1637_){
_start:
{
lean_object* v_toWorkspaceConfig_1638_; lean_object* v_toLeanConfig_1639_; uint8_t v_bootstrap_1640_; lean_object* v_extraDepTargets_1641_; uint8_t v_precompileModules_1642_; lean_object* v_moreGlobalServerArgs_1643_; lean_object* v_srcDir_1644_; lean_object* v_buildDir_1645_; lean_object* v_leanLibDir_1646_; lean_object* v_nativeLibDir_1647_; lean_object* v_binDir_1648_; lean_object* v_irDir_1649_; lean_object* v_releaseRepo_1650_; lean_object* v_buildArchive_1651_; uint8_t v_preferReleaseBuild_1652_; lean_object* v_testDriver_1653_; lean_object* v_testDriverArgs_1654_; lean_object* v_lintDriver_1655_; lean_object* v_lintDriverArgs_1656_; lean_object* v_version_1657_; lean_object* v_versionTags_1658_; lean_object* v_description_1659_; lean_object* v_keywords_1660_; lean_object* v_homepage_1661_; lean_object* v_license_1662_; lean_object* v_licenseFiles_1663_; lean_object* v_readmeFile_1664_; uint8_t v_reservoir_1665_; lean_object* v_enableArtifactCache_x3f_1666_; lean_object* v_restoreAllArtifacts_x3f_1667_; uint8_t v_libPrefixOnWindows_1668_; uint8_t v_allowImportAll_1669_; lean_object* v_builtinLint_x3f_1670_; uint8_t v_fixedToolchain_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1679_; 
v_toWorkspaceConfig_1638_ = lean_ctor_get(v_cfg_1637_, 0);
v_toLeanConfig_1639_ = lean_ctor_get(v_cfg_1637_, 1);
v_bootstrap_1640_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27);
v_extraDepTargets_1641_ = lean_ctor_get(v_cfg_1637_, 2);
v_precompileModules_1642_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1643_ = lean_ctor_get(v_cfg_1637_, 3);
v_srcDir_1644_ = lean_ctor_get(v_cfg_1637_, 4);
v_buildDir_1645_ = lean_ctor_get(v_cfg_1637_, 5);
v_leanLibDir_1646_ = lean_ctor_get(v_cfg_1637_, 6);
v_nativeLibDir_1647_ = lean_ctor_get(v_cfg_1637_, 7);
v_binDir_1648_ = lean_ctor_get(v_cfg_1637_, 8);
v_irDir_1649_ = lean_ctor_get(v_cfg_1637_, 9);
v_releaseRepo_1650_ = lean_ctor_get(v_cfg_1637_, 10);
v_buildArchive_1651_ = lean_ctor_get(v_cfg_1637_, 11);
v_preferReleaseBuild_1652_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27 + 2);
v_testDriver_1653_ = lean_ctor_get(v_cfg_1637_, 12);
v_testDriverArgs_1654_ = lean_ctor_get(v_cfg_1637_, 13);
v_lintDriver_1655_ = lean_ctor_get(v_cfg_1637_, 14);
v_lintDriverArgs_1656_ = lean_ctor_get(v_cfg_1637_, 15);
v_version_1657_ = lean_ctor_get(v_cfg_1637_, 16);
v_versionTags_1658_ = lean_ctor_get(v_cfg_1637_, 17);
v_description_1659_ = lean_ctor_get(v_cfg_1637_, 18);
v_keywords_1660_ = lean_ctor_get(v_cfg_1637_, 19);
v_homepage_1661_ = lean_ctor_get(v_cfg_1637_, 20);
v_license_1662_ = lean_ctor_get(v_cfg_1637_, 21);
v_licenseFiles_1663_ = lean_ctor_get(v_cfg_1637_, 22);
v_readmeFile_1664_ = lean_ctor_get(v_cfg_1637_, 23);
v_reservoir_1665_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1666_ = lean_ctor_get(v_cfg_1637_, 24);
v_restoreAllArtifacts_x3f_1667_ = lean_ctor_get(v_cfg_1637_, 25);
v_libPrefixOnWindows_1668_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27 + 4);
v_allowImportAll_1669_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1670_ = lean_ctor_get(v_cfg_1637_, 26);
v_fixedToolchain_1671_ = lean_ctor_get_uint8(v_cfg_1637_, sizeof(void*)*27 + 6);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_cfg_1637_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1673_ = v_cfg_1637_;
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_builtinLint_x3f_1670_);
lean_inc(v_restoreAllArtifacts_x3f_1667_);
lean_inc(v_enableArtifactCache_x3f_1666_);
lean_inc(v_readmeFile_1664_);
lean_inc(v_licenseFiles_1663_);
lean_inc(v_license_1662_);
lean_inc(v_homepage_1661_);
lean_inc(v_keywords_1660_);
lean_inc(v_description_1659_);
lean_inc(v_versionTags_1658_);
lean_inc(v_version_1657_);
lean_inc(v_lintDriverArgs_1656_);
lean_inc(v_lintDriver_1655_);
lean_inc(v_testDriverArgs_1654_);
lean_inc(v_testDriver_1653_);
lean_inc(v_buildArchive_1651_);
lean_inc(v_releaseRepo_1650_);
lean_inc(v_irDir_1649_);
lean_inc(v_binDir_1648_);
lean_inc(v_nativeLibDir_1647_);
lean_inc(v_leanLibDir_1646_);
lean_inc(v_buildDir_1645_);
lean_inc(v_srcDir_1644_);
lean_inc(v_moreGlobalServerArgs_1643_);
lean_inc(v_extraDepTargets_1641_);
lean_inc(v_toLeanConfig_1639_);
lean_inc(v_toWorkspaceConfig_1638_);
lean_dec(v_cfg_1637_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = lean_apply_1(v_f_1636_, v_testDriver_1653_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 12, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_toWorkspaceConfig_1638_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_toLeanConfig_1639_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_extraDepTargets_1641_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_moreGlobalServerArgs_1643_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v_srcDir_1644_);
lean_ctor_set(v_reuseFailAlloc_1678_, 5, v_buildDir_1645_);
lean_ctor_set(v_reuseFailAlloc_1678_, 6, v_leanLibDir_1646_);
lean_ctor_set(v_reuseFailAlloc_1678_, 7, v_nativeLibDir_1647_);
lean_ctor_set(v_reuseFailAlloc_1678_, 8, v_binDir_1648_);
lean_ctor_set(v_reuseFailAlloc_1678_, 9, v_irDir_1649_);
lean_ctor_set(v_reuseFailAlloc_1678_, 10, v_releaseRepo_1650_);
lean_ctor_set(v_reuseFailAlloc_1678_, 11, v_buildArchive_1651_);
lean_ctor_set(v_reuseFailAlloc_1678_, 12, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1678_, 13, v_testDriverArgs_1654_);
lean_ctor_set(v_reuseFailAlloc_1678_, 14, v_lintDriver_1655_);
lean_ctor_set(v_reuseFailAlloc_1678_, 15, v_lintDriverArgs_1656_);
lean_ctor_set(v_reuseFailAlloc_1678_, 16, v_version_1657_);
lean_ctor_set(v_reuseFailAlloc_1678_, 17, v_versionTags_1658_);
lean_ctor_set(v_reuseFailAlloc_1678_, 18, v_description_1659_);
lean_ctor_set(v_reuseFailAlloc_1678_, 19, v_keywords_1660_);
lean_ctor_set(v_reuseFailAlloc_1678_, 20, v_homepage_1661_);
lean_ctor_set(v_reuseFailAlloc_1678_, 21, v_license_1662_);
lean_ctor_set(v_reuseFailAlloc_1678_, 22, v_licenseFiles_1663_);
lean_ctor_set(v_reuseFailAlloc_1678_, 23, v_readmeFile_1664_);
lean_ctor_set(v_reuseFailAlloc_1678_, 24, v_enableArtifactCache_x3f_1666_);
lean_ctor_set(v_reuseFailAlloc_1678_, 25, v_restoreAllArtifacts_x3f_1667_);
lean_ctor_set(v_reuseFailAlloc_1678_, 26, v_builtinLint_x3f_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27, v_bootstrap_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27 + 1, v_precompileModules_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27 + 3, v_reservoir_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27 + 5, v_allowImportAll_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*27 + 6, v_fixedToolchain_1671_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lake_PackageConfig_testDriver___proj___lam__3(v_x_1682_);
lean_dec_ref(v_x_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1693_, lean_object* v_n_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1696_, lean_object* v_n_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lake_PackageConfig_testDriver___proj(v_p_1696_, v_n_1697_);
lean_dec(v_n_1697_);
lean_dec(v_p_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1699_, lean_object* v_n_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lake_PackageConfig_testDriver___proj(v_p_1699_, v_n_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1702_, lean_object* v_n_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1702_, v_n_1703_);
lean_dec(v_n_1703_);
lean_dec(v_p_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1705_, lean_object* v_n_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lake_PackageConfig_testDriver___proj(v_p_1705_, v_n_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1708_, lean_object* v_n_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1708_, v_n_1709_);
lean_dec(v_n_1709_);
lean_dec(v_p_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* v_cfg_1711_){
_start:
{
lean_object* v_testDriverArgs_1712_; 
v_testDriverArgs_1712_ = lean_ctor_get(v_cfg_1711_, 13);
lean_inc_ref(v_testDriverArgs_1712_);
return v_testDriverArgs_1712_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(v_cfg_1713_);
lean_dec_ref(v_cfg_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* v_val_1715_, lean_object* v_cfg_1716_){
_start:
{
lean_object* v_toWorkspaceConfig_1717_; lean_object* v_toLeanConfig_1718_; uint8_t v_bootstrap_1719_; lean_object* v_extraDepTargets_1720_; uint8_t v_precompileModules_1721_; lean_object* v_moreGlobalServerArgs_1722_; lean_object* v_srcDir_1723_; lean_object* v_buildDir_1724_; lean_object* v_leanLibDir_1725_; lean_object* v_nativeLibDir_1726_; lean_object* v_binDir_1727_; lean_object* v_irDir_1728_; lean_object* v_releaseRepo_1729_; lean_object* v_buildArchive_1730_; uint8_t v_preferReleaseBuild_1731_; lean_object* v_testDriver_1732_; lean_object* v_lintDriver_1733_; lean_object* v_lintDriverArgs_1734_; lean_object* v_version_1735_; lean_object* v_versionTags_1736_; lean_object* v_description_1737_; lean_object* v_keywords_1738_; lean_object* v_homepage_1739_; lean_object* v_license_1740_; lean_object* v_licenseFiles_1741_; lean_object* v_readmeFile_1742_; uint8_t v_reservoir_1743_; lean_object* v_enableArtifactCache_x3f_1744_; lean_object* v_restoreAllArtifacts_x3f_1745_; uint8_t v_libPrefixOnWindows_1746_; uint8_t v_allowImportAll_1747_; lean_object* v_builtinLint_x3f_1748_; uint8_t v_fixedToolchain_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
v_toWorkspaceConfig_1717_ = lean_ctor_get(v_cfg_1716_, 0);
v_toLeanConfig_1718_ = lean_ctor_get(v_cfg_1716_, 1);
v_bootstrap_1719_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27);
v_extraDepTargets_1720_ = lean_ctor_get(v_cfg_1716_, 2);
v_precompileModules_1721_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1722_ = lean_ctor_get(v_cfg_1716_, 3);
v_srcDir_1723_ = lean_ctor_get(v_cfg_1716_, 4);
v_buildDir_1724_ = lean_ctor_get(v_cfg_1716_, 5);
v_leanLibDir_1725_ = lean_ctor_get(v_cfg_1716_, 6);
v_nativeLibDir_1726_ = lean_ctor_get(v_cfg_1716_, 7);
v_binDir_1727_ = lean_ctor_get(v_cfg_1716_, 8);
v_irDir_1728_ = lean_ctor_get(v_cfg_1716_, 9);
v_releaseRepo_1729_ = lean_ctor_get(v_cfg_1716_, 10);
v_buildArchive_1730_ = lean_ctor_get(v_cfg_1716_, 11);
v_preferReleaseBuild_1731_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27 + 2);
v_testDriver_1732_ = lean_ctor_get(v_cfg_1716_, 12);
v_lintDriver_1733_ = lean_ctor_get(v_cfg_1716_, 14);
v_lintDriverArgs_1734_ = lean_ctor_get(v_cfg_1716_, 15);
v_version_1735_ = lean_ctor_get(v_cfg_1716_, 16);
v_versionTags_1736_ = lean_ctor_get(v_cfg_1716_, 17);
v_description_1737_ = lean_ctor_get(v_cfg_1716_, 18);
v_keywords_1738_ = lean_ctor_get(v_cfg_1716_, 19);
v_homepage_1739_ = lean_ctor_get(v_cfg_1716_, 20);
v_license_1740_ = lean_ctor_get(v_cfg_1716_, 21);
v_licenseFiles_1741_ = lean_ctor_get(v_cfg_1716_, 22);
v_readmeFile_1742_ = lean_ctor_get(v_cfg_1716_, 23);
v_reservoir_1743_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1744_ = lean_ctor_get(v_cfg_1716_, 24);
v_restoreAllArtifacts_x3f_1745_ = lean_ctor_get(v_cfg_1716_, 25);
v_libPrefixOnWindows_1746_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27 + 4);
v_allowImportAll_1747_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1748_ = lean_ctor_get(v_cfg_1716_, 26);
v_fixedToolchain_1749_ = lean_ctor_get_uint8(v_cfg_1716_, sizeof(void*)*27 + 6);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_cfg_1716_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v_cfg_1716_, 13);
lean_dec(v_unused_1757_);
v___x_1751_ = v_cfg_1716_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_builtinLint_x3f_1748_);
lean_inc(v_restoreAllArtifacts_x3f_1745_);
lean_inc(v_enableArtifactCache_x3f_1744_);
lean_inc(v_readmeFile_1742_);
lean_inc(v_licenseFiles_1741_);
lean_inc(v_license_1740_);
lean_inc(v_homepage_1739_);
lean_inc(v_keywords_1738_);
lean_inc(v_description_1737_);
lean_inc(v_versionTags_1736_);
lean_inc(v_version_1735_);
lean_inc(v_lintDriverArgs_1734_);
lean_inc(v_lintDriver_1733_);
lean_inc(v_testDriver_1732_);
lean_inc(v_buildArchive_1730_);
lean_inc(v_releaseRepo_1729_);
lean_inc(v_irDir_1728_);
lean_inc(v_binDir_1727_);
lean_inc(v_nativeLibDir_1726_);
lean_inc(v_leanLibDir_1725_);
lean_inc(v_buildDir_1724_);
lean_inc(v_srcDir_1723_);
lean_inc(v_moreGlobalServerArgs_1722_);
lean_inc(v_extraDepTargets_1720_);
lean_inc(v_toLeanConfig_1718_);
lean_inc(v_toWorkspaceConfig_1717_);
lean_dec(v_cfg_1716_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 13, v_val_1715_);
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_toWorkspaceConfig_1717_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_toLeanConfig_1718_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_extraDepTargets_1720_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_moreGlobalServerArgs_1722_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_srcDir_1723_);
lean_ctor_set(v_reuseFailAlloc_1755_, 5, v_buildDir_1724_);
lean_ctor_set(v_reuseFailAlloc_1755_, 6, v_leanLibDir_1725_);
lean_ctor_set(v_reuseFailAlloc_1755_, 7, v_nativeLibDir_1726_);
lean_ctor_set(v_reuseFailAlloc_1755_, 8, v_binDir_1727_);
lean_ctor_set(v_reuseFailAlloc_1755_, 9, v_irDir_1728_);
lean_ctor_set(v_reuseFailAlloc_1755_, 10, v_releaseRepo_1729_);
lean_ctor_set(v_reuseFailAlloc_1755_, 11, v_buildArchive_1730_);
lean_ctor_set(v_reuseFailAlloc_1755_, 12, v_testDriver_1732_);
lean_ctor_set(v_reuseFailAlloc_1755_, 13, v_val_1715_);
lean_ctor_set(v_reuseFailAlloc_1755_, 14, v_lintDriver_1733_);
lean_ctor_set(v_reuseFailAlloc_1755_, 15, v_lintDriverArgs_1734_);
lean_ctor_set(v_reuseFailAlloc_1755_, 16, v_version_1735_);
lean_ctor_set(v_reuseFailAlloc_1755_, 17, v_versionTags_1736_);
lean_ctor_set(v_reuseFailAlloc_1755_, 18, v_description_1737_);
lean_ctor_set(v_reuseFailAlloc_1755_, 19, v_keywords_1738_);
lean_ctor_set(v_reuseFailAlloc_1755_, 20, v_homepage_1739_);
lean_ctor_set(v_reuseFailAlloc_1755_, 21, v_license_1740_);
lean_ctor_set(v_reuseFailAlloc_1755_, 22, v_licenseFiles_1741_);
lean_ctor_set(v_reuseFailAlloc_1755_, 23, v_readmeFile_1742_);
lean_ctor_set(v_reuseFailAlloc_1755_, 24, v_enableArtifactCache_x3f_1744_);
lean_ctor_set(v_reuseFailAlloc_1755_, 25, v_restoreAllArtifacts_x3f_1745_);
lean_ctor_set(v_reuseFailAlloc_1755_, 26, v_builtinLint_x3f_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27, v_bootstrap_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27 + 1, v_precompileModules_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27 + 3, v_reservoir_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27 + 5, v_allowImportAll_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*27 + 6, v_fixedToolchain_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* v_f_1758_, lean_object* v_cfg_1759_){
_start:
{
lean_object* v_toWorkspaceConfig_1760_; lean_object* v_toLeanConfig_1761_; uint8_t v_bootstrap_1762_; lean_object* v_extraDepTargets_1763_; uint8_t v_precompileModules_1764_; lean_object* v_moreGlobalServerArgs_1765_; lean_object* v_srcDir_1766_; lean_object* v_buildDir_1767_; lean_object* v_leanLibDir_1768_; lean_object* v_nativeLibDir_1769_; lean_object* v_binDir_1770_; lean_object* v_irDir_1771_; lean_object* v_releaseRepo_1772_; lean_object* v_buildArchive_1773_; uint8_t v_preferReleaseBuild_1774_; lean_object* v_testDriver_1775_; lean_object* v_testDriverArgs_1776_; lean_object* v_lintDriver_1777_; lean_object* v_lintDriverArgs_1778_; lean_object* v_version_1779_; lean_object* v_versionTags_1780_; lean_object* v_description_1781_; lean_object* v_keywords_1782_; lean_object* v_homepage_1783_; lean_object* v_license_1784_; lean_object* v_licenseFiles_1785_; lean_object* v_readmeFile_1786_; uint8_t v_reservoir_1787_; lean_object* v_enableArtifactCache_x3f_1788_; lean_object* v_restoreAllArtifacts_x3f_1789_; uint8_t v_libPrefixOnWindows_1790_; uint8_t v_allowImportAll_1791_; lean_object* v_builtinLint_x3f_1792_; uint8_t v_fixedToolchain_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1801_; 
v_toWorkspaceConfig_1760_ = lean_ctor_get(v_cfg_1759_, 0);
v_toLeanConfig_1761_ = lean_ctor_get(v_cfg_1759_, 1);
v_bootstrap_1762_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27);
v_extraDepTargets_1763_ = lean_ctor_get(v_cfg_1759_, 2);
v_precompileModules_1764_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1765_ = lean_ctor_get(v_cfg_1759_, 3);
v_srcDir_1766_ = lean_ctor_get(v_cfg_1759_, 4);
v_buildDir_1767_ = lean_ctor_get(v_cfg_1759_, 5);
v_leanLibDir_1768_ = lean_ctor_get(v_cfg_1759_, 6);
v_nativeLibDir_1769_ = lean_ctor_get(v_cfg_1759_, 7);
v_binDir_1770_ = lean_ctor_get(v_cfg_1759_, 8);
v_irDir_1771_ = lean_ctor_get(v_cfg_1759_, 9);
v_releaseRepo_1772_ = lean_ctor_get(v_cfg_1759_, 10);
v_buildArchive_1773_ = lean_ctor_get(v_cfg_1759_, 11);
v_preferReleaseBuild_1774_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27 + 2);
v_testDriver_1775_ = lean_ctor_get(v_cfg_1759_, 12);
v_testDriverArgs_1776_ = lean_ctor_get(v_cfg_1759_, 13);
v_lintDriver_1777_ = lean_ctor_get(v_cfg_1759_, 14);
v_lintDriverArgs_1778_ = lean_ctor_get(v_cfg_1759_, 15);
v_version_1779_ = lean_ctor_get(v_cfg_1759_, 16);
v_versionTags_1780_ = lean_ctor_get(v_cfg_1759_, 17);
v_description_1781_ = lean_ctor_get(v_cfg_1759_, 18);
v_keywords_1782_ = lean_ctor_get(v_cfg_1759_, 19);
v_homepage_1783_ = lean_ctor_get(v_cfg_1759_, 20);
v_license_1784_ = lean_ctor_get(v_cfg_1759_, 21);
v_licenseFiles_1785_ = lean_ctor_get(v_cfg_1759_, 22);
v_readmeFile_1786_ = lean_ctor_get(v_cfg_1759_, 23);
v_reservoir_1787_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1788_ = lean_ctor_get(v_cfg_1759_, 24);
v_restoreAllArtifacts_x3f_1789_ = lean_ctor_get(v_cfg_1759_, 25);
v_libPrefixOnWindows_1790_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27 + 4);
v_allowImportAll_1791_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1792_ = lean_ctor_get(v_cfg_1759_, 26);
v_fixedToolchain_1793_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*27 + 6);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_cfg_1759_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1795_ = v_cfg_1759_;
v_isShared_1796_ = v_isSharedCheck_1801_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_builtinLint_x3f_1792_);
lean_inc(v_restoreAllArtifacts_x3f_1789_);
lean_inc(v_enableArtifactCache_x3f_1788_);
lean_inc(v_readmeFile_1786_);
lean_inc(v_licenseFiles_1785_);
lean_inc(v_license_1784_);
lean_inc(v_homepage_1783_);
lean_inc(v_keywords_1782_);
lean_inc(v_description_1781_);
lean_inc(v_versionTags_1780_);
lean_inc(v_version_1779_);
lean_inc(v_lintDriverArgs_1778_);
lean_inc(v_lintDriver_1777_);
lean_inc(v_testDriverArgs_1776_);
lean_inc(v_testDriver_1775_);
lean_inc(v_buildArchive_1773_);
lean_inc(v_releaseRepo_1772_);
lean_inc(v_irDir_1771_);
lean_inc(v_binDir_1770_);
lean_inc(v_nativeLibDir_1769_);
lean_inc(v_leanLibDir_1768_);
lean_inc(v_buildDir_1767_);
lean_inc(v_srcDir_1766_);
lean_inc(v_moreGlobalServerArgs_1765_);
lean_inc(v_extraDepTargets_1763_);
lean_inc(v_toLeanConfig_1761_);
lean_inc(v_toWorkspaceConfig_1760_);
lean_dec(v_cfg_1759_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1801_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = lean_apply_1(v_f_1758_, v_testDriverArgs_1776_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 13, v___x_1797_);
v___x_1799_ = v___x_1795_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_toWorkspaceConfig_1760_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_toLeanConfig_1761_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_extraDepTargets_1763_);
lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_moreGlobalServerArgs_1765_);
lean_ctor_set(v_reuseFailAlloc_1800_, 4, v_srcDir_1766_);
lean_ctor_set(v_reuseFailAlloc_1800_, 5, v_buildDir_1767_);
lean_ctor_set(v_reuseFailAlloc_1800_, 6, v_leanLibDir_1768_);
lean_ctor_set(v_reuseFailAlloc_1800_, 7, v_nativeLibDir_1769_);
lean_ctor_set(v_reuseFailAlloc_1800_, 8, v_binDir_1770_);
lean_ctor_set(v_reuseFailAlloc_1800_, 9, v_irDir_1771_);
lean_ctor_set(v_reuseFailAlloc_1800_, 10, v_releaseRepo_1772_);
lean_ctor_set(v_reuseFailAlloc_1800_, 11, v_buildArchive_1773_);
lean_ctor_set(v_reuseFailAlloc_1800_, 12, v_testDriver_1775_);
lean_ctor_set(v_reuseFailAlloc_1800_, 13, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1800_, 14, v_lintDriver_1777_);
lean_ctor_set(v_reuseFailAlloc_1800_, 15, v_lintDriverArgs_1778_);
lean_ctor_set(v_reuseFailAlloc_1800_, 16, v_version_1779_);
lean_ctor_set(v_reuseFailAlloc_1800_, 17, v_versionTags_1780_);
lean_ctor_set(v_reuseFailAlloc_1800_, 18, v_description_1781_);
lean_ctor_set(v_reuseFailAlloc_1800_, 19, v_keywords_1782_);
lean_ctor_set(v_reuseFailAlloc_1800_, 20, v_homepage_1783_);
lean_ctor_set(v_reuseFailAlloc_1800_, 21, v_license_1784_);
lean_ctor_set(v_reuseFailAlloc_1800_, 22, v_licenseFiles_1785_);
lean_ctor_set(v_reuseFailAlloc_1800_, 23, v_readmeFile_1786_);
lean_ctor_set(v_reuseFailAlloc_1800_, 24, v_enableArtifactCache_x3f_1788_);
lean_ctor_set(v_reuseFailAlloc_1800_, 25, v_restoreAllArtifacts_x3f_1789_);
lean_ctor_set(v_reuseFailAlloc_1800_, 26, v_builtinLint_x3f_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27, v_bootstrap_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27 + 1, v_precompileModules_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27 + 3, v_reservoir_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27 + 5, v_allowImportAll_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*27 + 6, v_fixedToolchain_1793_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1810_, lean_object* v_n_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1813_, lean_object* v_n_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1813_, v_n_1814_);
lean_dec(v_n_1814_);
lean_dec(v_p_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_1816_, lean_object* v_n_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1816_, v_n_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_1819_, lean_object* v_n_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_1819_, v_n_1820_);
lean_dec(v_n_1820_);
lean_dec(v_p_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* v_cfg_1822_){
_start:
{
lean_object* v_lintDriver_1823_; 
v_lintDriver_1823_ = lean_ctor_get(v_cfg_1822_, 14);
lean_inc_ref(v_lintDriver_1823_);
return v_lintDriver_1823_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* v_cfg_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lake_PackageConfig_lintDriver___proj___lam__0(v_cfg_1824_);
lean_dec_ref(v_cfg_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* v_val_1826_, lean_object* v_cfg_1827_){
_start:
{
lean_object* v_toWorkspaceConfig_1828_; lean_object* v_toLeanConfig_1829_; uint8_t v_bootstrap_1830_; lean_object* v_extraDepTargets_1831_; uint8_t v_precompileModules_1832_; lean_object* v_moreGlobalServerArgs_1833_; lean_object* v_srcDir_1834_; lean_object* v_buildDir_1835_; lean_object* v_leanLibDir_1836_; lean_object* v_nativeLibDir_1837_; lean_object* v_binDir_1838_; lean_object* v_irDir_1839_; lean_object* v_releaseRepo_1840_; lean_object* v_buildArchive_1841_; uint8_t v_preferReleaseBuild_1842_; lean_object* v_testDriver_1843_; lean_object* v_testDriverArgs_1844_; lean_object* v_lintDriverArgs_1845_; lean_object* v_version_1846_; lean_object* v_versionTags_1847_; lean_object* v_description_1848_; lean_object* v_keywords_1849_; lean_object* v_homepage_1850_; lean_object* v_license_1851_; lean_object* v_licenseFiles_1852_; lean_object* v_readmeFile_1853_; uint8_t v_reservoir_1854_; lean_object* v_enableArtifactCache_x3f_1855_; lean_object* v_restoreAllArtifacts_x3f_1856_; uint8_t v_libPrefixOnWindows_1857_; uint8_t v_allowImportAll_1858_; lean_object* v_builtinLint_x3f_1859_; uint8_t v_fixedToolchain_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_toWorkspaceConfig_1828_ = lean_ctor_get(v_cfg_1827_, 0);
v_toLeanConfig_1829_ = lean_ctor_get(v_cfg_1827_, 1);
v_bootstrap_1830_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27);
v_extraDepTargets_1831_ = lean_ctor_get(v_cfg_1827_, 2);
v_precompileModules_1832_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1833_ = lean_ctor_get(v_cfg_1827_, 3);
v_srcDir_1834_ = lean_ctor_get(v_cfg_1827_, 4);
v_buildDir_1835_ = lean_ctor_get(v_cfg_1827_, 5);
v_leanLibDir_1836_ = lean_ctor_get(v_cfg_1827_, 6);
v_nativeLibDir_1837_ = lean_ctor_get(v_cfg_1827_, 7);
v_binDir_1838_ = lean_ctor_get(v_cfg_1827_, 8);
v_irDir_1839_ = lean_ctor_get(v_cfg_1827_, 9);
v_releaseRepo_1840_ = lean_ctor_get(v_cfg_1827_, 10);
v_buildArchive_1841_ = lean_ctor_get(v_cfg_1827_, 11);
v_preferReleaseBuild_1842_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27 + 2);
v_testDriver_1843_ = lean_ctor_get(v_cfg_1827_, 12);
v_testDriverArgs_1844_ = lean_ctor_get(v_cfg_1827_, 13);
v_lintDriverArgs_1845_ = lean_ctor_get(v_cfg_1827_, 15);
v_version_1846_ = lean_ctor_get(v_cfg_1827_, 16);
v_versionTags_1847_ = lean_ctor_get(v_cfg_1827_, 17);
v_description_1848_ = lean_ctor_get(v_cfg_1827_, 18);
v_keywords_1849_ = lean_ctor_get(v_cfg_1827_, 19);
v_homepage_1850_ = lean_ctor_get(v_cfg_1827_, 20);
v_license_1851_ = lean_ctor_get(v_cfg_1827_, 21);
v_licenseFiles_1852_ = lean_ctor_get(v_cfg_1827_, 22);
v_readmeFile_1853_ = lean_ctor_get(v_cfg_1827_, 23);
v_reservoir_1854_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1855_ = lean_ctor_get(v_cfg_1827_, 24);
v_restoreAllArtifacts_x3f_1856_ = lean_ctor_get(v_cfg_1827_, 25);
v_libPrefixOnWindows_1857_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27 + 4);
v_allowImportAll_1858_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1859_ = lean_ctor_get(v_cfg_1827_, 26);
v_fixedToolchain_1860_ = lean_ctor_get_uint8(v_cfg_1827_, sizeof(void*)*27 + 6);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_cfg_1827_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v_cfg_1827_, 14);
lean_dec(v_unused_1868_);
v___x_1862_ = v_cfg_1827_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_builtinLint_x3f_1859_);
lean_inc(v_restoreAllArtifacts_x3f_1856_);
lean_inc(v_enableArtifactCache_x3f_1855_);
lean_inc(v_readmeFile_1853_);
lean_inc(v_licenseFiles_1852_);
lean_inc(v_license_1851_);
lean_inc(v_homepage_1850_);
lean_inc(v_keywords_1849_);
lean_inc(v_description_1848_);
lean_inc(v_versionTags_1847_);
lean_inc(v_version_1846_);
lean_inc(v_lintDriverArgs_1845_);
lean_inc(v_testDriverArgs_1844_);
lean_inc(v_testDriver_1843_);
lean_inc(v_buildArchive_1841_);
lean_inc(v_releaseRepo_1840_);
lean_inc(v_irDir_1839_);
lean_inc(v_binDir_1838_);
lean_inc(v_nativeLibDir_1837_);
lean_inc(v_leanLibDir_1836_);
lean_inc(v_buildDir_1835_);
lean_inc(v_srcDir_1834_);
lean_inc(v_moreGlobalServerArgs_1833_);
lean_inc(v_extraDepTargets_1831_);
lean_inc(v_toLeanConfig_1829_);
lean_inc(v_toWorkspaceConfig_1828_);
lean_dec(v_cfg_1827_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 14, v_val_1826_);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_toWorkspaceConfig_1828_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_toLeanConfig_1829_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_extraDepTargets_1831_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_moreGlobalServerArgs_1833_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_srcDir_1834_);
lean_ctor_set(v_reuseFailAlloc_1866_, 5, v_buildDir_1835_);
lean_ctor_set(v_reuseFailAlloc_1866_, 6, v_leanLibDir_1836_);
lean_ctor_set(v_reuseFailAlloc_1866_, 7, v_nativeLibDir_1837_);
lean_ctor_set(v_reuseFailAlloc_1866_, 8, v_binDir_1838_);
lean_ctor_set(v_reuseFailAlloc_1866_, 9, v_irDir_1839_);
lean_ctor_set(v_reuseFailAlloc_1866_, 10, v_releaseRepo_1840_);
lean_ctor_set(v_reuseFailAlloc_1866_, 11, v_buildArchive_1841_);
lean_ctor_set(v_reuseFailAlloc_1866_, 12, v_testDriver_1843_);
lean_ctor_set(v_reuseFailAlloc_1866_, 13, v_testDriverArgs_1844_);
lean_ctor_set(v_reuseFailAlloc_1866_, 14, v_val_1826_);
lean_ctor_set(v_reuseFailAlloc_1866_, 15, v_lintDriverArgs_1845_);
lean_ctor_set(v_reuseFailAlloc_1866_, 16, v_version_1846_);
lean_ctor_set(v_reuseFailAlloc_1866_, 17, v_versionTags_1847_);
lean_ctor_set(v_reuseFailAlloc_1866_, 18, v_description_1848_);
lean_ctor_set(v_reuseFailAlloc_1866_, 19, v_keywords_1849_);
lean_ctor_set(v_reuseFailAlloc_1866_, 20, v_homepage_1850_);
lean_ctor_set(v_reuseFailAlloc_1866_, 21, v_license_1851_);
lean_ctor_set(v_reuseFailAlloc_1866_, 22, v_licenseFiles_1852_);
lean_ctor_set(v_reuseFailAlloc_1866_, 23, v_readmeFile_1853_);
lean_ctor_set(v_reuseFailAlloc_1866_, 24, v_enableArtifactCache_x3f_1855_);
lean_ctor_set(v_reuseFailAlloc_1866_, 25, v_restoreAllArtifacts_x3f_1856_);
lean_ctor_set(v_reuseFailAlloc_1866_, 26, v_builtinLint_x3f_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27, v_bootstrap_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27 + 1, v_precompileModules_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27 + 3, v_reservoir_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27 + 5, v_allowImportAll_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*27 + 6, v_fixedToolchain_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* v_f_1869_, lean_object* v_cfg_1870_){
_start:
{
lean_object* v_toWorkspaceConfig_1871_; lean_object* v_toLeanConfig_1872_; uint8_t v_bootstrap_1873_; lean_object* v_extraDepTargets_1874_; uint8_t v_precompileModules_1875_; lean_object* v_moreGlobalServerArgs_1876_; lean_object* v_srcDir_1877_; lean_object* v_buildDir_1878_; lean_object* v_leanLibDir_1879_; lean_object* v_nativeLibDir_1880_; lean_object* v_binDir_1881_; lean_object* v_irDir_1882_; lean_object* v_releaseRepo_1883_; lean_object* v_buildArchive_1884_; uint8_t v_preferReleaseBuild_1885_; lean_object* v_testDriver_1886_; lean_object* v_testDriverArgs_1887_; lean_object* v_lintDriver_1888_; lean_object* v_lintDriverArgs_1889_; lean_object* v_version_1890_; lean_object* v_versionTags_1891_; lean_object* v_description_1892_; lean_object* v_keywords_1893_; lean_object* v_homepage_1894_; lean_object* v_license_1895_; lean_object* v_licenseFiles_1896_; lean_object* v_readmeFile_1897_; uint8_t v_reservoir_1898_; lean_object* v_enableArtifactCache_x3f_1899_; lean_object* v_restoreAllArtifacts_x3f_1900_; uint8_t v_libPrefixOnWindows_1901_; uint8_t v_allowImportAll_1902_; lean_object* v_builtinLint_x3f_1903_; uint8_t v_fixedToolchain_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1912_; 
v_toWorkspaceConfig_1871_ = lean_ctor_get(v_cfg_1870_, 0);
v_toLeanConfig_1872_ = lean_ctor_get(v_cfg_1870_, 1);
v_bootstrap_1873_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27);
v_extraDepTargets_1874_ = lean_ctor_get(v_cfg_1870_, 2);
v_precompileModules_1875_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1876_ = lean_ctor_get(v_cfg_1870_, 3);
v_srcDir_1877_ = lean_ctor_get(v_cfg_1870_, 4);
v_buildDir_1878_ = lean_ctor_get(v_cfg_1870_, 5);
v_leanLibDir_1879_ = lean_ctor_get(v_cfg_1870_, 6);
v_nativeLibDir_1880_ = lean_ctor_get(v_cfg_1870_, 7);
v_binDir_1881_ = lean_ctor_get(v_cfg_1870_, 8);
v_irDir_1882_ = lean_ctor_get(v_cfg_1870_, 9);
v_releaseRepo_1883_ = lean_ctor_get(v_cfg_1870_, 10);
v_buildArchive_1884_ = lean_ctor_get(v_cfg_1870_, 11);
v_preferReleaseBuild_1885_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27 + 2);
v_testDriver_1886_ = lean_ctor_get(v_cfg_1870_, 12);
v_testDriverArgs_1887_ = lean_ctor_get(v_cfg_1870_, 13);
v_lintDriver_1888_ = lean_ctor_get(v_cfg_1870_, 14);
v_lintDriverArgs_1889_ = lean_ctor_get(v_cfg_1870_, 15);
v_version_1890_ = lean_ctor_get(v_cfg_1870_, 16);
v_versionTags_1891_ = lean_ctor_get(v_cfg_1870_, 17);
v_description_1892_ = lean_ctor_get(v_cfg_1870_, 18);
v_keywords_1893_ = lean_ctor_get(v_cfg_1870_, 19);
v_homepage_1894_ = lean_ctor_get(v_cfg_1870_, 20);
v_license_1895_ = lean_ctor_get(v_cfg_1870_, 21);
v_licenseFiles_1896_ = lean_ctor_get(v_cfg_1870_, 22);
v_readmeFile_1897_ = lean_ctor_get(v_cfg_1870_, 23);
v_reservoir_1898_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1899_ = lean_ctor_get(v_cfg_1870_, 24);
v_restoreAllArtifacts_x3f_1900_ = lean_ctor_get(v_cfg_1870_, 25);
v_libPrefixOnWindows_1901_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27 + 4);
v_allowImportAll_1902_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1903_ = lean_ctor_get(v_cfg_1870_, 26);
v_fixedToolchain_1904_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*27 + 6);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_cfg_1870_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1906_ = v_cfg_1870_;
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_builtinLint_x3f_1903_);
lean_inc(v_restoreAllArtifacts_x3f_1900_);
lean_inc(v_enableArtifactCache_x3f_1899_);
lean_inc(v_readmeFile_1897_);
lean_inc(v_licenseFiles_1896_);
lean_inc(v_license_1895_);
lean_inc(v_homepage_1894_);
lean_inc(v_keywords_1893_);
lean_inc(v_description_1892_);
lean_inc(v_versionTags_1891_);
lean_inc(v_version_1890_);
lean_inc(v_lintDriverArgs_1889_);
lean_inc(v_lintDriver_1888_);
lean_inc(v_testDriverArgs_1887_);
lean_inc(v_testDriver_1886_);
lean_inc(v_buildArchive_1884_);
lean_inc(v_releaseRepo_1883_);
lean_inc(v_irDir_1882_);
lean_inc(v_binDir_1881_);
lean_inc(v_nativeLibDir_1880_);
lean_inc(v_leanLibDir_1879_);
lean_inc(v_buildDir_1878_);
lean_inc(v_srcDir_1877_);
lean_inc(v_moreGlobalServerArgs_1876_);
lean_inc(v_extraDepTargets_1874_);
lean_inc(v_toLeanConfig_1872_);
lean_inc(v_toWorkspaceConfig_1871_);
lean_dec(v_cfg_1870_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_apply_1(v_f_1869_, v_lintDriver_1888_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 14, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_toWorkspaceConfig_1871_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_toLeanConfig_1872_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_extraDepTargets_1874_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_moreGlobalServerArgs_1876_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_srcDir_1877_);
lean_ctor_set(v_reuseFailAlloc_1911_, 5, v_buildDir_1878_);
lean_ctor_set(v_reuseFailAlloc_1911_, 6, v_leanLibDir_1879_);
lean_ctor_set(v_reuseFailAlloc_1911_, 7, v_nativeLibDir_1880_);
lean_ctor_set(v_reuseFailAlloc_1911_, 8, v_binDir_1881_);
lean_ctor_set(v_reuseFailAlloc_1911_, 9, v_irDir_1882_);
lean_ctor_set(v_reuseFailAlloc_1911_, 10, v_releaseRepo_1883_);
lean_ctor_set(v_reuseFailAlloc_1911_, 11, v_buildArchive_1884_);
lean_ctor_set(v_reuseFailAlloc_1911_, 12, v_testDriver_1886_);
lean_ctor_set(v_reuseFailAlloc_1911_, 13, v_testDriverArgs_1887_);
lean_ctor_set(v_reuseFailAlloc_1911_, 14, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1911_, 15, v_lintDriverArgs_1889_);
lean_ctor_set(v_reuseFailAlloc_1911_, 16, v_version_1890_);
lean_ctor_set(v_reuseFailAlloc_1911_, 17, v_versionTags_1891_);
lean_ctor_set(v_reuseFailAlloc_1911_, 18, v_description_1892_);
lean_ctor_set(v_reuseFailAlloc_1911_, 19, v_keywords_1893_);
lean_ctor_set(v_reuseFailAlloc_1911_, 20, v_homepage_1894_);
lean_ctor_set(v_reuseFailAlloc_1911_, 21, v_license_1895_);
lean_ctor_set(v_reuseFailAlloc_1911_, 22, v_licenseFiles_1896_);
lean_ctor_set(v_reuseFailAlloc_1911_, 23, v_readmeFile_1897_);
lean_ctor_set(v_reuseFailAlloc_1911_, 24, v_enableArtifactCache_x3f_1899_);
lean_ctor_set(v_reuseFailAlloc_1911_, 25, v_restoreAllArtifacts_x3f_1900_);
lean_ctor_set(v_reuseFailAlloc_1911_, 26, v_builtinLint_x3f_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27, v_bootstrap_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27 + 1, v_precompileModules_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27 + 3, v_reservoir_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27 + 5, v_allowImportAll_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*27 + 6, v_fixedToolchain_1904_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_1921_, lean_object* v_n_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_1924_, lean_object* v_n_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1924_, v_n_1925_);
lean_dec(v_n_1925_);
lean_dec(v_p_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_1927_, lean_object* v_n_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1927_, v_n_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_1930_, lean_object* v_n_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_1930_, v_n_1931_);
lean_dec(v_n_1931_);
lean_dec(v_p_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* v_cfg_1933_){
_start:
{
lean_object* v_lintDriverArgs_1934_; 
v_lintDriverArgs_1934_ = lean_ctor_get(v_cfg_1933_, 15);
lean_inc_ref(v_lintDriverArgs_1934_);
return v_lintDriverArgs_1934_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(v_cfg_1935_);
lean_dec_ref(v_cfg_1935_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* v_val_1937_, lean_object* v_cfg_1938_){
_start:
{
lean_object* v_toWorkspaceConfig_1939_; lean_object* v_toLeanConfig_1940_; uint8_t v_bootstrap_1941_; lean_object* v_extraDepTargets_1942_; uint8_t v_precompileModules_1943_; lean_object* v_moreGlobalServerArgs_1944_; lean_object* v_srcDir_1945_; lean_object* v_buildDir_1946_; lean_object* v_leanLibDir_1947_; lean_object* v_nativeLibDir_1948_; lean_object* v_binDir_1949_; lean_object* v_irDir_1950_; lean_object* v_releaseRepo_1951_; lean_object* v_buildArchive_1952_; uint8_t v_preferReleaseBuild_1953_; lean_object* v_testDriver_1954_; lean_object* v_testDriverArgs_1955_; lean_object* v_lintDriver_1956_; lean_object* v_version_1957_; lean_object* v_versionTags_1958_; lean_object* v_description_1959_; lean_object* v_keywords_1960_; lean_object* v_homepage_1961_; lean_object* v_license_1962_; lean_object* v_licenseFiles_1963_; lean_object* v_readmeFile_1964_; uint8_t v_reservoir_1965_; lean_object* v_enableArtifactCache_x3f_1966_; lean_object* v_restoreAllArtifacts_x3f_1967_; uint8_t v_libPrefixOnWindows_1968_; uint8_t v_allowImportAll_1969_; lean_object* v_builtinLint_x3f_1970_; uint8_t v_fixedToolchain_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_toWorkspaceConfig_1939_ = lean_ctor_get(v_cfg_1938_, 0);
v_toLeanConfig_1940_ = lean_ctor_get(v_cfg_1938_, 1);
v_bootstrap_1941_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27);
v_extraDepTargets_1942_ = lean_ctor_get(v_cfg_1938_, 2);
v_precompileModules_1943_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1944_ = lean_ctor_get(v_cfg_1938_, 3);
v_srcDir_1945_ = lean_ctor_get(v_cfg_1938_, 4);
v_buildDir_1946_ = lean_ctor_get(v_cfg_1938_, 5);
v_leanLibDir_1947_ = lean_ctor_get(v_cfg_1938_, 6);
v_nativeLibDir_1948_ = lean_ctor_get(v_cfg_1938_, 7);
v_binDir_1949_ = lean_ctor_get(v_cfg_1938_, 8);
v_irDir_1950_ = lean_ctor_get(v_cfg_1938_, 9);
v_releaseRepo_1951_ = lean_ctor_get(v_cfg_1938_, 10);
v_buildArchive_1952_ = lean_ctor_get(v_cfg_1938_, 11);
v_preferReleaseBuild_1953_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27 + 2);
v_testDriver_1954_ = lean_ctor_get(v_cfg_1938_, 12);
v_testDriverArgs_1955_ = lean_ctor_get(v_cfg_1938_, 13);
v_lintDriver_1956_ = lean_ctor_get(v_cfg_1938_, 14);
v_version_1957_ = lean_ctor_get(v_cfg_1938_, 16);
v_versionTags_1958_ = lean_ctor_get(v_cfg_1938_, 17);
v_description_1959_ = lean_ctor_get(v_cfg_1938_, 18);
v_keywords_1960_ = lean_ctor_get(v_cfg_1938_, 19);
v_homepage_1961_ = lean_ctor_get(v_cfg_1938_, 20);
v_license_1962_ = lean_ctor_get(v_cfg_1938_, 21);
v_licenseFiles_1963_ = lean_ctor_get(v_cfg_1938_, 22);
v_readmeFile_1964_ = lean_ctor_get(v_cfg_1938_, 23);
v_reservoir_1965_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_1966_ = lean_ctor_get(v_cfg_1938_, 24);
v_restoreAllArtifacts_x3f_1967_ = lean_ctor_get(v_cfg_1938_, 25);
v_libPrefixOnWindows_1968_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27 + 4);
v_allowImportAll_1969_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_1970_ = lean_ctor_get(v_cfg_1938_, 26);
v_fixedToolchain_1971_ = lean_ctor_get_uint8(v_cfg_1938_, sizeof(void*)*27 + 6);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_cfg_1938_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v_cfg_1938_, 15);
lean_dec(v_unused_1979_);
v___x_1973_ = v_cfg_1938_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_builtinLint_x3f_1970_);
lean_inc(v_restoreAllArtifacts_x3f_1967_);
lean_inc(v_enableArtifactCache_x3f_1966_);
lean_inc(v_readmeFile_1964_);
lean_inc(v_licenseFiles_1963_);
lean_inc(v_license_1962_);
lean_inc(v_homepage_1961_);
lean_inc(v_keywords_1960_);
lean_inc(v_description_1959_);
lean_inc(v_versionTags_1958_);
lean_inc(v_version_1957_);
lean_inc(v_lintDriver_1956_);
lean_inc(v_testDriverArgs_1955_);
lean_inc(v_testDriver_1954_);
lean_inc(v_buildArchive_1952_);
lean_inc(v_releaseRepo_1951_);
lean_inc(v_irDir_1950_);
lean_inc(v_binDir_1949_);
lean_inc(v_nativeLibDir_1948_);
lean_inc(v_leanLibDir_1947_);
lean_inc(v_buildDir_1946_);
lean_inc(v_srcDir_1945_);
lean_inc(v_moreGlobalServerArgs_1944_);
lean_inc(v_extraDepTargets_1942_);
lean_inc(v_toLeanConfig_1940_);
lean_inc(v_toWorkspaceConfig_1939_);
lean_dec(v_cfg_1938_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 15, v_val_1937_);
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_toWorkspaceConfig_1939_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_toLeanConfig_1940_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_extraDepTargets_1942_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_moreGlobalServerArgs_1944_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_srcDir_1945_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v_buildDir_1946_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_leanLibDir_1947_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_nativeLibDir_1948_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_binDir_1949_);
lean_ctor_set(v_reuseFailAlloc_1977_, 9, v_irDir_1950_);
lean_ctor_set(v_reuseFailAlloc_1977_, 10, v_releaseRepo_1951_);
lean_ctor_set(v_reuseFailAlloc_1977_, 11, v_buildArchive_1952_);
lean_ctor_set(v_reuseFailAlloc_1977_, 12, v_testDriver_1954_);
lean_ctor_set(v_reuseFailAlloc_1977_, 13, v_testDriverArgs_1955_);
lean_ctor_set(v_reuseFailAlloc_1977_, 14, v_lintDriver_1956_);
lean_ctor_set(v_reuseFailAlloc_1977_, 15, v_val_1937_);
lean_ctor_set(v_reuseFailAlloc_1977_, 16, v_version_1957_);
lean_ctor_set(v_reuseFailAlloc_1977_, 17, v_versionTags_1958_);
lean_ctor_set(v_reuseFailAlloc_1977_, 18, v_description_1959_);
lean_ctor_set(v_reuseFailAlloc_1977_, 19, v_keywords_1960_);
lean_ctor_set(v_reuseFailAlloc_1977_, 20, v_homepage_1961_);
lean_ctor_set(v_reuseFailAlloc_1977_, 21, v_license_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 22, v_licenseFiles_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 23, v_readmeFile_1964_);
lean_ctor_set(v_reuseFailAlloc_1977_, 24, v_enableArtifactCache_x3f_1966_);
lean_ctor_set(v_reuseFailAlloc_1977_, 25, v_restoreAllArtifacts_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1977_, 26, v_builtinLint_x3f_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27, v_bootstrap_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27 + 1, v_precompileModules_1943_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27 + 3, v_reservoir_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27 + 5, v_allowImportAll_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*27 + 6, v_fixedToolchain_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* v_f_1980_, lean_object* v_cfg_1981_){
_start:
{
lean_object* v_toWorkspaceConfig_1982_; lean_object* v_toLeanConfig_1983_; uint8_t v_bootstrap_1984_; lean_object* v_extraDepTargets_1985_; uint8_t v_precompileModules_1986_; lean_object* v_moreGlobalServerArgs_1987_; lean_object* v_srcDir_1988_; lean_object* v_buildDir_1989_; lean_object* v_leanLibDir_1990_; lean_object* v_nativeLibDir_1991_; lean_object* v_binDir_1992_; lean_object* v_irDir_1993_; lean_object* v_releaseRepo_1994_; lean_object* v_buildArchive_1995_; uint8_t v_preferReleaseBuild_1996_; lean_object* v_testDriver_1997_; lean_object* v_testDriverArgs_1998_; lean_object* v_lintDriver_1999_; lean_object* v_lintDriverArgs_2000_; lean_object* v_version_2001_; lean_object* v_versionTags_2002_; lean_object* v_description_2003_; lean_object* v_keywords_2004_; lean_object* v_homepage_2005_; lean_object* v_license_2006_; lean_object* v_licenseFiles_2007_; lean_object* v_readmeFile_2008_; uint8_t v_reservoir_2009_; lean_object* v_enableArtifactCache_x3f_2010_; lean_object* v_restoreAllArtifacts_x3f_2011_; uint8_t v_libPrefixOnWindows_2012_; uint8_t v_allowImportAll_2013_; lean_object* v_builtinLint_x3f_2014_; uint8_t v_fixedToolchain_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
v_toWorkspaceConfig_1982_ = lean_ctor_get(v_cfg_1981_, 0);
v_toLeanConfig_1983_ = lean_ctor_get(v_cfg_1981_, 1);
v_bootstrap_1984_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27);
v_extraDepTargets_1985_ = lean_ctor_get(v_cfg_1981_, 2);
v_precompileModules_1986_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_1987_ = lean_ctor_get(v_cfg_1981_, 3);
v_srcDir_1988_ = lean_ctor_get(v_cfg_1981_, 4);
v_buildDir_1989_ = lean_ctor_get(v_cfg_1981_, 5);
v_leanLibDir_1990_ = lean_ctor_get(v_cfg_1981_, 6);
v_nativeLibDir_1991_ = lean_ctor_get(v_cfg_1981_, 7);
v_binDir_1992_ = lean_ctor_get(v_cfg_1981_, 8);
v_irDir_1993_ = lean_ctor_get(v_cfg_1981_, 9);
v_releaseRepo_1994_ = lean_ctor_get(v_cfg_1981_, 10);
v_buildArchive_1995_ = lean_ctor_get(v_cfg_1981_, 11);
v_preferReleaseBuild_1996_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27 + 2);
v_testDriver_1997_ = lean_ctor_get(v_cfg_1981_, 12);
v_testDriverArgs_1998_ = lean_ctor_get(v_cfg_1981_, 13);
v_lintDriver_1999_ = lean_ctor_get(v_cfg_1981_, 14);
v_lintDriverArgs_2000_ = lean_ctor_get(v_cfg_1981_, 15);
v_version_2001_ = lean_ctor_get(v_cfg_1981_, 16);
v_versionTags_2002_ = lean_ctor_get(v_cfg_1981_, 17);
v_description_2003_ = lean_ctor_get(v_cfg_1981_, 18);
v_keywords_2004_ = lean_ctor_get(v_cfg_1981_, 19);
v_homepage_2005_ = lean_ctor_get(v_cfg_1981_, 20);
v_license_2006_ = lean_ctor_get(v_cfg_1981_, 21);
v_licenseFiles_2007_ = lean_ctor_get(v_cfg_1981_, 22);
v_readmeFile_2008_ = lean_ctor_get(v_cfg_1981_, 23);
v_reservoir_2009_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2010_ = lean_ctor_get(v_cfg_1981_, 24);
v_restoreAllArtifacts_x3f_2011_ = lean_ctor_get(v_cfg_1981_, 25);
v_libPrefixOnWindows_2012_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27 + 4);
v_allowImportAll_2013_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2014_ = lean_ctor_get(v_cfg_1981_, 26);
v_fixedToolchain_2015_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*27 + 6);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_cfg_1981_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2017_ = v_cfg_1981_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_builtinLint_x3f_2014_);
lean_inc(v_restoreAllArtifacts_x3f_2011_);
lean_inc(v_enableArtifactCache_x3f_2010_);
lean_inc(v_readmeFile_2008_);
lean_inc(v_licenseFiles_2007_);
lean_inc(v_license_2006_);
lean_inc(v_homepage_2005_);
lean_inc(v_keywords_2004_);
lean_inc(v_description_2003_);
lean_inc(v_versionTags_2002_);
lean_inc(v_version_2001_);
lean_inc(v_lintDriverArgs_2000_);
lean_inc(v_lintDriver_1999_);
lean_inc(v_testDriverArgs_1998_);
lean_inc(v_testDriver_1997_);
lean_inc(v_buildArchive_1995_);
lean_inc(v_releaseRepo_1994_);
lean_inc(v_irDir_1993_);
lean_inc(v_binDir_1992_);
lean_inc(v_nativeLibDir_1991_);
lean_inc(v_leanLibDir_1990_);
lean_inc(v_buildDir_1989_);
lean_inc(v_srcDir_1988_);
lean_inc(v_moreGlobalServerArgs_1987_);
lean_inc(v_extraDepTargets_1985_);
lean_inc(v_toLeanConfig_1983_);
lean_inc(v_toWorkspaceConfig_1982_);
lean_dec(v_cfg_1981_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_apply_1(v_f_1980_, v_lintDriverArgs_2000_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 15, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_toWorkspaceConfig_1982_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_toLeanConfig_1983_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_extraDepTargets_1985_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_moreGlobalServerArgs_1987_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_srcDir_1988_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_buildDir_1989_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_leanLibDir_1990_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_nativeLibDir_1991_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_binDir_1992_);
lean_ctor_set(v_reuseFailAlloc_2022_, 9, v_irDir_1993_);
lean_ctor_set(v_reuseFailAlloc_2022_, 10, v_releaseRepo_1994_);
lean_ctor_set(v_reuseFailAlloc_2022_, 11, v_buildArchive_1995_);
lean_ctor_set(v_reuseFailAlloc_2022_, 12, v_testDriver_1997_);
lean_ctor_set(v_reuseFailAlloc_2022_, 13, v_testDriverArgs_1998_);
lean_ctor_set(v_reuseFailAlloc_2022_, 14, v_lintDriver_1999_);
lean_ctor_set(v_reuseFailAlloc_2022_, 15, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 16, v_version_2001_);
lean_ctor_set(v_reuseFailAlloc_2022_, 17, v_versionTags_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 18, v_description_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 19, v_keywords_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 20, v_homepage_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 21, v_license_2006_);
lean_ctor_set(v_reuseFailAlloc_2022_, 22, v_licenseFiles_2007_);
lean_ctor_set(v_reuseFailAlloc_2022_, 23, v_readmeFile_2008_);
lean_ctor_set(v_reuseFailAlloc_2022_, 24, v_enableArtifactCache_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2022_, 25, v_restoreAllArtifacts_x3f_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 26, v_builtinLint_x3f_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27, v_bootstrap_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27 + 1, v_precompileModules_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27 + 2, v_preferReleaseBuild_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27 + 3, v_reservoir_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27 + 5, v_allowImportAll_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*27 + 6, v_fixedToolchain_2015_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2032_, lean_object* v_n_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2035_, lean_object* v_n_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2035_, v_n_2036_);
lean_dec(v_n_2036_);
lean_dec(v_p_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2038_, lean_object* v_n_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2038_, v_n_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2041_, lean_object* v_n_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2041_, v_n_2042_);
lean_dec(v_n_2042_);
lean_dec(v_p_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* v_cfg_2044_){
_start:
{
lean_object* v_version_2045_; 
v_version_2045_ = lean_ctor_get(v_cfg_2044_, 16);
lean_inc_ref(v_version_2045_);
return v_version_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* v_cfg_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lake_PackageConfig_version___proj___lam__0(v_cfg_2046_);
lean_dec_ref(v_cfg_2046_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* v_val_2048_, lean_object* v_cfg_2049_){
_start:
{
lean_object* v_toWorkspaceConfig_2050_; lean_object* v_toLeanConfig_2051_; uint8_t v_bootstrap_2052_; lean_object* v_extraDepTargets_2053_; uint8_t v_precompileModules_2054_; lean_object* v_moreGlobalServerArgs_2055_; lean_object* v_srcDir_2056_; lean_object* v_buildDir_2057_; lean_object* v_leanLibDir_2058_; lean_object* v_nativeLibDir_2059_; lean_object* v_binDir_2060_; lean_object* v_irDir_2061_; lean_object* v_releaseRepo_2062_; lean_object* v_buildArchive_2063_; uint8_t v_preferReleaseBuild_2064_; lean_object* v_testDriver_2065_; lean_object* v_testDriverArgs_2066_; lean_object* v_lintDriver_2067_; lean_object* v_lintDriverArgs_2068_; lean_object* v_versionTags_2069_; lean_object* v_description_2070_; lean_object* v_keywords_2071_; lean_object* v_homepage_2072_; lean_object* v_license_2073_; lean_object* v_licenseFiles_2074_; lean_object* v_readmeFile_2075_; uint8_t v_reservoir_2076_; lean_object* v_enableArtifactCache_x3f_2077_; lean_object* v_restoreAllArtifacts_x3f_2078_; uint8_t v_libPrefixOnWindows_2079_; uint8_t v_allowImportAll_2080_; lean_object* v_builtinLint_x3f_2081_; uint8_t v_fixedToolchain_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_toWorkspaceConfig_2050_ = lean_ctor_get(v_cfg_2049_, 0);
v_toLeanConfig_2051_ = lean_ctor_get(v_cfg_2049_, 1);
v_bootstrap_2052_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27);
v_extraDepTargets_2053_ = lean_ctor_get(v_cfg_2049_, 2);
v_precompileModules_2054_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2055_ = lean_ctor_get(v_cfg_2049_, 3);
v_srcDir_2056_ = lean_ctor_get(v_cfg_2049_, 4);
v_buildDir_2057_ = lean_ctor_get(v_cfg_2049_, 5);
v_leanLibDir_2058_ = lean_ctor_get(v_cfg_2049_, 6);
v_nativeLibDir_2059_ = lean_ctor_get(v_cfg_2049_, 7);
v_binDir_2060_ = lean_ctor_get(v_cfg_2049_, 8);
v_irDir_2061_ = lean_ctor_get(v_cfg_2049_, 9);
v_releaseRepo_2062_ = lean_ctor_get(v_cfg_2049_, 10);
v_buildArchive_2063_ = lean_ctor_get(v_cfg_2049_, 11);
v_preferReleaseBuild_2064_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27 + 2);
v_testDriver_2065_ = lean_ctor_get(v_cfg_2049_, 12);
v_testDriverArgs_2066_ = lean_ctor_get(v_cfg_2049_, 13);
v_lintDriver_2067_ = lean_ctor_get(v_cfg_2049_, 14);
v_lintDriverArgs_2068_ = lean_ctor_get(v_cfg_2049_, 15);
v_versionTags_2069_ = lean_ctor_get(v_cfg_2049_, 17);
v_description_2070_ = lean_ctor_get(v_cfg_2049_, 18);
v_keywords_2071_ = lean_ctor_get(v_cfg_2049_, 19);
v_homepage_2072_ = lean_ctor_get(v_cfg_2049_, 20);
v_license_2073_ = lean_ctor_get(v_cfg_2049_, 21);
v_licenseFiles_2074_ = lean_ctor_get(v_cfg_2049_, 22);
v_readmeFile_2075_ = lean_ctor_get(v_cfg_2049_, 23);
v_reservoir_2076_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2077_ = lean_ctor_get(v_cfg_2049_, 24);
v_restoreAllArtifacts_x3f_2078_ = lean_ctor_get(v_cfg_2049_, 25);
v_libPrefixOnWindows_2079_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27 + 4);
v_allowImportAll_2080_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2081_ = lean_ctor_get(v_cfg_2049_, 26);
v_fixedToolchain_2082_ = lean_ctor_get_uint8(v_cfg_2049_, sizeof(void*)*27 + 6);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_cfg_2049_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v_cfg_2049_, 16);
lean_dec(v_unused_2090_);
v___x_2084_ = v_cfg_2049_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_builtinLint_x3f_2081_);
lean_inc(v_restoreAllArtifacts_x3f_2078_);
lean_inc(v_enableArtifactCache_x3f_2077_);
lean_inc(v_readmeFile_2075_);
lean_inc(v_licenseFiles_2074_);
lean_inc(v_license_2073_);
lean_inc(v_homepage_2072_);
lean_inc(v_keywords_2071_);
lean_inc(v_description_2070_);
lean_inc(v_versionTags_2069_);
lean_inc(v_lintDriverArgs_2068_);
lean_inc(v_lintDriver_2067_);
lean_inc(v_testDriverArgs_2066_);
lean_inc(v_testDriver_2065_);
lean_inc(v_buildArchive_2063_);
lean_inc(v_releaseRepo_2062_);
lean_inc(v_irDir_2061_);
lean_inc(v_binDir_2060_);
lean_inc(v_nativeLibDir_2059_);
lean_inc(v_leanLibDir_2058_);
lean_inc(v_buildDir_2057_);
lean_inc(v_srcDir_2056_);
lean_inc(v_moreGlobalServerArgs_2055_);
lean_inc(v_extraDepTargets_2053_);
lean_inc(v_toLeanConfig_2051_);
lean_inc(v_toWorkspaceConfig_2050_);
lean_dec(v_cfg_2049_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 16, v_val_2048_);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_toWorkspaceConfig_2050_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_toLeanConfig_2051_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_extraDepTargets_2053_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_moreGlobalServerArgs_2055_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_srcDir_2056_);
lean_ctor_set(v_reuseFailAlloc_2088_, 5, v_buildDir_2057_);
lean_ctor_set(v_reuseFailAlloc_2088_, 6, v_leanLibDir_2058_);
lean_ctor_set(v_reuseFailAlloc_2088_, 7, v_nativeLibDir_2059_);
lean_ctor_set(v_reuseFailAlloc_2088_, 8, v_binDir_2060_);
lean_ctor_set(v_reuseFailAlloc_2088_, 9, v_irDir_2061_);
lean_ctor_set(v_reuseFailAlloc_2088_, 10, v_releaseRepo_2062_);
lean_ctor_set(v_reuseFailAlloc_2088_, 11, v_buildArchive_2063_);
lean_ctor_set(v_reuseFailAlloc_2088_, 12, v_testDriver_2065_);
lean_ctor_set(v_reuseFailAlloc_2088_, 13, v_testDriverArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2088_, 14, v_lintDriver_2067_);
lean_ctor_set(v_reuseFailAlloc_2088_, 15, v_lintDriverArgs_2068_);
lean_ctor_set(v_reuseFailAlloc_2088_, 16, v_val_2048_);
lean_ctor_set(v_reuseFailAlloc_2088_, 17, v_versionTags_2069_);
lean_ctor_set(v_reuseFailAlloc_2088_, 18, v_description_2070_);
lean_ctor_set(v_reuseFailAlloc_2088_, 19, v_keywords_2071_);
lean_ctor_set(v_reuseFailAlloc_2088_, 20, v_homepage_2072_);
lean_ctor_set(v_reuseFailAlloc_2088_, 21, v_license_2073_);
lean_ctor_set(v_reuseFailAlloc_2088_, 22, v_licenseFiles_2074_);
lean_ctor_set(v_reuseFailAlloc_2088_, 23, v_readmeFile_2075_);
lean_ctor_set(v_reuseFailAlloc_2088_, 24, v_enableArtifactCache_x3f_2077_);
lean_ctor_set(v_reuseFailAlloc_2088_, 25, v_restoreAllArtifacts_x3f_2078_);
lean_ctor_set(v_reuseFailAlloc_2088_, 26, v_builtinLint_x3f_2081_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27, v_bootstrap_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27 + 1, v_precompileModules_2054_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27 + 3, v_reservoir_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27 + 5, v_allowImportAll_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*27 + 6, v_fixedToolchain_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* v_f_2091_, lean_object* v_cfg_2092_){
_start:
{
lean_object* v_toWorkspaceConfig_2093_; lean_object* v_toLeanConfig_2094_; uint8_t v_bootstrap_2095_; lean_object* v_extraDepTargets_2096_; uint8_t v_precompileModules_2097_; lean_object* v_moreGlobalServerArgs_2098_; lean_object* v_srcDir_2099_; lean_object* v_buildDir_2100_; lean_object* v_leanLibDir_2101_; lean_object* v_nativeLibDir_2102_; lean_object* v_binDir_2103_; lean_object* v_irDir_2104_; lean_object* v_releaseRepo_2105_; lean_object* v_buildArchive_2106_; uint8_t v_preferReleaseBuild_2107_; lean_object* v_testDriver_2108_; lean_object* v_testDriverArgs_2109_; lean_object* v_lintDriver_2110_; lean_object* v_lintDriverArgs_2111_; lean_object* v_version_2112_; lean_object* v_versionTags_2113_; lean_object* v_description_2114_; lean_object* v_keywords_2115_; lean_object* v_homepage_2116_; lean_object* v_license_2117_; lean_object* v_licenseFiles_2118_; lean_object* v_readmeFile_2119_; uint8_t v_reservoir_2120_; lean_object* v_enableArtifactCache_x3f_2121_; lean_object* v_restoreAllArtifacts_x3f_2122_; uint8_t v_libPrefixOnWindows_2123_; uint8_t v_allowImportAll_2124_; lean_object* v_builtinLint_x3f_2125_; uint8_t v_fixedToolchain_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2134_; 
v_toWorkspaceConfig_2093_ = lean_ctor_get(v_cfg_2092_, 0);
v_toLeanConfig_2094_ = lean_ctor_get(v_cfg_2092_, 1);
v_bootstrap_2095_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27);
v_extraDepTargets_2096_ = lean_ctor_get(v_cfg_2092_, 2);
v_precompileModules_2097_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2098_ = lean_ctor_get(v_cfg_2092_, 3);
v_srcDir_2099_ = lean_ctor_get(v_cfg_2092_, 4);
v_buildDir_2100_ = lean_ctor_get(v_cfg_2092_, 5);
v_leanLibDir_2101_ = lean_ctor_get(v_cfg_2092_, 6);
v_nativeLibDir_2102_ = lean_ctor_get(v_cfg_2092_, 7);
v_binDir_2103_ = lean_ctor_get(v_cfg_2092_, 8);
v_irDir_2104_ = lean_ctor_get(v_cfg_2092_, 9);
v_releaseRepo_2105_ = lean_ctor_get(v_cfg_2092_, 10);
v_buildArchive_2106_ = lean_ctor_get(v_cfg_2092_, 11);
v_preferReleaseBuild_2107_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27 + 2);
v_testDriver_2108_ = lean_ctor_get(v_cfg_2092_, 12);
v_testDriverArgs_2109_ = lean_ctor_get(v_cfg_2092_, 13);
v_lintDriver_2110_ = lean_ctor_get(v_cfg_2092_, 14);
v_lintDriverArgs_2111_ = lean_ctor_get(v_cfg_2092_, 15);
v_version_2112_ = lean_ctor_get(v_cfg_2092_, 16);
v_versionTags_2113_ = lean_ctor_get(v_cfg_2092_, 17);
v_description_2114_ = lean_ctor_get(v_cfg_2092_, 18);
v_keywords_2115_ = lean_ctor_get(v_cfg_2092_, 19);
v_homepage_2116_ = lean_ctor_get(v_cfg_2092_, 20);
v_license_2117_ = lean_ctor_get(v_cfg_2092_, 21);
v_licenseFiles_2118_ = lean_ctor_get(v_cfg_2092_, 22);
v_readmeFile_2119_ = lean_ctor_get(v_cfg_2092_, 23);
v_reservoir_2120_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2121_ = lean_ctor_get(v_cfg_2092_, 24);
v_restoreAllArtifacts_x3f_2122_ = lean_ctor_get(v_cfg_2092_, 25);
v_libPrefixOnWindows_2123_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27 + 4);
v_allowImportAll_2124_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2125_ = lean_ctor_get(v_cfg_2092_, 26);
v_fixedToolchain_2126_ = lean_ctor_get_uint8(v_cfg_2092_, sizeof(void*)*27 + 6);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_cfg_2092_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2128_ = v_cfg_2092_;
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_builtinLint_x3f_2125_);
lean_inc(v_restoreAllArtifacts_x3f_2122_);
lean_inc(v_enableArtifactCache_x3f_2121_);
lean_inc(v_readmeFile_2119_);
lean_inc(v_licenseFiles_2118_);
lean_inc(v_license_2117_);
lean_inc(v_homepage_2116_);
lean_inc(v_keywords_2115_);
lean_inc(v_description_2114_);
lean_inc(v_versionTags_2113_);
lean_inc(v_version_2112_);
lean_inc(v_lintDriverArgs_2111_);
lean_inc(v_lintDriver_2110_);
lean_inc(v_testDriverArgs_2109_);
lean_inc(v_testDriver_2108_);
lean_inc(v_buildArchive_2106_);
lean_inc(v_releaseRepo_2105_);
lean_inc(v_irDir_2104_);
lean_inc(v_binDir_2103_);
lean_inc(v_nativeLibDir_2102_);
lean_inc(v_leanLibDir_2101_);
lean_inc(v_buildDir_2100_);
lean_inc(v_srcDir_2099_);
lean_inc(v_moreGlobalServerArgs_2098_);
lean_inc(v_extraDepTargets_2096_);
lean_inc(v_toLeanConfig_2094_);
lean_inc(v_toWorkspaceConfig_2093_);
lean_dec(v_cfg_2092_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_apply_1(v_f_2091_, v_version_2112_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 16, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_toWorkspaceConfig_2093_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_toLeanConfig_2094_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_extraDepTargets_2096_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_moreGlobalServerArgs_2098_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_srcDir_2099_);
lean_ctor_set(v_reuseFailAlloc_2133_, 5, v_buildDir_2100_);
lean_ctor_set(v_reuseFailAlloc_2133_, 6, v_leanLibDir_2101_);
lean_ctor_set(v_reuseFailAlloc_2133_, 7, v_nativeLibDir_2102_);
lean_ctor_set(v_reuseFailAlloc_2133_, 8, v_binDir_2103_);
lean_ctor_set(v_reuseFailAlloc_2133_, 9, v_irDir_2104_);
lean_ctor_set(v_reuseFailAlloc_2133_, 10, v_releaseRepo_2105_);
lean_ctor_set(v_reuseFailAlloc_2133_, 11, v_buildArchive_2106_);
lean_ctor_set(v_reuseFailAlloc_2133_, 12, v_testDriver_2108_);
lean_ctor_set(v_reuseFailAlloc_2133_, 13, v_testDriverArgs_2109_);
lean_ctor_set(v_reuseFailAlloc_2133_, 14, v_lintDriver_2110_);
lean_ctor_set(v_reuseFailAlloc_2133_, 15, v_lintDriverArgs_2111_);
lean_ctor_set(v_reuseFailAlloc_2133_, 16, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2133_, 17, v_versionTags_2113_);
lean_ctor_set(v_reuseFailAlloc_2133_, 18, v_description_2114_);
lean_ctor_set(v_reuseFailAlloc_2133_, 19, v_keywords_2115_);
lean_ctor_set(v_reuseFailAlloc_2133_, 20, v_homepage_2116_);
lean_ctor_set(v_reuseFailAlloc_2133_, 21, v_license_2117_);
lean_ctor_set(v_reuseFailAlloc_2133_, 22, v_licenseFiles_2118_);
lean_ctor_set(v_reuseFailAlloc_2133_, 23, v_readmeFile_2119_);
lean_ctor_set(v_reuseFailAlloc_2133_, 24, v_enableArtifactCache_x3f_2121_);
lean_ctor_set(v_reuseFailAlloc_2133_, 25, v_restoreAllArtifacts_x3f_2122_);
lean_ctor_set(v_reuseFailAlloc_2133_, 26, v_builtinLint_x3f_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27, v_bootstrap_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27 + 1, v_precompileModules_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27 + 3, v_reservoir_2120_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27 + 5, v_allowImportAll_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*27 + 6, v_fixedToolchain_2126_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* v_x_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* v_x_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lake_PackageConfig_version___proj___lam__3(v_x_2137_);
lean_dec_ref(v_x_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2148_, lean_object* v_n_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2151_, lean_object* v_n_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lake_PackageConfig_version___proj(v_p_2151_, v_n_2152_);
lean_dec(v_n_2152_);
lean_dec(v_p_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2154_, lean_object* v_n_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lake_PackageConfig_version___proj(v_p_2154_, v_n_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2157_, lean_object* v_n_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lake_PackageConfig_version_instConfigField(v_p_2157_, v_n_2158_);
lean_dec(v_n_2158_);
lean_dec(v_p_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* v_cfg_2160_){
_start:
{
lean_object* v_versionTags_2161_; 
v_versionTags_2161_ = lean_ctor_get(v_cfg_2160_, 17);
lean_inc_ref(v_versionTags_2161_);
return v_versionTags_2161_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* v_cfg_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lake_PackageConfig_versionTags___proj___lam__0(v_cfg_2162_);
lean_dec_ref(v_cfg_2162_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* v_val_2164_, lean_object* v_cfg_2165_){
_start:
{
lean_object* v_toWorkspaceConfig_2166_; lean_object* v_toLeanConfig_2167_; uint8_t v_bootstrap_2168_; lean_object* v_extraDepTargets_2169_; uint8_t v_precompileModules_2170_; lean_object* v_moreGlobalServerArgs_2171_; lean_object* v_srcDir_2172_; lean_object* v_buildDir_2173_; lean_object* v_leanLibDir_2174_; lean_object* v_nativeLibDir_2175_; lean_object* v_binDir_2176_; lean_object* v_irDir_2177_; lean_object* v_releaseRepo_2178_; lean_object* v_buildArchive_2179_; uint8_t v_preferReleaseBuild_2180_; lean_object* v_testDriver_2181_; lean_object* v_testDriverArgs_2182_; lean_object* v_lintDriver_2183_; lean_object* v_lintDriverArgs_2184_; lean_object* v_version_2185_; lean_object* v_description_2186_; lean_object* v_keywords_2187_; lean_object* v_homepage_2188_; lean_object* v_license_2189_; lean_object* v_licenseFiles_2190_; lean_object* v_readmeFile_2191_; uint8_t v_reservoir_2192_; lean_object* v_enableArtifactCache_x3f_2193_; lean_object* v_restoreAllArtifacts_x3f_2194_; uint8_t v_libPrefixOnWindows_2195_; uint8_t v_allowImportAll_2196_; lean_object* v_builtinLint_x3f_2197_; uint8_t v_fixedToolchain_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
v_toWorkspaceConfig_2166_ = lean_ctor_get(v_cfg_2165_, 0);
v_toLeanConfig_2167_ = lean_ctor_get(v_cfg_2165_, 1);
v_bootstrap_2168_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27);
v_extraDepTargets_2169_ = lean_ctor_get(v_cfg_2165_, 2);
v_precompileModules_2170_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2171_ = lean_ctor_get(v_cfg_2165_, 3);
v_srcDir_2172_ = lean_ctor_get(v_cfg_2165_, 4);
v_buildDir_2173_ = lean_ctor_get(v_cfg_2165_, 5);
v_leanLibDir_2174_ = lean_ctor_get(v_cfg_2165_, 6);
v_nativeLibDir_2175_ = lean_ctor_get(v_cfg_2165_, 7);
v_binDir_2176_ = lean_ctor_get(v_cfg_2165_, 8);
v_irDir_2177_ = lean_ctor_get(v_cfg_2165_, 9);
v_releaseRepo_2178_ = lean_ctor_get(v_cfg_2165_, 10);
v_buildArchive_2179_ = lean_ctor_get(v_cfg_2165_, 11);
v_preferReleaseBuild_2180_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27 + 2);
v_testDriver_2181_ = lean_ctor_get(v_cfg_2165_, 12);
v_testDriverArgs_2182_ = lean_ctor_get(v_cfg_2165_, 13);
v_lintDriver_2183_ = lean_ctor_get(v_cfg_2165_, 14);
v_lintDriverArgs_2184_ = lean_ctor_get(v_cfg_2165_, 15);
v_version_2185_ = lean_ctor_get(v_cfg_2165_, 16);
v_description_2186_ = lean_ctor_get(v_cfg_2165_, 18);
v_keywords_2187_ = lean_ctor_get(v_cfg_2165_, 19);
v_homepage_2188_ = lean_ctor_get(v_cfg_2165_, 20);
v_license_2189_ = lean_ctor_get(v_cfg_2165_, 21);
v_licenseFiles_2190_ = lean_ctor_get(v_cfg_2165_, 22);
v_readmeFile_2191_ = lean_ctor_get(v_cfg_2165_, 23);
v_reservoir_2192_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2193_ = lean_ctor_get(v_cfg_2165_, 24);
v_restoreAllArtifacts_x3f_2194_ = lean_ctor_get(v_cfg_2165_, 25);
v_libPrefixOnWindows_2195_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27 + 4);
v_allowImportAll_2196_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2197_ = lean_ctor_get(v_cfg_2165_, 26);
v_fixedToolchain_2198_ = lean_ctor_get_uint8(v_cfg_2165_, sizeof(void*)*27 + 6);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_cfg_2165_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v_cfg_2165_, 17);
lean_dec(v_unused_2206_);
v___x_2200_ = v_cfg_2165_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_builtinLint_x3f_2197_);
lean_inc(v_restoreAllArtifacts_x3f_2194_);
lean_inc(v_enableArtifactCache_x3f_2193_);
lean_inc(v_readmeFile_2191_);
lean_inc(v_licenseFiles_2190_);
lean_inc(v_license_2189_);
lean_inc(v_homepage_2188_);
lean_inc(v_keywords_2187_);
lean_inc(v_description_2186_);
lean_inc(v_version_2185_);
lean_inc(v_lintDriverArgs_2184_);
lean_inc(v_lintDriver_2183_);
lean_inc(v_testDriverArgs_2182_);
lean_inc(v_testDriver_2181_);
lean_inc(v_buildArchive_2179_);
lean_inc(v_releaseRepo_2178_);
lean_inc(v_irDir_2177_);
lean_inc(v_binDir_2176_);
lean_inc(v_nativeLibDir_2175_);
lean_inc(v_leanLibDir_2174_);
lean_inc(v_buildDir_2173_);
lean_inc(v_srcDir_2172_);
lean_inc(v_moreGlobalServerArgs_2171_);
lean_inc(v_extraDepTargets_2169_);
lean_inc(v_toLeanConfig_2167_);
lean_inc(v_toWorkspaceConfig_2166_);
lean_dec(v_cfg_2165_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 17, v_val_2164_);
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_toWorkspaceConfig_2166_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_toLeanConfig_2167_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_extraDepTargets_2169_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_moreGlobalServerArgs_2171_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v_srcDir_2172_);
lean_ctor_set(v_reuseFailAlloc_2204_, 5, v_buildDir_2173_);
lean_ctor_set(v_reuseFailAlloc_2204_, 6, v_leanLibDir_2174_);
lean_ctor_set(v_reuseFailAlloc_2204_, 7, v_nativeLibDir_2175_);
lean_ctor_set(v_reuseFailAlloc_2204_, 8, v_binDir_2176_);
lean_ctor_set(v_reuseFailAlloc_2204_, 9, v_irDir_2177_);
lean_ctor_set(v_reuseFailAlloc_2204_, 10, v_releaseRepo_2178_);
lean_ctor_set(v_reuseFailAlloc_2204_, 11, v_buildArchive_2179_);
lean_ctor_set(v_reuseFailAlloc_2204_, 12, v_testDriver_2181_);
lean_ctor_set(v_reuseFailAlloc_2204_, 13, v_testDriverArgs_2182_);
lean_ctor_set(v_reuseFailAlloc_2204_, 14, v_lintDriver_2183_);
lean_ctor_set(v_reuseFailAlloc_2204_, 15, v_lintDriverArgs_2184_);
lean_ctor_set(v_reuseFailAlloc_2204_, 16, v_version_2185_);
lean_ctor_set(v_reuseFailAlloc_2204_, 17, v_val_2164_);
lean_ctor_set(v_reuseFailAlloc_2204_, 18, v_description_2186_);
lean_ctor_set(v_reuseFailAlloc_2204_, 19, v_keywords_2187_);
lean_ctor_set(v_reuseFailAlloc_2204_, 20, v_homepage_2188_);
lean_ctor_set(v_reuseFailAlloc_2204_, 21, v_license_2189_);
lean_ctor_set(v_reuseFailAlloc_2204_, 22, v_licenseFiles_2190_);
lean_ctor_set(v_reuseFailAlloc_2204_, 23, v_readmeFile_2191_);
lean_ctor_set(v_reuseFailAlloc_2204_, 24, v_enableArtifactCache_x3f_2193_);
lean_ctor_set(v_reuseFailAlloc_2204_, 25, v_restoreAllArtifacts_x3f_2194_);
lean_ctor_set(v_reuseFailAlloc_2204_, 26, v_builtinLint_x3f_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27, v_bootstrap_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27 + 1, v_precompileModules_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27 + 3, v_reservoir_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27 + 5, v_allowImportAll_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*27 + 6, v_fixedToolchain_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* v_f_2207_, lean_object* v_cfg_2208_){
_start:
{
lean_object* v_toWorkspaceConfig_2209_; lean_object* v_toLeanConfig_2210_; uint8_t v_bootstrap_2211_; lean_object* v_extraDepTargets_2212_; uint8_t v_precompileModules_2213_; lean_object* v_moreGlobalServerArgs_2214_; lean_object* v_srcDir_2215_; lean_object* v_buildDir_2216_; lean_object* v_leanLibDir_2217_; lean_object* v_nativeLibDir_2218_; lean_object* v_binDir_2219_; lean_object* v_irDir_2220_; lean_object* v_releaseRepo_2221_; lean_object* v_buildArchive_2222_; uint8_t v_preferReleaseBuild_2223_; lean_object* v_testDriver_2224_; lean_object* v_testDriverArgs_2225_; lean_object* v_lintDriver_2226_; lean_object* v_lintDriverArgs_2227_; lean_object* v_version_2228_; lean_object* v_versionTags_2229_; lean_object* v_description_2230_; lean_object* v_keywords_2231_; lean_object* v_homepage_2232_; lean_object* v_license_2233_; lean_object* v_licenseFiles_2234_; lean_object* v_readmeFile_2235_; uint8_t v_reservoir_2236_; lean_object* v_enableArtifactCache_x3f_2237_; lean_object* v_restoreAllArtifacts_x3f_2238_; uint8_t v_libPrefixOnWindows_2239_; uint8_t v_allowImportAll_2240_; lean_object* v_builtinLint_x3f_2241_; uint8_t v_fixedToolchain_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_toWorkspaceConfig_2209_ = lean_ctor_get(v_cfg_2208_, 0);
v_toLeanConfig_2210_ = lean_ctor_get(v_cfg_2208_, 1);
v_bootstrap_2211_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27);
v_extraDepTargets_2212_ = lean_ctor_get(v_cfg_2208_, 2);
v_precompileModules_2213_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2214_ = lean_ctor_get(v_cfg_2208_, 3);
v_srcDir_2215_ = lean_ctor_get(v_cfg_2208_, 4);
v_buildDir_2216_ = lean_ctor_get(v_cfg_2208_, 5);
v_leanLibDir_2217_ = lean_ctor_get(v_cfg_2208_, 6);
v_nativeLibDir_2218_ = lean_ctor_get(v_cfg_2208_, 7);
v_binDir_2219_ = lean_ctor_get(v_cfg_2208_, 8);
v_irDir_2220_ = lean_ctor_get(v_cfg_2208_, 9);
v_releaseRepo_2221_ = lean_ctor_get(v_cfg_2208_, 10);
v_buildArchive_2222_ = lean_ctor_get(v_cfg_2208_, 11);
v_preferReleaseBuild_2223_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27 + 2);
v_testDriver_2224_ = lean_ctor_get(v_cfg_2208_, 12);
v_testDriverArgs_2225_ = lean_ctor_get(v_cfg_2208_, 13);
v_lintDriver_2226_ = lean_ctor_get(v_cfg_2208_, 14);
v_lintDriverArgs_2227_ = lean_ctor_get(v_cfg_2208_, 15);
v_version_2228_ = lean_ctor_get(v_cfg_2208_, 16);
v_versionTags_2229_ = lean_ctor_get(v_cfg_2208_, 17);
v_description_2230_ = lean_ctor_get(v_cfg_2208_, 18);
v_keywords_2231_ = lean_ctor_get(v_cfg_2208_, 19);
v_homepage_2232_ = lean_ctor_get(v_cfg_2208_, 20);
v_license_2233_ = lean_ctor_get(v_cfg_2208_, 21);
v_licenseFiles_2234_ = lean_ctor_get(v_cfg_2208_, 22);
v_readmeFile_2235_ = lean_ctor_get(v_cfg_2208_, 23);
v_reservoir_2236_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2237_ = lean_ctor_get(v_cfg_2208_, 24);
v_restoreAllArtifacts_x3f_2238_ = lean_ctor_get(v_cfg_2208_, 25);
v_libPrefixOnWindows_2239_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27 + 4);
v_allowImportAll_2240_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2241_ = lean_ctor_get(v_cfg_2208_, 26);
v_fixedToolchain_2242_ = lean_ctor_get_uint8(v_cfg_2208_, sizeof(void*)*27 + 6);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_cfg_2208_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v_cfg_2208_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_builtinLint_x3f_2241_);
lean_inc(v_restoreAllArtifacts_x3f_2238_);
lean_inc(v_enableArtifactCache_x3f_2237_);
lean_inc(v_readmeFile_2235_);
lean_inc(v_licenseFiles_2234_);
lean_inc(v_license_2233_);
lean_inc(v_homepage_2232_);
lean_inc(v_keywords_2231_);
lean_inc(v_description_2230_);
lean_inc(v_versionTags_2229_);
lean_inc(v_version_2228_);
lean_inc(v_lintDriverArgs_2227_);
lean_inc(v_lintDriver_2226_);
lean_inc(v_testDriverArgs_2225_);
lean_inc(v_testDriver_2224_);
lean_inc(v_buildArchive_2222_);
lean_inc(v_releaseRepo_2221_);
lean_inc(v_irDir_2220_);
lean_inc(v_binDir_2219_);
lean_inc(v_nativeLibDir_2218_);
lean_inc(v_leanLibDir_2217_);
lean_inc(v_buildDir_2216_);
lean_inc(v_srcDir_2215_);
lean_inc(v_moreGlobalServerArgs_2214_);
lean_inc(v_extraDepTargets_2212_);
lean_inc(v_toLeanConfig_2210_);
lean_inc(v_toWorkspaceConfig_2209_);
lean_dec(v_cfg_2208_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = lean_apply_1(v_f_2207_, v_versionTags_2229_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 17, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_toWorkspaceConfig_2209_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_toLeanConfig_2210_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_extraDepTargets_2212_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_moreGlobalServerArgs_2214_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_srcDir_2215_);
lean_ctor_set(v_reuseFailAlloc_2249_, 5, v_buildDir_2216_);
lean_ctor_set(v_reuseFailAlloc_2249_, 6, v_leanLibDir_2217_);
lean_ctor_set(v_reuseFailAlloc_2249_, 7, v_nativeLibDir_2218_);
lean_ctor_set(v_reuseFailAlloc_2249_, 8, v_binDir_2219_);
lean_ctor_set(v_reuseFailAlloc_2249_, 9, v_irDir_2220_);
lean_ctor_set(v_reuseFailAlloc_2249_, 10, v_releaseRepo_2221_);
lean_ctor_set(v_reuseFailAlloc_2249_, 11, v_buildArchive_2222_);
lean_ctor_set(v_reuseFailAlloc_2249_, 12, v_testDriver_2224_);
lean_ctor_set(v_reuseFailAlloc_2249_, 13, v_testDriverArgs_2225_);
lean_ctor_set(v_reuseFailAlloc_2249_, 14, v_lintDriver_2226_);
lean_ctor_set(v_reuseFailAlloc_2249_, 15, v_lintDriverArgs_2227_);
lean_ctor_set(v_reuseFailAlloc_2249_, 16, v_version_2228_);
lean_ctor_set(v_reuseFailAlloc_2249_, 17, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2249_, 18, v_description_2230_);
lean_ctor_set(v_reuseFailAlloc_2249_, 19, v_keywords_2231_);
lean_ctor_set(v_reuseFailAlloc_2249_, 20, v_homepage_2232_);
lean_ctor_set(v_reuseFailAlloc_2249_, 21, v_license_2233_);
lean_ctor_set(v_reuseFailAlloc_2249_, 22, v_licenseFiles_2234_);
lean_ctor_set(v_reuseFailAlloc_2249_, 23, v_readmeFile_2235_);
lean_ctor_set(v_reuseFailAlloc_2249_, 24, v_enableArtifactCache_x3f_2237_);
lean_ctor_set(v_reuseFailAlloc_2249_, 25, v_restoreAllArtifacts_x3f_2238_);
lean_ctor_set(v_reuseFailAlloc_2249_, 26, v_builtinLint_x3f_2241_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27, v_bootstrap_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27 + 1, v_precompileModules_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2223_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27 + 3, v_reservoir_2236_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2239_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27 + 5, v_allowImportAll_2240_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*27 + 6, v_fixedToolchain_2242_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lake_defaultVersionTags;
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* v_x_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lake_PackageConfig_versionTags___proj___lam__3(v_x_2253_);
lean_dec_ref(v_x_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2264_, lean_object* v_n_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2267_, lean_object* v_n_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lake_PackageConfig_versionTags___proj(v_p_2267_, v_n_2268_);
lean_dec(v_n_2268_);
lean_dec(v_p_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2270_, lean_object* v_n_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lake_PackageConfig_versionTags___proj(v_p_2270_, v_n_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2273_, lean_object* v_n_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2273_, v_n_2274_);
lean_dec(v_n_2274_);
lean_dec(v_p_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* v_cfg_2276_){
_start:
{
lean_object* v_description_2277_; 
v_description_2277_ = lean_ctor_get(v_cfg_2276_, 18);
lean_inc_ref(v_description_2277_);
return v_description_2277_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* v_cfg_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lake_PackageConfig_description___proj___lam__0(v_cfg_2278_);
lean_dec_ref(v_cfg_2278_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* v_val_2280_, lean_object* v_cfg_2281_){
_start:
{
lean_object* v_toWorkspaceConfig_2282_; lean_object* v_toLeanConfig_2283_; uint8_t v_bootstrap_2284_; lean_object* v_extraDepTargets_2285_; uint8_t v_precompileModules_2286_; lean_object* v_moreGlobalServerArgs_2287_; lean_object* v_srcDir_2288_; lean_object* v_buildDir_2289_; lean_object* v_leanLibDir_2290_; lean_object* v_nativeLibDir_2291_; lean_object* v_binDir_2292_; lean_object* v_irDir_2293_; lean_object* v_releaseRepo_2294_; lean_object* v_buildArchive_2295_; uint8_t v_preferReleaseBuild_2296_; lean_object* v_testDriver_2297_; lean_object* v_testDriverArgs_2298_; lean_object* v_lintDriver_2299_; lean_object* v_lintDriverArgs_2300_; lean_object* v_version_2301_; lean_object* v_versionTags_2302_; lean_object* v_keywords_2303_; lean_object* v_homepage_2304_; lean_object* v_license_2305_; lean_object* v_licenseFiles_2306_; lean_object* v_readmeFile_2307_; uint8_t v_reservoir_2308_; lean_object* v_enableArtifactCache_x3f_2309_; lean_object* v_restoreAllArtifacts_x3f_2310_; uint8_t v_libPrefixOnWindows_2311_; uint8_t v_allowImportAll_2312_; lean_object* v_builtinLint_x3f_2313_; uint8_t v_fixedToolchain_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_toWorkspaceConfig_2282_ = lean_ctor_get(v_cfg_2281_, 0);
v_toLeanConfig_2283_ = lean_ctor_get(v_cfg_2281_, 1);
v_bootstrap_2284_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27);
v_extraDepTargets_2285_ = lean_ctor_get(v_cfg_2281_, 2);
v_precompileModules_2286_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2287_ = lean_ctor_get(v_cfg_2281_, 3);
v_srcDir_2288_ = lean_ctor_get(v_cfg_2281_, 4);
v_buildDir_2289_ = lean_ctor_get(v_cfg_2281_, 5);
v_leanLibDir_2290_ = lean_ctor_get(v_cfg_2281_, 6);
v_nativeLibDir_2291_ = lean_ctor_get(v_cfg_2281_, 7);
v_binDir_2292_ = lean_ctor_get(v_cfg_2281_, 8);
v_irDir_2293_ = lean_ctor_get(v_cfg_2281_, 9);
v_releaseRepo_2294_ = lean_ctor_get(v_cfg_2281_, 10);
v_buildArchive_2295_ = lean_ctor_get(v_cfg_2281_, 11);
v_preferReleaseBuild_2296_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27 + 2);
v_testDriver_2297_ = lean_ctor_get(v_cfg_2281_, 12);
v_testDriverArgs_2298_ = lean_ctor_get(v_cfg_2281_, 13);
v_lintDriver_2299_ = lean_ctor_get(v_cfg_2281_, 14);
v_lintDriverArgs_2300_ = lean_ctor_get(v_cfg_2281_, 15);
v_version_2301_ = lean_ctor_get(v_cfg_2281_, 16);
v_versionTags_2302_ = lean_ctor_get(v_cfg_2281_, 17);
v_keywords_2303_ = lean_ctor_get(v_cfg_2281_, 19);
v_homepage_2304_ = lean_ctor_get(v_cfg_2281_, 20);
v_license_2305_ = lean_ctor_get(v_cfg_2281_, 21);
v_licenseFiles_2306_ = lean_ctor_get(v_cfg_2281_, 22);
v_readmeFile_2307_ = lean_ctor_get(v_cfg_2281_, 23);
v_reservoir_2308_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2309_ = lean_ctor_get(v_cfg_2281_, 24);
v_restoreAllArtifacts_x3f_2310_ = lean_ctor_get(v_cfg_2281_, 25);
v_libPrefixOnWindows_2311_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27 + 4);
v_allowImportAll_2312_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2313_ = lean_ctor_get(v_cfg_2281_, 26);
v_fixedToolchain_2314_ = lean_ctor_get_uint8(v_cfg_2281_, sizeof(void*)*27 + 6);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_cfg_2281_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v_cfg_2281_, 18);
lean_dec(v_unused_2322_);
v___x_2316_ = v_cfg_2281_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_builtinLint_x3f_2313_);
lean_inc(v_restoreAllArtifacts_x3f_2310_);
lean_inc(v_enableArtifactCache_x3f_2309_);
lean_inc(v_readmeFile_2307_);
lean_inc(v_licenseFiles_2306_);
lean_inc(v_license_2305_);
lean_inc(v_homepage_2304_);
lean_inc(v_keywords_2303_);
lean_inc(v_versionTags_2302_);
lean_inc(v_version_2301_);
lean_inc(v_lintDriverArgs_2300_);
lean_inc(v_lintDriver_2299_);
lean_inc(v_testDriverArgs_2298_);
lean_inc(v_testDriver_2297_);
lean_inc(v_buildArchive_2295_);
lean_inc(v_releaseRepo_2294_);
lean_inc(v_irDir_2293_);
lean_inc(v_binDir_2292_);
lean_inc(v_nativeLibDir_2291_);
lean_inc(v_leanLibDir_2290_);
lean_inc(v_buildDir_2289_);
lean_inc(v_srcDir_2288_);
lean_inc(v_moreGlobalServerArgs_2287_);
lean_inc(v_extraDepTargets_2285_);
lean_inc(v_toLeanConfig_2283_);
lean_inc(v_toWorkspaceConfig_2282_);
lean_dec(v_cfg_2281_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 18, v_val_2280_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_toWorkspaceConfig_2282_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_toLeanConfig_2283_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_extraDepTargets_2285_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_moreGlobalServerArgs_2287_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_srcDir_2288_);
lean_ctor_set(v_reuseFailAlloc_2320_, 5, v_buildDir_2289_);
lean_ctor_set(v_reuseFailAlloc_2320_, 6, v_leanLibDir_2290_);
lean_ctor_set(v_reuseFailAlloc_2320_, 7, v_nativeLibDir_2291_);
lean_ctor_set(v_reuseFailAlloc_2320_, 8, v_binDir_2292_);
lean_ctor_set(v_reuseFailAlloc_2320_, 9, v_irDir_2293_);
lean_ctor_set(v_reuseFailAlloc_2320_, 10, v_releaseRepo_2294_);
lean_ctor_set(v_reuseFailAlloc_2320_, 11, v_buildArchive_2295_);
lean_ctor_set(v_reuseFailAlloc_2320_, 12, v_testDriver_2297_);
lean_ctor_set(v_reuseFailAlloc_2320_, 13, v_testDriverArgs_2298_);
lean_ctor_set(v_reuseFailAlloc_2320_, 14, v_lintDriver_2299_);
lean_ctor_set(v_reuseFailAlloc_2320_, 15, v_lintDriverArgs_2300_);
lean_ctor_set(v_reuseFailAlloc_2320_, 16, v_version_2301_);
lean_ctor_set(v_reuseFailAlloc_2320_, 17, v_versionTags_2302_);
lean_ctor_set(v_reuseFailAlloc_2320_, 18, v_val_2280_);
lean_ctor_set(v_reuseFailAlloc_2320_, 19, v_keywords_2303_);
lean_ctor_set(v_reuseFailAlloc_2320_, 20, v_homepage_2304_);
lean_ctor_set(v_reuseFailAlloc_2320_, 21, v_license_2305_);
lean_ctor_set(v_reuseFailAlloc_2320_, 22, v_licenseFiles_2306_);
lean_ctor_set(v_reuseFailAlloc_2320_, 23, v_readmeFile_2307_);
lean_ctor_set(v_reuseFailAlloc_2320_, 24, v_enableArtifactCache_x3f_2309_);
lean_ctor_set(v_reuseFailAlloc_2320_, 25, v_restoreAllArtifacts_x3f_2310_);
lean_ctor_set(v_reuseFailAlloc_2320_, 26, v_builtinLint_x3f_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27, v_bootstrap_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27 + 1, v_precompileModules_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27 + 3, v_reservoir_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27 + 5, v_allowImportAll_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*27 + 6, v_fixedToolchain_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* v_f_2323_, lean_object* v_cfg_2324_){
_start:
{
lean_object* v_toWorkspaceConfig_2325_; lean_object* v_toLeanConfig_2326_; uint8_t v_bootstrap_2327_; lean_object* v_extraDepTargets_2328_; uint8_t v_precompileModules_2329_; lean_object* v_moreGlobalServerArgs_2330_; lean_object* v_srcDir_2331_; lean_object* v_buildDir_2332_; lean_object* v_leanLibDir_2333_; lean_object* v_nativeLibDir_2334_; lean_object* v_binDir_2335_; lean_object* v_irDir_2336_; lean_object* v_releaseRepo_2337_; lean_object* v_buildArchive_2338_; uint8_t v_preferReleaseBuild_2339_; lean_object* v_testDriver_2340_; lean_object* v_testDriverArgs_2341_; lean_object* v_lintDriver_2342_; lean_object* v_lintDriverArgs_2343_; lean_object* v_version_2344_; lean_object* v_versionTags_2345_; lean_object* v_description_2346_; lean_object* v_keywords_2347_; lean_object* v_homepage_2348_; lean_object* v_license_2349_; lean_object* v_licenseFiles_2350_; lean_object* v_readmeFile_2351_; uint8_t v_reservoir_2352_; lean_object* v_enableArtifactCache_x3f_2353_; lean_object* v_restoreAllArtifacts_x3f_2354_; uint8_t v_libPrefixOnWindows_2355_; uint8_t v_allowImportAll_2356_; lean_object* v_builtinLint_x3f_2357_; uint8_t v_fixedToolchain_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2366_; 
v_toWorkspaceConfig_2325_ = lean_ctor_get(v_cfg_2324_, 0);
v_toLeanConfig_2326_ = lean_ctor_get(v_cfg_2324_, 1);
v_bootstrap_2327_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27);
v_extraDepTargets_2328_ = lean_ctor_get(v_cfg_2324_, 2);
v_precompileModules_2329_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2330_ = lean_ctor_get(v_cfg_2324_, 3);
v_srcDir_2331_ = lean_ctor_get(v_cfg_2324_, 4);
v_buildDir_2332_ = lean_ctor_get(v_cfg_2324_, 5);
v_leanLibDir_2333_ = lean_ctor_get(v_cfg_2324_, 6);
v_nativeLibDir_2334_ = lean_ctor_get(v_cfg_2324_, 7);
v_binDir_2335_ = lean_ctor_get(v_cfg_2324_, 8);
v_irDir_2336_ = lean_ctor_get(v_cfg_2324_, 9);
v_releaseRepo_2337_ = lean_ctor_get(v_cfg_2324_, 10);
v_buildArchive_2338_ = lean_ctor_get(v_cfg_2324_, 11);
v_preferReleaseBuild_2339_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27 + 2);
v_testDriver_2340_ = lean_ctor_get(v_cfg_2324_, 12);
v_testDriverArgs_2341_ = lean_ctor_get(v_cfg_2324_, 13);
v_lintDriver_2342_ = lean_ctor_get(v_cfg_2324_, 14);
v_lintDriverArgs_2343_ = lean_ctor_get(v_cfg_2324_, 15);
v_version_2344_ = lean_ctor_get(v_cfg_2324_, 16);
v_versionTags_2345_ = lean_ctor_get(v_cfg_2324_, 17);
v_description_2346_ = lean_ctor_get(v_cfg_2324_, 18);
v_keywords_2347_ = lean_ctor_get(v_cfg_2324_, 19);
v_homepage_2348_ = lean_ctor_get(v_cfg_2324_, 20);
v_license_2349_ = lean_ctor_get(v_cfg_2324_, 21);
v_licenseFiles_2350_ = lean_ctor_get(v_cfg_2324_, 22);
v_readmeFile_2351_ = lean_ctor_get(v_cfg_2324_, 23);
v_reservoir_2352_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2353_ = lean_ctor_get(v_cfg_2324_, 24);
v_restoreAllArtifacts_x3f_2354_ = lean_ctor_get(v_cfg_2324_, 25);
v_libPrefixOnWindows_2355_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27 + 4);
v_allowImportAll_2356_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2357_ = lean_ctor_get(v_cfg_2324_, 26);
v_fixedToolchain_2358_ = lean_ctor_get_uint8(v_cfg_2324_, sizeof(void*)*27 + 6);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_cfg_2324_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2360_ = v_cfg_2324_;
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_builtinLint_x3f_2357_);
lean_inc(v_restoreAllArtifacts_x3f_2354_);
lean_inc(v_enableArtifactCache_x3f_2353_);
lean_inc(v_readmeFile_2351_);
lean_inc(v_licenseFiles_2350_);
lean_inc(v_license_2349_);
lean_inc(v_homepage_2348_);
lean_inc(v_keywords_2347_);
lean_inc(v_description_2346_);
lean_inc(v_versionTags_2345_);
lean_inc(v_version_2344_);
lean_inc(v_lintDriverArgs_2343_);
lean_inc(v_lintDriver_2342_);
lean_inc(v_testDriverArgs_2341_);
lean_inc(v_testDriver_2340_);
lean_inc(v_buildArchive_2338_);
lean_inc(v_releaseRepo_2337_);
lean_inc(v_irDir_2336_);
lean_inc(v_binDir_2335_);
lean_inc(v_nativeLibDir_2334_);
lean_inc(v_leanLibDir_2333_);
lean_inc(v_buildDir_2332_);
lean_inc(v_srcDir_2331_);
lean_inc(v_moreGlobalServerArgs_2330_);
lean_inc(v_extraDepTargets_2328_);
lean_inc(v_toLeanConfig_2326_);
lean_inc(v_toWorkspaceConfig_2325_);
lean_dec(v_cfg_2324_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_apply_1(v_f_2323_, v_description_2346_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 18, v___x_2362_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_toWorkspaceConfig_2325_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_toLeanConfig_2326_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_extraDepTargets_2328_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_moreGlobalServerArgs_2330_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_srcDir_2331_);
lean_ctor_set(v_reuseFailAlloc_2365_, 5, v_buildDir_2332_);
lean_ctor_set(v_reuseFailAlloc_2365_, 6, v_leanLibDir_2333_);
lean_ctor_set(v_reuseFailAlloc_2365_, 7, v_nativeLibDir_2334_);
lean_ctor_set(v_reuseFailAlloc_2365_, 8, v_binDir_2335_);
lean_ctor_set(v_reuseFailAlloc_2365_, 9, v_irDir_2336_);
lean_ctor_set(v_reuseFailAlloc_2365_, 10, v_releaseRepo_2337_);
lean_ctor_set(v_reuseFailAlloc_2365_, 11, v_buildArchive_2338_);
lean_ctor_set(v_reuseFailAlloc_2365_, 12, v_testDriver_2340_);
lean_ctor_set(v_reuseFailAlloc_2365_, 13, v_testDriverArgs_2341_);
lean_ctor_set(v_reuseFailAlloc_2365_, 14, v_lintDriver_2342_);
lean_ctor_set(v_reuseFailAlloc_2365_, 15, v_lintDriverArgs_2343_);
lean_ctor_set(v_reuseFailAlloc_2365_, 16, v_version_2344_);
lean_ctor_set(v_reuseFailAlloc_2365_, 17, v_versionTags_2345_);
lean_ctor_set(v_reuseFailAlloc_2365_, 18, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2365_, 19, v_keywords_2347_);
lean_ctor_set(v_reuseFailAlloc_2365_, 20, v_homepage_2348_);
lean_ctor_set(v_reuseFailAlloc_2365_, 21, v_license_2349_);
lean_ctor_set(v_reuseFailAlloc_2365_, 22, v_licenseFiles_2350_);
lean_ctor_set(v_reuseFailAlloc_2365_, 23, v_readmeFile_2351_);
lean_ctor_set(v_reuseFailAlloc_2365_, 24, v_enableArtifactCache_x3f_2353_);
lean_ctor_set(v_reuseFailAlloc_2365_, 25, v_restoreAllArtifacts_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2365_, 26, v_builtinLint_x3f_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27, v_bootstrap_2327_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27 + 1, v_precompileModules_2329_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27 + 3, v_reservoir_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27 + 5, v_allowImportAll_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*27 + 6, v_fixedToolchain_2358_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2375_, lean_object* v_n_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2378_, lean_object* v_n_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lake_PackageConfig_description___proj(v_p_2378_, v_n_2379_);
lean_dec(v_n_2379_);
lean_dec(v_p_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2381_, lean_object* v_n_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lake_PackageConfig_description___proj(v_p_2381_, v_n_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2384_, lean_object* v_n_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lake_PackageConfig_description_instConfigField(v_p_2384_, v_n_2385_);
lean_dec(v_n_2385_);
lean_dec(v_p_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* v_cfg_2387_){
_start:
{
lean_object* v_keywords_2388_; 
v_keywords_2388_ = lean_ctor_get(v_cfg_2387_, 19);
lean_inc_ref(v_keywords_2388_);
return v_keywords_2388_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* v_cfg_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lake_PackageConfig_keywords___proj___lam__0(v_cfg_2389_);
lean_dec_ref(v_cfg_2389_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* v_val_2391_, lean_object* v_cfg_2392_){
_start:
{
lean_object* v_toWorkspaceConfig_2393_; lean_object* v_toLeanConfig_2394_; uint8_t v_bootstrap_2395_; lean_object* v_extraDepTargets_2396_; uint8_t v_precompileModules_2397_; lean_object* v_moreGlobalServerArgs_2398_; lean_object* v_srcDir_2399_; lean_object* v_buildDir_2400_; lean_object* v_leanLibDir_2401_; lean_object* v_nativeLibDir_2402_; lean_object* v_binDir_2403_; lean_object* v_irDir_2404_; lean_object* v_releaseRepo_2405_; lean_object* v_buildArchive_2406_; uint8_t v_preferReleaseBuild_2407_; lean_object* v_testDriver_2408_; lean_object* v_testDriverArgs_2409_; lean_object* v_lintDriver_2410_; lean_object* v_lintDriverArgs_2411_; lean_object* v_version_2412_; lean_object* v_versionTags_2413_; lean_object* v_description_2414_; lean_object* v_homepage_2415_; lean_object* v_license_2416_; lean_object* v_licenseFiles_2417_; lean_object* v_readmeFile_2418_; uint8_t v_reservoir_2419_; lean_object* v_enableArtifactCache_x3f_2420_; lean_object* v_restoreAllArtifacts_x3f_2421_; uint8_t v_libPrefixOnWindows_2422_; uint8_t v_allowImportAll_2423_; lean_object* v_builtinLint_x3f_2424_; uint8_t v_fixedToolchain_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v_toWorkspaceConfig_2393_ = lean_ctor_get(v_cfg_2392_, 0);
v_toLeanConfig_2394_ = lean_ctor_get(v_cfg_2392_, 1);
v_bootstrap_2395_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27);
v_extraDepTargets_2396_ = lean_ctor_get(v_cfg_2392_, 2);
v_precompileModules_2397_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2398_ = lean_ctor_get(v_cfg_2392_, 3);
v_srcDir_2399_ = lean_ctor_get(v_cfg_2392_, 4);
v_buildDir_2400_ = lean_ctor_get(v_cfg_2392_, 5);
v_leanLibDir_2401_ = lean_ctor_get(v_cfg_2392_, 6);
v_nativeLibDir_2402_ = lean_ctor_get(v_cfg_2392_, 7);
v_binDir_2403_ = lean_ctor_get(v_cfg_2392_, 8);
v_irDir_2404_ = lean_ctor_get(v_cfg_2392_, 9);
v_releaseRepo_2405_ = lean_ctor_get(v_cfg_2392_, 10);
v_buildArchive_2406_ = lean_ctor_get(v_cfg_2392_, 11);
v_preferReleaseBuild_2407_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27 + 2);
v_testDriver_2408_ = lean_ctor_get(v_cfg_2392_, 12);
v_testDriverArgs_2409_ = lean_ctor_get(v_cfg_2392_, 13);
v_lintDriver_2410_ = lean_ctor_get(v_cfg_2392_, 14);
v_lintDriverArgs_2411_ = lean_ctor_get(v_cfg_2392_, 15);
v_version_2412_ = lean_ctor_get(v_cfg_2392_, 16);
v_versionTags_2413_ = lean_ctor_get(v_cfg_2392_, 17);
v_description_2414_ = lean_ctor_get(v_cfg_2392_, 18);
v_homepage_2415_ = lean_ctor_get(v_cfg_2392_, 20);
v_license_2416_ = lean_ctor_get(v_cfg_2392_, 21);
v_licenseFiles_2417_ = lean_ctor_get(v_cfg_2392_, 22);
v_readmeFile_2418_ = lean_ctor_get(v_cfg_2392_, 23);
v_reservoir_2419_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2420_ = lean_ctor_get(v_cfg_2392_, 24);
v_restoreAllArtifacts_x3f_2421_ = lean_ctor_get(v_cfg_2392_, 25);
v_libPrefixOnWindows_2422_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27 + 4);
v_allowImportAll_2423_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2424_ = lean_ctor_get(v_cfg_2392_, 26);
v_fixedToolchain_2425_ = lean_ctor_get_uint8(v_cfg_2392_, sizeof(void*)*27 + 6);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_cfg_2392_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v_cfg_2392_, 19);
lean_dec(v_unused_2433_);
v___x_2427_ = v_cfg_2392_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_builtinLint_x3f_2424_);
lean_inc(v_restoreAllArtifacts_x3f_2421_);
lean_inc(v_enableArtifactCache_x3f_2420_);
lean_inc(v_readmeFile_2418_);
lean_inc(v_licenseFiles_2417_);
lean_inc(v_license_2416_);
lean_inc(v_homepage_2415_);
lean_inc(v_description_2414_);
lean_inc(v_versionTags_2413_);
lean_inc(v_version_2412_);
lean_inc(v_lintDriverArgs_2411_);
lean_inc(v_lintDriver_2410_);
lean_inc(v_testDriverArgs_2409_);
lean_inc(v_testDriver_2408_);
lean_inc(v_buildArchive_2406_);
lean_inc(v_releaseRepo_2405_);
lean_inc(v_irDir_2404_);
lean_inc(v_binDir_2403_);
lean_inc(v_nativeLibDir_2402_);
lean_inc(v_leanLibDir_2401_);
lean_inc(v_buildDir_2400_);
lean_inc(v_srcDir_2399_);
lean_inc(v_moreGlobalServerArgs_2398_);
lean_inc(v_extraDepTargets_2396_);
lean_inc(v_toLeanConfig_2394_);
lean_inc(v_toWorkspaceConfig_2393_);
lean_dec(v_cfg_2392_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 19, v_val_2391_);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_toWorkspaceConfig_2393_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_toLeanConfig_2394_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_extraDepTargets_2396_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_moreGlobalServerArgs_2398_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_srcDir_2399_);
lean_ctor_set(v_reuseFailAlloc_2431_, 5, v_buildDir_2400_);
lean_ctor_set(v_reuseFailAlloc_2431_, 6, v_leanLibDir_2401_);
lean_ctor_set(v_reuseFailAlloc_2431_, 7, v_nativeLibDir_2402_);
lean_ctor_set(v_reuseFailAlloc_2431_, 8, v_binDir_2403_);
lean_ctor_set(v_reuseFailAlloc_2431_, 9, v_irDir_2404_);
lean_ctor_set(v_reuseFailAlloc_2431_, 10, v_releaseRepo_2405_);
lean_ctor_set(v_reuseFailAlloc_2431_, 11, v_buildArchive_2406_);
lean_ctor_set(v_reuseFailAlloc_2431_, 12, v_testDriver_2408_);
lean_ctor_set(v_reuseFailAlloc_2431_, 13, v_testDriverArgs_2409_);
lean_ctor_set(v_reuseFailAlloc_2431_, 14, v_lintDriver_2410_);
lean_ctor_set(v_reuseFailAlloc_2431_, 15, v_lintDriverArgs_2411_);
lean_ctor_set(v_reuseFailAlloc_2431_, 16, v_version_2412_);
lean_ctor_set(v_reuseFailAlloc_2431_, 17, v_versionTags_2413_);
lean_ctor_set(v_reuseFailAlloc_2431_, 18, v_description_2414_);
lean_ctor_set(v_reuseFailAlloc_2431_, 19, v_val_2391_);
lean_ctor_set(v_reuseFailAlloc_2431_, 20, v_homepage_2415_);
lean_ctor_set(v_reuseFailAlloc_2431_, 21, v_license_2416_);
lean_ctor_set(v_reuseFailAlloc_2431_, 22, v_licenseFiles_2417_);
lean_ctor_set(v_reuseFailAlloc_2431_, 23, v_readmeFile_2418_);
lean_ctor_set(v_reuseFailAlloc_2431_, 24, v_enableArtifactCache_x3f_2420_);
lean_ctor_set(v_reuseFailAlloc_2431_, 25, v_restoreAllArtifacts_x3f_2421_);
lean_ctor_set(v_reuseFailAlloc_2431_, 26, v_builtinLint_x3f_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27, v_bootstrap_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27 + 1, v_precompileModules_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27 + 3, v_reservoir_2419_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27 + 5, v_allowImportAll_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*27 + 6, v_fixedToolchain_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* v_f_2434_, lean_object* v_cfg_2435_){
_start:
{
lean_object* v_toWorkspaceConfig_2436_; lean_object* v_toLeanConfig_2437_; uint8_t v_bootstrap_2438_; lean_object* v_extraDepTargets_2439_; uint8_t v_precompileModules_2440_; lean_object* v_moreGlobalServerArgs_2441_; lean_object* v_srcDir_2442_; lean_object* v_buildDir_2443_; lean_object* v_leanLibDir_2444_; lean_object* v_nativeLibDir_2445_; lean_object* v_binDir_2446_; lean_object* v_irDir_2447_; lean_object* v_releaseRepo_2448_; lean_object* v_buildArchive_2449_; uint8_t v_preferReleaseBuild_2450_; lean_object* v_testDriver_2451_; lean_object* v_testDriverArgs_2452_; lean_object* v_lintDriver_2453_; lean_object* v_lintDriverArgs_2454_; lean_object* v_version_2455_; lean_object* v_versionTags_2456_; lean_object* v_description_2457_; lean_object* v_keywords_2458_; lean_object* v_homepage_2459_; lean_object* v_license_2460_; lean_object* v_licenseFiles_2461_; lean_object* v_readmeFile_2462_; uint8_t v_reservoir_2463_; lean_object* v_enableArtifactCache_x3f_2464_; lean_object* v_restoreAllArtifacts_x3f_2465_; uint8_t v_libPrefixOnWindows_2466_; uint8_t v_allowImportAll_2467_; lean_object* v_builtinLint_x3f_2468_; uint8_t v_fixedToolchain_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
v_toWorkspaceConfig_2436_ = lean_ctor_get(v_cfg_2435_, 0);
v_toLeanConfig_2437_ = lean_ctor_get(v_cfg_2435_, 1);
v_bootstrap_2438_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27);
v_extraDepTargets_2439_ = lean_ctor_get(v_cfg_2435_, 2);
v_precompileModules_2440_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2441_ = lean_ctor_get(v_cfg_2435_, 3);
v_srcDir_2442_ = lean_ctor_get(v_cfg_2435_, 4);
v_buildDir_2443_ = lean_ctor_get(v_cfg_2435_, 5);
v_leanLibDir_2444_ = lean_ctor_get(v_cfg_2435_, 6);
v_nativeLibDir_2445_ = lean_ctor_get(v_cfg_2435_, 7);
v_binDir_2446_ = lean_ctor_get(v_cfg_2435_, 8);
v_irDir_2447_ = lean_ctor_get(v_cfg_2435_, 9);
v_releaseRepo_2448_ = lean_ctor_get(v_cfg_2435_, 10);
v_buildArchive_2449_ = lean_ctor_get(v_cfg_2435_, 11);
v_preferReleaseBuild_2450_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27 + 2);
v_testDriver_2451_ = lean_ctor_get(v_cfg_2435_, 12);
v_testDriverArgs_2452_ = lean_ctor_get(v_cfg_2435_, 13);
v_lintDriver_2453_ = lean_ctor_get(v_cfg_2435_, 14);
v_lintDriverArgs_2454_ = lean_ctor_get(v_cfg_2435_, 15);
v_version_2455_ = lean_ctor_get(v_cfg_2435_, 16);
v_versionTags_2456_ = lean_ctor_get(v_cfg_2435_, 17);
v_description_2457_ = lean_ctor_get(v_cfg_2435_, 18);
v_keywords_2458_ = lean_ctor_get(v_cfg_2435_, 19);
v_homepage_2459_ = lean_ctor_get(v_cfg_2435_, 20);
v_license_2460_ = lean_ctor_get(v_cfg_2435_, 21);
v_licenseFiles_2461_ = lean_ctor_get(v_cfg_2435_, 22);
v_readmeFile_2462_ = lean_ctor_get(v_cfg_2435_, 23);
v_reservoir_2463_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2464_ = lean_ctor_get(v_cfg_2435_, 24);
v_restoreAllArtifacts_x3f_2465_ = lean_ctor_get(v_cfg_2435_, 25);
v_libPrefixOnWindows_2466_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27 + 4);
v_allowImportAll_2467_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2468_ = lean_ctor_get(v_cfg_2435_, 26);
v_fixedToolchain_2469_ = lean_ctor_get_uint8(v_cfg_2435_, sizeof(void*)*27 + 6);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_cfg_2435_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2471_ = v_cfg_2435_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_builtinLint_x3f_2468_);
lean_inc(v_restoreAllArtifacts_x3f_2465_);
lean_inc(v_enableArtifactCache_x3f_2464_);
lean_inc(v_readmeFile_2462_);
lean_inc(v_licenseFiles_2461_);
lean_inc(v_license_2460_);
lean_inc(v_homepage_2459_);
lean_inc(v_keywords_2458_);
lean_inc(v_description_2457_);
lean_inc(v_versionTags_2456_);
lean_inc(v_version_2455_);
lean_inc(v_lintDriverArgs_2454_);
lean_inc(v_lintDriver_2453_);
lean_inc(v_testDriverArgs_2452_);
lean_inc(v_testDriver_2451_);
lean_inc(v_buildArchive_2449_);
lean_inc(v_releaseRepo_2448_);
lean_inc(v_irDir_2447_);
lean_inc(v_binDir_2446_);
lean_inc(v_nativeLibDir_2445_);
lean_inc(v_leanLibDir_2444_);
lean_inc(v_buildDir_2443_);
lean_inc(v_srcDir_2442_);
lean_inc(v_moreGlobalServerArgs_2441_);
lean_inc(v_extraDepTargets_2439_);
lean_inc(v_toLeanConfig_2437_);
lean_inc(v_toWorkspaceConfig_2436_);
lean_dec(v_cfg_2435_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_apply_1(v_f_2434_, v_keywords_2458_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 19, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_toWorkspaceConfig_2436_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_toLeanConfig_2437_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_extraDepTargets_2439_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_moreGlobalServerArgs_2441_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_srcDir_2442_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v_buildDir_2443_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_leanLibDir_2444_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_nativeLibDir_2445_);
lean_ctor_set(v_reuseFailAlloc_2476_, 8, v_binDir_2446_);
lean_ctor_set(v_reuseFailAlloc_2476_, 9, v_irDir_2447_);
lean_ctor_set(v_reuseFailAlloc_2476_, 10, v_releaseRepo_2448_);
lean_ctor_set(v_reuseFailAlloc_2476_, 11, v_buildArchive_2449_);
lean_ctor_set(v_reuseFailAlloc_2476_, 12, v_testDriver_2451_);
lean_ctor_set(v_reuseFailAlloc_2476_, 13, v_testDriverArgs_2452_);
lean_ctor_set(v_reuseFailAlloc_2476_, 14, v_lintDriver_2453_);
lean_ctor_set(v_reuseFailAlloc_2476_, 15, v_lintDriverArgs_2454_);
lean_ctor_set(v_reuseFailAlloc_2476_, 16, v_version_2455_);
lean_ctor_set(v_reuseFailAlloc_2476_, 17, v_versionTags_2456_);
lean_ctor_set(v_reuseFailAlloc_2476_, 18, v_description_2457_);
lean_ctor_set(v_reuseFailAlloc_2476_, 19, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2476_, 20, v_homepage_2459_);
lean_ctor_set(v_reuseFailAlloc_2476_, 21, v_license_2460_);
lean_ctor_set(v_reuseFailAlloc_2476_, 22, v_licenseFiles_2461_);
lean_ctor_set(v_reuseFailAlloc_2476_, 23, v_readmeFile_2462_);
lean_ctor_set(v_reuseFailAlloc_2476_, 24, v_enableArtifactCache_x3f_2464_);
lean_ctor_set(v_reuseFailAlloc_2476_, 25, v_restoreAllArtifacts_x3f_2465_);
lean_ctor_set(v_reuseFailAlloc_2476_, 26, v_builtinLint_x3f_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27, v_bootstrap_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27 + 1, v_precompileModules_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27 + 3, v_reservoir_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27 + 5, v_allowImportAll_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*27 + 6, v_fixedToolchain_2469_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2486_, lean_object* v_n_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2489_, lean_object* v_n_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lake_PackageConfig_keywords___proj(v_p_2489_, v_n_2490_);
lean_dec(v_n_2490_);
lean_dec(v_p_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2492_, lean_object* v_n_2493_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lake_PackageConfig_keywords___proj(v_p_2492_, v_n_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2495_, lean_object* v_n_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2495_, v_n_2496_);
lean_dec(v_n_2496_);
lean_dec(v_p_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* v_cfg_2498_){
_start:
{
lean_object* v_homepage_2499_; 
v_homepage_2499_ = lean_ctor_get(v_cfg_2498_, 20);
lean_inc_ref(v_homepage_2499_);
return v_homepage_2499_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* v_cfg_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lake_PackageConfig_homepage___proj___lam__0(v_cfg_2500_);
lean_dec_ref(v_cfg_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* v_val_2502_, lean_object* v_cfg_2503_){
_start:
{
lean_object* v_toWorkspaceConfig_2504_; lean_object* v_toLeanConfig_2505_; uint8_t v_bootstrap_2506_; lean_object* v_extraDepTargets_2507_; uint8_t v_precompileModules_2508_; lean_object* v_moreGlobalServerArgs_2509_; lean_object* v_srcDir_2510_; lean_object* v_buildDir_2511_; lean_object* v_leanLibDir_2512_; lean_object* v_nativeLibDir_2513_; lean_object* v_binDir_2514_; lean_object* v_irDir_2515_; lean_object* v_releaseRepo_2516_; lean_object* v_buildArchive_2517_; uint8_t v_preferReleaseBuild_2518_; lean_object* v_testDriver_2519_; lean_object* v_testDriverArgs_2520_; lean_object* v_lintDriver_2521_; lean_object* v_lintDriverArgs_2522_; lean_object* v_version_2523_; lean_object* v_versionTags_2524_; lean_object* v_description_2525_; lean_object* v_keywords_2526_; lean_object* v_license_2527_; lean_object* v_licenseFiles_2528_; lean_object* v_readmeFile_2529_; uint8_t v_reservoir_2530_; lean_object* v_enableArtifactCache_x3f_2531_; lean_object* v_restoreAllArtifacts_x3f_2532_; uint8_t v_libPrefixOnWindows_2533_; uint8_t v_allowImportAll_2534_; lean_object* v_builtinLint_x3f_2535_; uint8_t v_fixedToolchain_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_toWorkspaceConfig_2504_ = lean_ctor_get(v_cfg_2503_, 0);
v_toLeanConfig_2505_ = lean_ctor_get(v_cfg_2503_, 1);
v_bootstrap_2506_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27);
v_extraDepTargets_2507_ = lean_ctor_get(v_cfg_2503_, 2);
v_precompileModules_2508_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2509_ = lean_ctor_get(v_cfg_2503_, 3);
v_srcDir_2510_ = lean_ctor_get(v_cfg_2503_, 4);
v_buildDir_2511_ = lean_ctor_get(v_cfg_2503_, 5);
v_leanLibDir_2512_ = lean_ctor_get(v_cfg_2503_, 6);
v_nativeLibDir_2513_ = lean_ctor_get(v_cfg_2503_, 7);
v_binDir_2514_ = lean_ctor_get(v_cfg_2503_, 8);
v_irDir_2515_ = lean_ctor_get(v_cfg_2503_, 9);
v_releaseRepo_2516_ = lean_ctor_get(v_cfg_2503_, 10);
v_buildArchive_2517_ = lean_ctor_get(v_cfg_2503_, 11);
v_preferReleaseBuild_2518_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27 + 2);
v_testDriver_2519_ = lean_ctor_get(v_cfg_2503_, 12);
v_testDriverArgs_2520_ = lean_ctor_get(v_cfg_2503_, 13);
v_lintDriver_2521_ = lean_ctor_get(v_cfg_2503_, 14);
v_lintDriverArgs_2522_ = lean_ctor_get(v_cfg_2503_, 15);
v_version_2523_ = lean_ctor_get(v_cfg_2503_, 16);
v_versionTags_2524_ = lean_ctor_get(v_cfg_2503_, 17);
v_description_2525_ = lean_ctor_get(v_cfg_2503_, 18);
v_keywords_2526_ = lean_ctor_get(v_cfg_2503_, 19);
v_license_2527_ = lean_ctor_get(v_cfg_2503_, 21);
v_licenseFiles_2528_ = lean_ctor_get(v_cfg_2503_, 22);
v_readmeFile_2529_ = lean_ctor_get(v_cfg_2503_, 23);
v_reservoir_2530_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2531_ = lean_ctor_get(v_cfg_2503_, 24);
v_restoreAllArtifacts_x3f_2532_ = lean_ctor_get(v_cfg_2503_, 25);
v_libPrefixOnWindows_2533_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27 + 4);
v_allowImportAll_2534_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2535_ = lean_ctor_get(v_cfg_2503_, 26);
v_fixedToolchain_2536_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*27 + 6);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_cfg_2503_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v_cfg_2503_, 20);
lean_dec(v_unused_2544_);
v___x_2538_ = v_cfg_2503_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_builtinLint_x3f_2535_);
lean_inc(v_restoreAllArtifacts_x3f_2532_);
lean_inc(v_enableArtifactCache_x3f_2531_);
lean_inc(v_readmeFile_2529_);
lean_inc(v_licenseFiles_2528_);
lean_inc(v_license_2527_);
lean_inc(v_keywords_2526_);
lean_inc(v_description_2525_);
lean_inc(v_versionTags_2524_);
lean_inc(v_version_2523_);
lean_inc(v_lintDriverArgs_2522_);
lean_inc(v_lintDriver_2521_);
lean_inc(v_testDriverArgs_2520_);
lean_inc(v_testDriver_2519_);
lean_inc(v_buildArchive_2517_);
lean_inc(v_releaseRepo_2516_);
lean_inc(v_irDir_2515_);
lean_inc(v_binDir_2514_);
lean_inc(v_nativeLibDir_2513_);
lean_inc(v_leanLibDir_2512_);
lean_inc(v_buildDir_2511_);
lean_inc(v_srcDir_2510_);
lean_inc(v_moreGlobalServerArgs_2509_);
lean_inc(v_extraDepTargets_2507_);
lean_inc(v_toLeanConfig_2505_);
lean_inc(v_toWorkspaceConfig_2504_);
lean_dec(v_cfg_2503_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 20, v_val_2502_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_toWorkspaceConfig_2504_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_toLeanConfig_2505_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_extraDepTargets_2507_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_moreGlobalServerArgs_2509_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_srcDir_2510_);
lean_ctor_set(v_reuseFailAlloc_2542_, 5, v_buildDir_2511_);
lean_ctor_set(v_reuseFailAlloc_2542_, 6, v_leanLibDir_2512_);
lean_ctor_set(v_reuseFailAlloc_2542_, 7, v_nativeLibDir_2513_);
lean_ctor_set(v_reuseFailAlloc_2542_, 8, v_binDir_2514_);
lean_ctor_set(v_reuseFailAlloc_2542_, 9, v_irDir_2515_);
lean_ctor_set(v_reuseFailAlloc_2542_, 10, v_releaseRepo_2516_);
lean_ctor_set(v_reuseFailAlloc_2542_, 11, v_buildArchive_2517_);
lean_ctor_set(v_reuseFailAlloc_2542_, 12, v_testDriver_2519_);
lean_ctor_set(v_reuseFailAlloc_2542_, 13, v_testDriverArgs_2520_);
lean_ctor_set(v_reuseFailAlloc_2542_, 14, v_lintDriver_2521_);
lean_ctor_set(v_reuseFailAlloc_2542_, 15, v_lintDriverArgs_2522_);
lean_ctor_set(v_reuseFailAlloc_2542_, 16, v_version_2523_);
lean_ctor_set(v_reuseFailAlloc_2542_, 17, v_versionTags_2524_);
lean_ctor_set(v_reuseFailAlloc_2542_, 18, v_description_2525_);
lean_ctor_set(v_reuseFailAlloc_2542_, 19, v_keywords_2526_);
lean_ctor_set(v_reuseFailAlloc_2542_, 20, v_val_2502_);
lean_ctor_set(v_reuseFailAlloc_2542_, 21, v_license_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 22, v_licenseFiles_2528_);
lean_ctor_set(v_reuseFailAlloc_2542_, 23, v_readmeFile_2529_);
lean_ctor_set(v_reuseFailAlloc_2542_, 24, v_enableArtifactCache_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2542_, 25, v_restoreAllArtifacts_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2542_, 26, v_builtinLint_x3f_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27, v_bootstrap_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27 + 1, v_precompileModules_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27 + 3, v_reservoir_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27 + 5, v_allowImportAll_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2542_, sizeof(void*)*27 + 6, v_fixedToolchain_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* v_f_2545_, lean_object* v_cfg_2546_){
_start:
{
lean_object* v_toWorkspaceConfig_2547_; lean_object* v_toLeanConfig_2548_; uint8_t v_bootstrap_2549_; lean_object* v_extraDepTargets_2550_; uint8_t v_precompileModules_2551_; lean_object* v_moreGlobalServerArgs_2552_; lean_object* v_srcDir_2553_; lean_object* v_buildDir_2554_; lean_object* v_leanLibDir_2555_; lean_object* v_nativeLibDir_2556_; lean_object* v_binDir_2557_; lean_object* v_irDir_2558_; lean_object* v_releaseRepo_2559_; lean_object* v_buildArchive_2560_; uint8_t v_preferReleaseBuild_2561_; lean_object* v_testDriver_2562_; lean_object* v_testDriverArgs_2563_; lean_object* v_lintDriver_2564_; lean_object* v_lintDriverArgs_2565_; lean_object* v_version_2566_; lean_object* v_versionTags_2567_; lean_object* v_description_2568_; lean_object* v_keywords_2569_; lean_object* v_homepage_2570_; lean_object* v_license_2571_; lean_object* v_licenseFiles_2572_; lean_object* v_readmeFile_2573_; uint8_t v_reservoir_2574_; lean_object* v_enableArtifactCache_x3f_2575_; lean_object* v_restoreAllArtifacts_x3f_2576_; uint8_t v_libPrefixOnWindows_2577_; uint8_t v_allowImportAll_2578_; lean_object* v_builtinLint_x3f_2579_; uint8_t v_fixedToolchain_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2588_; 
v_toWorkspaceConfig_2547_ = lean_ctor_get(v_cfg_2546_, 0);
v_toLeanConfig_2548_ = lean_ctor_get(v_cfg_2546_, 1);
v_bootstrap_2549_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27);
v_extraDepTargets_2550_ = lean_ctor_get(v_cfg_2546_, 2);
v_precompileModules_2551_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2552_ = lean_ctor_get(v_cfg_2546_, 3);
v_srcDir_2553_ = lean_ctor_get(v_cfg_2546_, 4);
v_buildDir_2554_ = lean_ctor_get(v_cfg_2546_, 5);
v_leanLibDir_2555_ = lean_ctor_get(v_cfg_2546_, 6);
v_nativeLibDir_2556_ = lean_ctor_get(v_cfg_2546_, 7);
v_binDir_2557_ = lean_ctor_get(v_cfg_2546_, 8);
v_irDir_2558_ = lean_ctor_get(v_cfg_2546_, 9);
v_releaseRepo_2559_ = lean_ctor_get(v_cfg_2546_, 10);
v_buildArchive_2560_ = lean_ctor_get(v_cfg_2546_, 11);
v_preferReleaseBuild_2561_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27 + 2);
v_testDriver_2562_ = lean_ctor_get(v_cfg_2546_, 12);
v_testDriverArgs_2563_ = lean_ctor_get(v_cfg_2546_, 13);
v_lintDriver_2564_ = lean_ctor_get(v_cfg_2546_, 14);
v_lintDriverArgs_2565_ = lean_ctor_get(v_cfg_2546_, 15);
v_version_2566_ = lean_ctor_get(v_cfg_2546_, 16);
v_versionTags_2567_ = lean_ctor_get(v_cfg_2546_, 17);
v_description_2568_ = lean_ctor_get(v_cfg_2546_, 18);
v_keywords_2569_ = lean_ctor_get(v_cfg_2546_, 19);
v_homepage_2570_ = lean_ctor_get(v_cfg_2546_, 20);
v_license_2571_ = lean_ctor_get(v_cfg_2546_, 21);
v_licenseFiles_2572_ = lean_ctor_get(v_cfg_2546_, 22);
v_readmeFile_2573_ = lean_ctor_get(v_cfg_2546_, 23);
v_reservoir_2574_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2575_ = lean_ctor_get(v_cfg_2546_, 24);
v_restoreAllArtifacts_x3f_2576_ = lean_ctor_get(v_cfg_2546_, 25);
v_libPrefixOnWindows_2577_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27 + 4);
v_allowImportAll_2578_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2579_ = lean_ctor_get(v_cfg_2546_, 26);
v_fixedToolchain_2580_ = lean_ctor_get_uint8(v_cfg_2546_, sizeof(void*)*27 + 6);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_cfg_2546_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2582_ = v_cfg_2546_;
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_builtinLint_x3f_2579_);
lean_inc(v_restoreAllArtifacts_x3f_2576_);
lean_inc(v_enableArtifactCache_x3f_2575_);
lean_inc(v_readmeFile_2573_);
lean_inc(v_licenseFiles_2572_);
lean_inc(v_license_2571_);
lean_inc(v_homepage_2570_);
lean_inc(v_keywords_2569_);
lean_inc(v_description_2568_);
lean_inc(v_versionTags_2567_);
lean_inc(v_version_2566_);
lean_inc(v_lintDriverArgs_2565_);
lean_inc(v_lintDriver_2564_);
lean_inc(v_testDriverArgs_2563_);
lean_inc(v_testDriver_2562_);
lean_inc(v_buildArchive_2560_);
lean_inc(v_releaseRepo_2559_);
lean_inc(v_irDir_2558_);
lean_inc(v_binDir_2557_);
lean_inc(v_nativeLibDir_2556_);
lean_inc(v_leanLibDir_2555_);
lean_inc(v_buildDir_2554_);
lean_inc(v_srcDir_2553_);
lean_inc(v_moreGlobalServerArgs_2552_);
lean_inc(v_extraDepTargets_2550_);
lean_inc(v_toLeanConfig_2548_);
lean_inc(v_toWorkspaceConfig_2547_);
lean_dec(v_cfg_2546_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_apply_1(v_f_2545_, v_homepage_2570_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 20, v___x_2584_);
v___x_2586_ = v___x_2582_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_toWorkspaceConfig_2547_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_toLeanConfig_2548_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_extraDepTargets_2550_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_moreGlobalServerArgs_2552_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_srcDir_2553_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v_buildDir_2554_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_leanLibDir_2555_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_nativeLibDir_2556_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_binDir_2557_);
lean_ctor_set(v_reuseFailAlloc_2587_, 9, v_irDir_2558_);
lean_ctor_set(v_reuseFailAlloc_2587_, 10, v_releaseRepo_2559_);
lean_ctor_set(v_reuseFailAlloc_2587_, 11, v_buildArchive_2560_);
lean_ctor_set(v_reuseFailAlloc_2587_, 12, v_testDriver_2562_);
lean_ctor_set(v_reuseFailAlloc_2587_, 13, v_testDriverArgs_2563_);
lean_ctor_set(v_reuseFailAlloc_2587_, 14, v_lintDriver_2564_);
lean_ctor_set(v_reuseFailAlloc_2587_, 15, v_lintDriverArgs_2565_);
lean_ctor_set(v_reuseFailAlloc_2587_, 16, v_version_2566_);
lean_ctor_set(v_reuseFailAlloc_2587_, 17, v_versionTags_2567_);
lean_ctor_set(v_reuseFailAlloc_2587_, 18, v_description_2568_);
lean_ctor_set(v_reuseFailAlloc_2587_, 19, v_keywords_2569_);
lean_ctor_set(v_reuseFailAlloc_2587_, 20, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2587_, 21, v_license_2571_);
lean_ctor_set(v_reuseFailAlloc_2587_, 22, v_licenseFiles_2572_);
lean_ctor_set(v_reuseFailAlloc_2587_, 23, v_readmeFile_2573_);
lean_ctor_set(v_reuseFailAlloc_2587_, 24, v_enableArtifactCache_x3f_2575_);
lean_ctor_set(v_reuseFailAlloc_2587_, 25, v_restoreAllArtifacts_x3f_2576_);
lean_ctor_set(v_reuseFailAlloc_2587_, 26, v_builtinLint_x3f_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27, v_bootstrap_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27 + 1, v_precompileModules_2551_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27 + 3, v_reservoir_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27 + 5, v_allowImportAll_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*27 + 6, v_fixedToolchain_2580_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2597_, lean_object* v_n_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2600_, lean_object* v_n_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lake_PackageConfig_homepage___proj(v_p_2600_, v_n_2601_);
lean_dec(v_n_2601_);
lean_dec(v_p_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2603_, lean_object* v_n_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lake_PackageConfig_homepage___proj(v_p_2603_, v_n_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2606_, lean_object* v_n_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2606_, v_n_2607_);
lean_dec(v_n_2607_);
lean_dec(v_p_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* v_cfg_2609_){
_start:
{
lean_object* v_license_2610_; 
v_license_2610_ = lean_ctor_get(v_cfg_2609_, 21);
lean_inc_ref(v_license_2610_);
return v_license_2610_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* v_cfg_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lake_PackageConfig_license___proj___lam__0(v_cfg_2611_);
lean_dec_ref(v_cfg_2611_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* v_val_2613_, lean_object* v_cfg_2614_){
_start:
{
lean_object* v_toWorkspaceConfig_2615_; lean_object* v_toLeanConfig_2616_; uint8_t v_bootstrap_2617_; lean_object* v_extraDepTargets_2618_; uint8_t v_precompileModules_2619_; lean_object* v_moreGlobalServerArgs_2620_; lean_object* v_srcDir_2621_; lean_object* v_buildDir_2622_; lean_object* v_leanLibDir_2623_; lean_object* v_nativeLibDir_2624_; lean_object* v_binDir_2625_; lean_object* v_irDir_2626_; lean_object* v_releaseRepo_2627_; lean_object* v_buildArchive_2628_; uint8_t v_preferReleaseBuild_2629_; lean_object* v_testDriver_2630_; lean_object* v_testDriverArgs_2631_; lean_object* v_lintDriver_2632_; lean_object* v_lintDriverArgs_2633_; lean_object* v_version_2634_; lean_object* v_versionTags_2635_; lean_object* v_description_2636_; lean_object* v_keywords_2637_; lean_object* v_homepage_2638_; lean_object* v_licenseFiles_2639_; lean_object* v_readmeFile_2640_; uint8_t v_reservoir_2641_; lean_object* v_enableArtifactCache_x3f_2642_; lean_object* v_restoreAllArtifacts_x3f_2643_; uint8_t v_libPrefixOnWindows_2644_; uint8_t v_allowImportAll_2645_; lean_object* v_builtinLint_x3f_2646_; uint8_t v_fixedToolchain_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
v_toWorkspaceConfig_2615_ = lean_ctor_get(v_cfg_2614_, 0);
v_toLeanConfig_2616_ = lean_ctor_get(v_cfg_2614_, 1);
v_bootstrap_2617_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27);
v_extraDepTargets_2618_ = lean_ctor_get(v_cfg_2614_, 2);
v_precompileModules_2619_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2620_ = lean_ctor_get(v_cfg_2614_, 3);
v_srcDir_2621_ = lean_ctor_get(v_cfg_2614_, 4);
v_buildDir_2622_ = lean_ctor_get(v_cfg_2614_, 5);
v_leanLibDir_2623_ = lean_ctor_get(v_cfg_2614_, 6);
v_nativeLibDir_2624_ = lean_ctor_get(v_cfg_2614_, 7);
v_binDir_2625_ = lean_ctor_get(v_cfg_2614_, 8);
v_irDir_2626_ = lean_ctor_get(v_cfg_2614_, 9);
v_releaseRepo_2627_ = lean_ctor_get(v_cfg_2614_, 10);
v_buildArchive_2628_ = lean_ctor_get(v_cfg_2614_, 11);
v_preferReleaseBuild_2629_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27 + 2);
v_testDriver_2630_ = lean_ctor_get(v_cfg_2614_, 12);
v_testDriverArgs_2631_ = lean_ctor_get(v_cfg_2614_, 13);
v_lintDriver_2632_ = lean_ctor_get(v_cfg_2614_, 14);
v_lintDriverArgs_2633_ = lean_ctor_get(v_cfg_2614_, 15);
v_version_2634_ = lean_ctor_get(v_cfg_2614_, 16);
v_versionTags_2635_ = lean_ctor_get(v_cfg_2614_, 17);
v_description_2636_ = lean_ctor_get(v_cfg_2614_, 18);
v_keywords_2637_ = lean_ctor_get(v_cfg_2614_, 19);
v_homepage_2638_ = lean_ctor_get(v_cfg_2614_, 20);
v_licenseFiles_2639_ = lean_ctor_get(v_cfg_2614_, 22);
v_readmeFile_2640_ = lean_ctor_get(v_cfg_2614_, 23);
v_reservoir_2641_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2642_ = lean_ctor_get(v_cfg_2614_, 24);
v_restoreAllArtifacts_x3f_2643_ = lean_ctor_get(v_cfg_2614_, 25);
v_libPrefixOnWindows_2644_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27 + 4);
v_allowImportAll_2645_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2646_ = lean_ctor_get(v_cfg_2614_, 26);
v_fixedToolchain_2647_ = lean_ctor_get_uint8(v_cfg_2614_, sizeof(void*)*27 + 6);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_cfg_2614_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_cfg_2614_, 21);
lean_dec(v_unused_2655_);
v___x_2649_ = v_cfg_2614_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_builtinLint_x3f_2646_);
lean_inc(v_restoreAllArtifacts_x3f_2643_);
lean_inc(v_enableArtifactCache_x3f_2642_);
lean_inc(v_readmeFile_2640_);
lean_inc(v_licenseFiles_2639_);
lean_inc(v_homepage_2638_);
lean_inc(v_keywords_2637_);
lean_inc(v_description_2636_);
lean_inc(v_versionTags_2635_);
lean_inc(v_version_2634_);
lean_inc(v_lintDriverArgs_2633_);
lean_inc(v_lintDriver_2632_);
lean_inc(v_testDriverArgs_2631_);
lean_inc(v_testDriver_2630_);
lean_inc(v_buildArchive_2628_);
lean_inc(v_releaseRepo_2627_);
lean_inc(v_irDir_2626_);
lean_inc(v_binDir_2625_);
lean_inc(v_nativeLibDir_2624_);
lean_inc(v_leanLibDir_2623_);
lean_inc(v_buildDir_2622_);
lean_inc(v_srcDir_2621_);
lean_inc(v_moreGlobalServerArgs_2620_);
lean_inc(v_extraDepTargets_2618_);
lean_inc(v_toLeanConfig_2616_);
lean_inc(v_toWorkspaceConfig_2615_);
lean_dec(v_cfg_2614_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 21, v_val_2613_);
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_toWorkspaceConfig_2615_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_toLeanConfig_2616_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_extraDepTargets_2618_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_moreGlobalServerArgs_2620_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_srcDir_2621_);
lean_ctor_set(v_reuseFailAlloc_2653_, 5, v_buildDir_2622_);
lean_ctor_set(v_reuseFailAlloc_2653_, 6, v_leanLibDir_2623_);
lean_ctor_set(v_reuseFailAlloc_2653_, 7, v_nativeLibDir_2624_);
lean_ctor_set(v_reuseFailAlloc_2653_, 8, v_binDir_2625_);
lean_ctor_set(v_reuseFailAlloc_2653_, 9, v_irDir_2626_);
lean_ctor_set(v_reuseFailAlloc_2653_, 10, v_releaseRepo_2627_);
lean_ctor_set(v_reuseFailAlloc_2653_, 11, v_buildArchive_2628_);
lean_ctor_set(v_reuseFailAlloc_2653_, 12, v_testDriver_2630_);
lean_ctor_set(v_reuseFailAlloc_2653_, 13, v_testDriverArgs_2631_);
lean_ctor_set(v_reuseFailAlloc_2653_, 14, v_lintDriver_2632_);
lean_ctor_set(v_reuseFailAlloc_2653_, 15, v_lintDriverArgs_2633_);
lean_ctor_set(v_reuseFailAlloc_2653_, 16, v_version_2634_);
lean_ctor_set(v_reuseFailAlloc_2653_, 17, v_versionTags_2635_);
lean_ctor_set(v_reuseFailAlloc_2653_, 18, v_description_2636_);
lean_ctor_set(v_reuseFailAlloc_2653_, 19, v_keywords_2637_);
lean_ctor_set(v_reuseFailAlloc_2653_, 20, v_homepage_2638_);
lean_ctor_set(v_reuseFailAlloc_2653_, 21, v_val_2613_);
lean_ctor_set(v_reuseFailAlloc_2653_, 22, v_licenseFiles_2639_);
lean_ctor_set(v_reuseFailAlloc_2653_, 23, v_readmeFile_2640_);
lean_ctor_set(v_reuseFailAlloc_2653_, 24, v_enableArtifactCache_x3f_2642_);
lean_ctor_set(v_reuseFailAlloc_2653_, 25, v_restoreAllArtifacts_x3f_2643_);
lean_ctor_set(v_reuseFailAlloc_2653_, 26, v_builtinLint_x3f_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27, v_bootstrap_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27 + 1, v_precompileModules_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27 + 3, v_reservoir_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27 + 5, v_allowImportAll_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*27 + 6, v_fixedToolchain_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* v_f_2656_, lean_object* v_cfg_2657_){
_start:
{
lean_object* v_toWorkspaceConfig_2658_; lean_object* v_toLeanConfig_2659_; uint8_t v_bootstrap_2660_; lean_object* v_extraDepTargets_2661_; uint8_t v_precompileModules_2662_; lean_object* v_moreGlobalServerArgs_2663_; lean_object* v_srcDir_2664_; lean_object* v_buildDir_2665_; lean_object* v_leanLibDir_2666_; lean_object* v_nativeLibDir_2667_; lean_object* v_binDir_2668_; lean_object* v_irDir_2669_; lean_object* v_releaseRepo_2670_; lean_object* v_buildArchive_2671_; uint8_t v_preferReleaseBuild_2672_; lean_object* v_testDriver_2673_; lean_object* v_testDriverArgs_2674_; lean_object* v_lintDriver_2675_; lean_object* v_lintDriverArgs_2676_; lean_object* v_version_2677_; lean_object* v_versionTags_2678_; lean_object* v_description_2679_; lean_object* v_keywords_2680_; lean_object* v_homepage_2681_; lean_object* v_license_2682_; lean_object* v_licenseFiles_2683_; lean_object* v_readmeFile_2684_; uint8_t v_reservoir_2685_; lean_object* v_enableArtifactCache_x3f_2686_; lean_object* v_restoreAllArtifacts_x3f_2687_; uint8_t v_libPrefixOnWindows_2688_; uint8_t v_allowImportAll_2689_; lean_object* v_builtinLint_x3f_2690_; uint8_t v_fixedToolchain_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2699_; 
v_toWorkspaceConfig_2658_ = lean_ctor_get(v_cfg_2657_, 0);
v_toLeanConfig_2659_ = lean_ctor_get(v_cfg_2657_, 1);
v_bootstrap_2660_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27);
v_extraDepTargets_2661_ = lean_ctor_get(v_cfg_2657_, 2);
v_precompileModules_2662_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2663_ = lean_ctor_get(v_cfg_2657_, 3);
v_srcDir_2664_ = lean_ctor_get(v_cfg_2657_, 4);
v_buildDir_2665_ = lean_ctor_get(v_cfg_2657_, 5);
v_leanLibDir_2666_ = lean_ctor_get(v_cfg_2657_, 6);
v_nativeLibDir_2667_ = lean_ctor_get(v_cfg_2657_, 7);
v_binDir_2668_ = lean_ctor_get(v_cfg_2657_, 8);
v_irDir_2669_ = lean_ctor_get(v_cfg_2657_, 9);
v_releaseRepo_2670_ = lean_ctor_get(v_cfg_2657_, 10);
v_buildArchive_2671_ = lean_ctor_get(v_cfg_2657_, 11);
v_preferReleaseBuild_2672_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27 + 2);
v_testDriver_2673_ = lean_ctor_get(v_cfg_2657_, 12);
v_testDriverArgs_2674_ = lean_ctor_get(v_cfg_2657_, 13);
v_lintDriver_2675_ = lean_ctor_get(v_cfg_2657_, 14);
v_lintDriverArgs_2676_ = lean_ctor_get(v_cfg_2657_, 15);
v_version_2677_ = lean_ctor_get(v_cfg_2657_, 16);
v_versionTags_2678_ = lean_ctor_get(v_cfg_2657_, 17);
v_description_2679_ = lean_ctor_get(v_cfg_2657_, 18);
v_keywords_2680_ = lean_ctor_get(v_cfg_2657_, 19);
v_homepage_2681_ = lean_ctor_get(v_cfg_2657_, 20);
v_license_2682_ = lean_ctor_get(v_cfg_2657_, 21);
v_licenseFiles_2683_ = lean_ctor_get(v_cfg_2657_, 22);
v_readmeFile_2684_ = lean_ctor_get(v_cfg_2657_, 23);
v_reservoir_2685_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2686_ = lean_ctor_get(v_cfg_2657_, 24);
v_restoreAllArtifacts_x3f_2687_ = lean_ctor_get(v_cfg_2657_, 25);
v_libPrefixOnWindows_2688_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27 + 4);
v_allowImportAll_2689_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2690_ = lean_ctor_get(v_cfg_2657_, 26);
v_fixedToolchain_2691_ = lean_ctor_get_uint8(v_cfg_2657_, sizeof(void*)*27 + 6);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_cfg_2657_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2693_ = v_cfg_2657_;
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_builtinLint_x3f_2690_);
lean_inc(v_restoreAllArtifacts_x3f_2687_);
lean_inc(v_enableArtifactCache_x3f_2686_);
lean_inc(v_readmeFile_2684_);
lean_inc(v_licenseFiles_2683_);
lean_inc(v_license_2682_);
lean_inc(v_homepage_2681_);
lean_inc(v_keywords_2680_);
lean_inc(v_description_2679_);
lean_inc(v_versionTags_2678_);
lean_inc(v_version_2677_);
lean_inc(v_lintDriverArgs_2676_);
lean_inc(v_lintDriver_2675_);
lean_inc(v_testDriverArgs_2674_);
lean_inc(v_testDriver_2673_);
lean_inc(v_buildArchive_2671_);
lean_inc(v_releaseRepo_2670_);
lean_inc(v_irDir_2669_);
lean_inc(v_binDir_2668_);
lean_inc(v_nativeLibDir_2667_);
lean_inc(v_leanLibDir_2666_);
lean_inc(v_buildDir_2665_);
lean_inc(v_srcDir_2664_);
lean_inc(v_moreGlobalServerArgs_2663_);
lean_inc(v_extraDepTargets_2661_);
lean_inc(v_toLeanConfig_2659_);
lean_inc(v_toWorkspaceConfig_2658_);
lean_dec(v_cfg_2657_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = lean_apply_1(v_f_2656_, v_license_2682_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 21, v___x_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_toWorkspaceConfig_2658_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_toLeanConfig_2659_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_extraDepTargets_2661_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_moreGlobalServerArgs_2663_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_srcDir_2664_);
lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_buildDir_2665_);
lean_ctor_set(v_reuseFailAlloc_2698_, 6, v_leanLibDir_2666_);
lean_ctor_set(v_reuseFailAlloc_2698_, 7, v_nativeLibDir_2667_);
lean_ctor_set(v_reuseFailAlloc_2698_, 8, v_binDir_2668_);
lean_ctor_set(v_reuseFailAlloc_2698_, 9, v_irDir_2669_);
lean_ctor_set(v_reuseFailAlloc_2698_, 10, v_releaseRepo_2670_);
lean_ctor_set(v_reuseFailAlloc_2698_, 11, v_buildArchive_2671_);
lean_ctor_set(v_reuseFailAlloc_2698_, 12, v_testDriver_2673_);
lean_ctor_set(v_reuseFailAlloc_2698_, 13, v_testDriverArgs_2674_);
lean_ctor_set(v_reuseFailAlloc_2698_, 14, v_lintDriver_2675_);
lean_ctor_set(v_reuseFailAlloc_2698_, 15, v_lintDriverArgs_2676_);
lean_ctor_set(v_reuseFailAlloc_2698_, 16, v_version_2677_);
lean_ctor_set(v_reuseFailAlloc_2698_, 17, v_versionTags_2678_);
lean_ctor_set(v_reuseFailAlloc_2698_, 18, v_description_2679_);
lean_ctor_set(v_reuseFailAlloc_2698_, 19, v_keywords_2680_);
lean_ctor_set(v_reuseFailAlloc_2698_, 20, v_homepage_2681_);
lean_ctor_set(v_reuseFailAlloc_2698_, 21, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2698_, 22, v_licenseFiles_2683_);
lean_ctor_set(v_reuseFailAlloc_2698_, 23, v_readmeFile_2684_);
lean_ctor_set(v_reuseFailAlloc_2698_, 24, v_enableArtifactCache_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2698_, 25, v_restoreAllArtifacts_x3f_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 26, v_builtinLint_x3f_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27, v_bootstrap_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27 + 1, v_precompileModules_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2672_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27 + 3, v_reservoir_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27 + 5, v_allowImportAll_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*27 + 6, v_fixedToolchain_2691_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2708_, lean_object* v_n_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2711_, lean_object* v_n_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lake_PackageConfig_license___proj(v_p_2711_, v_n_2712_);
lean_dec(v_n_2712_);
lean_dec(v_p_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2714_, lean_object* v_n_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lake_PackageConfig_license___proj(v_p_2714_, v_n_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2717_, lean_object* v_n_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lake_PackageConfig_license_instConfigField(v_p_2717_, v_n_2718_);
lean_dec(v_n_2718_);
lean_dec(v_p_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* v_cfg_2720_){
_start:
{
lean_object* v_licenseFiles_2721_; 
v_licenseFiles_2721_ = lean_ctor_get(v_cfg_2720_, 22);
lean_inc_ref(v_licenseFiles_2721_);
return v_licenseFiles_2721_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* v_cfg_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lake_PackageConfig_licenseFiles___proj___lam__0(v_cfg_2722_);
lean_dec_ref(v_cfg_2722_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* v_val_2724_, lean_object* v_cfg_2725_){
_start:
{
lean_object* v_toWorkspaceConfig_2726_; lean_object* v_toLeanConfig_2727_; uint8_t v_bootstrap_2728_; lean_object* v_extraDepTargets_2729_; uint8_t v_precompileModules_2730_; lean_object* v_moreGlobalServerArgs_2731_; lean_object* v_srcDir_2732_; lean_object* v_buildDir_2733_; lean_object* v_leanLibDir_2734_; lean_object* v_nativeLibDir_2735_; lean_object* v_binDir_2736_; lean_object* v_irDir_2737_; lean_object* v_releaseRepo_2738_; lean_object* v_buildArchive_2739_; uint8_t v_preferReleaseBuild_2740_; lean_object* v_testDriver_2741_; lean_object* v_testDriverArgs_2742_; lean_object* v_lintDriver_2743_; lean_object* v_lintDriverArgs_2744_; lean_object* v_version_2745_; lean_object* v_versionTags_2746_; lean_object* v_description_2747_; lean_object* v_keywords_2748_; lean_object* v_homepage_2749_; lean_object* v_license_2750_; lean_object* v_readmeFile_2751_; uint8_t v_reservoir_2752_; lean_object* v_enableArtifactCache_x3f_2753_; lean_object* v_restoreAllArtifacts_x3f_2754_; uint8_t v_libPrefixOnWindows_2755_; uint8_t v_allowImportAll_2756_; lean_object* v_builtinLint_x3f_2757_; uint8_t v_fixedToolchain_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
v_toWorkspaceConfig_2726_ = lean_ctor_get(v_cfg_2725_, 0);
v_toLeanConfig_2727_ = lean_ctor_get(v_cfg_2725_, 1);
v_bootstrap_2728_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27);
v_extraDepTargets_2729_ = lean_ctor_get(v_cfg_2725_, 2);
v_precompileModules_2730_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2731_ = lean_ctor_get(v_cfg_2725_, 3);
v_srcDir_2732_ = lean_ctor_get(v_cfg_2725_, 4);
v_buildDir_2733_ = lean_ctor_get(v_cfg_2725_, 5);
v_leanLibDir_2734_ = lean_ctor_get(v_cfg_2725_, 6);
v_nativeLibDir_2735_ = lean_ctor_get(v_cfg_2725_, 7);
v_binDir_2736_ = lean_ctor_get(v_cfg_2725_, 8);
v_irDir_2737_ = lean_ctor_get(v_cfg_2725_, 9);
v_releaseRepo_2738_ = lean_ctor_get(v_cfg_2725_, 10);
v_buildArchive_2739_ = lean_ctor_get(v_cfg_2725_, 11);
v_preferReleaseBuild_2740_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27 + 2);
v_testDriver_2741_ = lean_ctor_get(v_cfg_2725_, 12);
v_testDriverArgs_2742_ = lean_ctor_get(v_cfg_2725_, 13);
v_lintDriver_2743_ = lean_ctor_get(v_cfg_2725_, 14);
v_lintDriverArgs_2744_ = lean_ctor_get(v_cfg_2725_, 15);
v_version_2745_ = lean_ctor_get(v_cfg_2725_, 16);
v_versionTags_2746_ = lean_ctor_get(v_cfg_2725_, 17);
v_description_2747_ = lean_ctor_get(v_cfg_2725_, 18);
v_keywords_2748_ = lean_ctor_get(v_cfg_2725_, 19);
v_homepage_2749_ = lean_ctor_get(v_cfg_2725_, 20);
v_license_2750_ = lean_ctor_get(v_cfg_2725_, 21);
v_readmeFile_2751_ = lean_ctor_get(v_cfg_2725_, 23);
v_reservoir_2752_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2753_ = lean_ctor_get(v_cfg_2725_, 24);
v_restoreAllArtifacts_x3f_2754_ = lean_ctor_get(v_cfg_2725_, 25);
v_libPrefixOnWindows_2755_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27 + 4);
v_allowImportAll_2756_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2757_ = lean_ctor_get(v_cfg_2725_, 26);
v_fixedToolchain_2758_ = lean_ctor_get_uint8(v_cfg_2725_, sizeof(void*)*27 + 6);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_cfg_2725_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v_cfg_2725_, 22);
lean_dec(v_unused_2766_);
v___x_2760_ = v_cfg_2725_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_builtinLint_x3f_2757_);
lean_inc(v_restoreAllArtifacts_x3f_2754_);
lean_inc(v_enableArtifactCache_x3f_2753_);
lean_inc(v_readmeFile_2751_);
lean_inc(v_license_2750_);
lean_inc(v_homepage_2749_);
lean_inc(v_keywords_2748_);
lean_inc(v_description_2747_);
lean_inc(v_versionTags_2746_);
lean_inc(v_version_2745_);
lean_inc(v_lintDriverArgs_2744_);
lean_inc(v_lintDriver_2743_);
lean_inc(v_testDriverArgs_2742_);
lean_inc(v_testDriver_2741_);
lean_inc(v_buildArchive_2739_);
lean_inc(v_releaseRepo_2738_);
lean_inc(v_irDir_2737_);
lean_inc(v_binDir_2736_);
lean_inc(v_nativeLibDir_2735_);
lean_inc(v_leanLibDir_2734_);
lean_inc(v_buildDir_2733_);
lean_inc(v_srcDir_2732_);
lean_inc(v_moreGlobalServerArgs_2731_);
lean_inc(v_extraDepTargets_2729_);
lean_inc(v_toLeanConfig_2727_);
lean_inc(v_toWorkspaceConfig_2726_);
lean_dec(v_cfg_2725_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 22, v_val_2724_);
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_toWorkspaceConfig_2726_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_toLeanConfig_2727_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_extraDepTargets_2729_);
lean_ctor_set(v_reuseFailAlloc_2764_, 3, v_moreGlobalServerArgs_2731_);
lean_ctor_set(v_reuseFailAlloc_2764_, 4, v_srcDir_2732_);
lean_ctor_set(v_reuseFailAlloc_2764_, 5, v_buildDir_2733_);
lean_ctor_set(v_reuseFailAlloc_2764_, 6, v_leanLibDir_2734_);
lean_ctor_set(v_reuseFailAlloc_2764_, 7, v_nativeLibDir_2735_);
lean_ctor_set(v_reuseFailAlloc_2764_, 8, v_binDir_2736_);
lean_ctor_set(v_reuseFailAlloc_2764_, 9, v_irDir_2737_);
lean_ctor_set(v_reuseFailAlloc_2764_, 10, v_releaseRepo_2738_);
lean_ctor_set(v_reuseFailAlloc_2764_, 11, v_buildArchive_2739_);
lean_ctor_set(v_reuseFailAlloc_2764_, 12, v_testDriver_2741_);
lean_ctor_set(v_reuseFailAlloc_2764_, 13, v_testDriverArgs_2742_);
lean_ctor_set(v_reuseFailAlloc_2764_, 14, v_lintDriver_2743_);
lean_ctor_set(v_reuseFailAlloc_2764_, 15, v_lintDriverArgs_2744_);
lean_ctor_set(v_reuseFailAlloc_2764_, 16, v_version_2745_);
lean_ctor_set(v_reuseFailAlloc_2764_, 17, v_versionTags_2746_);
lean_ctor_set(v_reuseFailAlloc_2764_, 18, v_description_2747_);
lean_ctor_set(v_reuseFailAlloc_2764_, 19, v_keywords_2748_);
lean_ctor_set(v_reuseFailAlloc_2764_, 20, v_homepage_2749_);
lean_ctor_set(v_reuseFailAlloc_2764_, 21, v_license_2750_);
lean_ctor_set(v_reuseFailAlloc_2764_, 22, v_val_2724_);
lean_ctor_set(v_reuseFailAlloc_2764_, 23, v_readmeFile_2751_);
lean_ctor_set(v_reuseFailAlloc_2764_, 24, v_enableArtifactCache_x3f_2753_);
lean_ctor_set(v_reuseFailAlloc_2764_, 25, v_restoreAllArtifacts_x3f_2754_);
lean_ctor_set(v_reuseFailAlloc_2764_, 26, v_builtinLint_x3f_2757_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27, v_bootstrap_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27 + 1, v_precompileModules_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2740_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27 + 3, v_reservoir_2752_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2755_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27 + 5, v_allowImportAll_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, sizeof(void*)*27 + 6, v_fixedToolchain_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* v_f_2767_, lean_object* v_cfg_2768_){
_start:
{
lean_object* v_toWorkspaceConfig_2769_; lean_object* v_toLeanConfig_2770_; uint8_t v_bootstrap_2771_; lean_object* v_extraDepTargets_2772_; uint8_t v_precompileModules_2773_; lean_object* v_moreGlobalServerArgs_2774_; lean_object* v_srcDir_2775_; lean_object* v_buildDir_2776_; lean_object* v_leanLibDir_2777_; lean_object* v_nativeLibDir_2778_; lean_object* v_binDir_2779_; lean_object* v_irDir_2780_; lean_object* v_releaseRepo_2781_; lean_object* v_buildArchive_2782_; uint8_t v_preferReleaseBuild_2783_; lean_object* v_testDriver_2784_; lean_object* v_testDriverArgs_2785_; lean_object* v_lintDriver_2786_; lean_object* v_lintDriverArgs_2787_; lean_object* v_version_2788_; lean_object* v_versionTags_2789_; lean_object* v_description_2790_; lean_object* v_keywords_2791_; lean_object* v_homepage_2792_; lean_object* v_license_2793_; lean_object* v_licenseFiles_2794_; lean_object* v_readmeFile_2795_; uint8_t v_reservoir_2796_; lean_object* v_enableArtifactCache_x3f_2797_; lean_object* v_restoreAllArtifacts_x3f_2798_; uint8_t v_libPrefixOnWindows_2799_; uint8_t v_allowImportAll_2800_; lean_object* v_builtinLint_x3f_2801_; uint8_t v_fixedToolchain_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2810_; 
v_toWorkspaceConfig_2769_ = lean_ctor_get(v_cfg_2768_, 0);
v_toLeanConfig_2770_ = lean_ctor_get(v_cfg_2768_, 1);
v_bootstrap_2771_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27);
v_extraDepTargets_2772_ = lean_ctor_get(v_cfg_2768_, 2);
v_precompileModules_2773_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2774_ = lean_ctor_get(v_cfg_2768_, 3);
v_srcDir_2775_ = lean_ctor_get(v_cfg_2768_, 4);
v_buildDir_2776_ = lean_ctor_get(v_cfg_2768_, 5);
v_leanLibDir_2777_ = lean_ctor_get(v_cfg_2768_, 6);
v_nativeLibDir_2778_ = lean_ctor_get(v_cfg_2768_, 7);
v_binDir_2779_ = lean_ctor_get(v_cfg_2768_, 8);
v_irDir_2780_ = lean_ctor_get(v_cfg_2768_, 9);
v_releaseRepo_2781_ = lean_ctor_get(v_cfg_2768_, 10);
v_buildArchive_2782_ = lean_ctor_get(v_cfg_2768_, 11);
v_preferReleaseBuild_2783_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27 + 2);
v_testDriver_2784_ = lean_ctor_get(v_cfg_2768_, 12);
v_testDriverArgs_2785_ = lean_ctor_get(v_cfg_2768_, 13);
v_lintDriver_2786_ = lean_ctor_get(v_cfg_2768_, 14);
v_lintDriverArgs_2787_ = lean_ctor_get(v_cfg_2768_, 15);
v_version_2788_ = lean_ctor_get(v_cfg_2768_, 16);
v_versionTags_2789_ = lean_ctor_get(v_cfg_2768_, 17);
v_description_2790_ = lean_ctor_get(v_cfg_2768_, 18);
v_keywords_2791_ = lean_ctor_get(v_cfg_2768_, 19);
v_homepage_2792_ = lean_ctor_get(v_cfg_2768_, 20);
v_license_2793_ = lean_ctor_get(v_cfg_2768_, 21);
v_licenseFiles_2794_ = lean_ctor_get(v_cfg_2768_, 22);
v_readmeFile_2795_ = lean_ctor_get(v_cfg_2768_, 23);
v_reservoir_2796_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2797_ = lean_ctor_get(v_cfg_2768_, 24);
v_restoreAllArtifacts_x3f_2798_ = lean_ctor_get(v_cfg_2768_, 25);
v_libPrefixOnWindows_2799_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27 + 4);
v_allowImportAll_2800_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2801_ = lean_ctor_get(v_cfg_2768_, 26);
v_fixedToolchain_2802_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*27 + 6);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_cfg_2768_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2804_ = v_cfg_2768_;
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_builtinLint_x3f_2801_);
lean_inc(v_restoreAllArtifacts_x3f_2798_);
lean_inc(v_enableArtifactCache_x3f_2797_);
lean_inc(v_readmeFile_2795_);
lean_inc(v_licenseFiles_2794_);
lean_inc(v_license_2793_);
lean_inc(v_homepage_2792_);
lean_inc(v_keywords_2791_);
lean_inc(v_description_2790_);
lean_inc(v_versionTags_2789_);
lean_inc(v_version_2788_);
lean_inc(v_lintDriverArgs_2787_);
lean_inc(v_lintDriver_2786_);
lean_inc(v_testDriverArgs_2785_);
lean_inc(v_testDriver_2784_);
lean_inc(v_buildArchive_2782_);
lean_inc(v_releaseRepo_2781_);
lean_inc(v_irDir_2780_);
lean_inc(v_binDir_2779_);
lean_inc(v_nativeLibDir_2778_);
lean_inc(v_leanLibDir_2777_);
lean_inc(v_buildDir_2776_);
lean_inc(v_srcDir_2775_);
lean_inc(v_moreGlobalServerArgs_2774_);
lean_inc(v_extraDepTargets_2772_);
lean_inc(v_toLeanConfig_2770_);
lean_inc(v_toWorkspaceConfig_2769_);
lean_dec(v_cfg_2768_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2806_ = lean_apply_1(v_f_2767_, v_licenseFiles_2794_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 22, v___x_2806_);
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_toWorkspaceConfig_2769_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_toLeanConfig_2770_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_extraDepTargets_2772_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_moreGlobalServerArgs_2774_);
lean_ctor_set(v_reuseFailAlloc_2809_, 4, v_srcDir_2775_);
lean_ctor_set(v_reuseFailAlloc_2809_, 5, v_buildDir_2776_);
lean_ctor_set(v_reuseFailAlloc_2809_, 6, v_leanLibDir_2777_);
lean_ctor_set(v_reuseFailAlloc_2809_, 7, v_nativeLibDir_2778_);
lean_ctor_set(v_reuseFailAlloc_2809_, 8, v_binDir_2779_);
lean_ctor_set(v_reuseFailAlloc_2809_, 9, v_irDir_2780_);
lean_ctor_set(v_reuseFailAlloc_2809_, 10, v_releaseRepo_2781_);
lean_ctor_set(v_reuseFailAlloc_2809_, 11, v_buildArchive_2782_);
lean_ctor_set(v_reuseFailAlloc_2809_, 12, v_testDriver_2784_);
lean_ctor_set(v_reuseFailAlloc_2809_, 13, v_testDriverArgs_2785_);
lean_ctor_set(v_reuseFailAlloc_2809_, 14, v_lintDriver_2786_);
lean_ctor_set(v_reuseFailAlloc_2809_, 15, v_lintDriverArgs_2787_);
lean_ctor_set(v_reuseFailAlloc_2809_, 16, v_version_2788_);
lean_ctor_set(v_reuseFailAlloc_2809_, 17, v_versionTags_2789_);
lean_ctor_set(v_reuseFailAlloc_2809_, 18, v_description_2790_);
lean_ctor_set(v_reuseFailAlloc_2809_, 19, v_keywords_2791_);
lean_ctor_set(v_reuseFailAlloc_2809_, 20, v_homepage_2792_);
lean_ctor_set(v_reuseFailAlloc_2809_, 21, v_license_2793_);
lean_ctor_set(v_reuseFailAlloc_2809_, 22, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2809_, 23, v_readmeFile_2795_);
lean_ctor_set(v_reuseFailAlloc_2809_, 24, v_enableArtifactCache_x3f_2797_);
lean_ctor_set(v_reuseFailAlloc_2809_, 25, v_restoreAllArtifacts_x3f_2798_);
lean_ctor_set(v_reuseFailAlloc_2809_, 26, v_builtinLint_x3f_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27, v_bootstrap_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27 + 1, v_precompileModules_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2783_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27 + 3, v_reservoir_2796_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27 + 5, v_allowImportAll_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2809_, sizeof(void*)*27 + 6, v_fixedToolchain_2802_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* v_x_2811_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_unsigned_to_nat(1u);
v___x_2813_ = lean_mk_empty_array_with_capacity(v___x_2812_);
lean_dec_ref(v___x_2813_);
v___x_2814_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* v_x_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lake_PackageConfig_licenseFiles___proj___lam__3(v_x_2815_);
lean_dec_ref(v_x_2815_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_2826_, lean_object* v_n_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_2829_, lean_object* v_n_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2829_, v_n_2830_);
lean_dec(v_n_2830_);
lean_dec(v_p_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_2832_, lean_object* v_n_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2832_, v_n_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_2835_, lean_object* v_n_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_2835_, v_n_2836_);
lean_dec(v_n_2836_);
lean_dec(v_p_2835_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* v_cfg_2838_){
_start:
{
lean_object* v_readmeFile_2839_; 
v_readmeFile_2839_ = lean_ctor_get(v_cfg_2838_, 23);
lean_inc_ref(v_readmeFile_2839_);
return v_readmeFile_2839_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* v_cfg_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lake_PackageConfig_readmeFile___proj___lam__0(v_cfg_2840_);
lean_dec_ref(v_cfg_2840_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* v_val_2842_, lean_object* v_cfg_2843_){
_start:
{
lean_object* v_toWorkspaceConfig_2844_; lean_object* v_toLeanConfig_2845_; uint8_t v_bootstrap_2846_; lean_object* v_extraDepTargets_2847_; uint8_t v_precompileModules_2848_; lean_object* v_moreGlobalServerArgs_2849_; lean_object* v_srcDir_2850_; lean_object* v_buildDir_2851_; lean_object* v_leanLibDir_2852_; lean_object* v_nativeLibDir_2853_; lean_object* v_binDir_2854_; lean_object* v_irDir_2855_; lean_object* v_releaseRepo_2856_; lean_object* v_buildArchive_2857_; uint8_t v_preferReleaseBuild_2858_; lean_object* v_testDriver_2859_; lean_object* v_testDriverArgs_2860_; lean_object* v_lintDriver_2861_; lean_object* v_lintDriverArgs_2862_; lean_object* v_version_2863_; lean_object* v_versionTags_2864_; lean_object* v_description_2865_; lean_object* v_keywords_2866_; lean_object* v_homepage_2867_; lean_object* v_license_2868_; lean_object* v_licenseFiles_2869_; uint8_t v_reservoir_2870_; lean_object* v_enableArtifactCache_x3f_2871_; lean_object* v_restoreAllArtifacts_x3f_2872_; uint8_t v_libPrefixOnWindows_2873_; uint8_t v_allowImportAll_2874_; lean_object* v_builtinLint_x3f_2875_; uint8_t v_fixedToolchain_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_toWorkspaceConfig_2844_ = lean_ctor_get(v_cfg_2843_, 0);
v_toLeanConfig_2845_ = lean_ctor_get(v_cfg_2843_, 1);
v_bootstrap_2846_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27);
v_extraDepTargets_2847_ = lean_ctor_get(v_cfg_2843_, 2);
v_precompileModules_2848_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2849_ = lean_ctor_get(v_cfg_2843_, 3);
v_srcDir_2850_ = lean_ctor_get(v_cfg_2843_, 4);
v_buildDir_2851_ = lean_ctor_get(v_cfg_2843_, 5);
v_leanLibDir_2852_ = lean_ctor_get(v_cfg_2843_, 6);
v_nativeLibDir_2853_ = lean_ctor_get(v_cfg_2843_, 7);
v_binDir_2854_ = lean_ctor_get(v_cfg_2843_, 8);
v_irDir_2855_ = lean_ctor_get(v_cfg_2843_, 9);
v_releaseRepo_2856_ = lean_ctor_get(v_cfg_2843_, 10);
v_buildArchive_2857_ = lean_ctor_get(v_cfg_2843_, 11);
v_preferReleaseBuild_2858_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27 + 2);
v_testDriver_2859_ = lean_ctor_get(v_cfg_2843_, 12);
v_testDriverArgs_2860_ = lean_ctor_get(v_cfg_2843_, 13);
v_lintDriver_2861_ = lean_ctor_get(v_cfg_2843_, 14);
v_lintDriverArgs_2862_ = lean_ctor_get(v_cfg_2843_, 15);
v_version_2863_ = lean_ctor_get(v_cfg_2843_, 16);
v_versionTags_2864_ = lean_ctor_get(v_cfg_2843_, 17);
v_description_2865_ = lean_ctor_get(v_cfg_2843_, 18);
v_keywords_2866_ = lean_ctor_get(v_cfg_2843_, 19);
v_homepage_2867_ = lean_ctor_get(v_cfg_2843_, 20);
v_license_2868_ = lean_ctor_get(v_cfg_2843_, 21);
v_licenseFiles_2869_ = lean_ctor_get(v_cfg_2843_, 22);
v_reservoir_2870_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2871_ = lean_ctor_get(v_cfg_2843_, 24);
v_restoreAllArtifacts_x3f_2872_ = lean_ctor_get(v_cfg_2843_, 25);
v_libPrefixOnWindows_2873_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27 + 4);
v_allowImportAll_2874_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2875_ = lean_ctor_get(v_cfg_2843_, 26);
v_fixedToolchain_2876_ = lean_ctor_get_uint8(v_cfg_2843_, sizeof(void*)*27 + 6);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_cfg_2843_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v_cfg_2843_, 23);
lean_dec(v_unused_2884_);
v___x_2878_ = v_cfg_2843_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_builtinLint_x3f_2875_);
lean_inc(v_restoreAllArtifacts_x3f_2872_);
lean_inc(v_enableArtifactCache_x3f_2871_);
lean_inc(v_licenseFiles_2869_);
lean_inc(v_license_2868_);
lean_inc(v_homepage_2867_);
lean_inc(v_keywords_2866_);
lean_inc(v_description_2865_);
lean_inc(v_versionTags_2864_);
lean_inc(v_version_2863_);
lean_inc(v_lintDriverArgs_2862_);
lean_inc(v_lintDriver_2861_);
lean_inc(v_testDriverArgs_2860_);
lean_inc(v_testDriver_2859_);
lean_inc(v_buildArchive_2857_);
lean_inc(v_releaseRepo_2856_);
lean_inc(v_irDir_2855_);
lean_inc(v_binDir_2854_);
lean_inc(v_nativeLibDir_2853_);
lean_inc(v_leanLibDir_2852_);
lean_inc(v_buildDir_2851_);
lean_inc(v_srcDir_2850_);
lean_inc(v_moreGlobalServerArgs_2849_);
lean_inc(v_extraDepTargets_2847_);
lean_inc(v_toLeanConfig_2845_);
lean_inc(v_toWorkspaceConfig_2844_);
lean_dec(v_cfg_2843_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 23, v_val_2842_);
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_toWorkspaceConfig_2844_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_toLeanConfig_2845_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_extraDepTargets_2847_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_moreGlobalServerArgs_2849_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_srcDir_2850_);
lean_ctor_set(v_reuseFailAlloc_2882_, 5, v_buildDir_2851_);
lean_ctor_set(v_reuseFailAlloc_2882_, 6, v_leanLibDir_2852_);
lean_ctor_set(v_reuseFailAlloc_2882_, 7, v_nativeLibDir_2853_);
lean_ctor_set(v_reuseFailAlloc_2882_, 8, v_binDir_2854_);
lean_ctor_set(v_reuseFailAlloc_2882_, 9, v_irDir_2855_);
lean_ctor_set(v_reuseFailAlloc_2882_, 10, v_releaseRepo_2856_);
lean_ctor_set(v_reuseFailAlloc_2882_, 11, v_buildArchive_2857_);
lean_ctor_set(v_reuseFailAlloc_2882_, 12, v_testDriver_2859_);
lean_ctor_set(v_reuseFailAlloc_2882_, 13, v_testDriverArgs_2860_);
lean_ctor_set(v_reuseFailAlloc_2882_, 14, v_lintDriver_2861_);
lean_ctor_set(v_reuseFailAlloc_2882_, 15, v_lintDriverArgs_2862_);
lean_ctor_set(v_reuseFailAlloc_2882_, 16, v_version_2863_);
lean_ctor_set(v_reuseFailAlloc_2882_, 17, v_versionTags_2864_);
lean_ctor_set(v_reuseFailAlloc_2882_, 18, v_description_2865_);
lean_ctor_set(v_reuseFailAlloc_2882_, 19, v_keywords_2866_);
lean_ctor_set(v_reuseFailAlloc_2882_, 20, v_homepage_2867_);
lean_ctor_set(v_reuseFailAlloc_2882_, 21, v_license_2868_);
lean_ctor_set(v_reuseFailAlloc_2882_, 22, v_licenseFiles_2869_);
lean_ctor_set(v_reuseFailAlloc_2882_, 23, v_val_2842_);
lean_ctor_set(v_reuseFailAlloc_2882_, 24, v_enableArtifactCache_x3f_2871_);
lean_ctor_set(v_reuseFailAlloc_2882_, 25, v_restoreAllArtifacts_x3f_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 26, v_builtinLint_x3f_2875_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27, v_bootstrap_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27 + 1, v_precompileModules_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27 + 3, v_reservoir_2870_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27 + 5, v_allowImportAll_2874_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*27 + 6, v_fixedToolchain_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* v_f_2885_, lean_object* v_cfg_2886_){
_start:
{
lean_object* v_toWorkspaceConfig_2887_; lean_object* v_toLeanConfig_2888_; uint8_t v_bootstrap_2889_; lean_object* v_extraDepTargets_2890_; uint8_t v_precompileModules_2891_; lean_object* v_moreGlobalServerArgs_2892_; lean_object* v_srcDir_2893_; lean_object* v_buildDir_2894_; lean_object* v_leanLibDir_2895_; lean_object* v_nativeLibDir_2896_; lean_object* v_binDir_2897_; lean_object* v_irDir_2898_; lean_object* v_releaseRepo_2899_; lean_object* v_buildArchive_2900_; uint8_t v_preferReleaseBuild_2901_; lean_object* v_testDriver_2902_; lean_object* v_testDriverArgs_2903_; lean_object* v_lintDriver_2904_; lean_object* v_lintDriverArgs_2905_; lean_object* v_version_2906_; lean_object* v_versionTags_2907_; lean_object* v_description_2908_; lean_object* v_keywords_2909_; lean_object* v_homepage_2910_; lean_object* v_license_2911_; lean_object* v_licenseFiles_2912_; lean_object* v_readmeFile_2913_; uint8_t v_reservoir_2914_; lean_object* v_enableArtifactCache_x3f_2915_; lean_object* v_restoreAllArtifacts_x3f_2916_; uint8_t v_libPrefixOnWindows_2917_; uint8_t v_allowImportAll_2918_; lean_object* v_builtinLint_x3f_2919_; uint8_t v_fixedToolchain_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2928_; 
v_toWorkspaceConfig_2887_ = lean_ctor_get(v_cfg_2886_, 0);
v_toLeanConfig_2888_ = lean_ctor_get(v_cfg_2886_, 1);
v_bootstrap_2889_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27);
v_extraDepTargets_2890_ = lean_ctor_get(v_cfg_2886_, 2);
v_precompileModules_2891_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2892_ = lean_ctor_get(v_cfg_2886_, 3);
v_srcDir_2893_ = lean_ctor_get(v_cfg_2886_, 4);
v_buildDir_2894_ = lean_ctor_get(v_cfg_2886_, 5);
v_leanLibDir_2895_ = lean_ctor_get(v_cfg_2886_, 6);
v_nativeLibDir_2896_ = lean_ctor_get(v_cfg_2886_, 7);
v_binDir_2897_ = lean_ctor_get(v_cfg_2886_, 8);
v_irDir_2898_ = lean_ctor_get(v_cfg_2886_, 9);
v_releaseRepo_2899_ = lean_ctor_get(v_cfg_2886_, 10);
v_buildArchive_2900_ = lean_ctor_get(v_cfg_2886_, 11);
v_preferReleaseBuild_2901_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27 + 2);
v_testDriver_2902_ = lean_ctor_get(v_cfg_2886_, 12);
v_testDriverArgs_2903_ = lean_ctor_get(v_cfg_2886_, 13);
v_lintDriver_2904_ = lean_ctor_get(v_cfg_2886_, 14);
v_lintDriverArgs_2905_ = lean_ctor_get(v_cfg_2886_, 15);
v_version_2906_ = lean_ctor_get(v_cfg_2886_, 16);
v_versionTags_2907_ = lean_ctor_get(v_cfg_2886_, 17);
v_description_2908_ = lean_ctor_get(v_cfg_2886_, 18);
v_keywords_2909_ = lean_ctor_get(v_cfg_2886_, 19);
v_homepage_2910_ = lean_ctor_get(v_cfg_2886_, 20);
v_license_2911_ = lean_ctor_get(v_cfg_2886_, 21);
v_licenseFiles_2912_ = lean_ctor_get(v_cfg_2886_, 22);
v_readmeFile_2913_ = lean_ctor_get(v_cfg_2886_, 23);
v_reservoir_2914_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_2915_ = lean_ctor_get(v_cfg_2886_, 24);
v_restoreAllArtifacts_x3f_2916_ = lean_ctor_get(v_cfg_2886_, 25);
v_libPrefixOnWindows_2917_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27 + 4);
v_allowImportAll_2918_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2919_ = lean_ctor_get(v_cfg_2886_, 26);
v_fixedToolchain_2920_ = lean_ctor_get_uint8(v_cfg_2886_, sizeof(void*)*27 + 6);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_cfg_2886_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2922_ = v_cfg_2886_;
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_builtinLint_x3f_2919_);
lean_inc(v_restoreAllArtifacts_x3f_2916_);
lean_inc(v_enableArtifactCache_x3f_2915_);
lean_inc(v_readmeFile_2913_);
lean_inc(v_licenseFiles_2912_);
lean_inc(v_license_2911_);
lean_inc(v_homepage_2910_);
lean_inc(v_keywords_2909_);
lean_inc(v_description_2908_);
lean_inc(v_versionTags_2907_);
lean_inc(v_version_2906_);
lean_inc(v_lintDriverArgs_2905_);
lean_inc(v_lintDriver_2904_);
lean_inc(v_testDriverArgs_2903_);
lean_inc(v_testDriver_2902_);
lean_inc(v_buildArchive_2900_);
lean_inc(v_releaseRepo_2899_);
lean_inc(v_irDir_2898_);
lean_inc(v_binDir_2897_);
lean_inc(v_nativeLibDir_2896_);
lean_inc(v_leanLibDir_2895_);
lean_inc(v_buildDir_2894_);
lean_inc(v_srcDir_2893_);
lean_inc(v_moreGlobalServerArgs_2892_);
lean_inc(v_extraDepTargets_2890_);
lean_inc(v_toLeanConfig_2888_);
lean_inc(v_toWorkspaceConfig_2887_);
lean_dec(v_cfg_2886_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = lean_apply_1(v_f_2885_, v_readmeFile_2913_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 23, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_toWorkspaceConfig_2887_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_toLeanConfig_2888_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_extraDepTargets_2890_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_moreGlobalServerArgs_2892_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_srcDir_2893_);
lean_ctor_set(v_reuseFailAlloc_2927_, 5, v_buildDir_2894_);
lean_ctor_set(v_reuseFailAlloc_2927_, 6, v_leanLibDir_2895_);
lean_ctor_set(v_reuseFailAlloc_2927_, 7, v_nativeLibDir_2896_);
lean_ctor_set(v_reuseFailAlloc_2927_, 8, v_binDir_2897_);
lean_ctor_set(v_reuseFailAlloc_2927_, 9, v_irDir_2898_);
lean_ctor_set(v_reuseFailAlloc_2927_, 10, v_releaseRepo_2899_);
lean_ctor_set(v_reuseFailAlloc_2927_, 11, v_buildArchive_2900_);
lean_ctor_set(v_reuseFailAlloc_2927_, 12, v_testDriver_2902_);
lean_ctor_set(v_reuseFailAlloc_2927_, 13, v_testDriverArgs_2903_);
lean_ctor_set(v_reuseFailAlloc_2927_, 14, v_lintDriver_2904_);
lean_ctor_set(v_reuseFailAlloc_2927_, 15, v_lintDriverArgs_2905_);
lean_ctor_set(v_reuseFailAlloc_2927_, 16, v_version_2906_);
lean_ctor_set(v_reuseFailAlloc_2927_, 17, v_versionTags_2907_);
lean_ctor_set(v_reuseFailAlloc_2927_, 18, v_description_2908_);
lean_ctor_set(v_reuseFailAlloc_2927_, 19, v_keywords_2909_);
lean_ctor_set(v_reuseFailAlloc_2927_, 20, v_homepage_2910_);
lean_ctor_set(v_reuseFailAlloc_2927_, 21, v_license_2911_);
lean_ctor_set(v_reuseFailAlloc_2927_, 22, v_licenseFiles_2912_);
lean_ctor_set(v_reuseFailAlloc_2927_, 23, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2927_, 24, v_enableArtifactCache_x3f_2915_);
lean_ctor_set(v_reuseFailAlloc_2927_, 25, v_restoreAllArtifacts_x3f_2916_);
lean_ctor_set(v_reuseFailAlloc_2927_, 26, v_builtinLint_x3f_2919_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27, v_bootstrap_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27 + 1, v_precompileModules_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27 + 3, v_reservoir_2914_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2917_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27 + 5, v_allowImportAll_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*27 + 6, v_fixedToolchain_2920_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* v_x_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* v_x_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lake_PackageConfig_readmeFile___proj___lam__3(v_x_2931_);
lean_dec_ref(v_x_2931_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_2942_, lean_object* v_n_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_2945_, lean_object* v_n_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2945_, v_n_2946_);
lean_dec(v_n_2946_);
lean_dec(v_p_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_2948_, lean_object* v_n_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2948_, v_n_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_2951_, lean_object* v_n_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_2951_, v_n_2952_);
lean_dec(v_n_2952_);
lean_dec(v_p_2951_);
return v_res_2953_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* v_cfg_2954_){
_start:
{
uint8_t v_reservoir_2955_; 
v_reservoir_2955_ = lean_ctor_get_uint8(v_cfg_2954_, sizeof(void*)*27 + 3);
return v_reservoir_2955_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* v_cfg_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l_Lake_PackageConfig_reservoir___proj___lam__0(v_cfg_2956_);
lean_dec_ref(v_cfg_2956_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t v_val_2959_, lean_object* v_cfg_2960_){
_start:
{
lean_object* v_toWorkspaceConfig_2961_; lean_object* v_toLeanConfig_2962_; uint8_t v_bootstrap_2963_; lean_object* v_extraDepTargets_2964_; uint8_t v_precompileModules_2965_; lean_object* v_moreGlobalServerArgs_2966_; lean_object* v_srcDir_2967_; lean_object* v_buildDir_2968_; lean_object* v_leanLibDir_2969_; lean_object* v_nativeLibDir_2970_; lean_object* v_binDir_2971_; lean_object* v_irDir_2972_; lean_object* v_releaseRepo_2973_; lean_object* v_buildArchive_2974_; uint8_t v_preferReleaseBuild_2975_; lean_object* v_testDriver_2976_; lean_object* v_testDriverArgs_2977_; lean_object* v_lintDriver_2978_; lean_object* v_lintDriverArgs_2979_; lean_object* v_version_2980_; lean_object* v_versionTags_2981_; lean_object* v_description_2982_; lean_object* v_keywords_2983_; lean_object* v_homepage_2984_; lean_object* v_license_2985_; lean_object* v_licenseFiles_2986_; lean_object* v_readmeFile_2987_; lean_object* v_enableArtifactCache_x3f_2988_; lean_object* v_restoreAllArtifacts_x3f_2989_; uint8_t v_libPrefixOnWindows_2990_; uint8_t v_allowImportAll_2991_; lean_object* v_builtinLint_x3f_2992_; uint8_t v_fixedToolchain_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_toWorkspaceConfig_2961_ = lean_ctor_get(v_cfg_2960_, 0);
v_toLeanConfig_2962_ = lean_ctor_get(v_cfg_2960_, 1);
v_bootstrap_2963_ = lean_ctor_get_uint8(v_cfg_2960_, sizeof(void*)*27);
v_extraDepTargets_2964_ = lean_ctor_get(v_cfg_2960_, 2);
v_precompileModules_2965_ = lean_ctor_get_uint8(v_cfg_2960_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_2966_ = lean_ctor_get(v_cfg_2960_, 3);
v_srcDir_2967_ = lean_ctor_get(v_cfg_2960_, 4);
v_buildDir_2968_ = lean_ctor_get(v_cfg_2960_, 5);
v_leanLibDir_2969_ = lean_ctor_get(v_cfg_2960_, 6);
v_nativeLibDir_2970_ = lean_ctor_get(v_cfg_2960_, 7);
v_binDir_2971_ = lean_ctor_get(v_cfg_2960_, 8);
v_irDir_2972_ = lean_ctor_get(v_cfg_2960_, 9);
v_releaseRepo_2973_ = lean_ctor_get(v_cfg_2960_, 10);
v_buildArchive_2974_ = lean_ctor_get(v_cfg_2960_, 11);
v_preferReleaseBuild_2975_ = lean_ctor_get_uint8(v_cfg_2960_, sizeof(void*)*27 + 2);
v_testDriver_2976_ = lean_ctor_get(v_cfg_2960_, 12);
v_testDriverArgs_2977_ = lean_ctor_get(v_cfg_2960_, 13);
v_lintDriver_2978_ = lean_ctor_get(v_cfg_2960_, 14);
v_lintDriverArgs_2979_ = lean_ctor_get(v_cfg_2960_, 15);
v_version_2980_ = lean_ctor_get(v_cfg_2960_, 16);
v_versionTags_2981_ = lean_ctor_get(v_cfg_2960_, 17);
v_description_2982_ = lean_ctor_get(v_cfg_2960_, 18);
v_keywords_2983_ = lean_ctor_get(v_cfg_2960_, 19);
v_homepage_2984_ = lean_ctor_get(v_cfg_2960_, 20);
v_license_2985_ = lean_ctor_get(v_cfg_2960_, 21);
v_licenseFiles_2986_ = lean_ctor_get(v_cfg_2960_, 22);
v_readmeFile_2987_ = lean_ctor_get(v_cfg_2960_, 23);
v_enableArtifactCache_x3f_2988_ = lean_ctor_get(v_cfg_2960_, 24);
v_restoreAllArtifacts_x3f_2989_ = lean_ctor_get(v_cfg_2960_, 25);
v_libPrefixOnWindows_2990_ = lean_ctor_get_uint8(v_cfg_2960_, sizeof(void*)*27 + 4);
v_allowImportAll_2991_ = lean_ctor_get_uint8(v_cfg_2960_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_2992_ = lean_ctor_get(v_cfg_2960_, 26);
v_fixedToolchain_2993_ = lean_ctor_get_uint8(v_cfg_2960_, sizeof(void*)*27 + 6);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_cfg_2960_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v_cfg_2960_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_builtinLint_x3f_2992_);
lean_inc(v_restoreAllArtifacts_x3f_2989_);
lean_inc(v_enableArtifactCache_x3f_2988_);
lean_inc(v_readmeFile_2987_);
lean_inc(v_licenseFiles_2986_);
lean_inc(v_license_2985_);
lean_inc(v_homepage_2984_);
lean_inc(v_keywords_2983_);
lean_inc(v_description_2982_);
lean_inc(v_versionTags_2981_);
lean_inc(v_version_2980_);
lean_inc(v_lintDriverArgs_2979_);
lean_inc(v_lintDriver_2978_);
lean_inc(v_testDriverArgs_2977_);
lean_inc(v_testDriver_2976_);
lean_inc(v_buildArchive_2974_);
lean_inc(v_releaseRepo_2973_);
lean_inc(v_irDir_2972_);
lean_inc(v_binDir_2971_);
lean_inc(v_nativeLibDir_2970_);
lean_inc(v_leanLibDir_2969_);
lean_inc(v_buildDir_2968_);
lean_inc(v_srcDir_2967_);
lean_inc(v_moreGlobalServerArgs_2966_);
lean_inc(v_extraDepTargets_2964_);
lean_inc(v_toLeanConfig_2962_);
lean_inc(v_toWorkspaceConfig_2961_);
lean_dec(v_cfg_2960_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_toWorkspaceConfig_2961_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_toLeanConfig_2962_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_extraDepTargets_2964_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_moreGlobalServerArgs_2966_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_srcDir_2967_);
lean_ctor_set(v_reuseFailAlloc_2999_, 5, v_buildDir_2968_);
lean_ctor_set(v_reuseFailAlloc_2999_, 6, v_leanLibDir_2969_);
lean_ctor_set(v_reuseFailAlloc_2999_, 7, v_nativeLibDir_2970_);
lean_ctor_set(v_reuseFailAlloc_2999_, 8, v_binDir_2971_);
lean_ctor_set(v_reuseFailAlloc_2999_, 9, v_irDir_2972_);
lean_ctor_set(v_reuseFailAlloc_2999_, 10, v_releaseRepo_2973_);
lean_ctor_set(v_reuseFailAlloc_2999_, 11, v_buildArchive_2974_);
lean_ctor_set(v_reuseFailAlloc_2999_, 12, v_testDriver_2976_);
lean_ctor_set(v_reuseFailAlloc_2999_, 13, v_testDriverArgs_2977_);
lean_ctor_set(v_reuseFailAlloc_2999_, 14, v_lintDriver_2978_);
lean_ctor_set(v_reuseFailAlloc_2999_, 15, v_lintDriverArgs_2979_);
lean_ctor_set(v_reuseFailAlloc_2999_, 16, v_version_2980_);
lean_ctor_set(v_reuseFailAlloc_2999_, 17, v_versionTags_2981_);
lean_ctor_set(v_reuseFailAlloc_2999_, 18, v_description_2982_);
lean_ctor_set(v_reuseFailAlloc_2999_, 19, v_keywords_2983_);
lean_ctor_set(v_reuseFailAlloc_2999_, 20, v_homepage_2984_);
lean_ctor_set(v_reuseFailAlloc_2999_, 21, v_license_2985_);
lean_ctor_set(v_reuseFailAlloc_2999_, 22, v_licenseFiles_2986_);
lean_ctor_set(v_reuseFailAlloc_2999_, 23, v_readmeFile_2987_);
lean_ctor_set(v_reuseFailAlloc_2999_, 24, v_enableArtifactCache_x3f_2988_);
lean_ctor_set(v_reuseFailAlloc_2999_, 25, v_restoreAllArtifacts_x3f_2989_);
lean_ctor_set(v_reuseFailAlloc_2999_, 26, v_builtinLint_x3f_2992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*27, v_bootstrap_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*27 + 1, v_precompileModules_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*27 + 2, v_preferReleaseBuild_2975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*27 + 5, v_allowImportAll_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*27 + 6, v_fixedToolchain_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*27 + 3, v_val_2959_);
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* v_val_3001_, lean_object* v_cfg_3002_){
_start:
{
uint8_t v_val_137__boxed_3003_; lean_object* v_res_3004_; 
v_val_137__boxed_3003_ = lean_unbox(v_val_3001_);
v_res_3004_ = l_Lake_PackageConfig_reservoir___proj___lam__1(v_val_137__boxed_3003_, v_cfg_3002_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* v_f_3005_, lean_object* v_cfg_3006_){
_start:
{
lean_object* v_toWorkspaceConfig_3007_; lean_object* v_toLeanConfig_3008_; uint8_t v_bootstrap_3009_; lean_object* v_extraDepTargets_3010_; uint8_t v_precompileModules_3011_; lean_object* v_moreGlobalServerArgs_3012_; lean_object* v_srcDir_3013_; lean_object* v_buildDir_3014_; lean_object* v_leanLibDir_3015_; lean_object* v_nativeLibDir_3016_; lean_object* v_binDir_3017_; lean_object* v_irDir_3018_; lean_object* v_releaseRepo_3019_; lean_object* v_buildArchive_3020_; uint8_t v_preferReleaseBuild_3021_; lean_object* v_testDriver_3022_; lean_object* v_testDriverArgs_3023_; lean_object* v_lintDriver_3024_; lean_object* v_lintDriverArgs_3025_; lean_object* v_version_3026_; lean_object* v_versionTags_3027_; lean_object* v_description_3028_; lean_object* v_keywords_3029_; lean_object* v_homepage_3030_; lean_object* v_license_3031_; lean_object* v_licenseFiles_3032_; lean_object* v_readmeFile_3033_; uint8_t v_reservoir_3034_; lean_object* v_enableArtifactCache_x3f_3035_; lean_object* v_restoreAllArtifacts_x3f_3036_; uint8_t v_libPrefixOnWindows_3037_; uint8_t v_allowImportAll_3038_; lean_object* v_builtinLint_x3f_3039_; uint8_t v_fixedToolchain_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3050_; 
v_toWorkspaceConfig_3007_ = lean_ctor_get(v_cfg_3006_, 0);
v_toLeanConfig_3008_ = lean_ctor_get(v_cfg_3006_, 1);
v_bootstrap_3009_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27);
v_extraDepTargets_3010_ = lean_ctor_get(v_cfg_3006_, 2);
v_precompileModules_3011_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3012_ = lean_ctor_get(v_cfg_3006_, 3);
v_srcDir_3013_ = lean_ctor_get(v_cfg_3006_, 4);
v_buildDir_3014_ = lean_ctor_get(v_cfg_3006_, 5);
v_leanLibDir_3015_ = lean_ctor_get(v_cfg_3006_, 6);
v_nativeLibDir_3016_ = lean_ctor_get(v_cfg_3006_, 7);
v_binDir_3017_ = lean_ctor_get(v_cfg_3006_, 8);
v_irDir_3018_ = lean_ctor_get(v_cfg_3006_, 9);
v_releaseRepo_3019_ = lean_ctor_get(v_cfg_3006_, 10);
v_buildArchive_3020_ = lean_ctor_get(v_cfg_3006_, 11);
v_preferReleaseBuild_3021_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 2);
v_testDriver_3022_ = lean_ctor_get(v_cfg_3006_, 12);
v_testDriverArgs_3023_ = lean_ctor_get(v_cfg_3006_, 13);
v_lintDriver_3024_ = lean_ctor_get(v_cfg_3006_, 14);
v_lintDriverArgs_3025_ = lean_ctor_get(v_cfg_3006_, 15);
v_version_3026_ = lean_ctor_get(v_cfg_3006_, 16);
v_versionTags_3027_ = lean_ctor_get(v_cfg_3006_, 17);
v_description_3028_ = lean_ctor_get(v_cfg_3006_, 18);
v_keywords_3029_ = lean_ctor_get(v_cfg_3006_, 19);
v_homepage_3030_ = lean_ctor_get(v_cfg_3006_, 20);
v_license_3031_ = lean_ctor_get(v_cfg_3006_, 21);
v_licenseFiles_3032_ = lean_ctor_get(v_cfg_3006_, 22);
v_readmeFile_3033_ = lean_ctor_get(v_cfg_3006_, 23);
v_reservoir_3034_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3035_ = lean_ctor_get(v_cfg_3006_, 24);
v_restoreAllArtifacts_x3f_3036_ = lean_ctor_get(v_cfg_3006_, 25);
v_libPrefixOnWindows_3037_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 4);
v_allowImportAll_3038_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3039_ = lean_ctor_get(v_cfg_3006_, 26);
v_fixedToolchain_3040_ = lean_ctor_get_uint8(v_cfg_3006_, sizeof(void*)*27 + 6);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_cfg_3006_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3042_ = v_cfg_3006_;
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_builtinLint_x3f_3039_);
lean_inc(v_restoreAllArtifacts_x3f_3036_);
lean_inc(v_enableArtifactCache_x3f_3035_);
lean_inc(v_readmeFile_3033_);
lean_inc(v_licenseFiles_3032_);
lean_inc(v_license_3031_);
lean_inc(v_homepage_3030_);
lean_inc(v_keywords_3029_);
lean_inc(v_description_3028_);
lean_inc(v_versionTags_3027_);
lean_inc(v_version_3026_);
lean_inc(v_lintDriverArgs_3025_);
lean_inc(v_lintDriver_3024_);
lean_inc(v_testDriverArgs_3023_);
lean_inc(v_testDriver_3022_);
lean_inc(v_buildArchive_3020_);
lean_inc(v_releaseRepo_3019_);
lean_inc(v_irDir_3018_);
lean_inc(v_binDir_3017_);
lean_inc(v_nativeLibDir_3016_);
lean_inc(v_leanLibDir_3015_);
lean_inc(v_buildDir_3014_);
lean_inc(v_srcDir_3013_);
lean_inc(v_moreGlobalServerArgs_3012_);
lean_inc(v_extraDepTargets_3010_);
lean_inc(v_toLeanConfig_3008_);
lean_inc(v_toWorkspaceConfig_3007_);
lean_dec(v_cfg_3006_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3044_ = lean_box(v_reservoir_3034_);
v___x_3045_ = lean_apply_1(v_f_3005_, v___x_3044_);
if (v_isShared_3043_ == 0)
{
v___x_3047_ = v___x_3042_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_toWorkspaceConfig_3007_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_toLeanConfig_3008_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_extraDepTargets_3010_);
lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_moreGlobalServerArgs_3012_);
lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_srcDir_3013_);
lean_ctor_set(v_reuseFailAlloc_3049_, 5, v_buildDir_3014_);
lean_ctor_set(v_reuseFailAlloc_3049_, 6, v_leanLibDir_3015_);
lean_ctor_set(v_reuseFailAlloc_3049_, 7, v_nativeLibDir_3016_);
lean_ctor_set(v_reuseFailAlloc_3049_, 8, v_binDir_3017_);
lean_ctor_set(v_reuseFailAlloc_3049_, 9, v_irDir_3018_);
lean_ctor_set(v_reuseFailAlloc_3049_, 10, v_releaseRepo_3019_);
lean_ctor_set(v_reuseFailAlloc_3049_, 11, v_buildArchive_3020_);
lean_ctor_set(v_reuseFailAlloc_3049_, 12, v_testDriver_3022_);
lean_ctor_set(v_reuseFailAlloc_3049_, 13, v_testDriverArgs_3023_);
lean_ctor_set(v_reuseFailAlloc_3049_, 14, v_lintDriver_3024_);
lean_ctor_set(v_reuseFailAlloc_3049_, 15, v_lintDriverArgs_3025_);
lean_ctor_set(v_reuseFailAlloc_3049_, 16, v_version_3026_);
lean_ctor_set(v_reuseFailAlloc_3049_, 17, v_versionTags_3027_);
lean_ctor_set(v_reuseFailAlloc_3049_, 18, v_description_3028_);
lean_ctor_set(v_reuseFailAlloc_3049_, 19, v_keywords_3029_);
lean_ctor_set(v_reuseFailAlloc_3049_, 20, v_homepage_3030_);
lean_ctor_set(v_reuseFailAlloc_3049_, 21, v_license_3031_);
lean_ctor_set(v_reuseFailAlloc_3049_, 22, v_licenseFiles_3032_);
lean_ctor_set(v_reuseFailAlloc_3049_, 23, v_readmeFile_3033_);
lean_ctor_set(v_reuseFailAlloc_3049_, 24, v_enableArtifactCache_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3049_, 25, v_restoreAllArtifacts_x3f_3036_);
lean_ctor_set(v_reuseFailAlloc_3049_, 26, v_builtinLint_x3f_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*27, v_bootstrap_3009_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*27 + 1, v_precompileModules_3011_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3021_);
v___x_3047_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_unbox(v___x_3045_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*27 + 3, v___x_3048_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3037_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*27 + 5, v_allowImportAll_3038_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*27 + 6, v_fixedToolchain_3040_);
return v___x_3047_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* v_x_3051_){
_start:
{
uint8_t v___x_3052_; 
v___x_3052_ = 1;
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* v_x_3053_){
_start:
{
uint8_t v_res_3054_; lean_object* v_r_3055_; 
v_res_3054_ = l_Lake_PackageConfig_reservoir___proj___lam__3(v_x_3053_);
lean_dec_ref(v_x_3053_);
v_r_3055_ = lean_box(v_res_3054_);
return v_r_3055_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3065_, lean_object* v_n_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3068_, lean_object* v_n_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lake_PackageConfig_reservoir___proj(v_p_3068_, v_n_3069_);
lean_dec(v_n_3069_);
lean_dec(v_p_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3071_, lean_object* v_n_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lake_PackageConfig_reservoir___proj(v_p_3071_, v_n_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3074_, lean_object* v_n_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3074_, v_n_3075_);
lean_dec(v_n_3075_);
lean_dec(v_p_3074_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* v_cfg_3077_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3078_; 
v_enableArtifactCache_x3f_3078_ = lean_ctor_get(v_cfg_3077_, 24);
lean_inc(v_enableArtifactCache_x3f_3078_);
return v_enableArtifactCache_x3f_3078_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* v_cfg_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(v_cfg_3079_);
lean_dec_ref(v_cfg_3079_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* v_val_3081_, lean_object* v_cfg_3082_){
_start:
{
lean_object* v_toWorkspaceConfig_3083_; lean_object* v_toLeanConfig_3084_; uint8_t v_bootstrap_3085_; lean_object* v_extraDepTargets_3086_; uint8_t v_precompileModules_3087_; lean_object* v_moreGlobalServerArgs_3088_; lean_object* v_srcDir_3089_; lean_object* v_buildDir_3090_; lean_object* v_leanLibDir_3091_; lean_object* v_nativeLibDir_3092_; lean_object* v_binDir_3093_; lean_object* v_irDir_3094_; lean_object* v_releaseRepo_3095_; lean_object* v_buildArchive_3096_; uint8_t v_preferReleaseBuild_3097_; lean_object* v_testDriver_3098_; lean_object* v_testDriverArgs_3099_; lean_object* v_lintDriver_3100_; lean_object* v_lintDriverArgs_3101_; lean_object* v_version_3102_; lean_object* v_versionTags_3103_; lean_object* v_description_3104_; lean_object* v_keywords_3105_; lean_object* v_homepage_3106_; lean_object* v_license_3107_; lean_object* v_licenseFiles_3108_; lean_object* v_readmeFile_3109_; uint8_t v_reservoir_3110_; lean_object* v_restoreAllArtifacts_x3f_3111_; uint8_t v_libPrefixOnWindows_3112_; uint8_t v_allowImportAll_3113_; lean_object* v_builtinLint_x3f_3114_; uint8_t v_fixedToolchain_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
v_toWorkspaceConfig_3083_ = lean_ctor_get(v_cfg_3082_, 0);
v_toLeanConfig_3084_ = lean_ctor_get(v_cfg_3082_, 1);
v_bootstrap_3085_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27);
v_extraDepTargets_3086_ = lean_ctor_get(v_cfg_3082_, 2);
v_precompileModules_3087_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3088_ = lean_ctor_get(v_cfg_3082_, 3);
v_srcDir_3089_ = lean_ctor_get(v_cfg_3082_, 4);
v_buildDir_3090_ = lean_ctor_get(v_cfg_3082_, 5);
v_leanLibDir_3091_ = lean_ctor_get(v_cfg_3082_, 6);
v_nativeLibDir_3092_ = lean_ctor_get(v_cfg_3082_, 7);
v_binDir_3093_ = lean_ctor_get(v_cfg_3082_, 8);
v_irDir_3094_ = lean_ctor_get(v_cfg_3082_, 9);
v_releaseRepo_3095_ = lean_ctor_get(v_cfg_3082_, 10);
v_buildArchive_3096_ = lean_ctor_get(v_cfg_3082_, 11);
v_preferReleaseBuild_3097_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27 + 2);
v_testDriver_3098_ = lean_ctor_get(v_cfg_3082_, 12);
v_testDriverArgs_3099_ = lean_ctor_get(v_cfg_3082_, 13);
v_lintDriver_3100_ = lean_ctor_get(v_cfg_3082_, 14);
v_lintDriverArgs_3101_ = lean_ctor_get(v_cfg_3082_, 15);
v_version_3102_ = lean_ctor_get(v_cfg_3082_, 16);
v_versionTags_3103_ = lean_ctor_get(v_cfg_3082_, 17);
v_description_3104_ = lean_ctor_get(v_cfg_3082_, 18);
v_keywords_3105_ = lean_ctor_get(v_cfg_3082_, 19);
v_homepage_3106_ = lean_ctor_get(v_cfg_3082_, 20);
v_license_3107_ = lean_ctor_get(v_cfg_3082_, 21);
v_licenseFiles_3108_ = lean_ctor_get(v_cfg_3082_, 22);
v_readmeFile_3109_ = lean_ctor_get(v_cfg_3082_, 23);
v_reservoir_3110_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27 + 3);
v_restoreAllArtifacts_x3f_3111_ = lean_ctor_get(v_cfg_3082_, 25);
v_libPrefixOnWindows_3112_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27 + 4);
v_allowImportAll_3113_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3114_ = lean_ctor_get(v_cfg_3082_, 26);
v_fixedToolchain_3115_ = lean_ctor_get_uint8(v_cfg_3082_, sizeof(void*)*27 + 6);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_cfg_3082_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v_cfg_3082_, 24);
lean_dec(v_unused_3123_);
v___x_3117_ = v_cfg_3082_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_builtinLint_x3f_3114_);
lean_inc(v_restoreAllArtifacts_x3f_3111_);
lean_inc(v_readmeFile_3109_);
lean_inc(v_licenseFiles_3108_);
lean_inc(v_license_3107_);
lean_inc(v_homepage_3106_);
lean_inc(v_keywords_3105_);
lean_inc(v_description_3104_);
lean_inc(v_versionTags_3103_);
lean_inc(v_version_3102_);
lean_inc(v_lintDriverArgs_3101_);
lean_inc(v_lintDriver_3100_);
lean_inc(v_testDriverArgs_3099_);
lean_inc(v_testDriver_3098_);
lean_inc(v_buildArchive_3096_);
lean_inc(v_releaseRepo_3095_);
lean_inc(v_irDir_3094_);
lean_inc(v_binDir_3093_);
lean_inc(v_nativeLibDir_3092_);
lean_inc(v_leanLibDir_3091_);
lean_inc(v_buildDir_3090_);
lean_inc(v_srcDir_3089_);
lean_inc(v_moreGlobalServerArgs_3088_);
lean_inc(v_extraDepTargets_3086_);
lean_inc(v_toLeanConfig_3084_);
lean_inc(v_toWorkspaceConfig_3083_);
lean_dec(v_cfg_3082_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 24, v_val_3081_);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_toWorkspaceConfig_3083_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_toLeanConfig_3084_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_extraDepTargets_3086_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_moreGlobalServerArgs_3088_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_srcDir_3089_);
lean_ctor_set(v_reuseFailAlloc_3121_, 5, v_buildDir_3090_);
lean_ctor_set(v_reuseFailAlloc_3121_, 6, v_leanLibDir_3091_);
lean_ctor_set(v_reuseFailAlloc_3121_, 7, v_nativeLibDir_3092_);
lean_ctor_set(v_reuseFailAlloc_3121_, 8, v_binDir_3093_);
lean_ctor_set(v_reuseFailAlloc_3121_, 9, v_irDir_3094_);
lean_ctor_set(v_reuseFailAlloc_3121_, 10, v_releaseRepo_3095_);
lean_ctor_set(v_reuseFailAlloc_3121_, 11, v_buildArchive_3096_);
lean_ctor_set(v_reuseFailAlloc_3121_, 12, v_testDriver_3098_);
lean_ctor_set(v_reuseFailAlloc_3121_, 13, v_testDriverArgs_3099_);
lean_ctor_set(v_reuseFailAlloc_3121_, 14, v_lintDriver_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 15, v_lintDriverArgs_3101_);
lean_ctor_set(v_reuseFailAlloc_3121_, 16, v_version_3102_);
lean_ctor_set(v_reuseFailAlloc_3121_, 17, v_versionTags_3103_);
lean_ctor_set(v_reuseFailAlloc_3121_, 18, v_description_3104_);
lean_ctor_set(v_reuseFailAlloc_3121_, 19, v_keywords_3105_);
lean_ctor_set(v_reuseFailAlloc_3121_, 20, v_homepage_3106_);
lean_ctor_set(v_reuseFailAlloc_3121_, 21, v_license_3107_);
lean_ctor_set(v_reuseFailAlloc_3121_, 22, v_licenseFiles_3108_);
lean_ctor_set(v_reuseFailAlloc_3121_, 23, v_readmeFile_3109_);
lean_ctor_set(v_reuseFailAlloc_3121_, 24, v_val_3081_);
lean_ctor_set(v_reuseFailAlloc_3121_, 25, v_restoreAllArtifacts_x3f_3111_);
lean_ctor_set(v_reuseFailAlloc_3121_, 26, v_builtinLint_x3f_3114_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27, v_bootstrap_3085_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27 + 1, v_precompileModules_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3097_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27 + 3, v_reservoir_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3112_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27 + 5, v_allowImportAll_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3121_, sizeof(void*)*27 + 6, v_fixedToolchain_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* v_f_3124_, lean_object* v_cfg_3125_){
_start:
{
lean_object* v_toWorkspaceConfig_3126_; lean_object* v_toLeanConfig_3127_; uint8_t v_bootstrap_3128_; lean_object* v_extraDepTargets_3129_; uint8_t v_precompileModules_3130_; lean_object* v_moreGlobalServerArgs_3131_; lean_object* v_srcDir_3132_; lean_object* v_buildDir_3133_; lean_object* v_leanLibDir_3134_; lean_object* v_nativeLibDir_3135_; lean_object* v_binDir_3136_; lean_object* v_irDir_3137_; lean_object* v_releaseRepo_3138_; lean_object* v_buildArchive_3139_; uint8_t v_preferReleaseBuild_3140_; lean_object* v_testDriver_3141_; lean_object* v_testDriverArgs_3142_; lean_object* v_lintDriver_3143_; lean_object* v_lintDriverArgs_3144_; lean_object* v_version_3145_; lean_object* v_versionTags_3146_; lean_object* v_description_3147_; lean_object* v_keywords_3148_; lean_object* v_homepage_3149_; lean_object* v_license_3150_; lean_object* v_licenseFiles_3151_; lean_object* v_readmeFile_3152_; uint8_t v_reservoir_3153_; lean_object* v_enableArtifactCache_x3f_3154_; lean_object* v_restoreAllArtifacts_x3f_3155_; uint8_t v_libPrefixOnWindows_3156_; uint8_t v_allowImportAll_3157_; lean_object* v_builtinLint_x3f_3158_; uint8_t v_fixedToolchain_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3167_; 
v_toWorkspaceConfig_3126_ = lean_ctor_get(v_cfg_3125_, 0);
v_toLeanConfig_3127_ = lean_ctor_get(v_cfg_3125_, 1);
v_bootstrap_3128_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27);
v_extraDepTargets_3129_ = lean_ctor_get(v_cfg_3125_, 2);
v_precompileModules_3130_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3131_ = lean_ctor_get(v_cfg_3125_, 3);
v_srcDir_3132_ = lean_ctor_get(v_cfg_3125_, 4);
v_buildDir_3133_ = lean_ctor_get(v_cfg_3125_, 5);
v_leanLibDir_3134_ = lean_ctor_get(v_cfg_3125_, 6);
v_nativeLibDir_3135_ = lean_ctor_get(v_cfg_3125_, 7);
v_binDir_3136_ = lean_ctor_get(v_cfg_3125_, 8);
v_irDir_3137_ = lean_ctor_get(v_cfg_3125_, 9);
v_releaseRepo_3138_ = lean_ctor_get(v_cfg_3125_, 10);
v_buildArchive_3139_ = lean_ctor_get(v_cfg_3125_, 11);
v_preferReleaseBuild_3140_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27 + 2);
v_testDriver_3141_ = lean_ctor_get(v_cfg_3125_, 12);
v_testDriverArgs_3142_ = lean_ctor_get(v_cfg_3125_, 13);
v_lintDriver_3143_ = lean_ctor_get(v_cfg_3125_, 14);
v_lintDriverArgs_3144_ = lean_ctor_get(v_cfg_3125_, 15);
v_version_3145_ = lean_ctor_get(v_cfg_3125_, 16);
v_versionTags_3146_ = lean_ctor_get(v_cfg_3125_, 17);
v_description_3147_ = lean_ctor_get(v_cfg_3125_, 18);
v_keywords_3148_ = lean_ctor_get(v_cfg_3125_, 19);
v_homepage_3149_ = lean_ctor_get(v_cfg_3125_, 20);
v_license_3150_ = lean_ctor_get(v_cfg_3125_, 21);
v_licenseFiles_3151_ = lean_ctor_get(v_cfg_3125_, 22);
v_readmeFile_3152_ = lean_ctor_get(v_cfg_3125_, 23);
v_reservoir_3153_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3154_ = lean_ctor_get(v_cfg_3125_, 24);
v_restoreAllArtifacts_x3f_3155_ = lean_ctor_get(v_cfg_3125_, 25);
v_libPrefixOnWindows_3156_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27 + 4);
v_allowImportAll_3157_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3158_ = lean_ctor_get(v_cfg_3125_, 26);
v_fixedToolchain_3159_ = lean_ctor_get_uint8(v_cfg_3125_, sizeof(void*)*27 + 6);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_cfg_3125_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3161_ = v_cfg_3125_;
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_builtinLint_x3f_3158_);
lean_inc(v_restoreAllArtifacts_x3f_3155_);
lean_inc(v_enableArtifactCache_x3f_3154_);
lean_inc(v_readmeFile_3152_);
lean_inc(v_licenseFiles_3151_);
lean_inc(v_license_3150_);
lean_inc(v_homepage_3149_);
lean_inc(v_keywords_3148_);
lean_inc(v_description_3147_);
lean_inc(v_versionTags_3146_);
lean_inc(v_version_3145_);
lean_inc(v_lintDriverArgs_3144_);
lean_inc(v_lintDriver_3143_);
lean_inc(v_testDriverArgs_3142_);
lean_inc(v_testDriver_3141_);
lean_inc(v_buildArchive_3139_);
lean_inc(v_releaseRepo_3138_);
lean_inc(v_irDir_3137_);
lean_inc(v_binDir_3136_);
lean_inc(v_nativeLibDir_3135_);
lean_inc(v_leanLibDir_3134_);
lean_inc(v_buildDir_3133_);
lean_inc(v_srcDir_3132_);
lean_inc(v_moreGlobalServerArgs_3131_);
lean_inc(v_extraDepTargets_3129_);
lean_inc(v_toLeanConfig_3127_);
lean_inc(v_toWorkspaceConfig_3126_);
lean_dec(v_cfg_3125_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3163_ = lean_apply_1(v_f_3124_, v_enableArtifactCache_x3f_3154_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 24, v___x_3163_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_toWorkspaceConfig_3126_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_toLeanConfig_3127_);
lean_ctor_set(v_reuseFailAlloc_3166_, 2, v_extraDepTargets_3129_);
lean_ctor_set(v_reuseFailAlloc_3166_, 3, v_moreGlobalServerArgs_3131_);
lean_ctor_set(v_reuseFailAlloc_3166_, 4, v_srcDir_3132_);
lean_ctor_set(v_reuseFailAlloc_3166_, 5, v_buildDir_3133_);
lean_ctor_set(v_reuseFailAlloc_3166_, 6, v_leanLibDir_3134_);
lean_ctor_set(v_reuseFailAlloc_3166_, 7, v_nativeLibDir_3135_);
lean_ctor_set(v_reuseFailAlloc_3166_, 8, v_binDir_3136_);
lean_ctor_set(v_reuseFailAlloc_3166_, 9, v_irDir_3137_);
lean_ctor_set(v_reuseFailAlloc_3166_, 10, v_releaseRepo_3138_);
lean_ctor_set(v_reuseFailAlloc_3166_, 11, v_buildArchive_3139_);
lean_ctor_set(v_reuseFailAlloc_3166_, 12, v_testDriver_3141_);
lean_ctor_set(v_reuseFailAlloc_3166_, 13, v_testDriverArgs_3142_);
lean_ctor_set(v_reuseFailAlloc_3166_, 14, v_lintDriver_3143_);
lean_ctor_set(v_reuseFailAlloc_3166_, 15, v_lintDriverArgs_3144_);
lean_ctor_set(v_reuseFailAlloc_3166_, 16, v_version_3145_);
lean_ctor_set(v_reuseFailAlloc_3166_, 17, v_versionTags_3146_);
lean_ctor_set(v_reuseFailAlloc_3166_, 18, v_description_3147_);
lean_ctor_set(v_reuseFailAlloc_3166_, 19, v_keywords_3148_);
lean_ctor_set(v_reuseFailAlloc_3166_, 20, v_homepage_3149_);
lean_ctor_set(v_reuseFailAlloc_3166_, 21, v_license_3150_);
lean_ctor_set(v_reuseFailAlloc_3166_, 22, v_licenseFiles_3151_);
lean_ctor_set(v_reuseFailAlloc_3166_, 23, v_readmeFile_3152_);
lean_ctor_set(v_reuseFailAlloc_3166_, 24, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3166_, 25, v_restoreAllArtifacts_x3f_3155_);
lean_ctor_set(v_reuseFailAlloc_3166_, 26, v_builtinLint_x3f_3158_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27, v_bootstrap_3128_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27 + 1, v_precompileModules_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27 + 3, v_reservoir_3153_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3156_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27 + 5, v_allowImportAll_3157_);
lean_ctor_set_uint8(v_reuseFailAlloc_3166_, sizeof(void*)*27 + 6, v_fixedToolchain_3159_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* v_x_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_box(0);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* v_x_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(v_x_3170_);
lean_dec_ref(v_x_3170_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3181_, lean_object* v_n_3182_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3184_, lean_object* v_n_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3184_, v_n_3185_);
lean_dec(v_n_3185_);
lean_dec(v_p_3184_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3187_, lean_object* v_n_3188_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3187_, v_n_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3190_, lean_object* v_n_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3190_, v_n_3191_);
lean_dec(v_n_3191_);
lean_dec(v_p_3190_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3193_, lean_object* v_n_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3193_, v_n_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3196_, lean_object* v_n_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3196_, v_n_3197_);
lean_dec(v_n_3197_);
lean_dec(v_p_3196_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object* v_cfg_3199_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3200_; 
v_restoreAllArtifacts_x3f_3200_ = lean_ctor_get(v_cfg_3199_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3200_);
return v_restoreAllArtifacts_x3f_3200_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object* v_cfg_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(v_cfg_3201_);
lean_dec_ref(v_cfg_3201_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object* v_val_3203_, lean_object* v_cfg_3204_){
_start:
{
lean_object* v_toWorkspaceConfig_3205_; lean_object* v_toLeanConfig_3206_; uint8_t v_bootstrap_3207_; lean_object* v_extraDepTargets_3208_; uint8_t v_precompileModules_3209_; lean_object* v_moreGlobalServerArgs_3210_; lean_object* v_srcDir_3211_; lean_object* v_buildDir_3212_; lean_object* v_leanLibDir_3213_; lean_object* v_nativeLibDir_3214_; lean_object* v_binDir_3215_; lean_object* v_irDir_3216_; lean_object* v_releaseRepo_3217_; lean_object* v_buildArchive_3218_; uint8_t v_preferReleaseBuild_3219_; lean_object* v_testDriver_3220_; lean_object* v_testDriverArgs_3221_; lean_object* v_lintDriver_3222_; lean_object* v_lintDriverArgs_3223_; lean_object* v_version_3224_; lean_object* v_versionTags_3225_; lean_object* v_description_3226_; lean_object* v_keywords_3227_; lean_object* v_homepage_3228_; lean_object* v_license_3229_; lean_object* v_licenseFiles_3230_; lean_object* v_readmeFile_3231_; uint8_t v_reservoir_3232_; lean_object* v_enableArtifactCache_x3f_3233_; uint8_t v_libPrefixOnWindows_3234_; uint8_t v_allowImportAll_3235_; lean_object* v_builtinLint_x3f_3236_; uint8_t v_fixedToolchain_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
v_toWorkspaceConfig_3205_ = lean_ctor_get(v_cfg_3204_, 0);
v_toLeanConfig_3206_ = lean_ctor_get(v_cfg_3204_, 1);
v_bootstrap_3207_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27);
v_extraDepTargets_3208_ = lean_ctor_get(v_cfg_3204_, 2);
v_precompileModules_3209_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3210_ = lean_ctor_get(v_cfg_3204_, 3);
v_srcDir_3211_ = lean_ctor_get(v_cfg_3204_, 4);
v_buildDir_3212_ = lean_ctor_get(v_cfg_3204_, 5);
v_leanLibDir_3213_ = lean_ctor_get(v_cfg_3204_, 6);
v_nativeLibDir_3214_ = lean_ctor_get(v_cfg_3204_, 7);
v_binDir_3215_ = lean_ctor_get(v_cfg_3204_, 8);
v_irDir_3216_ = lean_ctor_get(v_cfg_3204_, 9);
v_releaseRepo_3217_ = lean_ctor_get(v_cfg_3204_, 10);
v_buildArchive_3218_ = lean_ctor_get(v_cfg_3204_, 11);
v_preferReleaseBuild_3219_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27 + 2);
v_testDriver_3220_ = lean_ctor_get(v_cfg_3204_, 12);
v_testDriverArgs_3221_ = lean_ctor_get(v_cfg_3204_, 13);
v_lintDriver_3222_ = lean_ctor_get(v_cfg_3204_, 14);
v_lintDriverArgs_3223_ = lean_ctor_get(v_cfg_3204_, 15);
v_version_3224_ = lean_ctor_get(v_cfg_3204_, 16);
v_versionTags_3225_ = lean_ctor_get(v_cfg_3204_, 17);
v_description_3226_ = lean_ctor_get(v_cfg_3204_, 18);
v_keywords_3227_ = lean_ctor_get(v_cfg_3204_, 19);
v_homepage_3228_ = lean_ctor_get(v_cfg_3204_, 20);
v_license_3229_ = lean_ctor_get(v_cfg_3204_, 21);
v_licenseFiles_3230_ = lean_ctor_get(v_cfg_3204_, 22);
v_readmeFile_3231_ = lean_ctor_get(v_cfg_3204_, 23);
v_reservoir_3232_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3233_ = lean_ctor_get(v_cfg_3204_, 24);
v_libPrefixOnWindows_3234_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27 + 4);
v_allowImportAll_3235_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3236_ = lean_ctor_get(v_cfg_3204_, 26);
v_fixedToolchain_3237_ = lean_ctor_get_uint8(v_cfg_3204_, sizeof(void*)*27 + 6);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_cfg_3204_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_cfg_3204_, 25);
lean_dec(v_unused_3245_);
v___x_3239_ = v_cfg_3204_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_builtinLint_x3f_3236_);
lean_inc(v_enableArtifactCache_x3f_3233_);
lean_inc(v_readmeFile_3231_);
lean_inc(v_licenseFiles_3230_);
lean_inc(v_license_3229_);
lean_inc(v_homepage_3228_);
lean_inc(v_keywords_3227_);
lean_inc(v_description_3226_);
lean_inc(v_versionTags_3225_);
lean_inc(v_version_3224_);
lean_inc(v_lintDriverArgs_3223_);
lean_inc(v_lintDriver_3222_);
lean_inc(v_testDriverArgs_3221_);
lean_inc(v_testDriver_3220_);
lean_inc(v_buildArchive_3218_);
lean_inc(v_releaseRepo_3217_);
lean_inc(v_irDir_3216_);
lean_inc(v_binDir_3215_);
lean_inc(v_nativeLibDir_3214_);
lean_inc(v_leanLibDir_3213_);
lean_inc(v_buildDir_3212_);
lean_inc(v_srcDir_3211_);
lean_inc(v_moreGlobalServerArgs_3210_);
lean_inc(v_extraDepTargets_3208_);
lean_inc(v_toLeanConfig_3206_);
lean_inc(v_toWorkspaceConfig_3205_);
lean_dec(v_cfg_3204_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 25, v_val_3203_);
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_toWorkspaceConfig_3205_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_toLeanConfig_3206_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_extraDepTargets_3208_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_moreGlobalServerArgs_3210_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v_srcDir_3211_);
lean_ctor_set(v_reuseFailAlloc_3243_, 5, v_buildDir_3212_);
lean_ctor_set(v_reuseFailAlloc_3243_, 6, v_leanLibDir_3213_);
lean_ctor_set(v_reuseFailAlloc_3243_, 7, v_nativeLibDir_3214_);
lean_ctor_set(v_reuseFailAlloc_3243_, 8, v_binDir_3215_);
lean_ctor_set(v_reuseFailAlloc_3243_, 9, v_irDir_3216_);
lean_ctor_set(v_reuseFailAlloc_3243_, 10, v_releaseRepo_3217_);
lean_ctor_set(v_reuseFailAlloc_3243_, 11, v_buildArchive_3218_);
lean_ctor_set(v_reuseFailAlloc_3243_, 12, v_testDriver_3220_);
lean_ctor_set(v_reuseFailAlloc_3243_, 13, v_testDriverArgs_3221_);
lean_ctor_set(v_reuseFailAlloc_3243_, 14, v_lintDriver_3222_);
lean_ctor_set(v_reuseFailAlloc_3243_, 15, v_lintDriverArgs_3223_);
lean_ctor_set(v_reuseFailAlloc_3243_, 16, v_version_3224_);
lean_ctor_set(v_reuseFailAlloc_3243_, 17, v_versionTags_3225_);
lean_ctor_set(v_reuseFailAlloc_3243_, 18, v_description_3226_);
lean_ctor_set(v_reuseFailAlloc_3243_, 19, v_keywords_3227_);
lean_ctor_set(v_reuseFailAlloc_3243_, 20, v_homepage_3228_);
lean_ctor_set(v_reuseFailAlloc_3243_, 21, v_license_3229_);
lean_ctor_set(v_reuseFailAlloc_3243_, 22, v_licenseFiles_3230_);
lean_ctor_set(v_reuseFailAlloc_3243_, 23, v_readmeFile_3231_);
lean_ctor_set(v_reuseFailAlloc_3243_, 24, v_enableArtifactCache_x3f_3233_);
lean_ctor_set(v_reuseFailAlloc_3243_, 25, v_val_3203_);
lean_ctor_set(v_reuseFailAlloc_3243_, 26, v_builtinLint_x3f_3236_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27, v_bootstrap_3207_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27 + 1, v_precompileModules_3209_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3219_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27 + 3, v_reservoir_3232_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3234_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27 + 5, v_allowImportAll_3235_);
lean_ctor_set_uint8(v_reuseFailAlloc_3243_, sizeof(void*)*27 + 6, v_fixedToolchain_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object* v_f_3246_, lean_object* v_cfg_3247_){
_start:
{
lean_object* v_toWorkspaceConfig_3248_; lean_object* v_toLeanConfig_3249_; uint8_t v_bootstrap_3250_; lean_object* v_extraDepTargets_3251_; uint8_t v_precompileModules_3252_; lean_object* v_moreGlobalServerArgs_3253_; lean_object* v_srcDir_3254_; lean_object* v_buildDir_3255_; lean_object* v_leanLibDir_3256_; lean_object* v_nativeLibDir_3257_; lean_object* v_binDir_3258_; lean_object* v_irDir_3259_; lean_object* v_releaseRepo_3260_; lean_object* v_buildArchive_3261_; uint8_t v_preferReleaseBuild_3262_; lean_object* v_testDriver_3263_; lean_object* v_testDriverArgs_3264_; lean_object* v_lintDriver_3265_; lean_object* v_lintDriverArgs_3266_; lean_object* v_version_3267_; lean_object* v_versionTags_3268_; lean_object* v_description_3269_; lean_object* v_keywords_3270_; lean_object* v_homepage_3271_; lean_object* v_license_3272_; lean_object* v_licenseFiles_3273_; lean_object* v_readmeFile_3274_; uint8_t v_reservoir_3275_; lean_object* v_enableArtifactCache_x3f_3276_; lean_object* v_restoreAllArtifacts_x3f_3277_; uint8_t v_libPrefixOnWindows_3278_; uint8_t v_allowImportAll_3279_; lean_object* v_builtinLint_x3f_3280_; uint8_t v_fixedToolchain_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3289_; 
v_toWorkspaceConfig_3248_ = lean_ctor_get(v_cfg_3247_, 0);
v_toLeanConfig_3249_ = lean_ctor_get(v_cfg_3247_, 1);
v_bootstrap_3250_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27);
v_extraDepTargets_3251_ = lean_ctor_get(v_cfg_3247_, 2);
v_precompileModules_3252_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3253_ = lean_ctor_get(v_cfg_3247_, 3);
v_srcDir_3254_ = lean_ctor_get(v_cfg_3247_, 4);
v_buildDir_3255_ = lean_ctor_get(v_cfg_3247_, 5);
v_leanLibDir_3256_ = lean_ctor_get(v_cfg_3247_, 6);
v_nativeLibDir_3257_ = lean_ctor_get(v_cfg_3247_, 7);
v_binDir_3258_ = lean_ctor_get(v_cfg_3247_, 8);
v_irDir_3259_ = lean_ctor_get(v_cfg_3247_, 9);
v_releaseRepo_3260_ = lean_ctor_get(v_cfg_3247_, 10);
v_buildArchive_3261_ = lean_ctor_get(v_cfg_3247_, 11);
v_preferReleaseBuild_3262_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27 + 2);
v_testDriver_3263_ = lean_ctor_get(v_cfg_3247_, 12);
v_testDriverArgs_3264_ = lean_ctor_get(v_cfg_3247_, 13);
v_lintDriver_3265_ = lean_ctor_get(v_cfg_3247_, 14);
v_lintDriverArgs_3266_ = lean_ctor_get(v_cfg_3247_, 15);
v_version_3267_ = lean_ctor_get(v_cfg_3247_, 16);
v_versionTags_3268_ = lean_ctor_get(v_cfg_3247_, 17);
v_description_3269_ = lean_ctor_get(v_cfg_3247_, 18);
v_keywords_3270_ = lean_ctor_get(v_cfg_3247_, 19);
v_homepage_3271_ = lean_ctor_get(v_cfg_3247_, 20);
v_license_3272_ = lean_ctor_get(v_cfg_3247_, 21);
v_licenseFiles_3273_ = lean_ctor_get(v_cfg_3247_, 22);
v_readmeFile_3274_ = lean_ctor_get(v_cfg_3247_, 23);
v_reservoir_3275_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3276_ = lean_ctor_get(v_cfg_3247_, 24);
v_restoreAllArtifacts_x3f_3277_ = lean_ctor_get(v_cfg_3247_, 25);
v_libPrefixOnWindows_3278_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27 + 4);
v_allowImportAll_3279_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3280_ = lean_ctor_get(v_cfg_3247_, 26);
v_fixedToolchain_3281_ = lean_ctor_get_uint8(v_cfg_3247_, sizeof(void*)*27 + 6);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_cfg_3247_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3283_ = v_cfg_3247_;
v_isShared_3284_ = v_isSharedCheck_3289_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_builtinLint_x3f_3280_);
lean_inc(v_restoreAllArtifacts_x3f_3277_);
lean_inc(v_enableArtifactCache_x3f_3276_);
lean_inc(v_readmeFile_3274_);
lean_inc(v_licenseFiles_3273_);
lean_inc(v_license_3272_);
lean_inc(v_homepage_3271_);
lean_inc(v_keywords_3270_);
lean_inc(v_description_3269_);
lean_inc(v_versionTags_3268_);
lean_inc(v_version_3267_);
lean_inc(v_lintDriverArgs_3266_);
lean_inc(v_lintDriver_3265_);
lean_inc(v_testDriverArgs_3264_);
lean_inc(v_testDriver_3263_);
lean_inc(v_buildArchive_3261_);
lean_inc(v_releaseRepo_3260_);
lean_inc(v_irDir_3259_);
lean_inc(v_binDir_3258_);
lean_inc(v_nativeLibDir_3257_);
lean_inc(v_leanLibDir_3256_);
lean_inc(v_buildDir_3255_);
lean_inc(v_srcDir_3254_);
lean_inc(v_moreGlobalServerArgs_3253_);
lean_inc(v_extraDepTargets_3251_);
lean_inc(v_toLeanConfig_3249_);
lean_inc(v_toWorkspaceConfig_3248_);
lean_dec(v_cfg_3247_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3289_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3285_ = lean_apply_1(v_f_3246_, v_restoreAllArtifacts_x3f_3277_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 25, v___x_3285_);
v___x_3287_ = v___x_3283_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_toWorkspaceConfig_3248_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_toLeanConfig_3249_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v_extraDepTargets_3251_);
lean_ctor_set(v_reuseFailAlloc_3288_, 3, v_moreGlobalServerArgs_3253_);
lean_ctor_set(v_reuseFailAlloc_3288_, 4, v_srcDir_3254_);
lean_ctor_set(v_reuseFailAlloc_3288_, 5, v_buildDir_3255_);
lean_ctor_set(v_reuseFailAlloc_3288_, 6, v_leanLibDir_3256_);
lean_ctor_set(v_reuseFailAlloc_3288_, 7, v_nativeLibDir_3257_);
lean_ctor_set(v_reuseFailAlloc_3288_, 8, v_binDir_3258_);
lean_ctor_set(v_reuseFailAlloc_3288_, 9, v_irDir_3259_);
lean_ctor_set(v_reuseFailAlloc_3288_, 10, v_releaseRepo_3260_);
lean_ctor_set(v_reuseFailAlloc_3288_, 11, v_buildArchive_3261_);
lean_ctor_set(v_reuseFailAlloc_3288_, 12, v_testDriver_3263_);
lean_ctor_set(v_reuseFailAlloc_3288_, 13, v_testDriverArgs_3264_);
lean_ctor_set(v_reuseFailAlloc_3288_, 14, v_lintDriver_3265_);
lean_ctor_set(v_reuseFailAlloc_3288_, 15, v_lintDriverArgs_3266_);
lean_ctor_set(v_reuseFailAlloc_3288_, 16, v_version_3267_);
lean_ctor_set(v_reuseFailAlloc_3288_, 17, v_versionTags_3268_);
lean_ctor_set(v_reuseFailAlloc_3288_, 18, v_description_3269_);
lean_ctor_set(v_reuseFailAlloc_3288_, 19, v_keywords_3270_);
lean_ctor_set(v_reuseFailAlloc_3288_, 20, v_homepage_3271_);
lean_ctor_set(v_reuseFailAlloc_3288_, 21, v_license_3272_);
lean_ctor_set(v_reuseFailAlloc_3288_, 22, v_licenseFiles_3273_);
lean_ctor_set(v_reuseFailAlloc_3288_, 23, v_readmeFile_3274_);
lean_ctor_set(v_reuseFailAlloc_3288_, 24, v_enableArtifactCache_x3f_3276_);
lean_ctor_set(v_reuseFailAlloc_3288_, 25, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3288_, 26, v_builtinLint_x3f_3280_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27, v_bootstrap_3250_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27 + 1, v_precompileModules_3252_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3262_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27 + 3, v_reservoir_3275_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3278_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27 + 5, v_allowImportAll_3279_);
lean_ctor_set_uint8(v_reuseFailAlloc_3288_, sizeof(void*)*27 + 6, v_fixedToolchain_3281_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3298_, lean_object* v_n_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3));
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3301_, lean_object* v_n_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3301_, v_n_3302_);
lean_dec(v_n_3302_);
lean_dec(v_p_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3304_, lean_object* v_n_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3304_, v_n_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3307_, lean_object* v_n_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3307_, v_n_3308_);
lean_dec(v_n_3308_);
lean_dec(v_p_3307_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3310_, lean_object* v_n_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3310_, v_n_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3313_, lean_object* v_n_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3313_, v_n_3314_);
lean_dec(v_n_3314_);
lean_dec(v_p_3313_);
return v_res_3315_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_3316_){
_start:
{
uint8_t v_libPrefixOnWindows_3317_; 
v_libPrefixOnWindows_3317_ = lean_ctor_get_uint8(v_cfg_3316_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_3317_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_3318_){
_start:
{
uint8_t v_res_3319_; lean_object* v_r_3320_; 
v_res_3319_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(v_cfg_3318_);
lean_dec_ref(v_cfg_3318_);
v_r_3320_ = lean_box(v_res_3319_);
return v_r_3320_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_3321_, lean_object* v_cfg_3322_){
_start:
{
lean_object* v_toWorkspaceConfig_3323_; lean_object* v_toLeanConfig_3324_; uint8_t v_bootstrap_3325_; lean_object* v_extraDepTargets_3326_; uint8_t v_precompileModules_3327_; lean_object* v_moreGlobalServerArgs_3328_; lean_object* v_srcDir_3329_; lean_object* v_buildDir_3330_; lean_object* v_leanLibDir_3331_; lean_object* v_nativeLibDir_3332_; lean_object* v_binDir_3333_; lean_object* v_irDir_3334_; lean_object* v_releaseRepo_3335_; lean_object* v_buildArchive_3336_; uint8_t v_preferReleaseBuild_3337_; lean_object* v_testDriver_3338_; lean_object* v_testDriverArgs_3339_; lean_object* v_lintDriver_3340_; lean_object* v_lintDriverArgs_3341_; lean_object* v_version_3342_; lean_object* v_versionTags_3343_; lean_object* v_description_3344_; lean_object* v_keywords_3345_; lean_object* v_homepage_3346_; lean_object* v_license_3347_; lean_object* v_licenseFiles_3348_; lean_object* v_readmeFile_3349_; uint8_t v_reservoir_3350_; lean_object* v_enableArtifactCache_x3f_3351_; lean_object* v_restoreAllArtifacts_x3f_3352_; uint8_t v_allowImportAll_3353_; lean_object* v_builtinLint_x3f_3354_; uint8_t v_fixedToolchain_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
v_toWorkspaceConfig_3323_ = lean_ctor_get(v_cfg_3322_, 0);
v_toLeanConfig_3324_ = lean_ctor_get(v_cfg_3322_, 1);
v_bootstrap_3325_ = lean_ctor_get_uint8(v_cfg_3322_, sizeof(void*)*27);
v_extraDepTargets_3326_ = lean_ctor_get(v_cfg_3322_, 2);
v_precompileModules_3327_ = lean_ctor_get_uint8(v_cfg_3322_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3328_ = lean_ctor_get(v_cfg_3322_, 3);
v_srcDir_3329_ = lean_ctor_get(v_cfg_3322_, 4);
v_buildDir_3330_ = lean_ctor_get(v_cfg_3322_, 5);
v_leanLibDir_3331_ = lean_ctor_get(v_cfg_3322_, 6);
v_nativeLibDir_3332_ = lean_ctor_get(v_cfg_3322_, 7);
v_binDir_3333_ = lean_ctor_get(v_cfg_3322_, 8);
v_irDir_3334_ = lean_ctor_get(v_cfg_3322_, 9);
v_releaseRepo_3335_ = lean_ctor_get(v_cfg_3322_, 10);
v_buildArchive_3336_ = lean_ctor_get(v_cfg_3322_, 11);
v_preferReleaseBuild_3337_ = lean_ctor_get_uint8(v_cfg_3322_, sizeof(void*)*27 + 2);
v_testDriver_3338_ = lean_ctor_get(v_cfg_3322_, 12);
v_testDriverArgs_3339_ = lean_ctor_get(v_cfg_3322_, 13);
v_lintDriver_3340_ = lean_ctor_get(v_cfg_3322_, 14);
v_lintDriverArgs_3341_ = lean_ctor_get(v_cfg_3322_, 15);
v_version_3342_ = lean_ctor_get(v_cfg_3322_, 16);
v_versionTags_3343_ = lean_ctor_get(v_cfg_3322_, 17);
v_description_3344_ = lean_ctor_get(v_cfg_3322_, 18);
v_keywords_3345_ = lean_ctor_get(v_cfg_3322_, 19);
v_homepage_3346_ = lean_ctor_get(v_cfg_3322_, 20);
v_license_3347_ = lean_ctor_get(v_cfg_3322_, 21);
v_licenseFiles_3348_ = lean_ctor_get(v_cfg_3322_, 22);
v_readmeFile_3349_ = lean_ctor_get(v_cfg_3322_, 23);
v_reservoir_3350_ = lean_ctor_get_uint8(v_cfg_3322_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3351_ = lean_ctor_get(v_cfg_3322_, 24);
v_restoreAllArtifacts_x3f_3352_ = lean_ctor_get(v_cfg_3322_, 25);
v_allowImportAll_3353_ = lean_ctor_get_uint8(v_cfg_3322_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3354_ = lean_ctor_get(v_cfg_3322_, 26);
v_fixedToolchain_3355_ = lean_ctor_get_uint8(v_cfg_3322_, sizeof(void*)*27 + 6);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_cfg_3322_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v_cfg_3322_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_builtinLint_x3f_3354_);
lean_inc(v_restoreAllArtifacts_x3f_3352_);
lean_inc(v_enableArtifactCache_x3f_3351_);
lean_inc(v_readmeFile_3349_);
lean_inc(v_licenseFiles_3348_);
lean_inc(v_license_3347_);
lean_inc(v_homepage_3346_);
lean_inc(v_keywords_3345_);
lean_inc(v_description_3344_);
lean_inc(v_versionTags_3343_);
lean_inc(v_version_3342_);
lean_inc(v_lintDriverArgs_3341_);
lean_inc(v_lintDriver_3340_);
lean_inc(v_testDriverArgs_3339_);
lean_inc(v_testDriver_3338_);
lean_inc(v_buildArchive_3336_);
lean_inc(v_releaseRepo_3335_);
lean_inc(v_irDir_3334_);
lean_inc(v_binDir_3333_);
lean_inc(v_nativeLibDir_3332_);
lean_inc(v_leanLibDir_3331_);
lean_inc(v_buildDir_3330_);
lean_inc(v_srcDir_3329_);
lean_inc(v_moreGlobalServerArgs_3328_);
lean_inc(v_extraDepTargets_3326_);
lean_inc(v_toLeanConfig_3324_);
lean_inc(v_toWorkspaceConfig_3323_);
lean_dec(v_cfg_3322_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_toWorkspaceConfig_3323_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_toLeanConfig_3324_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_extraDepTargets_3326_);
lean_ctor_set(v_reuseFailAlloc_3361_, 3, v_moreGlobalServerArgs_3328_);
lean_ctor_set(v_reuseFailAlloc_3361_, 4, v_srcDir_3329_);
lean_ctor_set(v_reuseFailAlloc_3361_, 5, v_buildDir_3330_);
lean_ctor_set(v_reuseFailAlloc_3361_, 6, v_leanLibDir_3331_);
lean_ctor_set(v_reuseFailAlloc_3361_, 7, v_nativeLibDir_3332_);
lean_ctor_set(v_reuseFailAlloc_3361_, 8, v_binDir_3333_);
lean_ctor_set(v_reuseFailAlloc_3361_, 9, v_irDir_3334_);
lean_ctor_set(v_reuseFailAlloc_3361_, 10, v_releaseRepo_3335_);
lean_ctor_set(v_reuseFailAlloc_3361_, 11, v_buildArchive_3336_);
lean_ctor_set(v_reuseFailAlloc_3361_, 12, v_testDriver_3338_);
lean_ctor_set(v_reuseFailAlloc_3361_, 13, v_testDriverArgs_3339_);
lean_ctor_set(v_reuseFailAlloc_3361_, 14, v_lintDriver_3340_);
lean_ctor_set(v_reuseFailAlloc_3361_, 15, v_lintDriverArgs_3341_);
lean_ctor_set(v_reuseFailAlloc_3361_, 16, v_version_3342_);
lean_ctor_set(v_reuseFailAlloc_3361_, 17, v_versionTags_3343_);
lean_ctor_set(v_reuseFailAlloc_3361_, 18, v_description_3344_);
lean_ctor_set(v_reuseFailAlloc_3361_, 19, v_keywords_3345_);
lean_ctor_set(v_reuseFailAlloc_3361_, 20, v_homepage_3346_);
lean_ctor_set(v_reuseFailAlloc_3361_, 21, v_license_3347_);
lean_ctor_set(v_reuseFailAlloc_3361_, 22, v_licenseFiles_3348_);
lean_ctor_set(v_reuseFailAlloc_3361_, 23, v_readmeFile_3349_);
lean_ctor_set(v_reuseFailAlloc_3361_, 24, v_enableArtifactCache_x3f_3351_);
lean_ctor_set(v_reuseFailAlloc_3361_, 25, v_restoreAllArtifacts_x3f_3352_);
lean_ctor_set(v_reuseFailAlloc_3361_, 26, v_builtinLint_x3f_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*27, v_bootstrap_3325_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*27 + 1, v_precompileModules_3327_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3337_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*27 + 3, v_reservoir_3350_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*27 + 5, v_allowImportAll_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*27 + 6, v_fixedToolchain_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*27 + 4, v_val_3321_);
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_3363_, lean_object* v_cfg_3364_){
_start:
{
uint8_t v_val_137__boxed_3365_; lean_object* v_res_3366_; 
v_val_137__boxed_3365_ = lean_unbox(v_val_3363_);
v_res_3366_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(v_val_137__boxed_3365_, v_cfg_3364_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_3367_, lean_object* v_cfg_3368_){
_start:
{
lean_object* v_toWorkspaceConfig_3369_; lean_object* v_toLeanConfig_3370_; uint8_t v_bootstrap_3371_; lean_object* v_extraDepTargets_3372_; uint8_t v_precompileModules_3373_; lean_object* v_moreGlobalServerArgs_3374_; lean_object* v_srcDir_3375_; lean_object* v_buildDir_3376_; lean_object* v_leanLibDir_3377_; lean_object* v_nativeLibDir_3378_; lean_object* v_binDir_3379_; lean_object* v_irDir_3380_; lean_object* v_releaseRepo_3381_; lean_object* v_buildArchive_3382_; uint8_t v_preferReleaseBuild_3383_; lean_object* v_testDriver_3384_; lean_object* v_testDriverArgs_3385_; lean_object* v_lintDriver_3386_; lean_object* v_lintDriverArgs_3387_; lean_object* v_version_3388_; lean_object* v_versionTags_3389_; lean_object* v_description_3390_; lean_object* v_keywords_3391_; lean_object* v_homepage_3392_; lean_object* v_license_3393_; lean_object* v_licenseFiles_3394_; lean_object* v_readmeFile_3395_; uint8_t v_reservoir_3396_; lean_object* v_enableArtifactCache_x3f_3397_; lean_object* v_restoreAllArtifacts_x3f_3398_; uint8_t v_libPrefixOnWindows_3399_; uint8_t v_allowImportAll_3400_; lean_object* v_builtinLint_x3f_3401_; uint8_t v_fixedToolchain_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3412_; 
v_toWorkspaceConfig_3369_ = lean_ctor_get(v_cfg_3368_, 0);
v_toLeanConfig_3370_ = lean_ctor_get(v_cfg_3368_, 1);
v_bootstrap_3371_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27);
v_extraDepTargets_3372_ = lean_ctor_get(v_cfg_3368_, 2);
v_precompileModules_3373_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3374_ = lean_ctor_get(v_cfg_3368_, 3);
v_srcDir_3375_ = lean_ctor_get(v_cfg_3368_, 4);
v_buildDir_3376_ = lean_ctor_get(v_cfg_3368_, 5);
v_leanLibDir_3377_ = lean_ctor_get(v_cfg_3368_, 6);
v_nativeLibDir_3378_ = lean_ctor_get(v_cfg_3368_, 7);
v_binDir_3379_ = lean_ctor_get(v_cfg_3368_, 8);
v_irDir_3380_ = lean_ctor_get(v_cfg_3368_, 9);
v_releaseRepo_3381_ = lean_ctor_get(v_cfg_3368_, 10);
v_buildArchive_3382_ = lean_ctor_get(v_cfg_3368_, 11);
v_preferReleaseBuild_3383_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 2);
v_testDriver_3384_ = lean_ctor_get(v_cfg_3368_, 12);
v_testDriverArgs_3385_ = lean_ctor_get(v_cfg_3368_, 13);
v_lintDriver_3386_ = lean_ctor_get(v_cfg_3368_, 14);
v_lintDriverArgs_3387_ = lean_ctor_get(v_cfg_3368_, 15);
v_version_3388_ = lean_ctor_get(v_cfg_3368_, 16);
v_versionTags_3389_ = lean_ctor_get(v_cfg_3368_, 17);
v_description_3390_ = lean_ctor_get(v_cfg_3368_, 18);
v_keywords_3391_ = lean_ctor_get(v_cfg_3368_, 19);
v_homepage_3392_ = lean_ctor_get(v_cfg_3368_, 20);
v_license_3393_ = lean_ctor_get(v_cfg_3368_, 21);
v_licenseFiles_3394_ = lean_ctor_get(v_cfg_3368_, 22);
v_readmeFile_3395_ = lean_ctor_get(v_cfg_3368_, 23);
v_reservoir_3396_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3397_ = lean_ctor_get(v_cfg_3368_, 24);
v_restoreAllArtifacts_x3f_3398_ = lean_ctor_get(v_cfg_3368_, 25);
v_libPrefixOnWindows_3399_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 4);
v_allowImportAll_3400_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3401_ = lean_ctor_get(v_cfg_3368_, 26);
v_fixedToolchain_3402_ = lean_ctor_get_uint8(v_cfg_3368_, sizeof(void*)*27 + 6);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_cfg_3368_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3404_ = v_cfg_3368_;
v_isShared_3405_ = v_isSharedCheck_3412_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_builtinLint_x3f_3401_);
lean_inc(v_restoreAllArtifacts_x3f_3398_);
lean_inc(v_enableArtifactCache_x3f_3397_);
lean_inc(v_readmeFile_3395_);
lean_inc(v_licenseFiles_3394_);
lean_inc(v_license_3393_);
lean_inc(v_homepage_3392_);
lean_inc(v_keywords_3391_);
lean_inc(v_description_3390_);
lean_inc(v_versionTags_3389_);
lean_inc(v_version_3388_);
lean_inc(v_lintDriverArgs_3387_);
lean_inc(v_lintDriver_3386_);
lean_inc(v_testDriverArgs_3385_);
lean_inc(v_testDriver_3384_);
lean_inc(v_buildArchive_3382_);
lean_inc(v_releaseRepo_3381_);
lean_inc(v_irDir_3380_);
lean_inc(v_binDir_3379_);
lean_inc(v_nativeLibDir_3378_);
lean_inc(v_leanLibDir_3377_);
lean_inc(v_buildDir_3376_);
lean_inc(v_srcDir_3375_);
lean_inc(v_moreGlobalServerArgs_3374_);
lean_inc(v_extraDepTargets_3372_);
lean_inc(v_toLeanConfig_3370_);
lean_inc(v_toWorkspaceConfig_3369_);
lean_dec(v_cfg_3368_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3412_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3406_ = lean_box(v_libPrefixOnWindows_3399_);
v___x_3407_ = lean_apply_1(v_f_3367_, v___x_3406_);
if (v_isShared_3405_ == 0)
{
v___x_3409_ = v___x_3404_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_toWorkspaceConfig_3369_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_toLeanConfig_3370_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_extraDepTargets_3372_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_moreGlobalServerArgs_3374_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v_srcDir_3375_);
lean_ctor_set(v_reuseFailAlloc_3411_, 5, v_buildDir_3376_);
lean_ctor_set(v_reuseFailAlloc_3411_, 6, v_leanLibDir_3377_);
lean_ctor_set(v_reuseFailAlloc_3411_, 7, v_nativeLibDir_3378_);
lean_ctor_set(v_reuseFailAlloc_3411_, 8, v_binDir_3379_);
lean_ctor_set(v_reuseFailAlloc_3411_, 9, v_irDir_3380_);
lean_ctor_set(v_reuseFailAlloc_3411_, 10, v_releaseRepo_3381_);
lean_ctor_set(v_reuseFailAlloc_3411_, 11, v_buildArchive_3382_);
lean_ctor_set(v_reuseFailAlloc_3411_, 12, v_testDriver_3384_);
lean_ctor_set(v_reuseFailAlloc_3411_, 13, v_testDriverArgs_3385_);
lean_ctor_set(v_reuseFailAlloc_3411_, 14, v_lintDriver_3386_);
lean_ctor_set(v_reuseFailAlloc_3411_, 15, v_lintDriverArgs_3387_);
lean_ctor_set(v_reuseFailAlloc_3411_, 16, v_version_3388_);
lean_ctor_set(v_reuseFailAlloc_3411_, 17, v_versionTags_3389_);
lean_ctor_set(v_reuseFailAlloc_3411_, 18, v_description_3390_);
lean_ctor_set(v_reuseFailAlloc_3411_, 19, v_keywords_3391_);
lean_ctor_set(v_reuseFailAlloc_3411_, 20, v_homepage_3392_);
lean_ctor_set(v_reuseFailAlloc_3411_, 21, v_license_3393_);
lean_ctor_set(v_reuseFailAlloc_3411_, 22, v_licenseFiles_3394_);
lean_ctor_set(v_reuseFailAlloc_3411_, 23, v_readmeFile_3395_);
lean_ctor_set(v_reuseFailAlloc_3411_, 24, v_enableArtifactCache_x3f_3397_);
lean_ctor_set(v_reuseFailAlloc_3411_, 25, v_restoreAllArtifacts_x3f_3398_);
lean_ctor_set(v_reuseFailAlloc_3411_, 26, v_builtinLint_x3f_3401_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*27, v_bootstrap_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*27 + 1, v_precompileModules_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*27 + 3, v_reservoir_3396_);
v___x_3409_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
uint8_t v___x_3410_; 
v___x_3410_ = lean_unbox(v___x_3407_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*27 + 4, v___x_3410_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*27 + 5, v_allowImportAll_3400_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*27 + 6, v_fixedToolchain_3402_);
return v___x_3409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3421_, lean_object* v_n_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3424_, lean_object* v_n_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3424_, v_n_3425_);
lean_dec(v_n_3425_);
lean_dec(v_p_3424_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3427_, lean_object* v_n_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3427_, v_n_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3430_, lean_object* v_n_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3430_, v_n_3431_);
lean_dec(v_n_3431_);
lean_dec(v_p_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_3433_){
_start:
{
uint8_t v_allowImportAll_3434_; 
v_allowImportAll_3434_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*27 + 5);
return v_allowImportAll_3434_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_3435_){
_start:
{
uint8_t v_res_3436_; lean_object* v_r_3437_; 
v_res_3436_ = l_Lake_PackageConfig_allowImportAll___proj___lam__0(v_cfg_3435_);
lean_dec_ref(v_cfg_3435_);
v_r_3437_ = lean_box(v_res_3436_);
return v_r_3437_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t v_val_3438_, lean_object* v_cfg_3439_){
_start:
{
lean_object* v_toWorkspaceConfig_3440_; lean_object* v_toLeanConfig_3441_; uint8_t v_bootstrap_3442_; lean_object* v_extraDepTargets_3443_; uint8_t v_precompileModules_3444_; lean_object* v_moreGlobalServerArgs_3445_; lean_object* v_srcDir_3446_; lean_object* v_buildDir_3447_; lean_object* v_leanLibDir_3448_; lean_object* v_nativeLibDir_3449_; lean_object* v_binDir_3450_; lean_object* v_irDir_3451_; lean_object* v_releaseRepo_3452_; lean_object* v_buildArchive_3453_; uint8_t v_preferReleaseBuild_3454_; lean_object* v_testDriver_3455_; lean_object* v_testDriverArgs_3456_; lean_object* v_lintDriver_3457_; lean_object* v_lintDriverArgs_3458_; lean_object* v_version_3459_; lean_object* v_versionTags_3460_; lean_object* v_description_3461_; lean_object* v_keywords_3462_; lean_object* v_homepage_3463_; lean_object* v_license_3464_; lean_object* v_licenseFiles_3465_; lean_object* v_readmeFile_3466_; uint8_t v_reservoir_3467_; lean_object* v_enableArtifactCache_x3f_3468_; lean_object* v_restoreAllArtifacts_x3f_3469_; uint8_t v_libPrefixOnWindows_3470_; lean_object* v_builtinLint_x3f_3471_; uint8_t v_fixedToolchain_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
v_toWorkspaceConfig_3440_ = lean_ctor_get(v_cfg_3439_, 0);
v_toLeanConfig_3441_ = lean_ctor_get(v_cfg_3439_, 1);
v_bootstrap_3442_ = lean_ctor_get_uint8(v_cfg_3439_, sizeof(void*)*27);
v_extraDepTargets_3443_ = lean_ctor_get(v_cfg_3439_, 2);
v_precompileModules_3444_ = lean_ctor_get_uint8(v_cfg_3439_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3445_ = lean_ctor_get(v_cfg_3439_, 3);
v_srcDir_3446_ = lean_ctor_get(v_cfg_3439_, 4);
v_buildDir_3447_ = lean_ctor_get(v_cfg_3439_, 5);
v_leanLibDir_3448_ = lean_ctor_get(v_cfg_3439_, 6);
v_nativeLibDir_3449_ = lean_ctor_get(v_cfg_3439_, 7);
v_binDir_3450_ = lean_ctor_get(v_cfg_3439_, 8);
v_irDir_3451_ = lean_ctor_get(v_cfg_3439_, 9);
v_releaseRepo_3452_ = lean_ctor_get(v_cfg_3439_, 10);
v_buildArchive_3453_ = lean_ctor_get(v_cfg_3439_, 11);
v_preferReleaseBuild_3454_ = lean_ctor_get_uint8(v_cfg_3439_, sizeof(void*)*27 + 2);
v_testDriver_3455_ = lean_ctor_get(v_cfg_3439_, 12);
v_testDriverArgs_3456_ = lean_ctor_get(v_cfg_3439_, 13);
v_lintDriver_3457_ = lean_ctor_get(v_cfg_3439_, 14);
v_lintDriverArgs_3458_ = lean_ctor_get(v_cfg_3439_, 15);
v_version_3459_ = lean_ctor_get(v_cfg_3439_, 16);
v_versionTags_3460_ = lean_ctor_get(v_cfg_3439_, 17);
v_description_3461_ = lean_ctor_get(v_cfg_3439_, 18);
v_keywords_3462_ = lean_ctor_get(v_cfg_3439_, 19);
v_homepage_3463_ = lean_ctor_get(v_cfg_3439_, 20);
v_license_3464_ = lean_ctor_get(v_cfg_3439_, 21);
v_licenseFiles_3465_ = lean_ctor_get(v_cfg_3439_, 22);
v_readmeFile_3466_ = lean_ctor_get(v_cfg_3439_, 23);
v_reservoir_3467_ = lean_ctor_get_uint8(v_cfg_3439_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3468_ = lean_ctor_get(v_cfg_3439_, 24);
v_restoreAllArtifacts_x3f_3469_ = lean_ctor_get(v_cfg_3439_, 25);
v_libPrefixOnWindows_3470_ = lean_ctor_get_uint8(v_cfg_3439_, sizeof(void*)*27 + 4);
v_builtinLint_x3f_3471_ = lean_ctor_get(v_cfg_3439_, 26);
v_fixedToolchain_3472_ = lean_ctor_get_uint8(v_cfg_3439_, sizeof(void*)*27 + 6);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_cfg_3439_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v_cfg_3439_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_builtinLint_x3f_3471_);
lean_inc(v_restoreAllArtifacts_x3f_3469_);
lean_inc(v_enableArtifactCache_x3f_3468_);
lean_inc(v_readmeFile_3466_);
lean_inc(v_licenseFiles_3465_);
lean_inc(v_license_3464_);
lean_inc(v_homepage_3463_);
lean_inc(v_keywords_3462_);
lean_inc(v_description_3461_);
lean_inc(v_versionTags_3460_);
lean_inc(v_version_3459_);
lean_inc(v_lintDriverArgs_3458_);
lean_inc(v_lintDriver_3457_);
lean_inc(v_testDriverArgs_3456_);
lean_inc(v_testDriver_3455_);
lean_inc(v_buildArchive_3453_);
lean_inc(v_releaseRepo_3452_);
lean_inc(v_irDir_3451_);
lean_inc(v_binDir_3450_);
lean_inc(v_nativeLibDir_3449_);
lean_inc(v_leanLibDir_3448_);
lean_inc(v_buildDir_3447_);
lean_inc(v_srcDir_3446_);
lean_inc(v_moreGlobalServerArgs_3445_);
lean_inc(v_extraDepTargets_3443_);
lean_inc(v_toLeanConfig_3441_);
lean_inc(v_toWorkspaceConfig_3440_);
lean_dec(v_cfg_3439_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_toWorkspaceConfig_3440_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_toLeanConfig_3441_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_extraDepTargets_3443_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_moreGlobalServerArgs_3445_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_srcDir_3446_);
lean_ctor_set(v_reuseFailAlloc_3478_, 5, v_buildDir_3447_);
lean_ctor_set(v_reuseFailAlloc_3478_, 6, v_leanLibDir_3448_);
lean_ctor_set(v_reuseFailAlloc_3478_, 7, v_nativeLibDir_3449_);
lean_ctor_set(v_reuseFailAlloc_3478_, 8, v_binDir_3450_);
lean_ctor_set(v_reuseFailAlloc_3478_, 9, v_irDir_3451_);
lean_ctor_set(v_reuseFailAlloc_3478_, 10, v_releaseRepo_3452_);
lean_ctor_set(v_reuseFailAlloc_3478_, 11, v_buildArchive_3453_);
lean_ctor_set(v_reuseFailAlloc_3478_, 12, v_testDriver_3455_);
lean_ctor_set(v_reuseFailAlloc_3478_, 13, v_testDriverArgs_3456_);
lean_ctor_set(v_reuseFailAlloc_3478_, 14, v_lintDriver_3457_);
lean_ctor_set(v_reuseFailAlloc_3478_, 15, v_lintDriverArgs_3458_);
lean_ctor_set(v_reuseFailAlloc_3478_, 16, v_version_3459_);
lean_ctor_set(v_reuseFailAlloc_3478_, 17, v_versionTags_3460_);
lean_ctor_set(v_reuseFailAlloc_3478_, 18, v_description_3461_);
lean_ctor_set(v_reuseFailAlloc_3478_, 19, v_keywords_3462_);
lean_ctor_set(v_reuseFailAlloc_3478_, 20, v_homepage_3463_);
lean_ctor_set(v_reuseFailAlloc_3478_, 21, v_license_3464_);
lean_ctor_set(v_reuseFailAlloc_3478_, 22, v_licenseFiles_3465_);
lean_ctor_set(v_reuseFailAlloc_3478_, 23, v_readmeFile_3466_);
lean_ctor_set(v_reuseFailAlloc_3478_, 24, v_enableArtifactCache_x3f_3468_);
lean_ctor_set(v_reuseFailAlloc_3478_, 25, v_restoreAllArtifacts_x3f_3469_);
lean_ctor_set(v_reuseFailAlloc_3478_, 26, v_builtinLint_x3f_3471_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*27, v_bootstrap_3442_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*27 + 1, v_precompileModules_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3454_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*27 + 3, v_reservoir_3467_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3470_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*27 + 6, v_fixedToolchain_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*27 + 5, v_val_3438_);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_3480_, lean_object* v_cfg_3481_){
_start:
{
uint8_t v_val_137__boxed_3482_; lean_object* v_res_3483_; 
v_val_137__boxed_3482_ = lean_unbox(v_val_3480_);
v_res_3483_ = l_Lake_PackageConfig_allowImportAll___proj___lam__1(v_val_137__boxed_3482_, v_cfg_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* v_f_3484_, lean_object* v_cfg_3485_){
_start:
{
lean_object* v_toWorkspaceConfig_3486_; lean_object* v_toLeanConfig_3487_; uint8_t v_bootstrap_3488_; lean_object* v_extraDepTargets_3489_; uint8_t v_precompileModules_3490_; lean_object* v_moreGlobalServerArgs_3491_; lean_object* v_srcDir_3492_; lean_object* v_buildDir_3493_; lean_object* v_leanLibDir_3494_; lean_object* v_nativeLibDir_3495_; lean_object* v_binDir_3496_; lean_object* v_irDir_3497_; lean_object* v_releaseRepo_3498_; lean_object* v_buildArchive_3499_; uint8_t v_preferReleaseBuild_3500_; lean_object* v_testDriver_3501_; lean_object* v_testDriverArgs_3502_; lean_object* v_lintDriver_3503_; lean_object* v_lintDriverArgs_3504_; lean_object* v_version_3505_; lean_object* v_versionTags_3506_; lean_object* v_description_3507_; lean_object* v_keywords_3508_; lean_object* v_homepage_3509_; lean_object* v_license_3510_; lean_object* v_licenseFiles_3511_; lean_object* v_readmeFile_3512_; uint8_t v_reservoir_3513_; lean_object* v_enableArtifactCache_x3f_3514_; lean_object* v_restoreAllArtifacts_x3f_3515_; uint8_t v_libPrefixOnWindows_3516_; uint8_t v_allowImportAll_3517_; lean_object* v_builtinLint_x3f_3518_; uint8_t v_fixedToolchain_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3529_; 
v_toWorkspaceConfig_3486_ = lean_ctor_get(v_cfg_3485_, 0);
v_toLeanConfig_3487_ = lean_ctor_get(v_cfg_3485_, 1);
v_bootstrap_3488_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27);
v_extraDepTargets_3489_ = lean_ctor_get(v_cfg_3485_, 2);
v_precompileModules_3490_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3491_ = lean_ctor_get(v_cfg_3485_, 3);
v_srcDir_3492_ = lean_ctor_get(v_cfg_3485_, 4);
v_buildDir_3493_ = lean_ctor_get(v_cfg_3485_, 5);
v_leanLibDir_3494_ = lean_ctor_get(v_cfg_3485_, 6);
v_nativeLibDir_3495_ = lean_ctor_get(v_cfg_3485_, 7);
v_binDir_3496_ = lean_ctor_get(v_cfg_3485_, 8);
v_irDir_3497_ = lean_ctor_get(v_cfg_3485_, 9);
v_releaseRepo_3498_ = lean_ctor_get(v_cfg_3485_, 10);
v_buildArchive_3499_ = lean_ctor_get(v_cfg_3485_, 11);
v_preferReleaseBuild_3500_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27 + 2);
v_testDriver_3501_ = lean_ctor_get(v_cfg_3485_, 12);
v_testDriverArgs_3502_ = lean_ctor_get(v_cfg_3485_, 13);
v_lintDriver_3503_ = lean_ctor_get(v_cfg_3485_, 14);
v_lintDriverArgs_3504_ = lean_ctor_get(v_cfg_3485_, 15);
v_version_3505_ = lean_ctor_get(v_cfg_3485_, 16);
v_versionTags_3506_ = lean_ctor_get(v_cfg_3485_, 17);
v_description_3507_ = lean_ctor_get(v_cfg_3485_, 18);
v_keywords_3508_ = lean_ctor_get(v_cfg_3485_, 19);
v_homepage_3509_ = lean_ctor_get(v_cfg_3485_, 20);
v_license_3510_ = lean_ctor_get(v_cfg_3485_, 21);
v_licenseFiles_3511_ = lean_ctor_get(v_cfg_3485_, 22);
v_readmeFile_3512_ = lean_ctor_get(v_cfg_3485_, 23);
v_reservoir_3513_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3514_ = lean_ctor_get(v_cfg_3485_, 24);
v_restoreAllArtifacts_x3f_3515_ = lean_ctor_get(v_cfg_3485_, 25);
v_libPrefixOnWindows_3516_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27 + 4);
v_allowImportAll_3517_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3518_ = lean_ctor_get(v_cfg_3485_, 26);
v_fixedToolchain_3519_ = lean_ctor_get_uint8(v_cfg_3485_, sizeof(void*)*27 + 6);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_cfg_3485_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3521_ = v_cfg_3485_;
v_isShared_3522_ = v_isSharedCheck_3529_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_builtinLint_x3f_3518_);
lean_inc(v_restoreAllArtifacts_x3f_3515_);
lean_inc(v_enableArtifactCache_x3f_3514_);
lean_inc(v_readmeFile_3512_);
lean_inc(v_licenseFiles_3511_);
lean_inc(v_license_3510_);
lean_inc(v_homepage_3509_);
lean_inc(v_keywords_3508_);
lean_inc(v_description_3507_);
lean_inc(v_versionTags_3506_);
lean_inc(v_version_3505_);
lean_inc(v_lintDriverArgs_3504_);
lean_inc(v_lintDriver_3503_);
lean_inc(v_testDriverArgs_3502_);
lean_inc(v_testDriver_3501_);
lean_inc(v_buildArchive_3499_);
lean_inc(v_releaseRepo_3498_);
lean_inc(v_irDir_3497_);
lean_inc(v_binDir_3496_);
lean_inc(v_nativeLibDir_3495_);
lean_inc(v_leanLibDir_3494_);
lean_inc(v_buildDir_3493_);
lean_inc(v_srcDir_3492_);
lean_inc(v_moreGlobalServerArgs_3491_);
lean_inc(v_extraDepTargets_3489_);
lean_inc(v_toLeanConfig_3487_);
lean_inc(v_toWorkspaceConfig_3486_);
lean_dec(v_cfg_3485_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3529_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3523_ = lean_box(v_allowImportAll_3517_);
v___x_3524_ = lean_apply_1(v_f_3484_, v___x_3523_);
if (v_isShared_3522_ == 0)
{
v___x_3526_ = v___x_3521_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_toWorkspaceConfig_3486_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_toLeanConfig_3487_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_extraDepTargets_3489_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_moreGlobalServerArgs_3491_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v_srcDir_3492_);
lean_ctor_set(v_reuseFailAlloc_3528_, 5, v_buildDir_3493_);
lean_ctor_set(v_reuseFailAlloc_3528_, 6, v_leanLibDir_3494_);
lean_ctor_set(v_reuseFailAlloc_3528_, 7, v_nativeLibDir_3495_);
lean_ctor_set(v_reuseFailAlloc_3528_, 8, v_binDir_3496_);
lean_ctor_set(v_reuseFailAlloc_3528_, 9, v_irDir_3497_);
lean_ctor_set(v_reuseFailAlloc_3528_, 10, v_releaseRepo_3498_);
lean_ctor_set(v_reuseFailAlloc_3528_, 11, v_buildArchive_3499_);
lean_ctor_set(v_reuseFailAlloc_3528_, 12, v_testDriver_3501_);
lean_ctor_set(v_reuseFailAlloc_3528_, 13, v_testDriverArgs_3502_);
lean_ctor_set(v_reuseFailAlloc_3528_, 14, v_lintDriver_3503_);
lean_ctor_set(v_reuseFailAlloc_3528_, 15, v_lintDriverArgs_3504_);
lean_ctor_set(v_reuseFailAlloc_3528_, 16, v_version_3505_);
lean_ctor_set(v_reuseFailAlloc_3528_, 17, v_versionTags_3506_);
lean_ctor_set(v_reuseFailAlloc_3528_, 18, v_description_3507_);
lean_ctor_set(v_reuseFailAlloc_3528_, 19, v_keywords_3508_);
lean_ctor_set(v_reuseFailAlloc_3528_, 20, v_homepage_3509_);
lean_ctor_set(v_reuseFailAlloc_3528_, 21, v_license_3510_);
lean_ctor_set(v_reuseFailAlloc_3528_, 22, v_licenseFiles_3511_);
lean_ctor_set(v_reuseFailAlloc_3528_, 23, v_readmeFile_3512_);
lean_ctor_set(v_reuseFailAlloc_3528_, 24, v_enableArtifactCache_x3f_3514_);
lean_ctor_set(v_reuseFailAlloc_3528_, 25, v_restoreAllArtifacts_x3f_3515_);
lean_ctor_set(v_reuseFailAlloc_3528_, 26, v_builtinLint_x3f_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*27, v_bootstrap_3488_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*27 + 1, v_precompileModules_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3500_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*27 + 3, v_reservoir_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3516_);
v___x_3526_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_unbox(v___x_3524_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*27 + 5, v___x_3527_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*27 + 6, v_fixedToolchain_3519_);
return v___x_3526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3538_, lean_object* v_n_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3541_, lean_object* v_n_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3541_, v_n_3542_);
lean_dec(v_n_3542_);
lean_dec(v_p_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3544_, lean_object* v_n_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3544_, v_n_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3547_, lean_object* v_n_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3547_, v_n_3548_);
lean_dec(v_n_3548_);
lean_dec(v_p_3547_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0(lean_object* v_cfg_3550_){
_start:
{
lean_object* v_builtinLint_x3f_3551_; 
v_builtinLint_x3f_3551_ = lean_ctor_get(v_cfg_3550_, 26);
lean_inc(v_builtinLint_x3f_3551_);
return v_builtinLint_x3f_3551_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0___boxed(lean_object* v_cfg_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0(v_cfg_3552_);
lean_dec_ref(v_cfg_3552_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__1(lean_object* v_val_3554_, lean_object* v_cfg_3555_){
_start:
{
lean_object* v_toWorkspaceConfig_3556_; lean_object* v_toLeanConfig_3557_; uint8_t v_bootstrap_3558_; lean_object* v_extraDepTargets_3559_; uint8_t v_precompileModules_3560_; lean_object* v_moreGlobalServerArgs_3561_; lean_object* v_srcDir_3562_; lean_object* v_buildDir_3563_; lean_object* v_leanLibDir_3564_; lean_object* v_nativeLibDir_3565_; lean_object* v_binDir_3566_; lean_object* v_irDir_3567_; lean_object* v_releaseRepo_3568_; lean_object* v_buildArchive_3569_; uint8_t v_preferReleaseBuild_3570_; lean_object* v_testDriver_3571_; lean_object* v_testDriverArgs_3572_; lean_object* v_lintDriver_3573_; lean_object* v_lintDriverArgs_3574_; lean_object* v_version_3575_; lean_object* v_versionTags_3576_; lean_object* v_description_3577_; lean_object* v_keywords_3578_; lean_object* v_homepage_3579_; lean_object* v_license_3580_; lean_object* v_licenseFiles_3581_; lean_object* v_readmeFile_3582_; uint8_t v_reservoir_3583_; lean_object* v_enableArtifactCache_x3f_3584_; lean_object* v_restoreAllArtifacts_x3f_3585_; uint8_t v_libPrefixOnWindows_3586_; uint8_t v_allowImportAll_3587_; uint8_t v_fixedToolchain_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
v_toWorkspaceConfig_3556_ = lean_ctor_get(v_cfg_3555_, 0);
v_toLeanConfig_3557_ = lean_ctor_get(v_cfg_3555_, 1);
v_bootstrap_3558_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27);
v_extraDepTargets_3559_ = lean_ctor_get(v_cfg_3555_, 2);
v_precompileModules_3560_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3561_ = lean_ctor_get(v_cfg_3555_, 3);
v_srcDir_3562_ = lean_ctor_get(v_cfg_3555_, 4);
v_buildDir_3563_ = lean_ctor_get(v_cfg_3555_, 5);
v_leanLibDir_3564_ = lean_ctor_get(v_cfg_3555_, 6);
v_nativeLibDir_3565_ = lean_ctor_get(v_cfg_3555_, 7);
v_binDir_3566_ = lean_ctor_get(v_cfg_3555_, 8);
v_irDir_3567_ = lean_ctor_get(v_cfg_3555_, 9);
v_releaseRepo_3568_ = lean_ctor_get(v_cfg_3555_, 10);
v_buildArchive_3569_ = lean_ctor_get(v_cfg_3555_, 11);
v_preferReleaseBuild_3570_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27 + 2);
v_testDriver_3571_ = lean_ctor_get(v_cfg_3555_, 12);
v_testDriverArgs_3572_ = lean_ctor_get(v_cfg_3555_, 13);
v_lintDriver_3573_ = lean_ctor_get(v_cfg_3555_, 14);
v_lintDriverArgs_3574_ = lean_ctor_get(v_cfg_3555_, 15);
v_version_3575_ = lean_ctor_get(v_cfg_3555_, 16);
v_versionTags_3576_ = lean_ctor_get(v_cfg_3555_, 17);
v_description_3577_ = lean_ctor_get(v_cfg_3555_, 18);
v_keywords_3578_ = lean_ctor_get(v_cfg_3555_, 19);
v_homepage_3579_ = lean_ctor_get(v_cfg_3555_, 20);
v_license_3580_ = lean_ctor_get(v_cfg_3555_, 21);
v_licenseFiles_3581_ = lean_ctor_get(v_cfg_3555_, 22);
v_readmeFile_3582_ = lean_ctor_get(v_cfg_3555_, 23);
v_reservoir_3583_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3584_ = lean_ctor_get(v_cfg_3555_, 24);
v_restoreAllArtifacts_x3f_3585_ = lean_ctor_get(v_cfg_3555_, 25);
v_libPrefixOnWindows_3586_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27 + 4);
v_allowImportAll_3587_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27 + 5);
v_fixedToolchain_3588_ = lean_ctor_get_uint8(v_cfg_3555_, sizeof(void*)*27 + 6);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_cfg_3555_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v_cfg_3555_, 26);
lean_dec(v_unused_3596_);
v___x_3590_ = v_cfg_3555_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3585_);
lean_inc(v_enableArtifactCache_x3f_3584_);
lean_inc(v_readmeFile_3582_);
lean_inc(v_licenseFiles_3581_);
lean_inc(v_license_3580_);
lean_inc(v_homepage_3579_);
lean_inc(v_keywords_3578_);
lean_inc(v_description_3577_);
lean_inc(v_versionTags_3576_);
lean_inc(v_version_3575_);
lean_inc(v_lintDriverArgs_3574_);
lean_inc(v_lintDriver_3573_);
lean_inc(v_testDriverArgs_3572_);
lean_inc(v_testDriver_3571_);
lean_inc(v_buildArchive_3569_);
lean_inc(v_releaseRepo_3568_);
lean_inc(v_irDir_3567_);
lean_inc(v_binDir_3566_);
lean_inc(v_nativeLibDir_3565_);
lean_inc(v_leanLibDir_3564_);
lean_inc(v_buildDir_3563_);
lean_inc(v_srcDir_3562_);
lean_inc(v_moreGlobalServerArgs_3561_);
lean_inc(v_extraDepTargets_3559_);
lean_inc(v_toLeanConfig_3557_);
lean_inc(v_toWorkspaceConfig_3556_);
lean_dec(v_cfg_3555_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 26, v_val_3554_);
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_toWorkspaceConfig_3556_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_toLeanConfig_3557_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_extraDepTargets_3559_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_moreGlobalServerArgs_3561_);
lean_ctor_set(v_reuseFailAlloc_3594_, 4, v_srcDir_3562_);
lean_ctor_set(v_reuseFailAlloc_3594_, 5, v_buildDir_3563_);
lean_ctor_set(v_reuseFailAlloc_3594_, 6, v_leanLibDir_3564_);
lean_ctor_set(v_reuseFailAlloc_3594_, 7, v_nativeLibDir_3565_);
lean_ctor_set(v_reuseFailAlloc_3594_, 8, v_binDir_3566_);
lean_ctor_set(v_reuseFailAlloc_3594_, 9, v_irDir_3567_);
lean_ctor_set(v_reuseFailAlloc_3594_, 10, v_releaseRepo_3568_);
lean_ctor_set(v_reuseFailAlloc_3594_, 11, v_buildArchive_3569_);
lean_ctor_set(v_reuseFailAlloc_3594_, 12, v_testDriver_3571_);
lean_ctor_set(v_reuseFailAlloc_3594_, 13, v_testDriverArgs_3572_);
lean_ctor_set(v_reuseFailAlloc_3594_, 14, v_lintDriver_3573_);
lean_ctor_set(v_reuseFailAlloc_3594_, 15, v_lintDriverArgs_3574_);
lean_ctor_set(v_reuseFailAlloc_3594_, 16, v_version_3575_);
lean_ctor_set(v_reuseFailAlloc_3594_, 17, v_versionTags_3576_);
lean_ctor_set(v_reuseFailAlloc_3594_, 18, v_description_3577_);
lean_ctor_set(v_reuseFailAlloc_3594_, 19, v_keywords_3578_);
lean_ctor_set(v_reuseFailAlloc_3594_, 20, v_homepage_3579_);
lean_ctor_set(v_reuseFailAlloc_3594_, 21, v_license_3580_);
lean_ctor_set(v_reuseFailAlloc_3594_, 22, v_licenseFiles_3581_);
lean_ctor_set(v_reuseFailAlloc_3594_, 23, v_readmeFile_3582_);
lean_ctor_set(v_reuseFailAlloc_3594_, 24, v_enableArtifactCache_x3f_3584_);
lean_ctor_set(v_reuseFailAlloc_3594_, 25, v_restoreAllArtifacts_x3f_3585_);
lean_ctor_set(v_reuseFailAlloc_3594_, 26, v_val_3554_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27, v_bootstrap_3558_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27 + 1, v_precompileModules_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3570_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27 + 3, v_reservoir_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3586_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27 + 5, v_allowImportAll_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3594_, sizeof(void*)*27 + 6, v_fixedToolchain_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__2(lean_object* v_f_3597_, lean_object* v_cfg_3598_){
_start:
{
lean_object* v_toWorkspaceConfig_3599_; lean_object* v_toLeanConfig_3600_; uint8_t v_bootstrap_3601_; lean_object* v_extraDepTargets_3602_; uint8_t v_precompileModules_3603_; lean_object* v_moreGlobalServerArgs_3604_; lean_object* v_srcDir_3605_; lean_object* v_buildDir_3606_; lean_object* v_leanLibDir_3607_; lean_object* v_nativeLibDir_3608_; lean_object* v_binDir_3609_; lean_object* v_irDir_3610_; lean_object* v_releaseRepo_3611_; lean_object* v_buildArchive_3612_; uint8_t v_preferReleaseBuild_3613_; lean_object* v_testDriver_3614_; lean_object* v_testDriverArgs_3615_; lean_object* v_lintDriver_3616_; lean_object* v_lintDriverArgs_3617_; lean_object* v_version_3618_; lean_object* v_versionTags_3619_; lean_object* v_description_3620_; lean_object* v_keywords_3621_; lean_object* v_homepage_3622_; lean_object* v_license_3623_; lean_object* v_licenseFiles_3624_; lean_object* v_readmeFile_3625_; uint8_t v_reservoir_3626_; lean_object* v_enableArtifactCache_x3f_3627_; lean_object* v_restoreAllArtifacts_x3f_3628_; uint8_t v_libPrefixOnWindows_3629_; uint8_t v_allowImportAll_3630_; lean_object* v_builtinLint_x3f_3631_; uint8_t v_fixedToolchain_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3640_; 
v_toWorkspaceConfig_3599_ = lean_ctor_get(v_cfg_3598_, 0);
v_toLeanConfig_3600_ = lean_ctor_get(v_cfg_3598_, 1);
v_bootstrap_3601_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27);
v_extraDepTargets_3602_ = lean_ctor_get(v_cfg_3598_, 2);
v_precompileModules_3603_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3604_ = lean_ctor_get(v_cfg_3598_, 3);
v_srcDir_3605_ = lean_ctor_get(v_cfg_3598_, 4);
v_buildDir_3606_ = lean_ctor_get(v_cfg_3598_, 5);
v_leanLibDir_3607_ = lean_ctor_get(v_cfg_3598_, 6);
v_nativeLibDir_3608_ = lean_ctor_get(v_cfg_3598_, 7);
v_binDir_3609_ = lean_ctor_get(v_cfg_3598_, 8);
v_irDir_3610_ = lean_ctor_get(v_cfg_3598_, 9);
v_releaseRepo_3611_ = lean_ctor_get(v_cfg_3598_, 10);
v_buildArchive_3612_ = lean_ctor_get(v_cfg_3598_, 11);
v_preferReleaseBuild_3613_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27 + 2);
v_testDriver_3614_ = lean_ctor_get(v_cfg_3598_, 12);
v_testDriverArgs_3615_ = lean_ctor_get(v_cfg_3598_, 13);
v_lintDriver_3616_ = lean_ctor_get(v_cfg_3598_, 14);
v_lintDriverArgs_3617_ = lean_ctor_get(v_cfg_3598_, 15);
v_version_3618_ = lean_ctor_get(v_cfg_3598_, 16);
v_versionTags_3619_ = lean_ctor_get(v_cfg_3598_, 17);
v_description_3620_ = lean_ctor_get(v_cfg_3598_, 18);
v_keywords_3621_ = lean_ctor_get(v_cfg_3598_, 19);
v_homepage_3622_ = lean_ctor_get(v_cfg_3598_, 20);
v_license_3623_ = lean_ctor_get(v_cfg_3598_, 21);
v_licenseFiles_3624_ = lean_ctor_get(v_cfg_3598_, 22);
v_readmeFile_3625_ = lean_ctor_get(v_cfg_3598_, 23);
v_reservoir_3626_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3627_ = lean_ctor_get(v_cfg_3598_, 24);
v_restoreAllArtifacts_x3f_3628_ = lean_ctor_get(v_cfg_3598_, 25);
v_libPrefixOnWindows_3629_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27 + 4);
v_allowImportAll_3630_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3631_ = lean_ctor_get(v_cfg_3598_, 26);
v_fixedToolchain_3632_ = lean_ctor_get_uint8(v_cfg_3598_, sizeof(void*)*27 + 6);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_cfg_3598_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3634_ = v_cfg_3598_;
v_isShared_3635_ = v_isSharedCheck_3640_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_builtinLint_x3f_3631_);
lean_inc(v_restoreAllArtifacts_x3f_3628_);
lean_inc(v_enableArtifactCache_x3f_3627_);
lean_inc(v_readmeFile_3625_);
lean_inc(v_licenseFiles_3624_);
lean_inc(v_license_3623_);
lean_inc(v_homepage_3622_);
lean_inc(v_keywords_3621_);
lean_inc(v_description_3620_);
lean_inc(v_versionTags_3619_);
lean_inc(v_version_3618_);
lean_inc(v_lintDriverArgs_3617_);
lean_inc(v_lintDriver_3616_);
lean_inc(v_testDriverArgs_3615_);
lean_inc(v_testDriver_3614_);
lean_inc(v_buildArchive_3612_);
lean_inc(v_releaseRepo_3611_);
lean_inc(v_irDir_3610_);
lean_inc(v_binDir_3609_);
lean_inc(v_nativeLibDir_3608_);
lean_inc(v_leanLibDir_3607_);
lean_inc(v_buildDir_3606_);
lean_inc(v_srcDir_3605_);
lean_inc(v_moreGlobalServerArgs_3604_);
lean_inc(v_extraDepTargets_3602_);
lean_inc(v_toLeanConfig_3600_);
lean_inc(v_toWorkspaceConfig_3599_);
lean_dec(v_cfg_3598_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3640_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_apply_1(v_f_3597_, v_builtinLint_x3f_3631_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 26, v___x_3636_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_toWorkspaceConfig_3599_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_toLeanConfig_3600_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_extraDepTargets_3602_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_moreGlobalServerArgs_3604_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_srcDir_3605_);
lean_ctor_set(v_reuseFailAlloc_3639_, 5, v_buildDir_3606_);
lean_ctor_set(v_reuseFailAlloc_3639_, 6, v_leanLibDir_3607_);
lean_ctor_set(v_reuseFailAlloc_3639_, 7, v_nativeLibDir_3608_);
lean_ctor_set(v_reuseFailAlloc_3639_, 8, v_binDir_3609_);
lean_ctor_set(v_reuseFailAlloc_3639_, 9, v_irDir_3610_);
lean_ctor_set(v_reuseFailAlloc_3639_, 10, v_releaseRepo_3611_);
lean_ctor_set(v_reuseFailAlloc_3639_, 11, v_buildArchive_3612_);
lean_ctor_set(v_reuseFailAlloc_3639_, 12, v_testDriver_3614_);
lean_ctor_set(v_reuseFailAlloc_3639_, 13, v_testDriverArgs_3615_);
lean_ctor_set(v_reuseFailAlloc_3639_, 14, v_lintDriver_3616_);
lean_ctor_set(v_reuseFailAlloc_3639_, 15, v_lintDriverArgs_3617_);
lean_ctor_set(v_reuseFailAlloc_3639_, 16, v_version_3618_);
lean_ctor_set(v_reuseFailAlloc_3639_, 17, v_versionTags_3619_);
lean_ctor_set(v_reuseFailAlloc_3639_, 18, v_description_3620_);
lean_ctor_set(v_reuseFailAlloc_3639_, 19, v_keywords_3621_);
lean_ctor_set(v_reuseFailAlloc_3639_, 20, v_homepage_3622_);
lean_ctor_set(v_reuseFailAlloc_3639_, 21, v_license_3623_);
lean_ctor_set(v_reuseFailAlloc_3639_, 22, v_licenseFiles_3624_);
lean_ctor_set(v_reuseFailAlloc_3639_, 23, v_readmeFile_3625_);
lean_ctor_set(v_reuseFailAlloc_3639_, 24, v_enableArtifactCache_x3f_3627_);
lean_ctor_set(v_reuseFailAlloc_3639_, 25, v_restoreAllArtifacts_x3f_3628_);
lean_ctor_set(v_reuseFailAlloc_3639_, 26, v___x_3636_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27, v_bootstrap_3601_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27 + 1, v_precompileModules_3603_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27 + 3, v_reservoir_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27 + 5, v_allowImportAll_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*27 + 6, v_fixedToolchain_3632_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object* v_p_3649_, lean_object* v_n_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = ((lean_object*)(l_Lake_PackageConfig_builtinLint_x3f___proj___closed__3));
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object* v_p_3652_, lean_object* v_n_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_3652_, v_n_3653_);
lean_dec(v_n_3653_);
lean_dec(v_p_3652_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object* v_p_3655_, lean_object* v_n_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_3655_, v_n_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object* v_p_3658_, lean_object* v_n_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField(v_p_3658_, v_n_3659_);
lean_dec(v_n_3659_);
lean_dec(v_p_3658_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object* v_p_3661_, lean_object* v_n_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_3661_, v_n_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object* v_p_3664_, lean_object* v_n_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lake_PackageConfig_builtinLint_instConfigField(v_p_3664_, v_n_3665_);
lean_dec(v_n_3665_);
lean_dec(v_p_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___lam__0(lean_object* v_cfg_3667_){
_start:
{
uint8_t v_fixedToolchain_3668_; 
v_fixedToolchain_3668_ = lean_ctor_get_uint8(v_cfg_3667_, sizeof(void*)*27 + 6);
return v_fixedToolchain_3668_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed(lean_object* v_cfg_3669_){
_start:
{
uint8_t v_res_3670_; lean_object* v_r_3671_; 
v_res_3670_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__0(v_cfg_3669_);
lean_dec_ref(v_cfg_3669_);
v_r_3671_ = lean_box(v_res_3670_);
return v_r_3671_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1(uint8_t v_val_3672_, lean_object* v_cfg_3673_){
_start:
{
lean_object* v_toWorkspaceConfig_3674_; lean_object* v_toLeanConfig_3675_; uint8_t v_bootstrap_3676_; lean_object* v_extraDepTargets_3677_; uint8_t v_precompileModules_3678_; lean_object* v_moreGlobalServerArgs_3679_; lean_object* v_srcDir_3680_; lean_object* v_buildDir_3681_; lean_object* v_leanLibDir_3682_; lean_object* v_nativeLibDir_3683_; lean_object* v_binDir_3684_; lean_object* v_irDir_3685_; lean_object* v_releaseRepo_3686_; lean_object* v_buildArchive_3687_; uint8_t v_preferReleaseBuild_3688_; lean_object* v_testDriver_3689_; lean_object* v_testDriverArgs_3690_; lean_object* v_lintDriver_3691_; lean_object* v_lintDriverArgs_3692_; lean_object* v_version_3693_; lean_object* v_versionTags_3694_; lean_object* v_description_3695_; lean_object* v_keywords_3696_; lean_object* v_homepage_3697_; lean_object* v_license_3698_; lean_object* v_licenseFiles_3699_; lean_object* v_readmeFile_3700_; uint8_t v_reservoir_3701_; lean_object* v_enableArtifactCache_x3f_3702_; lean_object* v_restoreAllArtifacts_x3f_3703_; uint8_t v_libPrefixOnWindows_3704_; uint8_t v_allowImportAll_3705_; lean_object* v_builtinLint_x3f_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
v_toWorkspaceConfig_3674_ = lean_ctor_get(v_cfg_3673_, 0);
v_toLeanConfig_3675_ = lean_ctor_get(v_cfg_3673_, 1);
v_bootstrap_3676_ = lean_ctor_get_uint8(v_cfg_3673_, sizeof(void*)*27);
v_extraDepTargets_3677_ = lean_ctor_get(v_cfg_3673_, 2);
v_precompileModules_3678_ = lean_ctor_get_uint8(v_cfg_3673_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3679_ = lean_ctor_get(v_cfg_3673_, 3);
v_srcDir_3680_ = lean_ctor_get(v_cfg_3673_, 4);
v_buildDir_3681_ = lean_ctor_get(v_cfg_3673_, 5);
v_leanLibDir_3682_ = lean_ctor_get(v_cfg_3673_, 6);
v_nativeLibDir_3683_ = lean_ctor_get(v_cfg_3673_, 7);
v_binDir_3684_ = lean_ctor_get(v_cfg_3673_, 8);
v_irDir_3685_ = lean_ctor_get(v_cfg_3673_, 9);
v_releaseRepo_3686_ = lean_ctor_get(v_cfg_3673_, 10);
v_buildArchive_3687_ = lean_ctor_get(v_cfg_3673_, 11);
v_preferReleaseBuild_3688_ = lean_ctor_get_uint8(v_cfg_3673_, sizeof(void*)*27 + 2);
v_testDriver_3689_ = lean_ctor_get(v_cfg_3673_, 12);
v_testDriverArgs_3690_ = lean_ctor_get(v_cfg_3673_, 13);
v_lintDriver_3691_ = lean_ctor_get(v_cfg_3673_, 14);
v_lintDriverArgs_3692_ = lean_ctor_get(v_cfg_3673_, 15);
v_version_3693_ = lean_ctor_get(v_cfg_3673_, 16);
v_versionTags_3694_ = lean_ctor_get(v_cfg_3673_, 17);
v_description_3695_ = lean_ctor_get(v_cfg_3673_, 18);
v_keywords_3696_ = lean_ctor_get(v_cfg_3673_, 19);
v_homepage_3697_ = lean_ctor_get(v_cfg_3673_, 20);
v_license_3698_ = lean_ctor_get(v_cfg_3673_, 21);
v_licenseFiles_3699_ = lean_ctor_get(v_cfg_3673_, 22);
v_readmeFile_3700_ = lean_ctor_get(v_cfg_3673_, 23);
v_reservoir_3701_ = lean_ctor_get_uint8(v_cfg_3673_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3702_ = lean_ctor_get(v_cfg_3673_, 24);
v_restoreAllArtifacts_x3f_3703_ = lean_ctor_get(v_cfg_3673_, 25);
v_libPrefixOnWindows_3704_ = lean_ctor_get_uint8(v_cfg_3673_, sizeof(void*)*27 + 4);
v_allowImportAll_3705_ = lean_ctor_get_uint8(v_cfg_3673_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3706_ = lean_ctor_get(v_cfg_3673_, 26);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_cfg_3673_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v_cfg_3673_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_builtinLint_x3f_3706_);
lean_inc(v_restoreAllArtifacts_x3f_3703_);
lean_inc(v_enableArtifactCache_x3f_3702_);
lean_inc(v_readmeFile_3700_);
lean_inc(v_licenseFiles_3699_);
lean_inc(v_license_3698_);
lean_inc(v_homepage_3697_);
lean_inc(v_keywords_3696_);
lean_inc(v_description_3695_);
lean_inc(v_versionTags_3694_);
lean_inc(v_version_3693_);
lean_inc(v_lintDriverArgs_3692_);
lean_inc(v_lintDriver_3691_);
lean_inc(v_testDriverArgs_3690_);
lean_inc(v_testDriver_3689_);
lean_inc(v_buildArchive_3687_);
lean_inc(v_releaseRepo_3686_);
lean_inc(v_irDir_3685_);
lean_inc(v_binDir_3684_);
lean_inc(v_nativeLibDir_3683_);
lean_inc(v_leanLibDir_3682_);
lean_inc(v_buildDir_3681_);
lean_inc(v_srcDir_3680_);
lean_inc(v_moreGlobalServerArgs_3679_);
lean_inc(v_extraDepTargets_3677_);
lean_inc(v_toLeanConfig_3675_);
lean_inc(v_toWorkspaceConfig_3674_);
lean_dec(v_cfg_3673_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_toWorkspaceConfig_3674_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_toLeanConfig_3675_);
lean_ctor_set(v_reuseFailAlloc_3712_, 2, v_extraDepTargets_3677_);
lean_ctor_set(v_reuseFailAlloc_3712_, 3, v_moreGlobalServerArgs_3679_);
lean_ctor_set(v_reuseFailAlloc_3712_, 4, v_srcDir_3680_);
lean_ctor_set(v_reuseFailAlloc_3712_, 5, v_buildDir_3681_);
lean_ctor_set(v_reuseFailAlloc_3712_, 6, v_leanLibDir_3682_);
lean_ctor_set(v_reuseFailAlloc_3712_, 7, v_nativeLibDir_3683_);
lean_ctor_set(v_reuseFailAlloc_3712_, 8, v_binDir_3684_);
lean_ctor_set(v_reuseFailAlloc_3712_, 9, v_irDir_3685_);
lean_ctor_set(v_reuseFailAlloc_3712_, 10, v_releaseRepo_3686_);
lean_ctor_set(v_reuseFailAlloc_3712_, 11, v_buildArchive_3687_);
lean_ctor_set(v_reuseFailAlloc_3712_, 12, v_testDriver_3689_);
lean_ctor_set(v_reuseFailAlloc_3712_, 13, v_testDriverArgs_3690_);
lean_ctor_set(v_reuseFailAlloc_3712_, 14, v_lintDriver_3691_);
lean_ctor_set(v_reuseFailAlloc_3712_, 15, v_lintDriverArgs_3692_);
lean_ctor_set(v_reuseFailAlloc_3712_, 16, v_version_3693_);
lean_ctor_set(v_reuseFailAlloc_3712_, 17, v_versionTags_3694_);
lean_ctor_set(v_reuseFailAlloc_3712_, 18, v_description_3695_);
lean_ctor_set(v_reuseFailAlloc_3712_, 19, v_keywords_3696_);
lean_ctor_set(v_reuseFailAlloc_3712_, 20, v_homepage_3697_);
lean_ctor_set(v_reuseFailAlloc_3712_, 21, v_license_3698_);
lean_ctor_set(v_reuseFailAlloc_3712_, 22, v_licenseFiles_3699_);
lean_ctor_set(v_reuseFailAlloc_3712_, 23, v_readmeFile_3700_);
lean_ctor_set(v_reuseFailAlloc_3712_, 24, v_enableArtifactCache_x3f_3702_);
lean_ctor_set(v_reuseFailAlloc_3712_, 25, v_restoreAllArtifacts_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3712_, 26, v_builtinLint_x3f_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, sizeof(void*)*27, v_bootstrap_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, sizeof(void*)*27 + 1, v_precompileModules_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3688_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, sizeof(void*)*27 + 3, v_reservoir_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, sizeof(void*)*27 + 5, v_allowImportAll_3705_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_ctor_set_uint8(v___x_3711_, sizeof(void*)*27 + 6, v_val_3672_);
return v___x_3711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed(lean_object* v_val_3714_, lean_object* v_cfg_3715_){
_start:
{
uint8_t v_val_137__boxed_3716_; lean_object* v_res_3717_; 
v_val_137__boxed_3716_ = lean_unbox(v_val_3714_);
v_res_3717_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__1(v_val_137__boxed_3716_, v_cfg_3715_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__2(lean_object* v_f_3718_, lean_object* v_cfg_3719_){
_start:
{
lean_object* v_toWorkspaceConfig_3720_; lean_object* v_toLeanConfig_3721_; uint8_t v_bootstrap_3722_; lean_object* v_extraDepTargets_3723_; uint8_t v_precompileModules_3724_; lean_object* v_moreGlobalServerArgs_3725_; lean_object* v_srcDir_3726_; lean_object* v_buildDir_3727_; lean_object* v_leanLibDir_3728_; lean_object* v_nativeLibDir_3729_; lean_object* v_binDir_3730_; lean_object* v_irDir_3731_; lean_object* v_releaseRepo_3732_; lean_object* v_buildArchive_3733_; uint8_t v_preferReleaseBuild_3734_; lean_object* v_testDriver_3735_; lean_object* v_testDriverArgs_3736_; lean_object* v_lintDriver_3737_; lean_object* v_lintDriverArgs_3738_; lean_object* v_version_3739_; lean_object* v_versionTags_3740_; lean_object* v_description_3741_; lean_object* v_keywords_3742_; lean_object* v_homepage_3743_; lean_object* v_license_3744_; lean_object* v_licenseFiles_3745_; lean_object* v_readmeFile_3746_; uint8_t v_reservoir_3747_; lean_object* v_enableArtifactCache_x3f_3748_; lean_object* v_restoreAllArtifacts_x3f_3749_; uint8_t v_libPrefixOnWindows_3750_; uint8_t v_allowImportAll_3751_; lean_object* v_builtinLint_x3f_3752_; uint8_t v_fixedToolchain_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3763_; 
v_toWorkspaceConfig_3720_ = lean_ctor_get(v_cfg_3719_, 0);
v_toLeanConfig_3721_ = lean_ctor_get(v_cfg_3719_, 1);
v_bootstrap_3722_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27);
v_extraDepTargets_3723_ = lean_ctor_get(v_cfg_3719_, 2);
v_precompileModules_3724_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3725_ = lean_ctor_get(v_cfg_3719_, 3);
v_srcDir_3726_ = lean_ctor_get(v_cfg_3719_, 4);
v_buildDir_3727_ = lean_ctor_get(v_cfg_3719_, 5);
v_leanLibDir_3728_ = lean_ctor_get(v_cfg_3719_, 6);
v_nativeLibDir_3729_ = lean_ctor_get(v_cfg_3719_, 7);
v_binDir_3730_ = lean_ctor_get(v_cfg_3719_, 8);
v_irDir_3731_ = lean_ctor_get(v_cfg_3719_, 9);
v_releaseRepo_3732_ = lean_ctor_get(v_cfg_3719_, 10);
v_buildArchive_3733_ = lean_ctor_get(v_cfg_3719_, 11);
v_preferReleaseBuild_3734_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27 + 2);
v_testDriver_3735_ = lean_ctor_get(v_cfg_3719_, 12);
v_testDriverArgs_3736_ = lean_ctor_get(v_cfg_3719_, 13);
v_lintDriver_3737_ = lean_ctor_get(v_cfg_3719_, 14);
v_lintDriverArgs_3738_ = lean_ctor_get(v_cfg_3719_, 15);
v_version_3739_ = lean_ctor_get(v_cfg_3719_, 16);
v_versionTags_3740_ = lean_ctor_get(v_cfg_3719_, 17);
v_description_3741_ = lean_ctor_get(v_cfg_3719_, 18);
v_keywords_3742_ = lean_ctor_get(v_cfg_3719_, 19);
v_homepage_3743_ = lean_ctor_get(v_cfg_3719_, 20);
v_license_3744_ = lean_ctor_get(v_cfg_3719_, 21);
v_licenseFiles_3745_ = lean_ctor_get(v_cfg_3719_, 22);
v_readmeFile_3746_ = lean_ctor_get(v_cfg_3719_, 23);
v_reservoir_3747_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3748_ = lean_ctor_get(v_cfg_3719_, 24);
v_restoreAllArtifacts_x3f_3749_ = lean_ctor_get(v_cfg_3719_, 25);
v_libPrefixOnWindows_3750_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27 + 4);
v_allowImportAll_3751_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3752_ = lean_ctor_get(v_cfg_3719_, 26);
v_fixedToolchain_3753_ = lean_ctor_get_uint8(v_cfg_3719_, sizeof(void*)*27 + 6);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_cfg_3719_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3755_ = v_cfg_3719_;
v_isShared_3756_ = v_isSharedCheck_3763_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_builtinLint_x3f_3752_);
lean_inc(v_restoreAllArtifacts_x3f_3749_);
lean_inc(v_enableArtifactCache_x3f_3748_);
lean_inc(v_readmeFile_3746_);
lean_inc(v_licenseFiles_3745_);
lean_inc(v_license_3744_);
lean_inc(v_homepage_3743_);
lean_inc(v_keywords_3742_);
lean_inc(v_description_3741_);
lean_inc(v_versionTags_3740_);
lean_inc(v_version_3739_);
lean_inc(v_lintDriverArgs_3738_);
lean_inc(v_lintDriver_3737_);
lean_inc(v_testDriverArgs_3736_);
lean_inc(v_testDriver_3735_);
lean_inc(v_buildArchive_3733_);
lean_inc(v_releaseRepo_3732_);
lean_inc(v_irDir_3731_);
lean_inc(v_binDir_3730_);
lean_inc(v_nativeLibDir_3729_);
lean_inc(v_leanLibDir_3728_);
lean_inc(v_buildDir_3727_);
lean_inc(v_srcDir_3726_);
lean_inc(v_moreGlobalServerArgs_3725_);
lean_inc(v_extraDepTargets_3723_);
lean_inc(v_toLeanConfig_3721_);
lean_inc(v_toWorkspaceConfig_3720_);
lean_dec(v_cfg_3719_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3763_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3757_ = lean_box(v_fixedToolchain_3753_);
v___x_3758_ = lean_apply_1(v_f_3718_, v___x_3757_);
if (v_isShared_3756_ == 0)
{
v___x_3760_ = v___x_3755_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_toWorkspaceConfig_3720_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_toLeanConfig_3721_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_extraDepTargets_3723_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_moreGlobalServerArgs_3725_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_srcDir_3726_);
lean_ctor_set(v_reuseFailAlloc_3762_, 5, v_buildDir_3727_);
lean_ctor_set(v_reuseFailAlloc_3762_, 6, v_leanLibDir_3728_);
lean_ctor_set(v_reuseFailAlloc_3762_, 7, v_nativeLibDir_3729_);
lean_ctor_set(v_reuseFailAlloc_3762_, 8, v_binDir_3730_);
lean_ctor_set(v_reuseFailAlloc_3762_, 9, v_irDir_3731_);
lean_ctor_set(v_reuseFailAlloc_3762_, 10, v_releaseRepo_3732_);
lean_ctor_set(v_reuseFailAlloc_3762_, 11, v_buildArchive_3733_);
lean_ctor_set(v_reuseFailAlloc_3762_, 12, v_testDriver_3735_);
lean_ctor_set(v_reuseFailAlloc_3762_, 13, v_testDriverArgs_3736_);
lean_ctor_set(v_reuseFailAlloc_3762_, 14, v_lintDriver_3737_);
lean_ctor_set(v_reuseFailAlloc_3762_, 15, v_lintDriverArgs_3738_);
lean_ctor_set(v_reuseFailAlloc_3762_, 16, v_version_3739_);
lean_ctor_set(v_reuseFailAlloc_3762_, 17, v_versionTags_3740_);
lean_ctor_set(v_reuseFailAlloc_3762_, 18, v_description_3741_);
lean_ctor_set(v_reuseFailAlloc_3762_, 19, v_keywords_3742_);
lean_ctor_set(v_reuseFailAlloc_3762_, 20, v_homepage_3743_);
lean_ctor_set(v_reuseFailAlloc_3762_, 21, v_license_3744_);
lean_ctor_set(v_reuseFailAlloc_3762_, 22, v_licenseFiles_3745_);
lean_ctor_set(v_reuseFailAlloc_3762_, 23, v_readmeFile_3746_);
lean_ctor_set(v_reuseFailAlloc_3762_, 24, v_enableArtifactCache_x3f_3748_);
lean_ctor_set(v_reuseFailAlloc_3762_, 25, v_restoreAllArtifacts_x3f_3749_);
lean_ctor_set(v_reuseFailAlloc_3762_, 26, v_builtinLint_x3f_3752_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*27, v_bootstrap_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*27 + 1, v_precompileModules_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3734_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*27 + 3, v_reservoir_3747_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*27 + 5, v_allowImportAll_3751_);
v___x_3760_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
uint8_t v___x_3761_; 
v___x_3761_ = lean_unbox(v___x_3758_);
lean_ctor_set_uint8(v___x_3760_, sizeof(void*)*27 + 6, v___x_3761_);
return v___x_3760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_3772_, lean_object* v_n_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___closed__3));
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_3775_, lean_object* v_n_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3775_, v_n_3776_);
lean_dec(v_n_3776_);
lean_dec(v_p_3775_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_3778_, lean_object* v_n_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3778_, v_n_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_3781_, lean_object* v_n_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_3781_, v_n_3782_);
lean_dec(v_n_3782_);
lean_dec(v_p_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* v_cfg_3784_){
_start:
{
lean_object* v_toWorkspaceConfig_3785_; 
v_toWorkspaceConfig_3785_ = lean_ctor_get(v_cfg_3784_, 0);
lean_inc_ref(v_toWorkspaceConfig_3785_);
return v_toWorkspaceConfig_3785_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* v_cfg_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(v_cfg_3786_);
lean_dec_ref(v_cfg_3786_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* v_val_3788_, lean_object* v_cfg_3789_){
_start:
{
lean_object* v_toLeanConfig_3790_; uint8_t v_bootstrap_3791_; lean_object* v_extraDepTargets_3792_; uint8_t v_precompileModules_3793_; lean_object* v_moreGlobalServerArgs_3794_; lean_object* v_srcDir_3795_; lean_object* v_buildDir_3796_; lean_object* v_leanLibDir_3797_; lean_object* v_nativeLibDir_3798_; lean_object* v_binDir_3799_; lean_object* v_irDir_3800_; lean_object* v_releaseRepo_3801_; lean_object* v_buildArchive_3802_; uint8_t v_preferReleaseBuild_3803_; lean_object* v_testDriver_3804_; lean_object* v_testDriverArgs_3805_; lean_object* v_lintDriver_3806_; lean_object* v_lintDriverArgs_3807_; lean_object* v_version_3808_; lean_object* v_versionTags_3809_; lean_object* v_description_3810_; lean_object* v_keywords_3811_; lean_object* v_homepage_3812_; lean_object* v_license_3813_; lean_object* v_licenseFiles_3814_; lean_object* v_readmeFile_3815_; uint8_t v_reservoir_3816_; lean_object* v_enableArtifactCache_x3f_3817_; lean_object* v_restoreAllArtifacts_x3f_3818_; uint8_t v_libPrefixOnWindows_3819_; uint8_t v_allowImportAll_3820_; lean_object* v_builtinLint_x3f_3821_; uint8_t v_fixedToolchain_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
v_toLeanConfig_3790_ = lean_ctor_get(v_cfg_3789_, 1);
v_bootstrap_3791_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27);
v_extraDepTargets_3792_ = lean_ctor_get(v_cfg_3789_, 2);
v_precompileModules_3793_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3794_ = lean_ctor_get(v_cfg_3789_, 3);
v_srcDir_3795_ = lean_ctor_get(v_cfg_3789_, 4);
v_buildDir_3796_ = lean_ctor_get(v_cfg_3789_, 5);
v_leanLibDir_3797_ = lean_ctor_get(v_cfg_3789_, 6);
v_nativeLibDir_3798_ = lean_ctor_get(v_cfg_3789_, 7);
v_binDir_3799_ = lean_ctor_get(v_cfg_3789_, 8);
v_irDir_3800_ = lean_ctor_get(v_cfg_3789_, 9);
v_releaseRepo_3801_ = lean_ctor_get(v_cfg_3789_, 10);
v_buildArchive_3802_ = lean_ctor_get(v_cfg_3789_, 11);
v_preferReleaseBuild_3803_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27 + 2);
v_testDriver_3804_ = lean_ctor_get(v_cfg_3789_, 12);
v_testDriverArgs_3805_ = lean_ctor_get(v_cfg_3789_, 13);
v_lintDriver_3806_ = lean_ctor_get(v_cfg_3789_, 14);
v_lintDriverArgs_3807_ = lean_ctor_get(v_cfg_3789_, 15);
v_version_3808_ = lean_ctor_get(v_cfg_3789_, 16);
v_versionTags_3809_ = lean_ctor_get(v_cfg_3789_, 17);
v_description_3810_ = lean_ctor_get(v_cfg_3789_, 18);
v_keywords_3811_ = lean_ctor_get(v_cfg_3789_, 19);
v_homepage_3812_ = lean_ctor_get(v_cfg_3789_, 20);
v_license_3813_ = lean_ctor_get(v_cfg_3789_, 21);
v_licenseFiles_3814_ = lean_ctor_get(v_cfg_3789_, 22);
v_readmeFile_3815_ = lean_ctor_get(v_cfg_3789_, 23);
v_reservoir_3816_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3817_ = lean_ctor_get(v_cfg_3789_, 24);
v_restoreAllArtifacts_x3f_3818_ = lean_ctor_get(v_cfg_3789_, 25);
v_libPrefixOnWindows_3819_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27 + 4);
v_allowImportAll_3820_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3821_ = lean_ctor_get(v_cfg_3789_, 26);
v_fixedToolchain_3822_ = lean_ctor_get_uint8(v_cfg_3789_, sizeof(void*)*27 + 6);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_cfg_3789_);
if (v_isSharedCheck_3829_ == 0)
{
lean_object* v_unused_3830_; 
v_unused_3830_ = lean_ctor_get(v_cfg_3789_, 0);
lean_dec(v_unused_3830_);
v___x_3824_ = v_cfg_3789_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_builtinLint_x3f_3821_);
lean_inc(v_restoreAllArtifacts_x3f_3818_);
lean_inc(v_enableArtifactCache_x3f_3817_);
lean_inc(v_readmeFile_3815_);
lean_inc(v_licenseFiles_3814_);
lean_inc(v_license_3813_);
lean_inc(v_homepage_3812_);
lean_inc(v_keywords_3811_);
lean_inc(v_description_3810_);
lean_inc(v_versionTags_3809_);
lean_inc(v_version_3808_);
lean_inc(v_lintDriverArgs_3807_);
lean_inc(v_lintDriver_3806_);
lean_inc(v_testDriverArgs_3805_);
lean_inc(v_testDriver_3804_);
lean_inc(v_buildArchive_3802_);
lean_inc(v_releaseRepo_3801_);
lean_inc(v_irDir_3800_);
lean_inc(v_binDir_3799_);
lean_inc(v_nativeLibDir_3798_);
lean_inc(v_leanLibDir_3797_);
lean_inc(v_buildDir_3796_);
lean_inc(v_srcDir_3795_);
lean_inc(v_moreGlobalServerArgs_3794_);
lean_inc(v_extraDepTargets_3792_);
lean_inc(v_toLeanConfig_3790_);
lean_dec(v_cfg_3789_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v_val_3788_);
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_val_3788_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_toLeanConfig_3790_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v_extraDepTargets_3792_);
lean_ctor_set(v_reuseFailAlloc_3828_, 3, v_moreGlobalServerArgs_3794_);
lean_ctor_set(v_reuseFailAlloc_3828_, 4, v_srcDir_3795_);
lean_ctor_set(v_reuseFailAlloc_3828_, 5, v_buildDir_3796_);
lean_ctor_set(v_reuseFailAlloc_3828_, 6, v_leanLibDir_3797_);
lean_ctor_set(v_reuseFailAlloc_3828_, 7, v_nativeLibDir_3798_);
lean_ctor_set(v_reuseFailAlloc_3828_, 8, v_binDir_3799_);
lean_ctor_set(v_reuseFailAlloc_3828_, 9, v_irDir_3800_);
lean_ctor_set(v_reuseFailAlloc_3828_, 10, v_releaseRepo_3801_);
lean_ctor_set(v_reuseFailAlloc_3828_, 11, v_buildArchive_3802_);
lean_ctor_set(v_reuseFailAlloc_3828_, 12, v_testDriver_3804_);
lean_ctor_set(v_reuseFailAlloc_3828_, 13, v_testDriverArgs_3805_);
lean_ctor_set(v_reuseFailAlloc_3828_, 14, v_lintDriver_3806_);
lean_ctor_set(v_reuseFailAlloc_3828_, 15, v_lintDriverArgs_3807_);
lean_ctor_set(v_reuseFailAlloc_3828_, 16, v_version_3808_);
lean_ctor_set(v_reuseFailAlloc_3828_, 17, v_versionTags_3809_);
lean_ctor_set(v_reuseFailAlloc_3828_, 18, v_description_3810_);
lean_ctor_set(v_reuseFailAlloc_3828_, 19, v_keywords_3811_);
lean_ctor_set(v_reuseFailAlloc_3828_, 20, v_homepage_3812_);
lean_ctor_set(v_reuseFailAlloc_3828_, 21, v_license_3813_);
lean_ctor_set(v_reuseFailAlloc_3828_, 22, v_licenseFiles_3814_);
lean_ctor_set(v_reuseFailAlloc_3828_, 23, v_readmeFile_3815_);
lean_ctor_set(v_reuseFailAlloc_3828_, 24, v_enableArtifactCache_x3f_3817_);
lean_ctor_set(v_reuseFailAlloc_3828_, 25, v_restoreAllArtifacts_x3f_3818_);
lean_ctor_set(v_reuseFailAlloc_3828_, 26, v_builtinLint_x3f_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27, v_bootstrap_3791_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27 + 1, v_precompileModules_3793_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3803_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27 + 3, v_reservoir_3816_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27 + 5, v_allowImportAll_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3828_, sizeof(void*)*27 + 6, v_fixedToolchain_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* v_f_3831_, lean_object* v_cfg_3832_){
_start:
{
lean_object* v_toWorkspaceConfig_3833_; lean_object* v_toLeanConfig_3834_; uint8_t v_bootstrap_3835_; lean_object* v_extraDepTargets_3836_; uint8_t v_precompileModules_3837_; lean_object* v_moreGlobalServerArgs_3838_; lean_object* v_srcDir_3839_; lean_object* v_buildDir_3840_; lean_object* v_leanLibDir_3841_; lean_object* v_nativeLibDir_3842_; lean_object* v_binDir_3843_; lean_object* v_irDir_3844_; lean_object* v_releaseRepo_3845_; lean_object* v_buildArchive_3846_; uint8_t v_preferReleaseBuild_3847_; lean_object* v_testDriver_3848_; lean_object* v_testDriverArgs_3849_; lean_object* v_lintDriver_3850_; lean_object* v_lintDriverArgs_3851_; lean_object* v_version_3852_; lean_object* v_versionTags_3853_; lean_object* v_description_3854_; lean_object* v_keywords_3855_; lean_object* v_homepage_3856_; lean_object* v_license_3857_; lean_object* v_licenseFiles_3858_; lean_object* v_readmeFile_3859_; uint8_t v_reservoir_3860_; lean_object* v_enableArtifactCache_x3f_3861_; lean_object* v_restoreAllArtifacts_x3f_3862_; uint8_t v_libPrefixOnWindows_3863_; uint8_t v_allowImportAll_3864_; lean_object* v_builtinLint_x3f_3865_; uint8_t v_fixedToolchain_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3874_; 
v_toWorkspaceConfig_3833_ = lean_ctor_get(v_cfg_3832_, 0);
v_toLeanConfig_3834_ = lean_ctor_get(v_cfg_3832_, 1);
v_bootstrap_3835_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27);
v_extraDepTargets_3836_ = lean_ctor_get(v_cfg_3832_, 2);
v_precompileModules_3837_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3838_ = lean_ctor_get(v_cfg_3832_, 3);
v_srcDir_3839_ = lean_ctor_get(v_cfg_3832_, 4);
v_buildDir_3840_ = lean_ctor_get(v_cfg_3832_, 5);
v_leanLibDir_3841_ = lean_ctor_get(v_cfg_3832_, 6);
v_nativeLibDir_3842_ = lean_ctor_get(v_cfg_3832_, 7);
v_binDir_3843_ = lean_ctor_get(v_cfg_3832_, 8);
v_irDir_3844_ = lean_ctor_get(v_cfg_3832_, 9);
v_releaseRepo_3845_ = lean_ctor_get(v_cfg_3832_, 10);
v_buildArchive_3846_ = lean_ctor_get(v_cfg_3832_, 11);
v_preferReleaseBuild_3847_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27 + 2);
v_testDriver_3848_ = lean_ctor_get(v_cfg_3832_, 12);
v_testDriverArgs_3849_ = lean_ctor_get(v_cfg_3832_, 13);
v_lintDriver_3850_ = lean_ctor_get(v_cfg_3832_, 14);
v_lintDriverArgs_3851_ = lean_ctor_get(v_cfg_3832_, 15);
v_version_3852_ = lean_ctor_get(v_cfg_3832_, 16);
v_versionTags_3853_ = lean_ctor_get(v_cfg_3832_, 17);
v_description_3854_ = lean_ctor_get(v_cfg_3832_, 18);
v_keywords_3855_ = lean_ctor_get(v_cfg_3832_, 19);
v_homepage_3856_ = lean_ctor_get(v_cfg_3832_, 20);
v_license_3857_ = lean_ctor_get(v_cfg_3832_, 21);
v_licenseFiles_3858_ = lean_ctor_get(v_cfg_3832_, 22);
v_readmeFile_3859_ = lean_ctor_get(v_cfg_3832_, 23);
v_reservoir_3860_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3861_ = lean_ctor_get(v_cfg_3832_, 24);
v_restoreAllArtifacts_x3f_3862_ = lean_ctor_get(v_cfg_3832_, 25);
v_libPrefixOnWindows_3863_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27 + 4);
v_allowImportAll_3864_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3865_ = lean_ctor_get(v_cfg_3832_, 26);
v_fixedToolchain_3866_ = lean_ctor_get_uint8(v_cfg_3832_, sizeof(void*)*27 + 6);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_cfg_3832_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3868_ = v_cfg_3832_;
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_builtinLint_x3f_3865_);
lean_inc(v_restoreAllArtifacts_x3f_3862_);
lean_inc(v_enableArtifactCache_x3f_3861_);
lean_inc(v_readmeFile_3859_);
lean_inc(v_licenseFiles_3858_);
lean_inc(v_license_3857_);
lean_inc(v_homepage_3856_);
lean_inc(v_keywords_3855_);
lean_inc(v_description_3854_);
lean_inc(v_versionTags_3853_);
lean_inc(v_version_3852_);
lean_inc(v_lintDriverArgs_3851_);
lean_inc(v_lintDriver_3850_);
lean_inc(v_testDriverArgs_3849_);
lean_inc(v_testDriver_3848_);
lean_inc(v_buildArchive_3846_);
lean_inc(v_releaseRepo_3845_);
lean_inc(v_irDir_3844_);
lean_inc(v_binDir_3843_);
lean_inc(v_nativeLibDir_3842_);
lean_inc(v_leanLibDir_3841_);
lean_inc(v_buildDir_3840_);
lean_inc(v_srcDir_3839_);
lean_inc(v_moreGlobalServerArgs_3838_);
lean_inc(v_extraDepTargets_3836_);
lean_inc(v_toLeanConfig_3834_);
lean_inc(v_toWorkspaceConfig_3833_);
lean_dec(v_cfg_3832_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3870_ = lean_apply_1(v_f_3831_, v_toWorkspaceConfig_3833_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3870_);
v___x_3872_ = v___x_3868_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_toLeanConfig_3834_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_extraDepTargets_3836_);
lean_ctor_set(v_reuseFailAlloc_3873_, 3, v_moreGlobalServerArgs_3838_);
lean_ctor_set(v_reuseFailAlloc_3873_, 4, v_srcDir_3839_);
lean_ctor_set(v_reuseFailAlloc_3873_, 5, v_buildDir_3840_);
lean_ctor_set(v_reuseFailAlloc_3873_, 6, v_leanLibDir_3841_);
lean_ctor_set(v_reuseFailAlloc_3873_, 7, v_nativeLibDir_3842_);
lean_ctor_set(v_reuseFailAlloc_3873_, 8, v_binDir_3843_);
lean_ctor_set(v_reuseFailAlloc_3873_, 9, v_irDir_3844_);
lean_ctor_set(v_reuseFailAlloc_3873_, 10, v_releaseRepo_3845_);
lean_ctor_set(v_reuseFailAlloc_3873_, 11, v_buildArchive_3846_);
lean_ctor_set(v_reuseFailAlloc_3873_, 12, v_testDriver_3848_);
lean_ctor_set(v_reuseFailAlloc_3873_, 13, v_testDriverArgs_3849_);
lean_ctor_set(v_reuseFailAlloc_3873_, 14, v_lintDriver_3850_);
lean_ctor_set(v_reuseFailAlloc_3873_, 15, v_lintDriverArgs_3851_);
lean_ctor_set(v_reuseFailAlloc_3873_, 16, v_version_3852_);
lean_ctor_set(v_reuseFailAlloc_3873_, 17, v_versionTags_3853_);
lean_ctor_set(v_reuseFailAlloc_3873_, 18, v_description_3854_);
lean_ctor_set(v_reuseFailAlloc_3873_, 19, v_keywords_3855_);
lean_ctor_set(v_reuseFailAlloc_3873_, 20, v_homepage_3856_);
lean_ctor_set(v_reuseFailAlloc_3873_, 21, v_license_3857_);
lean_ctor_set(v_reuseFailAlloc_3873_, 22, v_licenseFiles_3858_);
lean_ctor_set(v_reuseFailAlloc_3873_, 23, v_readmeFile_3859_);
lean_ctor_set(v_reuseFailAlloc_3873_, 24, v_enableArtifactCache_x3f_3861_);
lean_ctor_set(v_reuseFailAlloc_3873_, 25, v_restoreAllArtifacts_x3f_3862_);
lean_ctor_set(v_reuseFailAlloc_3873_, 26, v_builtinLint_x3f_3865_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27, v_bootstrap_3835_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27 + 1, v_precompileModules_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3847_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27 + 3, v_reservoir_3860_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3863_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27 + 5, v_allowImportAll_3864_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*27 + 6, v_fixedToolchain_3866_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* v_x_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lake_defaultPackagesDir;
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* v_x_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(v_x_3877_);
lean_dec_ref(v_x_3877_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_3888_, lean_object* v_n_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_3891_, lean_object* v_n_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3891_, v_n_3892_);
lean_dec(v_n_3892_);
lean_dec(v_p_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_3894_, lean_object* v_n_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3894_, v_n_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_3897_, lean_object* v_n_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_3897_, v_n_3898_);
lean_dec(v_n_3898_);
lean_dec(v_p_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_3900_){
_start:
{
lean_object* v_toLeanConfig_3901_; 
v_toLeanConfig_3901_ = lean_ctor_get(v_cfg_3900_, 1);
lean_inc_ref(v_toLeanConfig_3901_);
return v_toLeanConfig_3901_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(v_cfg_3902_);
lean_dec_ref(v_cfg_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* v_val_3904_, lean_object* v_cfg_3905_){
_start:
{
lean_object* v_toWorkspaceConfig_3906_; uint8_t v_bootstrap_3907_; lean_object* v_extraDepTargets_3908_; uint8_t v_precompileModules_3909_; lean_object* v_moreGlobalServerArgs_3910_; lean_object* v_srcDir_3911_; lean_object* v_buildDir_3912_; lean_object* v_leanLibDir_3913_; lean_object* v_nativeLibDir_3914_; lean_object* v_binDir_3915_; lean_object* v_irDir_3916_; lean_object* v_releaseRepo_3917_; lean_object* v_buildArchive_3918_; uint8_t v_preferReleaseBuild_3919_; lean_object* v_testDriver_3920_; lean_object* v_testDriverArgs_3921_; lean_object* v_lintDriver_3922_; lean_object* v_lintDriverArgs_3923_; lean_object* v_version_3924_; lean_object* v_versionTags_3925_; lean_object* v_description_3926_; lean_object* v_keywords_3927_; lean_object* v_homepage_3928_; lean_object* v_license_3929_; lean_object* v_licenseFiles_3930_; lean_object* v_readmeFile_3931_; uint8_t v_reservoir_3932_; lean_object* v_enableArtifactCache_x3f_3933_; lean_object* v_restoreAllArtifacts_x3f_3934_; uint8_t v_libPrefixOnWindows_3935_; uint8_t v_allowImportAll_3936_; lean_object* v_builtinLint_x3f_3937_; uint8_t v_fixedToolchain_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
v_toWorkspaceConfig_3906_ = lean_ctor_get(v_cfg_3905_, 0);
v_bootstrap_3907_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27);
v_extraDepTargets_3908_ = lean_ctor_get(v_cfg_3905_, 2);
v_precompileModules_3909_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3910_ = lean_ctor_get(v_cfg_3905_, 3);
v_srcDir_3911_ = lean_ctor_get(v_cfg_3905_, 4);
v_buildDir_3912_ = lean_ctor_get(v_cfg_3905_, 5);
v_leanLibDir_3913_ = lean_ctor_get(v_cfg_3905_, 6);
v_nativeLibDir_3914_ = lean_ctor_get(v_cfg_3905_, 7);
v_binDir_3915_ = lean_ctor_get(v_cfg_3905_, 8);
v_irDir_3916_ = lean_ctor_get(v_cfg_3905_, 9);
v_releaseRepo_3917_ = lean_ctor_get(v_cfg_3905_, 10);
v_buildArchive_3918_ = lean_ctor_get(v_cfg_3905_, 11);
v_preferReleaseBuild_3919_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27 + 2);
v_testDriver_3920_ = lean_ctor_get(v_cfg_3905_, 12);
v_testDriverArgs_3921_ = lean_ctor_get(v_cfg_3905_, 13);
v_lintDriver_3922_ = lean_ctor_get(v_cfg_3905_, 14);
v_lintDriverArgs_3923_ = lean_ctor_get(v_cfg_3905_, 15);
v_version_3924_ = lean_ctor_get(v_cfg_3905_, 16);
v_versionTags_3925_ = lean_ctor_get(v_cfg_3905_, 17);
v_description_3926_ = lean_ctor_get(v_cfg_3905_, 18);
v_keywords_3927_ = lean_ctor_get(v_cfg_3905_, 19);
v_homepage_3928_ = lean_ctor_get(v_cfg_3905_, 20);
v_license_3929_ = lean_ctor_get(v_cfg_3905_, 21);
v_licenseFiles_3930_ = lean_ctor_get(v_cfg_3905_, 22);
v_readmeFile_3931_ = lean_ctor_get(v_cfg_3905_, 23);
v_reservoir_3932_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3933_ = lean_ctor_get(v_cfg_3905_, 24);
v_restoreAllArtifacts_x3f_3934_ = lean_ctor_get(v_cfg_3905_, 25);
v_libPrefixOnWindows_3935_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27 + 4);
v_allowImportAll_3936_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3937_ = lean_ctor_get(v_cfg_3905_, 26);
v_fixedToolchain_3938_ = lean_ctor_get_uint8(v_cfg_3905_, sizeof(void*)*27 + 6);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_cfg_3905_);
if (v_isSharedCheck_3945_ == 0)
{
lean_object* v_unused_3946_; 
v_unused_3946_ = lean_ctor_get(v_cfg_3905_, 1);
lean_dec(v_unused_3946_);
v___x_3940_ = v_cfg_3905_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_builtinLint_x3f_3937_);
lean_inc(v_restoreAllArtifacts_x3f_3934_);
lean_inc(v_enableArtifactCache_x3f_3933_);
lean_inc(v_readmeFile_3931_);
lean_inc(v_licenseFiles_3930_);
lean_inc(v_license_3929_);
lean_inc(v_homepage_3928_);
lean_inc(v_keywords_3927_);
lean_inc(v_description_3926_);
lean_inc(v_versionTags_3925_);
lean_inc(v_version_3924_);
lean_inc(v_lintDriverArgs_3923_);
lean_inc(v_lintDriver_3922_);
lean_inc(v_testDriverArgs_3921_);
lean_inc(v_testDriver_3920_);
lean_inc(v_buildArchive_3918_);
lean_inc(v_releaseRepo_3917_);
lean_inc(v_irDir_3916_);
lean_inc(v_binDir_3915_);
lean_inc(v_nativeLibDir_3914_);
lean_inc(v_leanLibDir_3913_);
lean_inc(v_buildDir_3912_);
lean_inc(v_srcDir_3911_);
lean_inc(v_moreGlobalServerArgs_3910_);
lean_inc(v_extraDepTargets_3908_);
lean_inc(v_toWorkspaceConfig_3906_);
lean_dec(v_cfg_3905_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 1, v_val_3904_);
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_toWorkspaceConfig_3906_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_val_3904_);
lean_ctor_set(v_reuseFailAlloc_3944_, 2, v_extraDepTargets_3908_);
lean_ctor_set(v_reuseFailAlloc_3944_, 3, v_moreGlobalServerArgs_3910_);
lean_ctor_set(v_reuseFailAlloc_3944_, 4, v_srcDir_3911_);
lean_ctor_set(v_reuseFailAlloc_3944_, 5, v_buildDir_3912_);
lean_ctor_set(v_reuseFailAlloc_3944_, 6, v_leanLibDir_3913_);
lean_ctor_set(v_reuseFailAlloc_3944_, 7, v_nativeLibDir_3914_);
lean_ctor_set(v_reuseFailAlloc_3944_, 8, v_binDir_3915_);
lean_ctor_set(v_reuseFailAlloc_3944_, 9, v_irDir_3916_);
lean_ctor_set(v_reuseFailAlloc_3944_, 10, v_releaseRepo_3917_);
lean_ctor_set(v_reuseFailAlloc_3944_, 11, v_buildArchive_3918_);
lean_ctor_set(v_reuseFailAlloc_3944_, 12, v_testDriver_3920_);
lean_ctor_set(v_reuseFailAlloc_3944_, 13, v_testDriverArgs_3921_);
lean_ctor_set(v_reuseFailAlloc_3944_, 14, v_lintDriver_3922_);
lean_ctor_set(v_reuseFailAlloc_3944_, 15, v_lintDriverArgs_3923_);
lean_ctor_set(v_reuseFailAlloc_3944_, 16, v_version_3924_);
lean_ctor_set(v_reuseFailAlloc_3944_, 17, v_versionTags_3925_);
lean_ctor_set(v_reuseFailAlloc_3944_, 18, v_description_3926_);
lean_ctor_set(v_reuseFailAlloc_3944_, 19, v_keywords_3927_);
lean_ctor_set(v_reuseFailAlloc_3944_, 20, v_homepage_3928_);
lean_ctor_set(v_reuseFailAlloc_3944_, 21, v_license_3929_);
lean_ctor_set(v_reuseFailAlloc_3944_, 22, v_licenseFiles_3930_);
lean_ctor_set(v_reuseFailAlloc_3944_, 23, v_readmeFile_3931_);
lean_ctor_set(v_reuseFailAlloc_3944_, 24, v_enableArtifactCache_x3f_3933_);
lean_ctor_set(v_reuseFailAlloc_3944_, 25, v_restoreAllArtifacts_x3f_3934_);
lean_ctor_set(v_reuseFailAlloc_3944_, 26, v_builtinLint_x3f_3937_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27, v_bootstrap_3907_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27 + 1, v_precompileModules_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3919_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27 + 3, v_reservoir_3932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3935_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27 + 5, v_allowImportAll_3936_);
lean_ctor_set_uint8(v_reuseFailAlloc_3944_, sizeof(void*)*27 + 6, v_fixedToolchain_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* v_f_3947_, lean_object* v_cfg_3948_){
_start:
{
lean_object* v_toWorkspaceConfig_3949_; lean_object* v_toLeanConfig_3950_; uint8_t v_bootstrap_3951_; lean_object* v_extraDepTargets_3952_; uint8_t v_precompileModules_3953_; lean_object* v_moreGlobalServerArgs_3954_; lean_object* v_srcDir_3955_; lean_object* v_buildDir_3956_; lean_object* v_leanLibDir_3957_; lean_object* v_nativeLibDir_3958_; lean_object* v_binDir_3959_; lean_object* v_irDir_3960_; lean_object* v_releaseRepo_3961_; lean_object* v_buildArchive_3962_; uint8_t v_preferReleaseBuild_3963_; lean_object* v_testDriver_3964_; lean_object* v_testDriverArgs_3965_; lean_object* v_lintDriver_3966_; lean_object* v_lintDriverArgs_3967_; lean_object* v_version_3968_; lean_object* v_versionTags_3969_; lean_object* v_description_3970_; lean_object* v_keywords_3971_; lean_object* v_homepage_3972_; lean_object* v_license_3973_; lean_object* v_licenseFiles_3974_; lean_object* v_readmeFile_3975_; uint8_t v_reservoir_3976_; lean_object* v_enableArtifactCache_x3f_3977_; lean_object* v_restoreAllArtifacts_x3f_3978_; uint8_t v_libPrefixOnWindows_3979_; uint8_t v_allowImportAll_3980_; lean_object* v_builtinLint_x3f_3981_; uint8_t v_fixedToolchain_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3990_; 
v_toWorkspaceConfig_3949_ = lean_ctor_get(v_cfg_3948_, 0);
v_toLeanConfig_3950_ = lean_ctor_get(v_cfg_3948_, 1);
v_bootstrap_3951_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27);
v_extraDepTargets_3952_ = lean_ctor_get(v_cfg_3948_, 2);
v_precompileModules_3953_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27 + 1);
v_moreGlobalServerArgs_3954_ = lean_ctor_get(v_cfg_3948_, 3);
v_srcDir_3955_ = lean_ctor_get(v_cfg_3948_, 4);
v_buildDir_3956_ = lean_ctor_get(v_cfg_3948_, 5);
v_leanLibDir_3957_ = lean_ctor_get(v_cfg_3948_, 6);
v_nativeLibDir_3958_ = lean_ctor_get(v_cfg_3948_, 7);
v_binDir_3959_ = lean_ctor_get(v_cfg_3948_, 8);
v_irDir_3960_ = lean_ctor_get(v_cfg_3948_, 9);
v_releaseRepo_3961_ = lean_ctor_get(v_cfg_3948_, 10);
v_buildArchive_3962_ = lean_ctor_get(v_cfg_3948_, 11);
v_preferReleaseBuild_3963_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27 + 2);
v_testDriver_3964_ = lean_ctor_get(v_cfg_3948_, 12);
v_testDriverArgs_3965_ = lean_ctor_get(v_cfg_3948_, 13);
v_lintDriver_3966_ = lean_ctor_get(v_cfg_3948_, 14);
v_lintDriverArgs_3967_ = lean_ctor_get(v_cfg_3948_, 15);
v_version_3968_ = lean_ctor_get(v_cfg_3948_, 16);
v_versionTags_3969_ = lean_ctor_get(v_cfg_3948_, 17);
v_description_3970_ = lean_ctor_get(v_cfg_3948_, 18);
v_keywords_3971_ = lean_ctor_get(v_cfg_3948_, 19);
v_homepage_3972_ = lean_ctor_get(v_cfg_3948_, 20);
v_license_3973_ = lean_ctor_get(v_cfg_3948_, 21);
v_licenseFiles_3974_ = lean_ctor_get(v_cfg_3948_, 22);
v_readmeFile_3975_ = lean_ctor_get(v_cfg_3948_, 23);
v_reservoir_3976_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27 + 3);
v_enableArtifactCache_x3f_3977_ = lean_ctor_get(v_cfg_3948_, 24);
v_restoreAllArtifacts_x3f_3978_ = lean_ctor_get(v_cfg_3948_, 25);
v_libPrefixOnWindows_3979_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27 + 4);
v_allowImportAll_3980_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27 + 5);
v_builtinLint_x3f_3981_ = lean_ctor_get(v_cfg_3948_, 26);
v_fixedToolchain_3982_ = lean_ctor_get_uint8(v_cfg_3948_, sizeof(void*)*27 + 6);
v_isSharedCheck_3990_ = !lean_is_exclusive(v_cfg_3948_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3984_ = v_cfg_3948_;
v_isShared_3985_ = v_isSharedCheck_3990_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_builtinLint_x3f_3981_);
lean_inc(v_restoreAllArtifacts_x3f_3978_);
lean_inc(v_enableArtifactCache_x3f_3977_);
lean_inc(v_readmeFile_3975_);
lean_inc(v_licenseFiles_3974_);
lean_inc(v_license_3973_);
lean_inc(v_homepage_3972_);
lean_inc(v_keywords_3971_);
lean_inc(v_description_3970_);
lean_inc(v_versionTags_3969_);
lean_inc(v_version_3968_);
lean_inc(v_lintDriverArgs_3967_);
lean_inc(v_lintDriver_3966_);
lean_inc(v_testDriverArgs_3965_);
lean_inc(v_testDriver_3964_);
lean_inc(v_buildArchive_3962_);
lean_inc(v_releaseRepo_3961_);
lean_inc(v_irDir_3960_);
lean_inc(v_binDir_3959_);
lean_inc(v_nativeLibDir_3958_);
lean_inc(v_leanLibDir_3957_);
lean_inc(v_buildDir_3956_);
lean_inc(v_srcDir_3955_);
lean_inc(v_moreGlobalServerArgs_3954_);
lean_inc(v_extraDepTargets_3952_);
lean_inc(v_toLeanConfig_3950_);
lean_inc(v_toWorkspaceConfig_3949_);
lean_dec(v_cfg_3948_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3990_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3986_ = lean_apply_1(v_f_3947_, v_toLeanConfig_3950_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v___x_3986_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_toWorkspaceConfig_3949_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_extraDepTargets_3952_);
lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_moreGlobalServerArgs_3954_);
lean_ctor_set(v_reuseFailAlloc_3989_, 4, v_srcDir_3955_);
lean_ctor_set(v_reuseFailAlloc_3989_, 5, v_buildDir_3956_);
lean_ctor_set(v_reuseFailAlloc_3989_, 6, v_leanLibDir_3957_);
lean_ctor_set(v_reuseFailAlloc_3989_, 7, v_nativeLibDir_3958_);
lean_ctor_set(v_reuseFailAlloc_3989_, 8, v_binDir_3959_);
lean_ctor_set(v_reuseFailAlloc_3989_, 9, v_irDir_3960_);
lean_ctor_set(v_reuseFailAlloc_3989_, 10, v_releaseRepo_3961_);
lean_ctor_set(v_reuseFailAlloc_3989_, 11, v_buildArchive_3962_);
lean_ctor_set(v_reuseFailAlloc_3989_, 12, v_testDriver_3964_);
lean_ctor_set(v_reuseFailAlloc_3989_, 13, v_testDriverArgs_3965_);
lean_ctor_set(v_reuseFailAlloc_3989_, 14, v_lintDriver_3966_);
lean_ctor_set(v_reuseFailAlloc_3989_, 15, v_lintDriverArgs_3967_);
lean_ctor_set(v_reuseFailAlloc_3989_, 16, v_version_3968_);
lean_ctor_set(v_reuseFailAlloc_3989_, 17, v_versionTags_3969_);
lean_ctor_set(v_reuseFailAlloc_3989_, 18, v_description_3970_);
lean_ctor_set(v_reuseFailAlloc_3989_, 19, v_keywords_3971_);
lean_ctor_set(v_reuseFailAlloc_3989_, 20, v_homepage_3972_);
lean_ctor_set(v_reuseFailAlloc_3989_, 21, v_license_3973_);
lean_ctor_set(v_reuseFailAlloc_3989_, 22, v_licenseFiles_3974_);
lean_ctor_set(v_reuseFailAlloc_3989_, 23, v_readmeFile_3975_);
lean_ctor_set(v_reuseFailAlloc_3989_, 24, v_enableArtifactCache_x3f_3977_);
lean_ctor_set(v_reuseFailAlloc_3989_, 25, v_restoreAllArtifacts_x3f_3978_);
lean_ctor_set(v_reuseFailAlloc_3989_, 26, v_builtinLint_x3f_3981_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27, v_bootstrap_3951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27 + 1, v_precompileModules_3953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27 + 2, v_preferReleaseBuild_3963_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27 + 3, v_reservoir_3976_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27 + 4, v_libPrefixOnWindows_3979_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27 + 5, v_allowImportAll_3980_);
lean_ctor_set_uint8(v_reuseFailAlloc_3989_, sizeof(void*)*27 + 6, v_fixedToolchain_3982_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* v_x_3998_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__3(v_x_4000_);
lean_dec_ref(v_x_4000_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_4011_, lean_object* v_n_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___closed__4));
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_4014_, lean_object* v_n_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4014_, v_n_4015_);
lean_dec(v_n_4015_);
lean_dec(v_p_4014_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_4017_, lean_object* v_n_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4017_, v_n_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_4020_, lean_object* v_n_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_4020_, v_n_4021_);
lean_dec(v_n_4021_);
lean_dec(v_p_4020_);
return v_res_4022_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_4033_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_4034_ = lean_array_push(v___x_4033_, v___x_4032_);
return v___x_4034_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_4043_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_4044_ = lean_array_push(v___x_4043_, v___x_4042_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_4053_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_4054_ = lean_array_push(v___x_4053_, v___x_4052_);
return v___x_4054_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_4063_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_4064_ = lean_array_push(v___x_4063_, v___x_4062_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_4073_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_4074_ = lean_array_push(v___x_4073_, v___x_4072_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_4083_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_4084_ = lean_array_push(v___x_4083_, v___x_4082_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_4093_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_4094_ = lean_array_push(v___x_4093_, v___x_4092_);
return v___x_4094_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_4103_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_4104_ = lean_array_push(v___x_4103_, v___x_4102_);
return v___x_4104_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_4113_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_4114_ = lean_array_push(v___x_4113_, v___x_4112_);
return v___x_4114_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_4123_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_4124_ = lean_array_push(v___x_4123_, v___x_4122_);
return v___x_4124_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4132_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_4133_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_4134_ = lean_array_push(v___x_4133_, v___x_4132_);
return v___x_4134_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_4143_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_4144_ = lean_array_push(v___x_4143_, v___x_4142_);
return v___x_4144_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_4153_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_4154_ = lean_array_push(v___x_4153_, v___x_4152_);
return v___x_4154_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4162_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_4163_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_4164_ = lean_array_push(v___x_4163_, v___x_4162_);
return v___x_4164_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_4173_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_4174_ = lean_array_push(v___x_4173_, v___x_4172_);
return v___x_4174_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4182_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_4183_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_4184_ = lean_array_push(v___x_4183_, v___x_4182_);
return v___x_4184_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__67));
v___x_4193_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4194_ = lean_array_push(v___x_4193_, v___x_4192_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4203_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4202_);
return v___x_4204_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4213_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4214_ = lean_array_push(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4222_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4223_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4224_ = lean_array_push(v___x_4223_, v___x_4222_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4232_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4233_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4234_ = lean_array_push(v___x_4233_, v___x_4232_);
return v___x_4234_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4242_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4243_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4244_ = lean_array_push(v___x_4243_, v___x_4242_);
return v___x_4244_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4253_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4254_ = lean_array_push(v___x_4253_, v___x_4252_);
return v___x_4254_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_4263_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4264_ = lean_array_push(v___x_4263_, v___x_4262_);
return v___x_4264_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_4273_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4274_ = lean_array_push(v___x_4273_, v___x_4272_);
return v___x_4274_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_4283_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4284_ = lean_array_push(v___x_4283_, v___x_4282_);
return v___x_4284_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_4293_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4294_ = lean_array_push(v___x_4293_, v___x_4292_);
return v___x_4294_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_4303_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4304_ = lean_array_push(v___x_4303_, v___x_4302_);
return v___x_4304_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4312_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_4313_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4314_ = lean_array_push(v___x_4313_, v___x_4312_);
return v___x_4314_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4322_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_4323_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4324_ = lean_array_push(v___x_4323_, v___x_4322_);
return v___x_4324_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_4333_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4334_ = lean_array_push(v___x_4333_, v___x_4332_);
return v___x_4334_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_4343_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4344_ = lean_array_push(v___x_4343_, v___x_4342_);
return v___x_4344_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4353_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4354_ = lean_array_push(v___x_4353_, v___x_4352_);
return v___x_4354_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_4363_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4364_ = lean_array_push(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_4373_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_4374_ = lean_array_push(v___x_4373_, v___x_4372_);
return v___x_4374_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_4383_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_4384_ = lean_array_push(v___x_4383_, v___x_4382_);
return v___x_4384_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4392_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_4393_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_4394_ = lean_array_push(v___x_4393_, v___x_4392_);
return v___x_4394_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__152(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__151));
v___x_4403_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_4404_ = lean_array_push(v___x_4403_, v___x_4402_);
return v___x_4404_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__156(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4412_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__155));
v___x_4413_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__152, &l_Lake_PackageConfig___fields___closed__152_once, _init_l_Lake_PackageConfig___fields___closed__152);
v___x_4414_ = lean_array_push(v___x_4413_, v___x_4412_);
return v___x_4414_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__157(void){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4415_ = l_Lake_WorkspaceConfig___fields;
v___x_4416_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__156, &l_Lake_PackageConfig___fields___closed__156_once, _init_l_Lake_PackageConfig___fields___closed__156);
v___x_4417_ = l_Array_append___redArg(v___x_4416_, v___x_4415_);
return v___x_4417_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__161(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4425_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__160));
v___x_4426_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__157, &l_Lake_PackageConfig___fields___closed__157_once, _init_l_Lake_PackageConfig___fields___closed__157);
v___x_4427_ = lean_array_push(v___x_4426_, v___x_4425_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__162(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = l_Lake_LeanConfig___fields;
v___x_4429_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__161, &l_Lake_PackageConfig___fields___closed__161_once, _init_l_Lake_PackageConfig___fields___closed__161);
v___x_4430_ = l_Array_append___redArg(v___x_4429_, v___x_4428_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__166(void){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__165));
v___x_4439_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__162, &l_Lake_PackageConfig___fields___closed__162_once, _init_l_Lake_PackageConfig___fields___closed__162);
v___x_4440_ = lean_array_push(v___x_4439_, v___x_4438_);
return v___x_4440_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__166, &l_Lake_PackageConfig___fields___closed__166_once, _init_l_Lake_PackageConfig___fields___closed__166);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_4442_, lean_object* v_n_4443_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lake_PackageConfig___fields;
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_4445_, lean_object* v_n_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lake_PackageConfig_instConfigFields(v_p_4445_, v_n_4446_);
lean_dec(v_n_4446_);
lean_dec(v_p_4445_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_4448_, lean_object* v_x2_4449_){
_start:
{
lean_object* v_name_4450_; lean_object* v___x_4451_; 
v_name_4450_ = lean_ctor_get(v_x2_4449_, 0);
lean_inc(v_name_4450_);
v___x_4451_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_4450_, v_x2_4449_, v_x1_4448_);
return v___x_4451_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = l_Lake_PackageConfig___fields;
v___x_4453_ = lean_array_get_size(v___x_4452_);
return v___x_4453_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; 
v___x_4473_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4474_ = lean_unsigned_to_nat(0u);
v___x_4475_ = lean_nat_dec_lt(v___x_4474_, v___x_4473_);
return v___x_4475_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_4477_; uint8_t v___x_4478_; 
v___x_4477_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4478_ = lean_nat_dec_le(v___x_4477_, v___x_4477_);
return v___x_4478_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_4479_; size_t v___x_4480_; 
v___x_4479_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4480_ = lean_usize_of_nat(v___x_4479_);
return v___x_4480_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_4481_; size_t v___x_4482_; size_t v___x_4483_; lean_object* v___x_4484_; lean_object* v___f_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4481_ = lean_box(1);
v___x_4482_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_4483_ = ((size_t)0ULL);
v___x_4484_ = l_Lake_PackageConfig___fields;
v___f_4485_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_4486_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4486_, v___f_4485_, v___x_4484_, v___x_4483_, v___x_4482_, v___x_4481_);
return v___x_4487_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___y_4490_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v___x_4488_ = l_Lake_PackageConfig___fields;
v___x_4493_ = lean_box(1);
v___x_4494_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_4494_ == 0)
{
v___y_4490_ = v___x_4493_;
goto v___jp_4489_;
}
else
{
uint8_t v___x_4495_; 
v___x_4495_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_4495_ == 0)
{
if (v___x_4494_ == 0)
{
v___y_4490_ = v___x_4493_;
goto v___jp_4489_;
}
else
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4490_ = v___x_4496_;
goto v___jp_4489_;
}
}
else
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4490_ = v___x_4497_;
goto v___jp_4489_;
}
}
v___jp_4489_:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_4490_);
v___x_4492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4488_);
lean_ctor_set(v___x_4492_, 1, v___y_4490_);
lean_ctor_set(v___x_4492_, 2, v___x_4491_);
return v___x_4492_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
uint8_t v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4498_ = 1;
v___x_4499_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
v___x_4500_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
v___x_4501_ = l_Lake_defaultVersionTags;
v___x_4502_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
v___x_4503_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
v___x_4504_ = lean_box(0);
v___x_4505_ = l_Lake_defaultIrDir;
v___x_4506_ = l_Lake_defaultBinDir;
v___x_4507_ = l_Lake_defaultNativeLibDir;
v___x_4508_ = l_Lake_defaultLeanLibDir;
v___x_4509_ = l_Lake_defaultBuildDir;
v___x_4510_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_4511_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_4512_ = 0;
v___x_4513_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_4514_ = l_Lake_defaultPackagesDir;
v___x_4515_ = lean_alloc_ctor(0, 27, 7);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
lean_ctor_set(v___x_4515_, 1, v___x_4513_);
lean_ctor_set(v___x_4515_, 2, v___x_4511_);
lean_ctor_set(v___x_4515_, 3, v___x_4511_);
lean_ctor_set(v___x_4515_, 4, v___x_4510_);
lean_ctor_set(v___x_4515_, 5, v___x_4509_);
lean_ctor_set(v___x_4515_, 6, v___x_4508_);
lean_ctor_set(v___x_4515_, 7, v___x_4507_);
lean_ctor_set(v___x_4515_, 8, v___x_4506_);
lean_ctor_set(v___x_4515_, 9, v___x_4505_);
lean_ctor_set(v___x_4515_, 10, v___x_4504_);
lean_ctor_set(v___x_4515_, 11, v___x_4504_);
lean_ctor_set(v___x_4515_, 12, v___x_4503_);
lean_ctor_set(v___x_4515_, 13, v___x_4511_);
lean_ctor_set(v___x_4515_, 14, v___x_4503_);
lean_ctor_set(v___x_4515_, 15, v___x_4511_);
lean_ctor_set(v___x_4515_, 16, v___x_4502_);
lean_ctor_set(v___x_4515_, 17, v___x_4501_);
lean_ctor_set(v___x_4515_, 18, v___x_4503_);
lean_ctor_set(v___x_4515_, 19, v___x_4511_);
lean_ctor_set(v___x_4515_, 20, v___x_4503_);
lean_ctor_set(v___x_4515_, 21, v___x_4503_);
lean_ctor_set(v___x_4515_, 22, v___x_4500_);
lean_ctor_set(v___x_4515_, 23, v___x_4499_);
lean_ctor_set(v___x_4515_, 24, v___x_4504_);
lean_ctor_set(v___x_4515_, 25, v___x_4504_);
lean_ctor_set(v___x_4515_, 26, v___x_4504_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27, v___x_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27 + 1, v___x_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27 + 2, v___x_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27 + 3, v___x_4498_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27 + 4, v___x_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27 + 5, v___x_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*27 + 6, v___x_4512_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_4516_, lean_object* v_n_4517_){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_4519_, lean_object* v_n_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lake_PackageConfig_instEmptyCollection(v_p_4519_, v_n_4520_);
lean_dec(v_n_4520_);
lean_dec(v_p_4519_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_4522_){
_start:
{
lean_inc(v_n_4522_);
return v_n_4522_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lake_PackageConfig_origName___redArg(v_n_4523_);
lean_dec(v_n_4523_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_4525_, lean_object* v_n_4526_, lean_object* v_x_4527_){
_start:
{
lean_inc(v_n_4526_);
return v_n_4526_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_4528_, lean_object* v_n_4529_, lean_object* v_x_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lake_PackageConfig_origName(v_p_4528_, v_n_4529_, v_x_4530_);
lean_dec_ref(v_x_4530_);
lean_dec(v_n_4529_);
lean_dec(v_p_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_4539_){
_start:
{
lean_object* v_keyName_4540_; 
v_keyName_4540_ = lean_ctor_get(v_self_4539_, 1);
lean_inc(v_keyName_4540_);
return v_keyName_4540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lake_PackageDecl_name(v_self_4541_);
lean_dec_ref(v_self_4541_);
return v_res_4542_;
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
