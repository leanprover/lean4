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
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
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
v___x_44_ = lean_alloc_ctor(0, 26, 7);
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
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26 + 1, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26 + 2, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26 + 3, v___x_27_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26 + 4, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26 + 5, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*26 + 6, v___x_41_);
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
v_bootstrap_58_ = lean_ctor_get_uint8(v_cfg_57_, sizeof(void*)*26);
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
lean_object* v_toWorkspaceConfig_64_; lean_object* v_toLeanConfig_65_; lean_object* v_extraDepTargets_66_; uint8_t v_precompileModules_67_; lean_object* v_moreGlobalServerArgs_68_; lean_object* v_srcDir_69_; lean_object* v_buildDir_70_; lean_object* v_leanLibDir_71_; lean_object* v_nativeLibDir_72_; lean_object* v_binDir_73_; lean_object* v_irDir_74_; lean_object* v_releaseRepo_75_; lean_object* v_buildArchive_76_; uint8_t v_preferReleaseBuild_77_; lean_object* v_testDriver_78_; lean_object* v_testDriverArgs_79_; lean_object* v_lintDriver_80_; lean_object* v_lintDriverArgs_81_; lean_object* v_version_82_; lean_object* v_versionTags_83_; lean_object* v_description_84_; lean_object* v_keywords_85_; lean_object* v_homepage_86_; lean_object* v_license_87_; lean_object* v_licenseFiles_88_; lean_object* v_readmeFile_89_; uint8_t v_reservoir_90_; lean_object* v_enableArtifactCache_x3f_91_; lean_object* v_restoreAllArtifacts_x3f_92_; uint8_t v_libPrefixOnWindows_93_; uint8_t v_allowImportAll_94_; uint8_t v_fixedToolchain_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_toWorkspaceConfig_64_ = lean_ctor_get(v_cfg_63_, 0);
v_toLeanConfig_65_ = lean_ctor_get(v_cfg_63_, 1);
v_extraDepTargets_66_ = lean_ctor_get(v_cfg_63_, 2);
v_precompileModules_67_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_68_ = lean_ctor_get(v_cfg_63_, 3);
v_srcDir_69_ = lean_ctor_get(v_cfg_63_, 4);
v_buildDir_70_ = lean_ctor_get(v_cfg_63_, 5);
v_leanLibDir_71_ = lean_ctor_get(v_cfg_63_, 6);
v_nativeLibDir_72_ = lean_ctor_get(v_cfg_63_, 7);
v_binDir_73_ = lean_ctor_get(v_cfg_63_, 8);
v_irDir_74_ = lean_ctor_get(v_cfg_63_, 9);
v_releaseRepo_75_ = lean_ctor_get(v_cfg_63_, 10);
v_buildArchive_76_ = lean_ctor_get(v_cfg_63_, 11);
v_preferReleaseBuild_77_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*26 + 2);
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
v_reservoir_90_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_91_ = lean_ctor_get(v_cfg_63_, 24);
v_restoreAllArtifacts_x3f_92_ = lean_ctor_get(v_cfg_63_, 25);
v_libPrefixOnWindows_93_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*26 + 4);
v_allowImportAll_94_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*26 + 5);
v_fixedToolchain_95_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*26 + 6);
v_isSharedCheck_102_ = !lean_is_exclusive(v_cfg_63_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v_cfg_63_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
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
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_toWorkspaceConfig_64_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_toLeanConfig_65_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_extraDepTargets_66_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_moreGlobalServerArgs_68_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v_srcDir_69_);
lean_ctor_set(v_reuseFailAlloc_101_, 5, v_buildDir_70_);
lean_ctor_set(v_reuseFailAlloc_101_, 6, v_leanLibDir_71_);
lean_ctor_set(v_reuseFailAlloc_101_, 7, v_nativeLibDir_72_);
lean_ctor_set(v_reuseFailAlloc_101_, 8, v_binDir_73_);
lean_ctor_set(v_reuseFailAlloc_101_, 9, v_irDir_74_);
lean_ctor_set(v_reuseFailAlloc_101_, 10, v_releaseRepo_75_);
lean_ctor_set(v_reuseFailAlloc_101_, 11, v_buildArchive_76_);
lean_ctor_set(v_reuseFailAlloc_101_, 12, v_testDriver_78_);
lean_ctor_set(v_reuseFailAlloc_101_, 13, v_testDriverArgs_79_);
lean_ctor_set(v_reuseFailAlloc_101_, 14, v_lintDriver_80_);
lean_ctor_set(v_reuseFailAlloc_101_, 15, v_lintDriverArgs_81_);
lean_ctor_set(v_reuseFailAlloc_101_, 16, v_version_82_);
lean_ctor_set(v_reuseFailAlloc_101_, 17, v_versionTags_83_);
lean_ctor_set(v_reuseFailAlloc_101_, 18, v_description_84_);
lean_ctor_set(v_reuseFailAlloc_101_, 19, v_keywords_85_);
lean_ctor_set(v_reuseFailAlloc_101_, 20, v_homepage_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 21, v_license_87_);
lean_ctor_set(v_reuseFailAlloc_101_, 22, v_licenseFiles_88_);
lean_ctor_set(v_reuseFailAlloc_101_, 23, v_readmeFile_89_);
lean_ctor_set(v_reuseFailAlloc_101_, 24, v_enableArtifactCache_x3f_91_);
lean_ctor_set(v_reuseFailAlloc_101_, 25, v_restoreAllArtifacts_x3f_92_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*26 + 1, v_precompileModules_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*26 + 2, v_preferReleaseBuild_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*26 + 3, v_reservoir_90_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*26 + 5, v_allowImportAll_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_101_, sizeof(void*)*26 + 6, v_fixedToolchain_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*26, v_val_62_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object* v_val_103_, lean_object* v_cfg_104_){
_start:
{
uint8_t v_val_134__boxed_105_; lean_object* v_res_106_; 
v_val_134__boxed_105_ = lean_unbox(v_val_103_);
v_res_106_ = l_Lake_PackageConfig_bootstrap___proj___lam__1(v_val_134__boxed_105_, v_cfg_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object* v_f_107_, lean_object* v_cfg_108_){
_start:
{
lean_object* v_toWorkspaceConfig_109_; lean_object* v_toLeanConfig_110_; uint8_t v_bootstrap_111_; lean_object* v_extraDepTargets_112_; uint8_t v_precompileModules_113_; lean_object* v_moreGlobalServerArgs_114_; lean_object* v_srcDir_115_; lean_object* v_buildDir_116_; lean_object* v_leanLibDir_117_; lean_object* v_nativeLibDir_118_; lean_object* v_binDir_119_; lean_object* v_irDir_120_; lean_object* v_releaseRepo_121_; lean_object* v_buildArchive_122_; uint8_t v_preferReleaseBuild_123_; lean_object* v_testDriver_124_; lean_object* v_testDriverArgs_125_; lean_object* v_lintDriver_126_; lean_object* v_lintDriverArgs_127_; lean_object* v_version_128_; lean_object* v_versionTags_129_; lean_object* v_description_130_; lean_object* v_keywords_131_; lean_object* v_homepage_132_; lean_object* v_license_133_; lean_object* v_licenseFiles_134_; lean_object* v_readmeFile_135_; uint8_t v_reservoir_136_; lean_object* v_enableArtifactCache_x3f_137_; lean_object* v_restoreAllArtifacts_x3f_138_; uint8_t v_libPrefixOnWindows_139_; uint8_t v_allowImportAll_140_; uint8_t v_fixedToolchain_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_151_; 
v_toWorkspaceConfig_109_ = lean_ctor_get(v_cfg_108_, 0);
v_toLeanConfig_110_ = lean_ctor_get(v_cfg_108_, 1);
v_bootstrap_111_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26);
v_extraDepTargets_112_ = lean_ctor_get(v_cfg_108_, 2);
v_precompileModules_113_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_114_ = lean_ctor_get(v_cfg_108_, 3);
v_srcDir_115_ = lean_ctor_get(v_cfg_108_, 4);
v_buildDir_116_ = lean_ctor_get(v_cfg_108_, 5);
v_leanLibDir_117_ = lean_ctor_get(v_cfg_108_, 6);
v_nativeLibDir_118_ = lean_ctor_get(v_cfg_108_, 7);
v_binDir_119_ = lean_ctor_get(v_cfg_108_, 8);
v_irDir_120_ = lean_ctor_get(v_cfg_108_, 9);
v_releaseRepo_121_ = lean_ctor_get(v_cfg_108_, 10);
v_buildArchive_122_ = lean_ctor_get(v_cfg_108_, 11);
v_preferReleaseBuild_123_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26 + 2);
v_testDriver_124_ = lean_ctor_get(v_cfg_108_, 12);
v_testDriverArgs_125_ = lean_ctor_get(v_cfg_108_, 13);
v_lintDriver_126_ = lean_ctor_get(v_cfg_108_, 14);
v_lintDriverArgs_127_ = lean_ctor_get(v_cfg_108_, 15);
v_version_128_ = lean_ctor_get(v_cfg_108_, 16);
v_versionTags_129_ = lean_ctor_get(v_cfg_108_, 17);
v_description_130_ = lean_ctor_get(v_cfg_108_, 18);
v_keywords_131_ = lean_ctor_get(v_cfg_108_, 19);
v_homepage_132_ = lean_ctor_get(v_cfg_108_, 20);
v_license_133_ = lean_ctor_get(v_cfg_108_, 21);
v_licenseFiles_134_ = lean_ctor_get(v_cfg_108_, 22);
v_readmeFile_135_ = lean_ctor_get(v_cfg_108_, 23);
v_reservoir_136_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_137_ = lean_ctor_get(v_cfg_108_, 24);
v_restoreAllArtifacts_x3f_138_ = lean_ctor_get(v_cfg_108_, 25);
v_libPrefixOnWindows_139_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26 + 4);
v_allowImportAll_140_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26 + 5);
v_fixedToolchain_141_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*26 + 6);
v_isSharedCheck_151_ = !lean_is_exclusive(v_cfg_108_);
if (v_isSharedCheck_151_ == 0)
{
v___x_143_ = v_cfg_108_;
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_138_);
lean_inc(v_enableArtifactCache_x3f_137_);
lean_inc(v_readmeFile_135_);
lean_inc(v_licenseFiles_134_);
lean_inc(v_license_133_);
lean_inc(v_homepage_132_);
lean_inc(v_keywords_131_);
lean_inc(v_description_130_);
lean_inc(v_versionTags_129_);
lean_inc(v_version_128_);
lean_inc(v_lintDriverArgs_127_);
lean_inc(v_lintDriver_126_);
lean_inc(v_testDriverArgs_125_);
lean_inc(v_testDriver_124_);
lean_inc(v_buildArchive_122_);
lean_inc(v_releaseRepo_121_);
lean_inc(v_irDir_120_);
lean_inc(v_binDir_119_);
lean_inc(v_nativeLibDir_118_);
lean_inc(v_leanLibDir_117_);
lean_inc(v_buildDir_116_);
lean_inc(v_srcDir_115_);
lean_inc(v_moreGlobalServerArgs_114_);
lean_inc(v_extraDepTargets_112_);
lean_inc(v_toLeanConfig_110_);
lean_inc(v_toWorkspaceConfig_109_);
lean_dec(v_cfg_108_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_145_ = lean_box(v_bootstrap_111_);
v___x_146_ = lean_apply_1(v_f_107_, v___x_145_);
if (v_isShared_144_ == 0)
{
v___x_148_ = v___x_143_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_toWorkspaceConfig_109_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_toLeanConfig_110_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_extraDepTargets_112_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_moreGlobalServerArgs_114_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_srcDir_115_);
lean_ctor_set(v_reuseFailAlloc_150_, 5, v_buildDir_116_);
lean_ctor_set(v_reuseFailAlloc_150_, 6, v_leanLibDir_117_);
lean_ctor_set(v_reuseFailAlloc_150_, 7, v_nativeLibDir_118_);
lean_ctor_set(v_reuseFailAlloc_150_, 8, v_binDir_119_);
lean_ctor_set(v_reuseFailAlloc_150_, 9, v_irDir_120_);
lean_ctor_set(v_reuseFailAlloc_150_, 10, v_releaseRepo_121_);
lean_ctor_set(v_reuseFailAlloc_150_, 11, v_buildArchive_122_);
lean_ctor_set(v_reuseFailAlloc_150_, 12, v_testDriver_124_);
lean_ctor_set(v_reuseFailAlloc_150_, 13, v_testDriverArgs_125_);
lean_ctor_set(v_reuseFailAlloc_150_, 14, v_lintDriver_126_);
lean_ctor_set(v_reuseFailAlloc_150_, 15, v_lintDriverArgs_127_);
lean_ctor_set(v_reuseFailAlloc_150_, 16, v_version_128_);
lean_ctor_set(v_reuseFailAlloc_150_, 17, v_versionTags_129_);
lean_ctor_set(v_reuseFailAlloc_150_, 18, v_description_130_);
lean_ctor_set(v_reuseFailAlloc_150_, 19, v_keywords_131_);
lean_ctor_set(v_reuseFailAlloc_150_, 20, v_homepage_132_);
lean_ctor_set(v_reuseFailAlloc_150_, 21, v_license_133_);
lean_ctor_set(v_reuseFailAlloc_150_, 22, v_licenseFiles_134_);
lean_ctor_set(v_reuseFailAlloc_150_, 23, v_readmeFile_135_);
lean_ctor_set(v_reuseFailAlloc_150_, 24, v_enableArtifactCache_x3f_137_);
lean_ctor_set(v_reuseFailAlloc_150_, 25, v_restoreAllArtifacts_x3f_138_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
uint8_t v___x_149_; 
v___x_149_ = lean_unbox(v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26, v___x_149_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26 + 1, v_precompileModules_113_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26 + 2, v_preferReleaseBuild_123_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26 + 3, v_reservoir_136_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_139_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26 + 5, v_allowImportAll_140_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*26 + 6, v_fixedToolchain_141_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object* v_x_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object* v_x_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lake_PackageConfig_bootstrap___proj___lam__3(v_x_154_);
lean_dec_ref(v_x_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_166_, lean_object* v_n_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___closed__4));
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_169_, lean_object* v_n_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lake_PackageConfig_bootstrap___proj(v_p_169_, v_n_170_);
lean_dec(v_n_170_);
lean_dec(v_p_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_172_, lean_object* v_n_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lake_PackageConfig_bootstrap___proj(v_p_172_, v_n_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_175_, lean_object* v_n_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_175_, v_n_176_);
lean_dec(v_n_176_);
lean_dec(v_p_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_178_){
_start:
{
lean_object* v_extraDepTargets_179_; 
v_extraDepTargets_179_ = lean_ctor_get(v_cfg_178_, 2);
lean_inc_ref(v_extraDepTargets_179_);
return v_extraDepTargets_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(v_cfg_180_);
lean_dec_ref(v_cfg_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* v_val_182_, lean_object* v_cfg_183_){
_start:
{
lean_object* v_toWorkspaceConfig_184_; lean_object* v_toLeanConfig_185_; uint8_t v_bootstrap_186_; uint8_t v_precompileModules_187_; lean_object* v_moreGlobalServerArgs_188_; lean_object* v_srcDir_189_; lean_object* v_buildDir_190_; lean_object* v_leanLibDir_191_; lean_object* v_nativeLibDir_192_; lean_object* v_binDir_193_; lean_object* v_irDir_194_; lean_object* v_releaseRepo_195_; lean_object* v_buildArchive_196_; uint8_t v_preferReleaseBuild_197_; lean_object* v_testDriver_198_; lean_object* v_testDriverArgs_199_; lean_object* v_lintDriver_200_; lean_object* v_lintDriverArgs_201_; lean_object* v_version_202_; lean_object* v_versionTags_203_; lean_object* v_description_204_; lean_object* v_keywords_205_; lean_object* v_homepage_206_; lean_object* v_license_207_; lean_object* v_licenseFiles_208_; lean_object* v_readmeFile_209_; uint8_t v_reservoir_210_; lean_object* v_enableArtifactCache_x3f_211_; lean_object* v_restoreAllArtifacts_x3f_212_; uint8_t v_libPrefixOnWindows_213_; uint8_t v_allowImportAll_214_; uint8_t v_fixedToolchain_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_toWorkspaceConfig_184_ = lean_ctor_get(v_cfg_183_, 0);
v_toLeanConfig_185_ = lean_ctor_get(v_cfg_183_, 1);
v_bootstrap_186_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26);
v_precompileModules_187_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_188_ = lean_ctor_get(v_cfg_183_, 3);
v_srcDir_189_ = lean_ctor_get(v_cfg_183_, 4);
v_buildDir_190_ = lean_ctor_get(v_cfg_183_, 5);
v_leanLibDir_191_ = lean_ctor_get(v_cfg_183_, 6);
v_nativeLibDir_192_ = lean_ctor_get(v_cfg_183_, 7);
v_binDir_193_ = lean_ctor_get(v_cfg_183_, 8);
v_irDir_194_ = lean_ctor_get(v_cfg_183_, 9);
v_releaseRepo_195_ = lean_ctor_get(v_cfg_183_, 10);
v_buildArchive_196_ = lean_ctor_get(v_cfg_183_, 11);
v_preferReleaseBuild_197_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26 + 2);
v_testDriver_198_ = lean_ctor_get(v_cfg_183_, 12);
v_testDriverArgs_199_ = lean_ctor_get(v_cfg_183_, 13);
v_lintDriver_200_ = lean_ctor_get(v_cfg_183_, 14);
v_lintDriverArgs_201_ = lean_ctor_get(v_cfg_183_, 15);
v_version_202_ = lean_ctor_get(v_cfg_183_, 16);
v_versionTags_203_ = lean_ctor_get(v_cfg_183_, 17);
v_description_204_ = lean_ctor_get(v_cfg_183_, 18);
v_keywords_205_ = lean_ctor_get(v_cfg_183_, 19);
v_homepage_206_ = lean_ctor_get(v_cfg_183_, 20);
v_license_207_ = lean_ctor_get(v_cfg_183_, 21);
v_licenseFiles_208_ = lean_ctor_get(v_cfg_183_, 22);
v_readmeFile_209_ = lean_ctor_get(v_cfg_183_, 23);
v_reservoir_210_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_211_ = lean_ctor_get(v_cfg_183_, 24);
v_restoreAllArtifacts_x3f_212_ = lean_ctor_get(v_cfg_183_, 25);
v_libPrefixOnWindows_213_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26 + 4);
v_allowImportAll_214_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26 + 5);
v_fixedToolchain_215_ = lean_ctor_get_uint8(v_cfg_183_, sizeof(void*)*26 + 6);
v_isSharedCheck_222_ = !lean_is_exclusive(v_cfg_183_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_cfg_183_, 2);
lean_dec(v_unused_223_);
v___x_217_ = v_cfg_183_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_212_);
lean_inc(v_enableArtifactCache_x3f_211_);
lean_inc(v_readmeFile_209_);
lean_inc(v_licenseFiles_208_);
lean_inc(v_license_207_);
lean_inc(v_homepage_206_);
lean_inc(v_keywords_205_);
lean_inc(v_description_204_);
lean_inc(v_versionTags_203_);
lean_inc(v_version_202_);
lean_inc(v_lintDriverArgs_201_);
lean_inc(v_lintDriver_200_);
lean_inc(v_testDriverArgs_199_);
lean_inc(v_testDriver_198_);
lean_inc(v_buildArchive_196_);
lean_inc(v_releaseRepo_195_);
lean_inc(v_irDir_194_);
lean_inc(v_binDir_193_);
lean_inc(v_nativeLibDir_192_);
lean_inc(v_leanLibDir_191_);
lean_inc(v_buildDir_190_);
lean_inc(v_srcDir_189_);
lean_inc(v_moreGlobalServerArgs_188_);
lean_inc(v_toLeanConfig_185_);
lean_inc(v_toWorkspaceConfig_184_);
lean_dec(v_cfg_183_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 2, v_val_182_);
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_toWorkspaceConfig_184_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_toLeanConfig_185_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_val_182_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v_moreGlobalServerArgs_188_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_srcDir_189_);
lean_ctor_set(v_reuseFailAlloc_221_, 5, v_buildDir_190_);
lean_ctor_set(v_reuseFailAlloc_221_, 6, v_leanLibDir_191_);
lean_ctor_set(v_reuseFailAlloc_221_, 7, v_nativeLibDir_192_);
lean_ctor_set(v_reuseFailAlloc_221_, 8, v_binDir_193_);
lean_ctor_set(v_reuseFailAlloc_221_, 9, v_irDir_194_);
lean_ctor_set(v_reuseFailAlloc_221_, 10, v_releaseRepo_195_);
lean_ctor_set(v_reuseFailAlloc_221_, 11, v_buildArchive_196_);
lean_ctor_set(v_reuseFailAlloc_221_, 12, v_testDriver_198_);
lean_ctor_set(v_reuseFailAlloc_221_, 13, v_testDriverArgs_199_);
lean_ctor_set(v_reuseFailAlloc_221_, 14, v_lintDriver_200_);
lean_ctor_set(v_reuseFailAlloc_221_, 15, v_lintDriverArgs_201_);
lean_ctor_set(v_reuseFailAlloc_221_, 16, v_version_202_);
lean_ctor_set(v_reuseFailAlloc_221_, 17, v_versionTags_203_);
lean_ctor_set(v_reuseFailAlloc_221_, 18, v_description_204_);
lean_ctor_set(v_reuseFailAlloc_221_, 19, v_keywords_205_);
lean_ctor_set(v_reuseFailAlloc_221_, 20, v_homepage_206_);
lean_ctor_set(v_reuseFailAlloc_221_, 21, v_license_207_);
lean_ctor_set(v_reuseFailAlloc_221_, 22, v_licenseFiles_208_);
lean_ctor_set(v_reuseFailAlloc_221_, 23, v_readmeFile_209_);
lean_ctor_set(v_reuseFailAlloc_221_, 24, v_enableArtifactCache_x3f_211_);
lean_ctor_set(v_reuseFailAlloc_221_, 25, v_restoreAllArtifacts_x3f_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26, v_bootstrap_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26 + 1, v_precompileModules_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26 + 2, v_preferReleaseBuild_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26 + 3, v_reservoir_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_213_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26 + 5, v_allowImportAll_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_221_, sizeof(void*)*26 + 6, v_fixedToolchain_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* v_f_224_, lean_object* v_cfg_225_){
_start:
{
lean_object* v_toWorkspaceConfig_226_; lean_object* v_toLeanConfig_227_; uint8_t v_bootstrap_228_; lean_object* v_extraDepTargets_229_; uint8_t v_precompileModules_230_; lean_object* v_moreGlobalServerArgs_231_; lean_object* v_srcDir_232_; lean_object* v_buildDir_233_; lean_object* v_leanLibDir_234_; lean_object* v_nativeLibDir_235_; lean_object* v_binDir_236_; lean_object* v_irDir_237_; lean_object* v_releaseRepo_238_; lean_object* v_buildArchive_239_; uint8_t v_preferReleaseBuild_240_; lean_object* v_testDriver_241_; lean_object* v_testDriverArgs_242_; lean_object* v_lintDriver_243_; lean_object* v_lintDriverArgs_244_; lean_object* v_version_245_; lean_object* v_versionTags_246_; lean_object* v_description_247_; lean_object* v_keywords_248_; lean_object* v_homepage_249_; lean_object* v_license_250_; lean_object* v_licenseFiles_251_; lean_object* v_readmeFile_252_; uint8_t v_reservoir_253_; lean_object* v_enableArtifactCache_x3f_254_; lean_object* v_restoreAllArtifacts_x3f_255_; uint8_t v_libPrefixOnWindows_256_; uint8_t v_allowImportAll_257_; uint8_t v_fixedToolchain_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_toWorkspaceConfig_226_ = lean_ctor_get(v_cfg_225_, 0);
v_toLeanConfig_227_ = lean_ctor_get(v_cfg_225_, 1);
v_bootstrap_228_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26);
v_extraDepTargets_229_ = lean_ctor_get(v_cfg_225_, 2);
v_precompileModules_230_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_231_ = lean_ctor_get(v_cfg_225_, 3);
v_srcDir_232_ = lean_ctor_get(v_cfg_225_, 4);
v_buildDir_233_ = lean_ctor_get(v_cfg_225_, 5);
v_leanLibDir_234_ = lean_ctor_get(v_cfg_225_, 6);
v_nativeLibDir_235_ = lean_ctor_get(v_cfg_225_, 7);
v_binDir_236_ = lean_ctor_get(v_cfg_225_, 8);
v_irDir_237_ = lean_ctor_get(v_cfg_225_, 9);
v_releaseRepo_238_ = lean_ctor_get(v_cfg_225_, 10);
v_buildArchive_239_ = lean_ctor_get(v_cfg_225_, 11);
v_preferReleaseBuild_240_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26 + 2);
v_testDriver_241_ = lean_ctor_get(v_cfg_225_, 12);
v_testDriverArgs_242_ = lean_ctor_get(v_cfg_225_, 13);
v_lintDriver_243_ = lean_ctor_get(v_cfg_225_, 14);
v_lintDriverArgs_244_ = lean_ctor_get(v_cfg_225_, 15);
v_version_245_ = lean_ctor_get(v_cfg_225_, 16);
v_versionTags_246_ = lean_ctor_get(v_cfg_225_, 17);
v_description_247_ = lean_ctor_get(v_cfg_225_, 18);
v_keywords_248_ = lean_ctor_get(v_cfg_225_, 19);
v_homepage_249_ = lean_ctor_get(v_cfg_225_, 20);
v_license_250_ = lean_ctor_get(v_cfg_225_, 21);
v_licenseFiles_251_ = lean_ctor_get(v_cfg_225_, 22);
v_readmeFile_252_ = lean_ctor_get(v_cfg_225_, 23);
v_reservoir_253_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_254_ = lean_ctor_get(v_cfg_225_, 24);
v_restoreAllArtifacts_x3f_255_ = lean_ctor_get(v_cfg_225_, 25);
v_libPrefixOnWindows_256_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26 + 4);
v_allowImportAll_257_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26 + 5);
v_fixedToolchain_258_ = lean_ctor_get_uint8(v_cfg_225_, sizeof(void*)*26 + 6);
v_isSharedCheck_266_ = !lean_is_exclusive(v_cfg_225_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v_cfg_225_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_255_);
lean_inc(v_enableArtifactCache_x3f_254_);
lean_inc(v_readmeFile_252_);
lean_inc(v_licenseFiles_251_);
lean_inc(v_license_250_);
lean_inc(v_homepage_249_);
lean_inc(v_keywords_248_);
lean_inc(v_description_247_);
lean_inc(v_versionTags_246_);
lean_inc(v_version_245_);
lean_inc(v_lintDriverArgs_244_);
lean_inc(v_lintDriver_243_);
lean_inc(v_testDriverArgs_242_);
lean_inc(v_testDriver_241_);
lean_inc(v_buildArchive_239_);
lean_inc(v_releaseRepo_238_);
lean_inc(v_irDir_237_);
lean_inc(v_binDir_236_);
lean_inc(v_nativeLibDir_235_);
lean_inc(v_leanLibDir_234_);
lean_inc(v_buildDir_233_);
lean_inc(v_srcDir_232_);
lean_inc(v_moreGlobalServerArgs_231_);
lean_inc(v_extraDepTargets_229_);
lean_inc(v_toLeanConfig_227_);
lean_inc(v_toWorkspaceConfig_226_);
lean_dec(v_cfg_225_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_apply_1(v_f_224_, v_extraDepTargets_229_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 2, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_toWorkspaceConfig_226_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_toLeanConfig_227_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_moreGlobalServerArgs_231_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_srcDir_232_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_buildDir_233_);
lean_ctor_set(v_reuseFailAlloc_265_, 6, v_leanLibDir_234_);
lean_ctor_set(v_reuseFailAlloc_265_, 7, v_nativeLibDir_235_);
lean_ctor_set(v_reuseFailAlloc_265_, 8, v_binDir_236_);
lean_ctor_set(v_reuseFailAlloc_265_, 9, v_irDir_237_);
lean_ctor_set(v_reuseFailAlloc_265_, 10, v_releaseRepo_238_);
lean_ctor_set(v_reuseFailAlloc_265_, 11, v_buildArchive_239_);
lean_ctor_set(v_reuseFailAlloc_265_, 12, v_testDriver_241_);
lean_ctor_set(v_reuseFailAlloc_265_, 13, v_testDriverArgs_242_);
lean_ctor_set(v_reuseFailAlloc_265_, 14, v_lintDriver_243_);
lean_ctor_set(v_reuseFailAlloc_265_, 15, v_lintDriverArgs_244_);
lean_ctor_set(v_reuseFailAlloc_265_, 16, v_version_245_);
lean_ctor_set(v_reuseFailAlloc_265_, 17, v_versionTags_246_);
lean_ctor_set(v_reuseFailAlloc_265_, 18, v_description_247_);
lean_ctor_set(v_reuseFailAlloc_265_, 19, v_keywords_248_);
lean_ctor_set(v_reuseFailAlloc_265_, 20, v_homepage_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 21, v_license_250_);
lean_ctor_set(v_reuseFailAlloc_265_, 22, v_licenseFiles_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 23, v_readmeFile_252_);
lean_ctor_set(v_reuseFailAlloc_265_, 24, v_enableArtifactCache_x3f_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 25, v_restoreAllArtifacts_x3f_255_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26, v_bootstrap_228_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26 + 1, v_precompileModules_230_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26 + 2, v_preferReleaseBuild_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26 + 3, v_reservoir_253_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_256_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26 + 5, v_allowImportAll_257_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*26 + 6, v_fixedToolchain_258_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(v_x_269_);
lean_dec_ref(v_x_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_280_, lean_object* v_n_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_283_, lean_object* v_n_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_283_, v_n_284_);
lean_dec(v_n_284_);
lean_dec(v_p_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_286_, lean_object* v_n_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_286_, v_n_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_289_, lean_object* v_n_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_289_, v_n_290_);
lean_dec(v_n_290_);
lean_dec(v_p_289_);
return v_res_291_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* v_cfg_292_){
_start:
{
uint8_t v_precompileModules_293_; 
v_precompileModules_293_ = lean_ctor_get_uint8(v_cfg_292_, sizeof(void*)*26 + 1);
return v_precompileModules_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Lake_PackageConfig_precompileModules___proj___lam__0(v_cfg_294_);
lean_dec_ref(v_cfg_294_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t v_val_297_, lean_object* v_cfg_298_){
_start:
{
lean_object* v_toWorkspaceConfig_299_; lean_object* v_toLeanConfig_300_; uint8_t v_bootstrap_301_; lean_object* v_extraDepTargets_302_; lean_object* v_moreGlobalServerArgs_303_; lean_object* v_srcDir_304_; lean_object* v_buildDir_305_; lean_object* v_leanLibDir_306_; lean_object* v_nativeLibDir_307_; lean_object* v_binDir_308_; lean_object* v_irDir_309_; lean_object* v_releaseRepo_310_; lean_object* v_buildArchive_311_; uint8_t v_preferReleaseBuild_312_; lean_object* v_testDriver_313_; lean_object* v_testDriverArgs_314_; lean_object* v_lintDriver_315_; lean_object* v_lintDriverArgs_316_; lean_object* v_version_317_; lean_object* v_versionTags_318_; lean_object* v_description_319_; lean_object* v_keywords_320_; lean_object* v_homepage_321_; lean_object* v_license_322_; lean_object* v_licenseFiles_323_; lean_object* v_readmeFile_324_; uint8_t v_reservoir_325_; lean_object* v_enableArtifactCache_x3f_326_; lean_object* v_restoreAllArtifacts_x3f_327_; uint8_t v_libPrefixOnWindows_328_; uint8_t v_allowImportAll_329_; uint8_t v_fixedToolchain_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_toWorkspaceConfig_299_ = lean_ctor_get(v_cfg_298_, 0);
v_toLeanConfig_300_ = lean_ctor_get(v_cfg_298_, 1);
v_bootstrap_301_ = lean_ctor_get_uint8(v_cfg_298_, sizeof(void*)*26);
v_extraDepTargets_302_ = lean_ctor_get(v_cfg_298_, 2);
v_moreGlobalServerArgs_303_ = lean_ctor_get(v_cfg_298_, 3);
v_srcDir_304_ = lean_ctor_get(v_cfg_298_, 4);
v_buildDir_305_ = lean_ctor_get(v_cfg_298_, 5);
v_leanLibDir_306_ = lean_ctor_get(v_cfg_298_, 6);
v_nativeLibDir_307_ = lean_ctor_get(v_cfg_298_, 7);
v_binDir_308_ = lean_ctor_get(v_cfg_298_, 8);
v_irDir_309_ = lean_ctor_get(v_cfg_298_, 9);
v_releaseRepo_310_ = lean_ctor_get(v_cfg_298_, 10);
v_buildArchive_311_ = lean_ctor_get(v_cfg_298_, 11);
v_preferReleaseBuild_312_ = lean_ctor_get_uint8(v_cfg_298_, sizeof(void*)*26 + 2);
v_testDriver_313_ = lean_ctor_get(v_cfg_298_, 12);
v_testDriverArgs_314_ = lean_ctor_get(v_cfg_298_, 13);
v_lintDriver_315_ = lean_ctor_get(v_cfg_298_, 14);
v_lintDriverArgs_316_ = lean_ctor_get(v_cfg_298_, 15);
v_version_317_ = lean_ctor_get(v_cfg_298_, 16);
v_versionTags_318_ = lean_ctor_get(v_cfg_298_, 17);
v_description_319_ = lean_ctor_get(v_cfg_298_, 18);
v_keywords_320_ = lean_ctor_get(v_cfg_298_, 19);
v_homepage_321_ = lean_ctor_get(v_cfg_298_, 20);
v_license_322_ = lean_ctor_get(v_cfg_298_, 21);
v_licenseFiles_323_ = lean_ctor_get(v_cfg_298_, 22);
v_readmeFile_324_ = lean_ctor_get(v_cfg_298_, 23);
v_reservoir_325_ = lean_ctor_get_uint8(v_cfg_298_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_326_ = lean_ctor_get(v_cfg_298_, 24);
v_restoreAllArtifacts_x3f_327_ = lean_ctor_get(v_cfg_298_, 25);
v_libPrefixOnWindows_328_ = lean_ctor_get_uint8(v_cfg_298_, sizeof(void*)*26 + 4);
v_allowImportAll_329_ = lean_ctor_get_uint8(v_cfg_298_, sizeof(void*)*26 + 5);
v_fixedToolchain_330_ = lean_ctor_get_uint8(v_cfg_298_, sizeof(void*)*26 + 6);
v_isSharedCheck_337_ = !lean_is_exclusive(v_cfg_298_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v_cfg_298_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_327_);
lean_inc(v_enableArtifactCache_x3f_326_);
lean_inc(v_readmeFile_324_);
lean_inc(v_licenseFiles_323_);
lean_inc(v_license_322_);
lean_inc(v_homepage_321_);
lean_inc(v_keywords_320_);
lean_inc(v_description_319_);
lean_inc(v_versionTags_318_);
lean_inc(v_version_317_);
lean_inc(v_lintDriverArgs_316_);
lean_inc(v_lintDriver_315_);
lean_inc(v_testDriverArgs_314_);
lean_inc(v_testDriver_313_);
lean_inc(v_buildArchive_311_);
lean_inc(v_releaseRepo_310_);
lean_inc(v_irDir_309_);
lean_inc(v_binDir_308_);
lean_inc(v_nativeLibDir_307_);
lean_inc(v_leanLibDir_306_);
lean_inc(v_buildDir_305_);
lean_inc(v_srcDir_304_);
lean_inc(v_moreGlobalServerArgs_303_);
lean_inc(v_extraDepTargets_302_);
lean_inc(v_toLeanConfig_300_);
lean_inc(v_toWorkspaceConfig_299_);
lean_dec(v_cfg_298_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_toWorkspaceConfig_299_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_toLeanConfig_300_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_extraDepTargets_302_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_moreGlobalServerArgs_303_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_srcDir_304_);
lean_ctor_set(v_reuseFailAlloc_336_, 5, v_buildDir_305_);
lean_ctor_set(v_reuseFailAlloc_336_, 6, v_leanLibDir_306_);
lean_ctor_set(v_reuseFailAlloc_336_, 7, v_nativeLibDir_307_);
lean_ctor_set(v_reuseFailAlloc_336_, 8, v_binDir_308_);
lean_ctor_set(v_reuseFailAlloc_336_, 9, v_irDir_309_);
lean_ctor_set(v_reuseFailAlloc_336_, 10, v_releaseRepo_310_);
lean_ctor_set(v_reuseFailAlloc_336_, 11, v_buildArchive_311_);
lean_ctor_set(v_reuseFailAlloc_336_, 12, v_testDriver_313_);
lean_ctor_set(v_reuseFailAlloc_336_, 13, v_testDriverArgs_314_);
lean_ctor_set(v_reuseFailAlloc_336_, 14, v_lintDriver_315_);
lean_ctor_set(v_reuseFailAlloc_336_, 15, v_lintDriverArgs_316_);
lean_ctor_set(v_reuseFailAlloc_336_, 16, v_version_317_);
lean_ctor_set(v_reuseFailAlloc_336_, 17, v_versionTags_318_);
lean_ctor_set(v_reuseFailAlloc_336_, 18, v_description_319_);
lean_ctor_set(v_reuseFailAlloc_336_, 19, v_keywords_320_);
lean_ctor_set(v_reuseFailAlloc_336_, 20, v_homepage_321_);
lean_ctor_set(v_reuseFailAlloc_336_, 21, v_license_322_);
lean_ctor_set(v_reuseFailAlloc_336_, 22, v_licenseFiles_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 23, v_readmeFile_324_);
lean_ctor_set(v_reuseFailAlloc_336_, 24, v_enableArtifactCache_x3f_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 25, v_restoreAllArtifacts_x3f_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*26, v_bootstrap_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*26 + 2, v_preferReleaseBuild_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*26 + 3, v_reservoir_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*26 + 5, v_allowImportAll_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*26 + 6, v_fixedToolchain_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*26 + 1, v_val_297_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_338_, lean_object* v_cfg_339_){
_start:
{
uint8_t v_val_134__boxed_340_; lean_object* v_res_341_; 
v_val_134__boxed_340_ = lean_unbox(v_val_338_);
v_res_341_ = l_Lake_PackageConfig_precompileModules___proj___lam__1(v_val_134__boxed_340_, v_cfg_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* v_f_342_, lean_object* v_cfg_343_){
_start:
{
lean_object* v_toWorkspaceConfig_344_; lean_object* v_toLeanConfig_345_; uint8_t v_bootstrap_346_; lean_object* v_extraDepTargets_347_; uint8_t v_precompileModules_348_; lean_object* v_moreGlobalServerArgs_349_; lean_object* v_srcDir_350_; lean_object* v_buildDir_351_; lean_object* v_leanLibDir_352_; lean_object* v_nativeLibDir_353_; lean_object* v_binDir_354_; lean_object* v_irDir_355_; lean_object* v_releaseRepo_356_; lean_object* v_buildArchive_357_; uint8_t v_preferReleaseBuild_358_; lean_object* v_testDriver_359_; lean_object* v_testDriverArgs_360_; lean_object* v_lintDriver_361_; lean_object* v_lintDriverArgs_362_; lean_object* v_version_363_; lean_object* v_versionTags_364_; lean_object* v_description_365_; lean_object* v_keywords_366_; lean_object* v_homepage_367_; lean_object* v_license_368_; lean_object* v_licenseFiles_369_; lean_object* v_readmeFile_370_; uint8_t v_reservoir_371_; lean_object* v_enableArtifactCache_x3f_372_; lean_object* v_restoreAllArtifacts_x3f_373_; uint8_t v_libPrefixOnWindows_374_; uint8_t v_allowImportAll_375_; uint8_t v_fixedToolchain_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_386_; 
v_toWorkspaceConfig_344_ = lean_ctor_get(v_cfg_343_, 0);
v_toLeanConfig_345_ = lean_ctor_get(v_cfg_343_, 1);
v_bootstrap_346_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26);
v_extraDepTargets_347_ = lean_ctor_get(v_cfg_343_, 2);
v_precompileModules_348_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_349_ = lean_ctor_get(v_cfg_343_, 3);
v_srcDir_350_ = lean_ctor_get(v_cfg_343_, 4);
v_buildDir_351_ = lean_ctor_get(v_cfg_343_, 5);
v_leanLibDir_352_ = lean_ctor_get(v_cfg_343_, 6);
v_nativeLibDir_353_ = lean_ctor_get(v_cfg_343_, 7);
v_binDir_354_ = lean_ctor_get(v_cfg_343_, 8);
v_irDir_355_ = lean_ctor_get(v_cfg_343_, 9);
v_releaseRepo_356_ = lean_ctor_get(v_cfg_343_, 10);
v_buildArchive_357_ = lean_ctor_get(v_cfg_343_, 11);
v_preferReleaseBuild_358_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26 + 2);
v_testDriver_359_ = lean_ctor_get(v_cfg_343_, 12);
v_testDriverArgs_360_ = lean_ctor_get(v_cfg_343_, 13);
v_lintDriver_361_ = lean_ctor_get(v_cfg_343_, 14);
v_lintDriverArgs_362_ = lean_ctor_get(v_cfg_343_, 15);
v_version_363_ = lean_ctor_get(v_cfg_343_, 16);
v_versionTags_364_ = lean_ctor_get(v_cfg_343_, 17);
v_description_365_ = lean_ctor_get(v_cfg_343_, 18);
v_keywords_366_ = lean_ctor_get(v_cfg_343_, 19);
v_homepage_367_ = lean_ctor_get(v_cfg_343_, 20);
v_license_368_ = lean_ctor_get(v_cfg_343_, 21);
v_licenseFiles_369_ = lean_ctor_get(v_cfg_343_, 22);
v_readmeFile_370_ = lean_ctor_get(v_cfg_343_, 23);
v_reservoir_371_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_372_ = lean_ctor_get(v_cfg_343_, 24);
v_restoreAllArtifacts_x3f_373_ = lean_ctor_get(v_cfg_343_, 25);
v_libPrefixOnWindows_374_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26 + 4);
v_allowImportAll_375_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26 + 5);
v_fixedToolchain_376_ = lean_ctor_get_uint8(v_cfg_343_, sizeof(void*)*26 + 6);
v_isSharedCheck_386_ = !lean_is_exclusive(v_cfg_343_);
if (v_isSharedCheck_386_ == 0)
{
v___x_378_ = v_cfg_343_;
v_isShared_379_ = v_isSharedCheck_386_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_373_);
lean_inc(v_enableArtifactCache_x3f_372_);
lean_inc(v_readmeFile_370_);
lean_inc(v_licenseFiles_369_);
lean_inc(v_license_368_);
lean_inc(v_homepage_367_);
lean_inc(v_keywords_366_);
lean_inc(v_description_365_);
lean_inc(v_versionTags_364_);
lean_inc(v_version_363_);
lean_inc(v_lintDriverArgs_362_);
lean_inc(v_lintDriver_361_);
lean_inc(v_testDriverArgs_360_);
lean_inc(v_testDriver_359_);
lean_inc(v_buildArchive_357_);
lean_inc(v_releaseRepo_356_);
lean_inc(v_irDir_355_);
lean_inc(v_binDir_354_);
lean_inc(v_nativeLibDir_353_);
lean_inc(v_leanLibDir_352_);
lean_inc(v_buildDir_351_);
lean_inc(v_srcDir_350_);
lean_inc(v_moreGlobalServerArgs_349_);
lean_inc(v_extraDepTargets_347_);
lean_inc(v_toLeanConfig_345_);
lean_inc(v_toWorkspaceConfig_344_);
lean_dec(v_cfg_343_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_386_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = lean_box(v_precompileModules_348_);
v___x_381_ = lean_apply_1(v_f_342_, v___x_380_);
if (v_isShared_379_ == 0)
{
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_toWorkspaceConfig_344_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_toLeanConfig_345_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_extraDepTargets_347_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_moreGlobalServerArgs_349_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v_srcDir_350_);
lean_ctor_set(v_reuseFailAlloc_385_, 5, v_buildDir_351_);
lean_ctor_set(v_reuseFailAlloc_385_, 6, v_leanLibDir_352_);
lean_ctor_set(v_reuseFailAlloc_385_, 7, v_nativeLibDir_353_);
lean_ctor_set(v_reuseFailAlloc_385_, 8, v_binDir_354_);
lean_ctor_set(v_reuseFailAlloc_385_, 9, v_irDir_355_);
lean_ctor_set(v_reuseFailAlloc_385_, 10, v_releaseRepo_356_);
lean_ctor_set(v_reuseFailAlloc_385_, 11, v_buildArchive_357_);
lean_ctor_set(v_reuseFailAlloc_385_, 12, v_testDriver_359_);
lean_ctor_set(v_reuseFailAlloc_385_, 13, v_testDriverArgs_360_);
lean_ctor_set(v_reuseFailAlloc_385_, 14, v_lintDriver_361_);
lean_ctor_set(v_reuseFailAlloc_385_, 15, v_lintDriverArgs_362_);
lean_ctor_set(v_reuseFailAlloc_385_, 16, v_version_363_);
lean_ctor_set(v_reuseFailAlloc_385_, 17, v_versionTags_364_);
lean_ctor_set(v_reuseFailAlloc_385_, 18, v_description_365_);
lean_ctor_set(v_reuseFailAlloc_385_, 19, v_keywords_366_);
lean_ctor_set(v_reuseFailAlloc_385_, 20, v_homepage_367_);
lean_ctor_set(v_reuseFailAlloc_385_, 21, v_license_368_);
lean_ctor_set(v_reuseFailAlloc_385_, 22, v_licenseFiles_369_);
lean_ctor_set(v_reuseFailAlloc_385_, 23, v_readmeFile_370_);
lean_ctor_set(v_reuseFailAlloc_385_, 24, v_enableArtifactCache_x3f_372_);
lean_ctor_set(v_reuseFailAlloc_385_, 25, v_restoreAllArtifacts_x3f_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_385_, sizeof(void*)*26, v_bootstrap_346_);
v___x_383_ = v_reuseFailAlloc_385_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
uint8_t v___x_384_; 
v___x_384_ = lean_unbox(v___x_381_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*26 + 1, v___x_384_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*26 + 2, v_preferReleaseBuild_358_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*26 + 3, v_reservoir_371_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_374_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*26 + 5, v_allowImportAll_375_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*26 + 6, v_fixedToolchain_376_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_395_, lean_object* v_n_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_398_, lean_object* v_n_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lake_PackageConfig_precompileModules___proj(v_p_398_, v_n_399_);
lean_dec(v_n_399_);
lean_dec(v_p_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_401_, lean_object* v_n_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lake_PackageConfig_precompileModules___proj(v_p_401_, v_n_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_404_, lean_object* v_n_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_404_, v_n_405_);
lean_dec(v_n_405_);
lean_dec(v_p_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* v_cfg_407_){
_start:
{
lean_object* v_moreGlobalServerArgs_408_; 
v_moreGlobalServerArgs_408_ = lean_ctor_get(v_cfg_407_, 3);
lean_inc_ref(v_moreGlobalServerArgs_408_);
return v_moreGlobalServerArgs_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* v_cfg_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(v_cfg_409_);
lean_dec_ref(v_cfg_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* v_val_411_, lean_object* v_cfg_412_){
_start:
{
lean_object* v_toWorkspaceConfig_413_; lean_object* v_toLeanConfig_414_; uint8_t v_bootstrap_415_; lean_object* v_extraDepTargets_416_; uint8_t v_precompileModules_417_; lean_object* v_srcDir_418_; lean_object* v_buildDir_419_; lean_object* v_leanLibDir_420_; lean_object* v_nativeLibDir_421_; lean_object* v_binDir_422_; lean_object* v_irDir_423_; lean_object* v_releaseRepo_424_; lean_object* v_buildArchive_425_; uint8_t v_preferReleaseBuild_426_; lean_object* v_testDriver_427_; lean_object* v_testDriverArgs_428_; lean_object* v_lintDriver_429_; lean_object* v_lintDriverArgs_430_; lean_object* v_version_431_; lean_object* v_versionTags_432_; lean_object* v_description_433_; lean_object* v_keywords_434_; lean_object* v_homepage_435_; lean_object* v_license_436_; lean_object* v_licenseFiles_437_; lean_object* v_readmeFile_438_; uint8_t v_reservoir_439_; lean_object* v_enableArtifactCache_x3f_440_; lean_object* v_restoreAllArtifacts_x3f_441_; uint8_t v_libPrefixOnWindows_442_; uint8_t v_allowImportAll_443_; uint8_t v_fixedToolchain_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_toWorkspaceConfig_413_ = lean_ctor_get(v_cfg_412_, 0);
v_toLeanConfig_414_ = lean_ctor_get(v_cfg_412_, 1);
v_bootstrap_415_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26);
v_extraDepTargets_416_ = lean_ctor_get(v_cfg_412_, 2);
v_precompileModules_417_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26 + 1);
v_srcDir_418_ = lean_ctor_get(v_cfg_412_, 4);
v_buildDir_419_ = lean_ctor_get(v_cfg_412_, 5);
v_leanLibDir_420_ = lean_ctor_get(v_cfg_412_, 6);
v_nativeLibDir_421_ = lean_ctor_get(v_cfg_412_, 7);
v_binDir_422_ = lean_ctor_get(v_cfg_412_, 8);
v_irDir_423_ = lean_ctor_get(v_cfg_412_, 9);
v_releaseRepo_424_ = lean_ctor_get(v_cfg_412_, 10);
v_buildArchive_425_ = lean_ctor_get(v_cfg_412_, 11);
v_preferReleaseBuild_426_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26 + 2);
v_testDriver_427_ = lean_ctor_get(v_cfg_412_, 12);
v_testDriverArgs_428_ = lean_ctor_get(v_cfg_412_, 13);
v_lintDriver_429_ = lean_ctor_get(v_cfg_412_, 14);
v_lintDriverArgs_430_ = lean_ctor_get(v_cfg_412_, 15);
v_version_431_ = lean_ctor_get(v_cfg_412_, 16);
v_versionTags_432_ = lean_ctor_get(v_cfg_412_, 17);
v_description_433_ = lean_ctor_get(v_cfg_412_, 18);
v_keywords_434_ = lean_ctor_get(v_cfg_412_, 19);
v_homepage_435_ = lean_ctor_get(v_cfg_412_, 20);
v_license_436_ = lean_ctor_get(v_cfg_412_, 21);
v_licenseFiles_437_ = lean_ctor_get(v_cfg_412_, 22);
v_readmeFile_438_ = lean_ctor_get(v_cfg_412_, 23);
v_reservoir_439_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_440_ = lean_ctor_get(v_cfg_412_, 24);
v_restoreAllArtifacts_x3f_441_ = lean_ctor_get(v_cfg_412_, 25);
v_libPrefixOnWindows_442_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26 + 4);
v_allowImportAll_443_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26 + 5);
v_fixedToolchain_444_ = lean_ctor_get_uint8(v_cfg_412_, sizeof(void*)*26 + 6);
v_isSharedCheck_451_ = !lean_is_exclusive(v_cfg_412_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v_cfg_412_, 3);
lean_dec(v_unused_452_);
v___x_446_ = v_cfg_412_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_441_);
lean_inc(v_enableArtifactCache_x3f_440_);
lean_inc(v_readmeFile_438_);
lean_inc(v_licenseFiles_437_);
lean_inc(v_license_436_);
lean_inc(v_homepage_435_);
lean_inc(v_keywords_434_);
lean_inc(v_description_433_);
lean_inc(v_versionTags_432_);
lean_inc(v_version_431_);
lean_inc(v_lintDriverArgs_430_);
lean_inc(v_lintDriver_429_);
lean_inc(v_testDriverArgs_428_);
lean_inc(v_testDriver_427_);
lean_inc(v_buildArchive_425_);
lean_inc(v_releaseRepo_424_);
lean_inc(v_irDir_423_);
lean_inc(v_binDir_422_);
lean_inc(v_nativeLibDir_421_);
lean_inc(v_leanLibDir_420_);
lean_inc(v_buildDir_419_);
lean_inc(v_srcDir_418_);
lean_inc(v_extraDepTargets_416_);
lean_inc(v_toLeanConfig_414_);
lean_inc(v_toWorkspaceConfig_413_);
lean_dec(v_cfg_412_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 3, v_val_411_);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_toWorkspaceConfig_413_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_toLeanConfig_414_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_extraDepTargets_416_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_val_411_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_srcDir_418_);
lean_ctor_set(v_reuseFailAlloc_450_, 5, v_buildDir_419_);
lean_ctor_set(v_reuseFailAlloc_450_, 6, v_leanLibDir_420_);
lean_ctor_set(v_reuseFailAlloc_450_, 7, v_nativeLibDir_421_);
lean_ctor_set(v_reuseFailAlloc_450_, 8, v_binDir_422_);
lean_ctor_set(v_reuseFailAlloc_450_, 9, v_irDir_423_);
lean_ctor_set(v_reuseFailAlloc_450_, 10, v_releaseRepo_424_);
lean_ctor_set(v_reuseFailAlloc_450_, 11, v_buildArchive_425_);
lean_ctor_set(v_reuseFailAlloc_450_, 12, v_testDriver_427_);
lean_ctor_set(v_reuseFailAlloc_450_, 13, v_testDriverArgs_428_);
lean_ctor_set(v_reuseFailAlloc_450_, 14, v_lintDriver_429_);
lean_ctor_set(v_reuseFailAlloc_450_, 15, v_lintDriverArgs_430_);
lean_ctor_set(v_reuseFailAlloc_450_, 16, v_version_431_);
lean_ctor_set(v_reuseFailAlloc_450_, 17, v_versionTags_432_);
lean_ctor_set(v_reuseFailAlloc_450_, 18, v_description_433_);
lean_ctor_set(v_reuseFailAlloc_450_, 19, v_keywords_434_);
lean_ctor_set(v_reuseFailAlloc_450_, 20, v_homepage_435_);
lean_ctor_set(v_reuseFailAlloc_450_, 21, v_license_436_);
lean_ctor_set(v_reuseFailAlloc_450_, 22, v_licenseFiles_437_);
lean_ctor_set(v_reuseFailAlloc_450_, 23, v_readmeFile_438_);
lean_ctor_set(v_reuseFailAlloc_450_, 24, v_enableArtifactCache_x3f_440_);
lean_ctor_set(v_reuseFailAlloc_450_, 25, v_restoreAllArtifacts_x3f_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26, v_bootstrap_415_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26 + 1, v_precompileModules_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26 + 2, v_preferReleaseBuild_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26 + 3, v_reservoir_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26 + 5, v_allowImportAll_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*26 + 6, v_fixedToolchain_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object* v_f_453_, lean_object* v_cfg_454_){
_start:
{
lean_object* v_toWorkspaceConfig_455_; lean_object* v_toLeanConfig_456_; uint8_t v_bootstrap_457_; lean_object* v_extraDepTargets_458_; uint8_t v_precompileModules_459_; lean_object* v_moreGlobalServerArgs_460_; lean_object* v_srcDir_461_; lean_object* v_buildDir_462_; lean_object* v_leanLibDir_463_; lean_object* v_nativeLibDir_464_; lean_object* v_binDir_465_; lean_object* v_irDir_466_; lean_object* v_releaseRepo_467_; lean_object* v_buildArchive_468_; uint8_t v_preferReleaseBuild_469_; lean_object* v_testDriver_470_; lean_object* v_testDriverArgs_471_; lean_object* v_lintDriver_472_; lean_object* v_lintDriverArgs_473_; lean_object* v_version_474_; lean_object* v_versionTags_475_; lean_object* v_description_476_; lean_object* v_keywords_477_; lean_object* v_homepage_478_; lean_object* v_license_479_; lean_object* v_licenseFiles_480_; lean_object* v_readmeFile_481_; uint8_t v_reservoir_482_; lean_object* v_enableArtifactCache_x3f_483_; lean_object* v_restoreAllArtifacts_x3f_484_; uint8_t v_libPrefixOnWindows_485_; uint8_t v_allowImportAll_486_; uint8_t v_fixedToolchain_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
v_toWorkspaceConfig_455_ = lean_ctor_get(v_cfg_454_, 0);
v_toLeanConfig_456_ = lean_ctor_get(v_cfg_454_, 1);
v_bootstrap_457_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26);
v_extraDepTargets_458_ = lean_ctor_get(v_cfg_454_, 2);
v_precompileModules_459_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_460_ = lean_ctor_get(v_cfg_454_, 3);
v_srcDir_461_ = lean_ctor_get(v_cfg_454_, 4);
v_buildDir_462_ = lean_ctor_get(v_cfg_454_, 5);
v_leanLibDir_463_ = lean_ctor_get(v_cfg_454_, 6);
v_nativeLibDir_464_ = lean_ctor_get(v_cfg_454_, 7);
v_binDir_465_ = lean_ctor_get(v_cfg_454_, 8);
v_irDir_466_ = lean_ctor_get(v_cfg_454_, 9);
v_releaseRepo_467_ = lean_ctor_get(v_cfg_454_, 10);
v_buildArchive_468_ = lean_ctor_get(v_cfg_454_, 11);
v_preferReleaseBuild_469_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26 + 2);
v_testDriver_470_ = lean_ctor_get(v_cfg_454_, 12);
v_testDriverArgs_471_ = lean_ctor_get(v_cfg_454_, 13);
v_lintDriver_472_ = lean_ctor_get(v_cfg_454_, 14);
v_lintDriverArgs_473_ = lean_ctor_get(v_cfg_454_, 15);
v_version_474_ = lean_ctor_get(v_cfg_454_, 16);
v_versionTags_475_ = lean_ctor_get(v_cfg_454_, 17);
v_description_476_ = lean_ctor_get(v_cfg_454_, 18);
v_keywords_477_ = lean_ctor_get(v_cfg_454_, 19);
v_homepage_478_ = lean_ctor_get(v_cfg_454_, 20);
v_license_479_ = lean_ctor_get(v_cfg_454_, 21);
v_licenseFiles_480_ = lean_ctor_get(v_cfg_454_, 22);
v_readmeFile_481_ = lean_ctor_get(v_cfg_454_, 23);
v_reservoir_482_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_483_ = lean_ctor_get(v_cfg_454_, 24);
v_restoreAllArtifacts_x3f_484_ = lean_ctor_get(v_cfg_454_, 25);
v_libPrefixOnWindows_485_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26 + 4);
v_allowImportAll_486_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26 + 5);
v_fixedToolchain_487_ = lean_ctor_get_uint8(v_cfg_454_, sizeof(void*)*26 + 6);
v_isSharedCheck_495_ = !lean_is_exclusive(v_cfg_454_);
if (v_isSharedCheck_495_ == 0)
{
v___x_489_ = v_cfg_454_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_484_);
lean_inc(v_enableArtifactCache_x3f_483_);
lean_inc(v_readmeFile_481_);
lean_inc(v_licenseFiles_480_);
lean_inc(v_license_479_);
lean_inc(v_homepage_478_);
lean_inc(v_keywords_477_);
lean_inc(v_description_476_);
lean_inc(v_versionTags_475_);
lean_inc(v_version_474_);
lean_inc(v_lintDriverArgs_473_);
lean_inc(v_lintDriver_472_);
lean_inc(v_testDriverArgs_471_);
lean_inc(v_testDriver_470_);
lean_inc(v_buildArchive_468_);
lean_inc(v_releaseRepo_467_);
lean_inc(v_irDir_466_);
lean_inc(v_binDir_465_);
lean_inc(v_nativeLibDir_464_);
lean_inc(v_leanLibDir_463_);
lean_inc(v_buildDir_462_);
lean_inc(v_srcDir_461_);
lean_inc(v_moreGlobalServerArgs_460_);
lean_inc(v_extraDepTargets_458_);
lean_inc(v_toLeanConfig_456_);
lean_inc(v_toWorkspaceConfig_455_);
lean_dec(v_cfg_454_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_apply_1(v_f_453_, v_moreGlobalServerArgs_460_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 3, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_toWorkspaceConfig_455_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_toLeanConfig_456_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_extraDepTargets_458_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_srcDir_461_);
lean_ctor_set(v_reuseFailAlloc_494_, 5, v_buildDir_462_);
lean_ctor_set(v_reuseFailAlloc_494_, 6, v_leanLibDir_463_);
lean_ctor_set(v_reuseFailAlloc_494_, 7, v_nativeLibDir_464_);
lean_ctor_set(v_reuseFailAlloc_494_, 8, v_binDir_465_);
lean_ctor_set(v_reuseFailAlloc_494_, 9, v_irDir_466_);
lean_ctor_set(v_reuseFailAlloc_494_, 10, v_releaseRepo_467_);
lean_ctor_set(v_reuseFailAlloc_494_, 11, v_buildArchive_468_);
lean_ctor_set(v_reuseFailAlloc_494_, 12, v_testDriver_470_);
lean_ctor_set(v_reuseFailAlloc_494_, 13, v_testDriverArgs_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 14, v_lintDriver_472_);
lean_ctor_set(v_reuseFailAlloc_494_, 15, v_lintDriverArgs_473_);
lean_ctor_set(v_reuseFailAlloc_494_, 16, v_version_474_);
lean_ctor_set(v_reuseFailAlloc_494_, 17, v_versionTags_475_);
lean_ctor_set(v_reuseFailAlloc_494_, 18, v_description_476_);
lean_ctor_set(v_reuseFailAlloc_494_, 19, v_keywords_477_);
lean_ctor_set(v_reuseFailAlloc_494_, 20, v_homepage_478_);
lean_ctor_set(v_reuseFailAlloc_494_, 21, v_license_479_);
lean_ctor_set(v_reuseFailAlloc_494_, 22, v_licenseFiles_480_);
lean_ctor_set(v_reuseFailAlloc_494_, 23, v_readmeFile_481_);
lean_ctor_set(v_reuseFailAlloc_494_, 24, v_enableArtifactCache_x3f_483_);
lean_ctor_set(v_reuseFailAlloc_494_, 25, v_restoreAllArtifacts_x3f_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26, v_bootstrap_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26 + 1, v_precompileModules_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26 + 2, v_preferReleaseBuild_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26 + 3, v_reservoir_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26 + 5, v_allowImportAll_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_494_, sizeof(void*)*26 + 6, v_fixedToolchain_487_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* v_x_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(v_x_500_);
lean_dec_ref(v_x_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_511_, lean_object* v_n_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_514_, lean_object* v_n_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_514_, v_n_515_);
lean_dec(v_n_515_);
lean_dec(v_p_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_517_, lean_object* v_n_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_517_, v_n_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_520_, lean_object* v_n_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_520_, v_n_521_);
lean_dec(v_n_521_);
lean_dec(v_p_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_523_, lean_object* v_n_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_523_, v_n_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_526_, lean_object* v_n_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_526_, v_n_527_);
lean_dec(v_n_527_);
lean_dec(v_p_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* v_cfg_529_){
_start:
{
lean_object* v_srcDir_530_; 
v_srcDir_530_ = lean_ctor_get(v_cfg_529_, 4);
lean_inc_ref(v_srcDir_530_);
return v_srcDir_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lake_PackageConfig_srcDir___proj___lam__0(v_cfg_531_);
lean_dec_ref(v_cfg_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* v_val_533_, lean_object* v_cfg_534_){
_start:
{
lean_object* v_toWorkspaceConfig_535_; lean_object* v_toLeanConfig_536_; uint8_t v_bootstrap_537_; lean_object* v_extraDepTargets_538_; uint8_t v_precompileModules_539_; lean_object* v_moreGlobalServerArgs_540_; lean_object* v_buildDir_541_; lean_object* v_leanLibDir_542_; lean_object* v_nativeLibDir_543_; lean_object* v_binDir_544_; lean_object* v_irDir_545_; lean_object* v_releaseRepo_546_; lean_object* v_buildArchive_547_; uint8_t v_preferReleaseBuild_548_; lean_object* v_testDriver_549_; lean_object* v_testDriverArgs_550_; lean_object* v_lintDriver_551_; lean_object* v_lintDriverArgs_552_; lean_object* v_version_553_; lean_object* v_versionTags_554_; lean_object* v_description_555_; lean_object* v_keywords_556_; lean_object* v_homepage_557_; lean_object* v_license_558_; lean_object* v_licenseFiles_559_; lean_object* v_readmeFile_560_; uint8_t v_reservoir_561_; lean_object* v_enableArtifactCache_x3f_562_; lean_object* v_restoreAllArtifacts_x3f_563_; uint8_t v_libPrefixOnWindows_564_; uint8_t v_allowImportAll_565_; uint8_t v_fixedToolchain_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_toWorkspaceConfig_535_ = lean_ctor_get(v_cfg_534_, 0);
v_toLeanConfig_536_ = lean_ctor_get(v_cfg_534_, 1);
v_bootstrap_537_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26);
v_extraDepTargets_538_ = lean_ctor_get(v_cfg_534_, 2);
v_precompileModules_539_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_540_ = lean_ctor_get(v_cfg_534_, 3);
v_buildDir_541_ = lean_ctor_get(v_cfg_534_, 5);
v_leanLibDir_542_ = lean_ctor_get(v_cfg_534_, 6);
v_nativeLibDir_543_ = lean_ctor_get(v_cfg_534_, 7);
v_binDir_544_ = lean_ctor_get(v_cfg_534_, 8);
v_irDir_545_ = lean_ctor_get(v_cfg_534_, 9);
v_releaseRepo_546_ = lean_ctor_get(v_cfg_534_, 10);
v_buildArchive_547_ = lean_ctor_get(v_cfg_534_, 11);
v_preferReleaseBuild_548_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26 + 2);
v_testDriver_549_ = lean_ctor_get(v_cfg_534_, 12);
v_testDriverArgs_550_ = lean_ctor_get(v_cfg_534_, 13);
v_lintDriver_551_ = lean_ctor_get(v_cfg_534_, 14);
v_lintDriverArgs_552_ = lean_ctor_get(v_cfg_534_, 15);
v_version_553_ = lean_ctor_get(v_cfg_534_, 16);
v_versionTags_554_ = lean_ctor_get(v_cfg_534_, 17);
v_description_555_ = lean_ctor_get(v_cfg_534_, 18);
v_keywords_556_ = lean_ctor_get(v_cfg_534_, 19);
v_homepage_557_ = lean_ctor_get(v_cfg_534_, 20);
v_license_558_ = lean_ctor_get(v_cfg_534_, 21);
v_licenseFiles_559_ = lean_ctor_get(v_cfg_534_, 22);
v_readmeFile_560_ = lean_ctor_get(v_cfg_534_, 23);
v_reservoir_561_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_562_ = lean_ctor_get(v_cfg_534_, 24);
v_restoreAllArtifacts_x3f_563_ = lean_ctor_get(v_cfg_534_, 25);
v_libPrefixOnWindows_564_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26 + 4);
v_allowImportAll_565_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26 + 5);
v_fixedToolchain_566_ = lean_ctor_get_uint8(v_cfg_534_, sizeof(void*)*26 + 6);
v_isSharedCheck_573_ = !lean_is_exclusive(v_cfg_534_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_cfg_534_, 4);
lean_dec(v_unused_574_);
v___x_568_ = v_cfg_534_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_563_);
lean_inc(v_enableArtifactCache_x3f_562_);
lean_inc(v_readmeFile_560_);
lean_inc(v_licenseFiles_559_);
lean_inc(v_license_558_);
lean_inc(v_homepage_557_);
lean_inc(v_keywords_556_);
lean_inc(v_description_555_);
lean_inc(v_versionTags_554_);
lean_inc(v_version_553_);
lean_inc(v_lintDriverArgs_552_);
lean_inc(v_lintDriver_551_);
lean_inc(v_testDriverArgs_550_);
lean_inc(v_testDriver_549_);
lean_inc(v_buildArchive_547_);
lean_inc(v_releaseRepo_546_);
lean_inc(v_irDir_545_);
lean_inc(v_binDir_544_);
lean_inc(v_nativeLibDir_543_);
lean_inc(v_leanLibDir_542_);
lean_inc(v_buildDir_541_);
lean_inc(v_moreGlobalServerArgs_540_);
lean_inc(v_extraDepTargets_538_);
lean_inc(v_toLeanConfig_536_);
lean_inc(v_toWorkspaceConfig_535_);
lean_dec(v_cfg_534_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_val_533_);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_toWorkspaceConfig_535_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_toLeanConfig_536_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_extraDepTargets_538_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_moreGlobalServerArgs_540_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_val_533_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v_buildDir_541_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_leanLibDir_542_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_nativeLibDir_543_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_binDir_544_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v_irDir_545_);
lean_ctor_set(v_reuseFailAlloc_572_, 10, v_releaseRepo_546_);
lean_ctor_set(v_reuseFailAlloc_572_, 11, v_buildArchive_547_);
lean_ctor_set(v_reuseFailAlloc_572_, 12, v_testDriver_549_);
lean_ctor_set(v_reuseFailAlloc_572_, 13, v_testDriverArgs_550_);
lean_ctor_set(v_reuseFailAlloc_572_, 14, v_lintDriver_551_);
lean_ctor_set(v_reuseFailAlloc_572_, 15, v_lintDriverArgs_552_);
lean_ctor_set(v_reuseFailAlloc_572_, 16, v_version_553_);
lean_ctor_set(v_reuseFailAlloc_572_, 17, v_versionTags_554_);
lean_ctor_set(v_reuseFailAlloc_572_, 18, v_description_555_);
lean_ctor_set(v_reuseFailAlloc_572_, 19, v_keywords_556_);
lean_ctor_set(v_reuseFailAlloc_572_, 20, v_homepage_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 21, v_license_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 22, v_licenseFiles_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 23, v_readmeFile_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 24, v_enableArtifactCache_x3f_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 25, v_restoreAllArtifacts_x3f_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26, v_bootstrap_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26 + 1, v_precompileModules_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26 + 2, v_preferReleaseBuild_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26 + 3, v_reservoir_561_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26 + 5, v_allowImportAll_565_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*26 + 6, v_fixedToolchain_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* v_f_575_, lean_object* v_cfg_576_){
_start:
{
lean_object* v_toWorkspaceConfig_577_; lean_object* v_toLeanConfig_578_; uint8_t v_bootstrap_579_; lean_object* v_extraDepTargets_580_; uint8_t v_precompileModules_581_; lean_object* v_moreGlobalServerArgs_582_; lean_object* v_srcDir_583_; lean_object* v_buildDir_584_; lean_object* v_leanLibDir_585_; lean_object* v_nativeLibDir_586_; lean_object* v_binDir_587_; lean_object* v_irDir_588_; lean_object* v_releaseRepo_589_; lean_object* v_buildArchive_590_; uint8_t v_preferReleaseBuild_591_; lean_object* v_testDriver_592_; lean_object* v_testDriverArgs_593_; lean_object* v_lintDriver_594_; lean_object* v_lintDriverArgs_595_; lean_object* v_version_596_; lean_object* v_versionTags_597_; lean_object* v_description_598_; lean_object* v_keywords_599_; lean_object* v_homepage_600_; lean_object* v_license_601_; lean_object* v_licenseFiles_602_; lean_object* v_readmeFile_603_; uint8_t v_reservoir_604_; lean_object* v_enableArtifactCache_x3f_605_; lean_object* v_restoreAllArtifacts_x3f_606_; uint8_t v_libPrefixOnWindows_607_; uint8_t v_allowImportAll_608_; uint8_t v_fixedToolchain_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_617_; 
v_toWorkspaceConfig_577_ = lean_ctor_get(v_cfg_576_, 0);
v_toLeanConfig_578_ = lean_ctor_get(v_cfg_576_, 1);
v_bootstrap_579_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26);
v_extraDepTargets_580_ = lean_ctor_get(v_cfg_576_, 2);
v_precompileModules_581_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_582_ = lean_ctor_get(v_cfg_576_, 3);
v_srcDir_583_ = lean_ctor_get(v_cfg_576_, 4);
v_buildDir_584_ = lean_ctor_get(v_cfg_576_, 5);
v_leanLibDir_585_ = lean_ctor_get(v_cfg_576_, 6);
v_nativeLibDir_586_ = lean_ctor_get(v_cfg_576_, 7);
v_binDir_587_ = lean_ctor_get(v_cfg_576_, 8);
v_irDir_588_ = lean_ctor_get(v_cfg_576_, 9);
v_releaseRepo_589_ = lean_ctor_get(v_cfg_576_, 10);
v_buildArchive_590_ = lean_ctor_get(v_cfg_576_, 11);
v_preferReleaseBuild_591_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26 + 2);
v_testDriver_592_ = lean_ctor_get(v_cfg_576_, 12);
v_testDriverArgs_593_ = lean_ctor_get(v_cfg_576_, 13);
v_lintDriver_594_ = lean_ctor_get(v_cfg_576_, 14);
v_lintDriverArgs_595_ = lean_ctor_get(v_cfg_576_, 15);
v_version_596_ = lean_ctor_get(v_cfg_576_, 16);
v_versionTags_597_ = lean_ctor_get(v_cfg_576_, 17);
v_description_598_ = lean_ctor_get(v_cfg_576_, 18);
v_keywords_599_ = lean_ctor_get(v_cfg_576_, 19);
v_homepage_600_ = lean_ctor_get(v_cfg_576_, 20);
v_license_601_ = lean_ctor_get(v_cfg_576_, 21);
v_licenseFiles_602_ = lean_ctor_get(v_cfg_576_, 22);
v_readmeFile_603_ = lean_ctor_get(v_cfg_576_, 23);
v_reservoir_604_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_605_ = lean_ctor_get(v_cfg_576_, 24);
v_restoreAllArtifacts_x3f_606_ = lean_ctor_get(v_cfg_576_, 25);
v_libPrefixOnWindows_607_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26 + 4);
v_allowImportAll_608_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26 + 5);
v_fixedToolchain_609_ = lean_ctor_get_uint8(v_cfg_576_, sizeof(void*)*26 + 6);
v_isSharedCheck_617_ = !lean_is_exclusive(v_cfg_576_);
if (v_isSharedCheck_617_ == 0)
{
v___x_611_ = v_cfg_576_;
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_606_);
lean_inc(v_enableArtifactCache_x3f_605_);
lean_inc(v_readmeFile_603_);
lean_inc(v_licenseFiles_602_);
lean_inc(v_license_601_);
lean_inc(v_homepage_600_);
lean_inc(v_keywords_599_);
lean_inc(v_description_598_);
lean_inc(v_versionTags_597_);
lean_inc(v_version_596_);
lean_inc(v_lintDriverArgs_595_);
lean_inc(v_lintDriver_594_);
lean_inc(v_testDriverArgs_593_);
lean_inc(v_testDriver_592_);
lean_inc(v_buildArchive_590_);
lean_inc(v_releaseRepo_589_);
lean_inc(v_irDir_588_);
lean_inc(v_binDir_587_);
lean_inc(v_nativeLibDir_586_);
lean_inc(v_leanLibDir_585_);
lean_inc(v_buildDir_584_);
lean_inc(v_srcDir_583_);
lean_inc(v_moreGlobalServerArgs_582_);
lean_inc(v_extraDepTargets_580_);
lean_inc(v_toLeanConfig_578_);
lean_inc(v_toWorkspaceConfig_577_);
lean_dec(v_cfg_576_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_apply_1(v_f_575_, v_srcDir_583_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_toWorkspaceConfig_577_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_toLeanConfig_578_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_extraDepTargets_580_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_moreGlobalServerArgs_582_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_buildDir_584_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_leanLibDir_585_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_nativeLibDir_586_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_binDir_587_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_irDir_588_);
lean_ctor_set(v_reuseFailAlloc_616_, 10, v_releaseRepo_589_);
lean_ctor_set(v_reuseFailAlloc_616_, 11, v_buildArchive_590_);
lean_ctor_set(v_reuseFailAlloc_616_, 12, v_testDriver_592_);
lean_ctor_set(v_reuseFailAlloc_616_, 13, v_testDriverArgs_593_);
lean_ctor_set(v_reuseFailAlloc_616_, 14, v_lintDriver_594_);
lean_ctor_set(v_reuseFailAlloc_616_, 15, v_lintDriverArgs_595_);
lean_ctor_set(v_reuseFailAlloc_616_, 16, v_version_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 17, v_versionTags_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 18, v_description_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 19, v_keywords_599_);
lean_ctor_set(v_reuseFailAlloc_616_, 20, v_homepage_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 21, v_license_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 22, v_licenseFiles_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 23, v_readmeFile_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 24, v_enableArtifactCache_x3f_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 25, v_restoreAllArtifacts_x3f_606_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26, v_bootstrap_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26 + 1, v_precompileModules_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26 + 2, v_preferReleaseBuild_591_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26 + 3, v_reservoir_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_607_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26 + 5, v_allowImportAll_608_);
lean_ctor_set_uint8(v_reuseFailAlloc_616_, sizeof(void*)*26 + 6, v_fixedToolchain_609_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lake_PackageConfig_srcDir___proj___lam__3(v_x_620_);
lean_dec_ref(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_631_, lean_object* v_n_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_634_, lean_object* v_n_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lake_PackageConfig_srcDir___proj(v_p_634_, v_n_635_);
lean_dec(v_n_635_);
lean_dec(v_p_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_637_, lean_object* v_n_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lake_PackageConfig_srcDir___proj(v_p_637_, v_n_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_640_, lean_object* v_n_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_640_, v_n_641_);
lean_dec(v_n_641_);
lean_dec(v_p_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* v_cfg_643_){
_start:
{
lean_object* v_buildDir_644_; 
v_buildDir_644_ = lean_ctor_get(v_cfg_643_, 5);
lean_inc_ref(v_buildDir_644_);
return v_buildDir_644_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* v_cfg_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lake_PackageConfig_buildDir___proj___lam__0(v_cfg_645_);
lean_dec_ref(v_cfg_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* v_val_647_, lean_object* v_cfg_648_){
_start:
{
lean_object* v_toWorkspaceConfig_649_; lean_object* v_toLeanConfig_650_; uint8_t v_bootstrap_651_; lean_object* v_extraDepTargets_652_; uint8_t v_precompileModules_653_; lean_object* v_moreGlobalServerArgs_654_; lean_object* v_srcDir_655_; lean_object* v_leanLibDir_656_; lean_object* v_nativeLibDir_657_; lean_object* v_binDir_658_; lean_object* v_irDir_659_; lean_object* v_releaseRepo_660_; lean_object* v_buildArchive_661_; uint8_t v_preferReleaseBuild_662_; lean_object* v_testDriver_663_; lean_object* v_testDriverArgs_664_; lean_object* v_lintDriver_665_; lean_object* v_lintDriverArgs_666_; lean_object* v_version_667_; lean_object* v_versionTags_668_; lean_object* v_description_669_; lean_object* v_keywords_670_; lean_object* v_homepage_671_; lean_object* v_license_672_; lean_object* v_licenseFiles_673_; lean_object* v_readmeFile_674_; uint8_t v_reservoir_675_; lean_object* v_enableArtifactCache_x3f_676_; lean_object* v_restoreAllArtifacts_x3f_677_; uint8_t v_libPrefixOnWindows_678_; uint8_t v_allowImportAll_679_; uint8_t v_fixedToolchain_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_toWorkspaceConfig_649_ = lean_ctor_get(v_cfg_648_, 0);
v_toLeanConfig_650_ = lean_ctor_get(v_cfg_648_, 1);
v_bootstrap_651_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26);
v_extraDepTargets_652_ = lean_ctor_get(v_cfg_648_, 2);
v_precompileModules_653_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_654_ = lean_ctor_get(v_cfg_648_, 3);
v_srcDir_655_ = lean_ctor_get(v_cfg_648_, 4);
v_leanLibDir_656_ = lean_ctor_get(v_cfg_648_, 6);
v_nativeLibDir_657_ = lean_ctor_get(v_cfg_648_, 7);
v_binDir_658_ = lean_ctor_get(v_cfg_648_, 8);
v_irDir_659_ = lean_ctor_get(v_cfg_648_, 9);
v_releaseRepo_660_ = lean_ctor_get(v_cfg_648_, 10);
v_buildArchive_661_ = lean_ctor_get(v_cfg_648_, 11);
v_preferReleaseBuild_662_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26 + 2);
v_testDriver_663_ = lean_ctor_get(v_cfg_648_, 12);
v_testDriverArgs_664_ = lean_ctor_get(v_cfg_648_, 13);
v_lintDriver_665_ = lean_ctor_get(v_cfg_648_, 14);
v_lintDriverArgs_666_ = lean_ctor_get(v_cfg_648_, 15);
v_version_667_ = lean_ctor_get(v_cfg_648_, 16);
v_versionTags_668_ = lean_ctor_get(v_cfg_648_, 17);
v_description_669_ = lean_ctor_get(v_cfg_648_, 18);
v_keywords_670_ = lean_ctor_get(v_cfg_648_, 19);
v_homepage_671_ = lean_ctor_get(v_cfg_648_, 20);
v_license_672_ = lean_ctor_get(v_cfg_648_, 21);
v_licenseFiles_673_ = lean_ctor_get(v_cfg_648_, 22);
v_readmeFile_674_ = lean_ctor_get(v_cfg_648_, 23);
v_reservoir_675_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_676_ = lean_ctor_get(v_cfg_648_, 24);
v_restoreAllArtifacts_x3f_677_ = lean_ctor_get(v_cfg_648_, 25);
v_libPrefixOnWindows_678_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26 + 4);
v_allowImportAll_679_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26 + 5);
v_fixedToolchain_680_ = lean_ctor_get_uint8(v_cfg_648_, sizeof(void*)*26 + 6);
v_isSharedCheck_687_ = !lean_is_exclusive(v_cfg_648_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_cfg_648_, 5);
lean_dec(v_unused_688_);
v___x_682_ = v_cfg_648_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_677_);
lean_inc(v_enableArtifactCache_x3f_676_);
lean_inc(v_readmeFile_674_);
lean_inc(v_licenseFiles_673_);
lean_inc(v_license_672_);
lean_inc(v_homepage_671_);
lean_inc(v_keywords_670_);
lean_inc(v_description_669_);
lean_inc(v_versionTags_668_);
lean_inc(v_version_667_);
lean_inc(v_lintDriverArgs_666_);
lean_inc(v_lintDriver_665_);
lean_inc(v_testDriverArgs_664_);
lean_inc(v_testDriver_663_);
lean_inc(v_buildArchive_661_);
lean_inc(v_releaseRepo_660_);
lean_inc(v_irDir_659_);
lean_inc(v_binDir_658_);
lean_inc(v_nativeLibDir_657_);
lean_inc(v_leanLibDir_656_);
lean_inc(v_srcDir_655_);
lean_inc(v_moreGlobalServerArgs_654_);
lean_inc(v_extraDepTargets_652_);
lean_inc(v_toLeanConfig_650_);
lean_inc(v_toWorkspaceConfig_649_);
lean_dec(v_cfg_648_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 5, v_val_647_);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_toWorkspaceConfig_649_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_toLeanConfig_650_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_extraDepTargets_652_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_moreGlobalServerArgs_654_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_srcDir_655_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_val_647_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_leanLibDir_656_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v_nativeLibDir_657_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_binDir_658_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_irDir_659_);
lean_ctor_set(v_reuseFailAlloc_686_, 10, v_releaseRepo_660_);
lean_ctor_set(v_reuseFailAlloc_686_, 11, v_buildArchive_661_);
lean_ctor_set(v_reuseFailAlloc_686_, 12, v_testDriver_663_);
lean_ctor_set(v_reuseFailAlloc_686_, 13, v_testDriverArgs_664_);
lean_ctor_set(v_reuseFailAlloc_686_, 14, v_lintDriver_665_);
lean_ctor_set(v_reuseFailAlloc_686_, 15, v_lintDriverArgs_666_);
lean_ctor_set(v_reuseFailAlloc_686_, 16, v_version_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 17, v_versionTags_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 18, v_description_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 19, v_keywords_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 20, v_homepage_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 21, v_license_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 22, v_licenseFiles_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 23, v_readmeFile_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 24, v_enableArtifactCache_x3f_676_);
lean_ctor_set(v_reuseFailAlloc_686_, 25, v_restoreAllArtifacts_x3f_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26, v_bootstrap_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26 + 1, v_precompileModules_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26 + 2, v_preferReleaseBuild_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26 + 3, v_reservoir_675_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26 + 5, v_allowImportAll_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*26 + 6, v_fixedToolchain_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* v_f_689_, lean_object* v_cfg_690_){
_start:
{
lean_object* v_toWorkspaceConfig_691_; lean_object* v_toLeanConfig_692_; uint8_t v_bootstrap_693_; lean_object* v_extraDepTargets_694_; uint8_t v_precompileModules_695_; lean_object* v_moreGlobalServerArgs_696_; lean_object* v_srcDir_697_; lean_object* v_buildDir_698_; lean_object* v_leanLibDir_699_; lean_object* v_nativeLibDir_700_; lean_object* v_binDir_701_; lean_object* v_irDir_702_; lean_object* v_releaseRepo_703_; lean_object* v_buildArchive_704_; uint8_t v_preferReleaseBuild_705_; lean_object* v_testDriver_706_; lean_object* v_testDriverArgs_707_; lean_object* v_lintDriver_708_; lean_object* v_lintDriverArgs_709_; lean_object* v_version_710_; lean_object* v_versionTags_711_; lean_object* v_description_712_; lean_object* v_keywords_713_; lean_object* v_homepage_714_; lean_object* v_license_715_; lean_object* v_licenseFiles_716_; lean_object* v_readmeFile_717_; uint8_t v_reservoir_718_; lean_object* v_enableArtifactCache_x3f_719_; lean_object* v_restoreAllArtifacts_x3f_720_; uint8_t v_libPrefixOnWindows_721_; uint8_t v_allowImportAll_722_; uint8_t v_fixedToolchain_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
v_toWorkspaceConfig_691_ = lean_ctor_get(v_cfg_690_, 0);
v_toLeanConfig_692_ = lean_ctor_get(v_cfg_690_, 1);
v_bootstrap_693_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26);
v_extraDepTargets_694_ = lean_ctor_get(v_cfg_690_, 2);
v_precompileModules_695_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_696_ = lean_ctor_get(v_cfg_690_, 3);
v_srcDir_697_ = lean_ctor_get(v_cfg_690_, 4);
v_buildDir_698_ = lean_ctor_get(v_cfg_690_, 5);
v_leanLibDir_699_ = lean_ctor_get(v_cfg_690_, 6);
v_nativeLibDir_700_ = lean_ctor_get(v_cfg_690_, 7);
v_binDir_701_ = lean_ctor_get(v_cfg_690_, 8);
v_irDir_702_ = lean_ctor_get(v_cfg_690_, 9);
v_releaseRepo_703_ = lean_ctor_get(v_cfg_690_, 10);
v_buildArchive_704_ = lean_ctor_get(v_cfg_690_, 11);
v_preferReleaseBuild_705_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26 + 2);
v_testDriver_706_ = lean_ctor_get(v_cfg_690_, 12);
v_testDriverArgs_707_ = lean_ctor_get(v_cfg_690_, 13);
v_lintDriver_708_ = lean_ctor_get(v_cfg_690_, 14);
v_lintDriverArgs_709_ = lean_ctor_get(v_cfg_690_, 15);
v_version_710_ = lean_ctor_get(v_cfg_690_, 16);
v_versionTags_711_ = lean_ctor_get(v_cfg_690_, 17);
v_description_712_ = lean_ctor_get(v_cfg_690_, 18);
v_keywords_713_ = lean_ctor_get(v_cfg_690_, 19);
v_homepage_714_ = lean_ctor_get(v_cfg_690_, 20);
v_license_715_ = lean_ctor_get(v_cfg_690_, 21);
v_licenseFiles_716_ = lean_ctor_get(v_cfg_690_, 22);
v_readmeFile_717_ = lean_ctor_get(v_cfg_690_, 23);
v_reservoir_718_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_719_ = lean_ctor_get(v_cfg_690_, 24);
v_restoreAllArtifacts_x3f_720_ = lean_ctor_get(v_cfg_690_, 25);
v_libPrefixOnWindows_721_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26 + 4);
v_allowImportAll_722_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26 + 5);
v_fixedToolchain_723_ = lean_ctor_get_uint8(v_cfg_690_, sizeof(void*)*26 + 6);
v_isSharedCheck_731_ = !lean_is_exclusive(v_cfg_690_);
if (v_isSharedCheck_731_ == 0)
{
v___x_725_ = v_cfg_690_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_720_);
lean_inc(v_enableArtifactCache_x3f_719_);
lean_inc(v_readmeFile_717_);
lean_inc(v_licenseFiles_716_);
lean_inc(v_license_715_);
lean_inc(v_homepage_714_);
lean_inc(v_keywords_713_);
lean_inc(v_description_712_);
lean_inc(v_versionTags_711_);
lean_inc(v_version_710_);
lean_inc(v_lintDriverArgs_709_);
lean_inc(v_lintDriver_708_);
lean_inc(v_testDriverArgs_707_);
lean_inc(v_testDriver_706_);
lean_inc(v_buildArchive_704_);
lean_inc(v_releaseRepo_703_);
lean_inc(v_irDir_702_);
lean_inc(v_binDir_701_);
lean_inc(v_nativeLibDir_700_);
lean_inc(v_leanLibDir_699_);
lean_inc(v_buildDir_698_);
lean_inc(v_srcDir_697_);
lean_inc(v_moreGlobalServerArgs_696_);
lean_inc(v_extraDepTargets_694_);
lean_inc(v_toLeanConfig_692_);
lean_inc(v_toWorkspaceConfig_691_);
lean_dec(v_cfg_690_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_apply_1(v_f_689_, v_buildDir_698_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 5, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_toWorkspaceConfig_691_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_toLeanConfig_692_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_extraDepTargets_694_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_moreGlobalServerArgs_696_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_srcDir_697_);
lean_ctor_set(v_reuseFailAlloc_730_, 5, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 6, v_leanLibDir_699_);
lean_ctor_set(v_reuseFailAlloc_730_, 7, v_nativeLibDir_700_);
lean_ctor_set(v_reuseFailAlloc_730_, 8, v_binDir_701_);
lean_ctor_set(v_reuseFailAlloc_730_, 9, v_irDir_702_);
lean_ctor_set(v_reuseFailAlloc_730_, 10, v_releaseRepo_703_);
lean_ctor_set(v_reuseFailAlloc_730_, 11, v_buildArchive_704_);
lean_ctor_set(v_reuseFailAlloc_730_, 12, v_testDriver_706_);
lean_ctor_set(v_reuseFailAlloc_730_, 13, v_testDriverArgs_707_);
lean_ctor_set(v_reuseFailAlloc_730_, 14, v_lintDriver_708_);
lean_ctor_set(v_reuseFailAlloc_730_, 15, v_lintDriverArgs_709_);
lean_ctor_set(v_reuseFailAlloc_730_, 16, v_version_710_);
lean_ctor_set(v_reuseFailAlloc_730_, 17, v_versionTags_711_);
lean_ctor_set(v_reuseFailAlloc_730_, 18, v_description_712_);
lean_ctor_set(v_reuseFailAlloc_730_, 19, v_keywords_713_);
lean_ctor_set(v_reuseFailAlloc_730_, 20, v_homepage_714_);
lean_ctor_set(v_reuseFailAlloc_730_, 21, v_license_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 22, v_licenseFiles_716_);
lean_ctor_set(v_reuseFailAlloc_730_, 23, v_readmeFile_717_);
lean_ctor_set(v_reuseFailAlloc_730_, 24, v_enableArtifactCache_x3f_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 25, v_restoreAllArtifacts_x3f_720_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26, v_bootstrap_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26 + 1, v_precompileModules_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26 + 2, v_preferReleaseBuild_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26 + 3, v_reservoir_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_721_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26 + 5, v_allowImportAll_722_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*26 + 6, v_fixedToolchain_723_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lake_defaultBuildDir;
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* v_x_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lake_PackageConfig_buildDir___proj___lam__3(v_x_734_);
lean_dec_ref(v_x_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_745_, lean_object* v_n_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_748_, lean_object* v_n_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lake_PackageConfig_buildDir___proj(v_p_748_, v_n_749_);
lean_dec(v_n_749_);
lean_dec(v_p_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_751_, lean_object* v_n_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lake_PackageConfig_buildDir___proj(v_p_751_, v_n_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_754_, lean_object* v_n_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_754_, v_n_755_);
lean_dec(v_n_755_);
lean_dec(v_p_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* v_cfg_757_){
_start:
{
lean_object* v_leanLibDir_758_; 
v_leanLibDir_758_ = lean_ctor_get(v_cfg_757_, 6);
lean_inc_ref(v_leanLibDir_758_);
return v_leanLibDir_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* v_cfg_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lake_PackageConfig_leanLibDir___proj___lam__0(v_cfg_759_);
lean_dec_ref(v_cfg_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* v_val_761_, lean_object* v_cfg_762_){
_start:
{
lean_object* v_toWorkspaceConfig_763_; lean_object* v_toLeanConfig_764_; uint8_t v_bootstrap_765_; lean_object* v_extraDepTargets_766_; uint8_t v_precompileModules_767_; lean_object* v_moreGlobalServerArgs_768_; lean_object* v_srcDir_769_; lean_object* v_buildDir_770_; lean_object* v_nativeLibDir_771_; lean_object* v_binDir_772_; lean_object* v_irDir_773_; lean_object* v_releaseRepo_774_; lean_object* v_buildArchive_775_; uint8_t v_preferReleaseBuild_776_; lean_object* v_testDriver_777_; lean_object* v_testDriverArgs_778_; lean_object* v_lintDriver_779_; lean_object* v_lintDriverArgs_780_; lean_object* v_version_781_; lean_object* v_versionTags_782_; lean_object* v_description_783_; lean_object* v_keywords_784_; lean_object* v_homepage_785_; lean_object* v_license_786_; lean_object* v_licenseFiles_787_; lean_object* v_readmeFile_788_; uint8_t v_reservoir_789_; lean_object* v_enableArtifactCache_x3f_790_; lean_object* v_restoreAllArtifacts_x3f_791_; uint8_t v_libPrefixOnWindows_792_; uint8_t v_allowImportAll_793_; uint8_t v_fixedToolchain_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_toWorkspaceConfig_763_ = lean_ctor_get(v_cfg_762_, 0);
v_toLeanConfig_764_ = lean_ctor_get(v_cfg_762_, 1);
v_bootstrap_765_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26);
v_extraDepTargets_766_ = lean_ctor_get(v_cfg_762_, 2);
v_precompileModules_767_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_768_ = lean_ctor_get(v_cfg_762_, 3);
v_srcDir_769_ = lean_ctor_get(v_cfg_762_, 4);
v_buildDir_770_ = lean_ctor_get(v_cfg_762_, 5);
v_nativeLibDir_771_ = lean_ctor_get(v_cfg_762_, 7);
v_binDir_772_ = lean_ctor_get(v_cfg_762_, 8);
v_irDir_773_ = lean_ctor_get(v_cfg_762_, 9);
v_releaseRepo_774_ = lean_ctor_get(v_cfg_762_, 10);
v_buildArchive_775_ = lean_ctor_get(v_cfg_762_, 11);
v_preferReleaseBuild_776_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26 + 2);
v_testDriver_777_ = lean_ctor_get(v_cfg_762_, 12);
v_testDriverArgs_778_ = lean_ctor_get(v_cfg_762_, 13);
v_lintDriver_779_ = lean_ctor_get(v_cfg_762_, 14);
v_lintDriverArgs_780_ = lean_ctor_get(v_cfg_762_, 15);
v_version_781_ = lean_ctor_get(v_cfg_762_, 16);
v_versionTags_782_ = lean_ctor_get(v_cfg_762_, 17);
v_description_783_ = lean_ctor_get(v_cfg_762_, 18);
v_keywords_784_ = lean_ctor_get(v_cfg_762_, 19);
v_homepage_785_ = lean_ctor_get(v_cfg_762_, 20);
v_license_786_ = lean_ctor_get(v_cfg_762_, 21);
v_licenseFiles_787_ = lean_ctor_get(v_cfg_762_, 22);
v_readmeFile_788_ = lean_ctor_get(v_cfg_762_, 23);
v_reservoir_789_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_790_ = lean_ctor_get(v_cfg_762_, 24);
v_restoreAllArtifacts_x3f_791_ = lean_ctor_get(v_cfg_762_, 25);
v_libPrefixOnWindows_792_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26 + 4);
v_allowImportAll_793_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26 + 5);
v_fixedToolchain_794_ = lean_ctor_get_uint8(v_cfg_762_, sizeof(void*)*26 + 6);
v_isSharedCheck_801_ = !lean_is_exclusive(v_cfg_762_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_cfg_762_, 6);
lean_dec(v_unused_802_);
v___x_796_ = v_cfg_762_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_791_);
lean_inc(v_enableArtifactCache_x3f_790_);
lean_inc(v_readmeFile_788_);
lean_inc(v_licenseFiles_787_);
lean_inc(v_license_786_);
lean_inc(v_homepage_785_);
lean_inc(v_keywords_784_);
lean_inc(v_description_783_);
lean_inc(v_versionTags_782_);
lean_inc(v_version_781_);
lean_inc(v_lintDriverArgs_780_);
lean_inc(v_lintDriver_779_);
lean_inc(v_testDriverArgs_778_);
lean_inc(v_testDriver_777_);
lean_inc(v_buildArchive_775_);
lean_inc(v_releaseRepo_774_);
lean_inc(v_irDir_773_);
lean_inc(v_binDir_772_);
lean_inc(v_nativeLibDir_771_);
lean_inc(v_buildDir_770_);
lean_inc(v_srcDir_769_);
lean_inc(v_moreGlobalServerArgs_768_);
lean_inc(v_extraDepTargets_766_);
lean_inc(v_toLeanConfig_764_);
lean_inc(v_toWorkspaceConfig_763_);
lean_dec(v_cfg_762_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 6, v_val_761_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_toWorkspaceConfig_763_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_toLeanConfig_764_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_extraDepTargets_766_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_moreGlobalServerArgs_768_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_srcDir_769_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v_buildDir_770_);
lean_ctor_set(v_reuseFailAlloc_800_, 6, v_val_761_);
lean_ctor_set(v_reuseFailAlloc_800_, 7, v_nativeLibDir_771_);
lean_ctor_set(v_reuseFailAlloc_800_, 8, v_binDir_772_);
lean_ctor_set(v_reuseFailAlloc_800_, 9, v_irDir_773_);
lean_ctor_set(v_reuseFailAlloc_800_, 10, v_releaseRepo_774_);
lean_ctor_set(v_reuseFailAlloc_800_, 11, v_buildArchive_775_);
lean_ctor_set(v_reuseFailAlloc_800_, 12, v_testDriver_777_);
lean_ctor_set(v_reuseFailAlloc_800_, 13, v_testDriverArgs_778_);
lean_ctor_set(v_reuseFailAlloc_800_, 14, v_lintDriver_779_);
lean_ctor_set(v_reuseFailAlloc_800_, 15, v_lintDriverArgs_780_);
lean_ctor_set(v_reuseFailAlloc_800_, 16, v_version_781_);
lean_ctor_set(v_reuseFailAlloc_800_, 17, v_versionTags_782_);
lean_ctor_set(v_reuseFailAlloc_800_, 18, v_description_783_);
lean_ctor_set(v_reuseFailAlloc_800_, 19, v_keywords_784_);
lean_ctor_set(v_reuseFailAlloc_800_, 20, v_homepage_785_);
lean_ctor_set(v_reuseFailAlloc_800_, 21, v_license_786_);
lean_ctor_set(v_reuseFailAlloc_800_, 22, v_licenseFiles_787_);
lean_ctor_set(v_reuseFailAlloc_800_, 23, v_readmeFile_788_);
lean_ctor_set(v_reuseFailAlloc_800_, 24, v_enableArtifactCache_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_800_, 25, v_restoreAllArtifacts_x3f_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26, v_bootstrap_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26 + 1, v_precompileModules_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26 + 2, v_preferReleaseBuild_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26 + 3, v_reservoir_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26 + 5, v_allowImportAll_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*26 + 6, v_fixedToolchain_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* v_f_803_, lean_object* v_cfg_804_){
_start:
{
lean_object* v_toWorkspaceConfig_805_; lean_object* v_toLeanConfig_806_; uint8_t v_bootstrap_807_; lean_object* v_extraDepTargets_808_; uint8_t v_precompileModules_809_; lean_object* v_moreGlobalServerArgs_810_; lean_object* v_srcDir_811_; lean_object* v_buildDir_812_; lean_object* v_leanLibDir_813_; lean_object* v_nativeLibDir_814_; lean_object* v_binDir_815_; lean_object* v_irDir_816_; lean_object* v_releaseRepo_817_; lean_object* v_buildArchive_818_; uint8_t v_preferReleaseBuild_819_; lean_object* v_testDriver_820_; lean_object* v_testDriverArgs_821_; lean_object* v_lintDriver_822_; lean_object* v_lintDriverArgs_823_; lean_object* v_version_824_; lean_object* v_versionTags_825_; lean_object* v_description_826_; lean_object* v_keywords_827_; lean_object* v_homepage_828_; lean_object* v_license_829_; lean_object* v_licenseFiles_830_; lean_object* v_readmeFile_831_; uint8_t v_reservoir_832_; lean_object* v_enableArtifactCache_x3f_833_; lean_object* v_restoreAllArtifacts_x3f_834_; uint8_t v_libPrefixOnWindows_835_; uint8_t v_allowImportAll_836_; uint8_t v_fixedToolchain_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_toWorkspaceConfig_805_ = lean_ctor_get(v_cfg_804_, 0);
v_toLeanConfig_806_ = lean_ctor_get(v_cfg_804_, 1);
v_bootstrap_807_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26);
v_extraDepTargets_808_ = lean_ctor_get(v_cfg_804_, 2);
v_precompileModules_809_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_810_ = lean_ctor_get(v_cfg_804_, 3);
v_srcDir_811_ = lean_ctor_get(v_cfg_804_, 4);
v_buildDir_812_ = lean_ctor_get(v_cfg_804_, 5);
v_leanLibDir_813_ = lean_ctor_get(v_cfg_804_, 6);
v_nativeLibDir_814_ = lean_ctor_get(v_cfg_804_, 7);
v_binDir_815_ = lean_ctor_get(v_cfg_804_, 8);
v_irDir_816_ = lean_ctor_get(v_cfg_804_, 9);
v_releaseRepo_817_ = lean_ctor_get(v_cfg_804_, 10);
v_buildArchive_818_ = lean_ctor_get(v_cfg_804_, 11);
v_preferReleaseBuild_819_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26 + 2);
v_testDriver_820_ = lean_ctor_get(v_cfg_804_, 12);
v_testDriverArgs_821_ = lean_ctor_get(v_cfg_804_, 13);
v_lintDriver_822_ = lean_ctor_get(v_cfg_804_, 14);
v_lintDriverArgs_823_ = lean_ctor_get(v_cfg_804_, 15);
v_version_824_ = lean_ctor_get(v_cfg_804_, 16);
v_versionTags_825_ = lean_ctor_get(v_cfg_804_, 17);
v_description_826_ = lean_ctor_get(v_cfg_804_, 18);
v_keywords_827_ = lean_ctor_get(v_cfg_804_, 19);
v_homepage_828_ = lean_ctor_get(v_cfg_804_, 20);
v_license_829_ = lean_ctor_get(v_cfg_804_, 21);
v_licenseFiles_830_ = lean_ctor_get(v_cfg_804_, 22);
v_readmeFile_831_ = lean_ctor_get(v_cfg_804_, 23);
v_reservoir_832_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_833_ = lean_ctor_get(v_cfg_804_, 24);
v_restoreAllArtifacts_x3f_834_ = lean_ctor_get(v_cfg_804_, 25);
v_libPrefixOnWindows_835_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26 + 4);
v_allowImportAll_836_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26 + 5);
v_fixedToolchain_837_ = lean_ctor_get_uint8(v_cfg_804_, sizeof(void*)*26 + 6);
v_isSharedCheck_845_ = !lean_is_exclusive(v_cfg_804_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v_cfg_804_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_834_);
lean_inc(v_enableArtifactCache_x3f_833_);
lean_inc(v_readmeFile_831_);
lean_inc(v_licenseFiles_830_);
lean_inc(v_license_829_);
lean_inc(v_homepage_828_);
lean_inc(v_keywords_827_);
lean_inc(v_description_826_);
lean_inc(v_versionTags_825_);
lean_inc(v_version_824_);
lean_inc(v_lintDriverArgs_823_);
lean_inc(v_lintDriver_822_);
lean_inc(v_testDriverArgs_821_);
lean_inc(v_testDriver_820_);
lean_inc(v_buildArchive_818_);
lean_inc(v_releaseRepo_817_);
lean_inc(v_irDir_816_);
lean_inc(v_binDir_815_);
lean_inc(v_nativeLibDir_814_);
lean_inc(v_leanLibDir_813_);
lean_inc(v_buildDir_812_);
lean_inc(v_srcDir_811_);
lean_inc(v_moreGlobalServerArgs_810_);
lean_inc(v_extraDepTargets_808_);
lean_inc(v_toLeanConfig_806_);
lean_inc(v_toWorkspaceConfig_805_);
lean_dec(v_cfg_804_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_apply_1(v_f_803_, v_leanLibDir_813_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 6, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_toWorkspaceConfig_805_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_toLeanConfig_806_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_extraDepTargets_808_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_moreGlobalServerArgs_810_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_srcDir_811_);
lean_ctor_set(v_reuseFailAlloc_844_, 5, v_buildDir_812_);
lean_ctor_set(v_reuseFailAlloc_844_, 6, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 7, v_nativeLibDir_814_);
lean_ctor_set(v_reuseFailAlloc_844_, 8, v_binDir_815_);
lean_ctor_set(v_reuseFailAlloc_844_, 9, v_irDir_816_);
lean_ctor_set(v_reuseFailAlloc_844_, 10, v_releaseRepo_817_);
lean_ctor_set(v_reuseFailAlloc_844_, 11, v_buildArchive_818_);
lean_ctor_set(v_reuseFailAlloc_844_, 12, v_testDriver_820_);
lean_ctor_set(v_reuseFailAlloc_844_, 13, v_testDriverArgs_821_);
lean_ctor_set(v_reuseFailAlloc_844_, 14, v_lintDriver_822_);
lean_ctor_set(v_reuseFailAlloc_844_, 15, v_lintDriverArgs_823_);
lean_ctor_set(v_reuseFailAlloc_844_, 16, v_version_824_);
lean_ctor_set(v_reuseFailAlloc_844_, 17, v_versionTags_825_);
lean_ctor_set(v_reuseFailAlloc_844_, 18, v_description_826_);
lean_ctor_set(v_reuseFailAlloc_844_, 19, v_keywords_827_);
lean_ctor_set(v_reuseFailAlloc_844_, 20, v_homepage_828_);
lean_ctor_set(v_reuseFailAlloc_844_, 21, v_license_829_);
lean_ctor_set(v_reuseFailAlloc_844_, 22, v_licenseFiles_830_);
lean_ctor_set(v_reuseFailAlloc_844_, 23, v_readmeFile_831_);
lean_ctor_set(v_reuseFailAlloc_844_, 24, v_enableArtifactCache_x3f_833_);
lean_ctor_set(v_reuseFailAlloc_844_, 25, v_restoreAllArtifacts_x3f_834_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26, v_bootstrap_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26 + 1, v_precompileModules_809_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26 + 2, v_preferReleaseBuild_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26 + 3, v_reservoir_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26 + 5, v_allowImportAll_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*26 + 6, v_fixedToolchain_837_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lake_defaultLeanLibDir;
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lake_PackageConfig_leanLibDir___proj___lam__3(v_x_848_);
lean_dec_ref(v_x_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_859_, lean_object* v_n_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_862_, lean_object* v_n_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_862_, v_n_863_);
lean_dec(v_n_863_);
lean_dec(v_p_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_865_, lean_object* v_n_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_865_, v_n_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_868_, lean_object* v_n_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_868_, v_n_869_);
lean_dec(v_n_869_);
lean_dec(v_p_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* v_cfg_871_){
_start:
{
lean_object* v_nativeLibDir_872_; 
v_nativeLibDir_872_ = lean_ctor_get(v_cfg_871_, 7);
lean_inc_ref(v_nativeLibDir_872_);
return v_nativeLibDir_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* v_cfg_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(v_cfg_873_);
lean_dec_ref(v_cfg_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* v_val_875_, lean_object* v_cfg_876_){
_start:
{
lean_object* v_toWorkspaceConfig_877_; lean_object* v_toLeanConfig_878_; uint8_t v_bootstrap_879_; lean_object* v_extraDepTargets_880_; uint8_t v_precompileModules_881_; lean_object* v_moreGlobalServerArgs_882_; lean_object* v_srcDir_883_; lean_object* v_buildDir_884_; lean_object* v_leanLibDir_885_; lean_object* v_binDir_886_; lean_object* v_irDir_887_; lean_object* v_releaseRepo_888_; lean_object* v_buildArchive_889_; uint8_t v_preferReleaseBuild_890_; lean_object* v_testDriver_891_; lean_object* v_testDriverArgs_892_; lean_object* v_lintDriver_893_; lean_object* v_lintDriverArgs_894_; lean_object* v_version_895_; lean_object* v_versionTags_896_; lean_object* v_description_897_; lean_object* v_keywords_898_; lean_object* v_homepage_899_; lean_object* v_license_900_; lean_object* v_licenseFiles_901_; lean_object* v_readmeFile_902_; uint8_t v_reservoir_903_; lean_object* v_enableArtifactCache_x3f_904_; lean_object* v_restoreAllArtifacts_x3f_905_; uint8_t v_libPrefixOnWindows_906_; uint8_t v_allowImportAll_907_; uint8_t v_fixedToolchain_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_toWorkspaceConfig_877_ = lean_ctor_get(v_cfg_876_, 0);
v_toLeanConfig_878_ = lean_ctor_get(v_cfg_876_, 1);
v_bootstrap_879_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26);
v_extraDepTargets_880_ = lean_ctor_get(v_cfg_876_, 2);
v_precompileModules_881_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_882_ = lean_ctor_get(v_cfg_876_, 3);
v_srcDir_883_ = lean_ctor_get(v_cfg_876_, 4);
v_buildDir_884_ = lean_ctor_get(v_cfg_876_, 5);
v_leanLibDir_885_ = lean_ctor_get(v_cfg_876_, 6);
v_binDir_886_ = lean_ctor_get(v_cfg_876_, 8);
v_irDir_887_ = lean_ctor_get(v_cfg_876_, 9);
v_releaseRepo_888_ = lean_ctor_get(v_cfg_876_, 10);
v_buildArchive_889_ = lean_ctor_get(v_cfg_876_, 11);
v_preferReleaseBuild_890_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26 + 2);
v_testDriver_891_ = lean_ctor_get(v_cfg_876_, 12);
v_testDriverArgs_892_ = lean_ctor_get(v_cfg_876_, 13);
v_lintDriver_893_ = lean_ctor_get(v_cfg_876_, 14);
v_lintDriverArgs_894_ = lean_ctor_get(v_cfg_876_, 15);
v_version_895_ = lean_ctor_get(v_cfg_876_, 16);
v_versionTags_896_ = lean_ctor_get(v_cfg_876_, 17);
v_description_897_ = lean_ctor_get(v_cfg_876_, 18);
v_keywords_898_ = lean_ctor_get(v_cfg_876_, 19);
v_homepage_899_ = lean_ctor_get(v_cfg_876_, 20);
v_license_900_ = lean_ctor_get(v_cfg_876_, 21);
v_licenseFiles_901_ = lean_ctor_get(v_cfg_876_, 22);
v_readmeFile_902_ = lean_ctor_get(v_cfg_876_, 23);
v_reservoir_903_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_904_ = lean_ctor_get(v_cfg_876_, 24);
v_restoreAllArtifacts_x3f_905_ = lean_ctor_get(v_cfg_876_, 25);
v_libPrefixOnWindows_906_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26 + 4);
v_allowImportAll_907_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26 + 5);
v_fixedToolchain_908_ = lean_ctor_get_uint8(v_cfg_876_, sizeof(void*)*26 + 6);
v_isSharedCheck_915_ = !lean_is_exclusive(v_cfg_876_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_cfg_876_, 7);
lean_dec(v_unused_916_);
v___x_910_ = v_cfg_876_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_905_);
lean_inc(v_enableArtifactCache_x3f_904_);
lean_inc(v_readmeFile_902_);
lean_inc(v_licenseFiles_901_);
lean_inc(v_license_900_);
lean_inc(v_homepage_899_);
lean_inc(v_keywords_898_);
lean_inc(v_description_897_);
lean_inc(v_versionTags_896_);
lean_inc(v_version_895_);
lean_inc(v_lintDriverArgs_894_);
lean_inc(v_lintDriver_893_);
lean_inc(v_testDriverArgs_892_);
lean_inc(v_testDriver_891_);
lean_inc(v_buildArchive_889_);
lean_inc(v_releaseRepo_888_);
lean_inc(v_irDir_887_);
lean_inc(v_binDir_886_);
lean_inc(v_leanLibDir_885_);
lean_inc(v_buildDir_884_);
lean_inc(v_srcDir_883_);
lean_inc(v_moreGlobalServerArgs_882_);
lean_inc(v_extraDepTargets_880_);
lean_inc(v_toLeanConfig_878_);
lean_inc(v_toWorkspaceConfig_877_);
lean_dec(v_cfg_876_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 7, v_val_875_);
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_toWorkspaceConfig_877_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_toLeanConfig_878_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_extraDepTargets_880_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_moreGlobalServerArgs_882_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_srcDir_883_);
lean_ctor_set(v_reuseFailAlloc_914_, 5, v_buildDir_884_);
lean_ctor_set(v_reuseFailAlloc_914_, 6, v_leanLibDir_885_);
lean_ctor_set(v_reuseFailAlloc_914_, 7, v_val_875_);
lean_ctor_set(v_reuseFailAlloc_914_, 8, v_binDir_886_);
lean_ctor_set(v_reuseFailAlloc_914_, 9, v_irDir_887_);
lean_ctor_set(v_reuseFailAlloc_914_, 10, v_releaseRepo_888_);
lean_ctor_set(v_reuseFailAlloc_914_, 11, v_buildArchive_889_);
lean_ctor_set(v_reuseFailAlloc_914_, 12, v_testDriver_891_);
lean_ctor_set(v_reuseFailAlloc_914_, 13, v_testDriverArgs_892_);
lean_ctor_set(v_reuseFailAlloc_914_, 14, v_lintDriver_893_);
lean_ctor_set(v_reuseFailAlloc_914_, 15, v_lintDriverArgs_894_);
lean_ctor_set(v_reuseFailAlloc_914_, 16, v_version_895_);
lean_ctor_set(v_reuseFailAlloc_914_, 17, v_versionTags_896_);
lean_ctor_set(v_reuseFailAlloc_914_, 18, v_description_897_);
lean_ctor_set(v_reuseFailAlloc_914_, 19, v_keywords_898_);
lean_ctor_set(v_reuseFailAlloc_914_, 20, v_homepage_899_);
lean_ctor_set(v_reuseFailAlloc_914_, 21, v_license_900_);
lean_ctor_set(v_reuseFailAlloc_914_, 22, v_licenseFiles_901_);
lean_ctor_set(v_reuseFailAlloc_914_, 23, v_readmeFile_902_);
lean_ctor_set(v_reuseFailAlloc_914_, 24, v_enableArtifactCache_x3f_904_);
lean_ctor_set(v_reuseFailAlloc_914_, 25, v_restoreAllArtifacts_x3f_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26, v_bootstrap_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26 + 1, v_precompileModules_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26 + 2, v_preferReleaseBuild_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26 + 3, v_reservoir_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26 + 5, v_allowImportAll_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*26 + 6, v_fixedToolchain_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* v_f_917_, lean_object* v_cfg_918_){
_start:
{
lean_object* v_toWorkspaceConfig_919_; lean_object* v_toLeanConfig_920_; uint8_t v_bootstrap_921_; lean_object* v_extraDepTargets_922_; uint8_t v_precompileModules_923_; lean_object* v_moreGlobalServerArgs_924_; lean_object* v_srcDir_925_; lean_object* v_buildDir_926_; lean_object* v_leanLibDir_927_; lean_object* v_nativeLibDir_928_; lean_object* v_binDir_929_; lean_object* v_irDir_930_; lean_object* v_releaseRepo_931_; lean_object* v_buildArchive_932_; uint8_t v_preferReleaseBuild_933_; lean_object* v_testDriver_934_; lean_object* v_testDriverArgs_935_; lean_object* v_lintDriver_936_; lean_object* v_lintDriverArgs_937_; lean_object* v_version_938_; lean_object* v_versionTags_939_; lean_object* v_description_940_; lean_object* v_keywords_941_; lean_object* v_homepage_942_; lean_object* v_license_943_; lean_object* v_licenseFiles_944_; lean_object* v_readmeFile_945_; uint8_t v_reservoir_946_; lean_object* v_enableArtifactCache_x3f_947_; lean_object* v_restoreAllArtifacts_x3f_948_; uint8_t v_libPrefixOnWindows_949_; uint8_t v_allowImportAll_950_; uint8_t v_fixedToolchain_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
v_toWorkspaceConfig_919_ = lean_ctor_get(v_cfg_918_, 0);
v_toLeanConfig_920_ = lean_ctor_get(v_cfg_918_, 1);
v_bootstrap_921_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26);
v_extraDepTargets_922_ = lean_ctor_get(v_cfg_918_, 2);
v_precompileModules_923_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_924_ = lean_ctor_get(v_cfg_918_, 3);
v_srcDir_925_ = lean_ctor_get(v_cfg_918_, 4);
v_buildDir_926_ = lean_ctor_get(v_cfg_918_, 5);
v_leanLibDir_927_ = lean_ctor_get(v_cfg_918_, 6);
v_nativeLibDir_928_ = lean_ctor_get(v_cfg_918_, 7);
v_binDir_929_ = lean_ctor_get(v_cfg_918_, 8);
v_irDir_930_ = lean_ctor_get(v_cfg_918_, 9);
v_releaseRepo_931_ = lean_ctor_get(v_cfg_918_, 10);
v_buildArchive_932_ = lean_ctor_get(v_cfg_918_, 11);
v_preferReleaseBuild_933_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26 + 2);
v_testDriver_934_ = lean_ctor_get(v_cfg_918_, 12);
v_testDriverArgs_935_ = lean_ctor_get(v_cfg_918_, 13);
v_lintDriver_936_ = lean_ctor_get(v_cfg_918_, 14);
v_lintDriverArgs_937_ = lean_ctor_get(v_cfg_918_, 15);
v_version_938_ = lean_ctor_get(v_cfg_918_, 16);
v_versionTags_939_ = lean_ctor_get(v_cfg_918_, 17);
v_description_940_ = lean_ctor_get(v_cfg_918_, 18);
v_keywords_941_ = lean_ctor_get(v_cfg_918_, 19);
v_homepage_942_ = lean_ctor_get(v_cfg_918_, 20);
v_license_943_ = lean_ctor_get(v_cfg_918_, 21);
v_licenseFiles_944_ = lean_ctor_get(v_cfg_918_, 22);
v_readmeFile_945_ = lean_ctor_get(v_cfg_918_, 23);
v_reservoir_946_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_947_ = lean_ctor_get(v_cfg_918_, 24);
v_restoreAllArtifacts_x3f_948_ = lean_ctor_get(v_cfg_918_, 25);
v_libPrefixOnWindows_949_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26 + 4);
v_allowImportAll_950_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26 + 5);
v_fixedToolchain_951_ = lean_ctor_get_uint8(v_cfg_918_, sizeof(void*)*26 + 6);
v_isSharedCheck_959_ = !lean_is_exclusive(v_cfg_918_);
if (v_isSharedCheck_959_ == 0)
{
v___x_953_ = v_cfg_918_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_948_);
lean_inc(v_enableArtifactCache_x3f_947_);
lean_inc(v_readmeFile_945_);
lean_inc(v_licenseFiles_944_);
lean_inc(v_license_943_);
lean_inc(v_homepage_942_);
lean_inc(v_keywords_941_);
lean_inc(v_description_940_);
lean_inc(v_versionTags_939_);
lean_inc(v_version_938_);
lean_inc(v_lintDriverArgs_937_);
lean_inc(v_lintDriver_936_);
lean_inc(v_testDriverArgs_935_);
lean_inc(v_testDriver_934_);
lean_inc(v_buildArchive_932_);
lean_inc(v_releaseRepo_931_);
lean_inc(v_irDir_930_);
lean_inc(v_binDir_929_);
lean_inc(v_nativeLibDir_928_);
lean_inc(v_leanLibDir_927_);
lean_inc(v_buildDir_926_);
lean_inc(v_srcDir_925_);
lean_inc(v_moreGlobalServerArgs_924_);
lean_inc(v_extraDepTargets_922_);
lean_inc(v_toLeanConfig_920_);
lean_inc(v_toWorkspaceConfig_919_);
lean_dec(v_cfg_918_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_apply_1(v_f_917_, v_nativeLibDir_928_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 7, v___x_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_toWorkspaceConfig_919_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_toLeanConfig_920_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_extraDepTargets_922_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_moreGlobalServerArgs_924_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_srcDir_925_);
lean_ctor_set(v_reuseFailAlloc_958_, 5, v_buildDir_926_);
lean_ctor_set(v_reuseFailAlloc_958_, 6, v_leanLibDir_927_);
lean_ctor_set(v_reuseFailAlloc_958_, 7, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 8, v_binDir_929_);
lean_ctor_set(v_reuseFailAlloc_958_, 9, v_irDir_930_);
lean_ctor_set(v_reuseFailAlloc_958_, 10, v_releaseRepo_931_);
lean_ctor_set(v_reuseFailAlloc_958_, 11, v_buildArchive_932_);
lean_ctor_set(v_reuseFailAlloc_958_, 12, v_testDriver_934_);
lean_ctor_set(v_reuseFailAlloc_958_, 13, v_testDriverArgs_935_);
lean_ctor_set(v_reuseFailAlloc_958_, 14, v_lintDriver_936_);
lean_ctor_set(v_reuseFailAlloc_958_, 15, v_lintDriverArgs_937_);
lean_ctor_set(v_reuseFailAlloc_958_, 16, v_version_938_);
lean_ctor_set(v_reuseFailAlloc_958_, 17, v_versionTags_939_);
lean_ctor_set(v_reuseFailAlloc_958_, 18, v_description_940_);
lean_ctor_set(v_reuseFailAlloc_958_, 19, v_keywords_941_);
lean_ctor_set(v_reuseFailAlloc_958_, 20, v_homepage_942_);
lean_ctor_set(v_reuseFailAlloc_958_, 21, v_license_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 22, v_licenseFiles_944_);
lean_ctor_set(v_reuseFailAlloc_958_, 23, v_readmeFile_945_);
lean_ctor_set(v_reuseFailAlloc_958_, 24, v_enableArtifactCache_x3f_947_);
lean_ctor_set(v_reuseFailAlloc_958_, 25, v_restoreAllArtifacts_x3f_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26, v_bootstrap_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26 + 1, v_precompileModules_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26 + 2, v_preferReleaseBuild_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26 + 3, v_reservoir_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26 + 5, v_allowImportAll_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*26 + 6, v_fixedToolchain_951_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lake_defaultNativeLibDir;
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(v_x_962_);
lean_dec_ref(v_x_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_973_, lean_object* v_n_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_976_, lean_object* v_n_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_976_, v_n_977_);
lean_dec(v_n_977_);
lean_dec(v_p_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_979_, lean_object* v_n_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_979_, v_n_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_982_, lean_object* v_n_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_982_, v_n_983_);
lean_dec(v_n_983_);
lean_dec(v_p_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* v_cfg_985_){
_start:
{
lean_object* v_binDir_986_; 
v_binDir_986_ = lean_ctor_get(v_cfg_985_, 8);
lean_inc_ref(v_binDir_986_);
return v_binDir_986_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* v_cfg_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lake_PackageConfig_binDir___proj___lam__0(v_cfg_987_);
lean_dec_ref(v_cfg_987_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* v_val_989_, lean_object* v_cfg_990_){
_start:
{
lean_object* v_toWorkspaceConfig_991_; lean_object* v_toLeanConfig_992_; uint8_t v_bootstrap_993_; lean_object* v_extraDepTargets_994_; uint8_t v_precompileModules_995_; lean_object* v_moreGlobalServerArgs_996_; lean_object* v_srcDir_997_; lean_object* v_buildDir_998_; lean_object* v_leanLibDir_999_; lean_object* v_nativeLibDir_1000_; lean_object* v_irDir_1001_; lean_object* v_releaseRepo_1002_; lean_object* v_buildArchive_1003_; uint8_t v_preferReleaseBuild_1004_; lean_object* v_testDriver_1005_; lean_object* v_testDriverArgs_1006_; lean_object* v_lintDriver_1007_; lean_object* v_lintDriverArgs_1008_; lean_object* v_version_1009_; lean_object* v_versionTags_1010_; lean_object* v_description_1011_; lean_object* v_keywords_1012_; lean_object* v_homepage_1013_; lean_object* v_license_1014_; lean_object* v_licenseFiles_1015_; lean_object* v_readmeFile_1016_; uint8_t v_reservoir_1017_; lean_object* v_enableArtifactCache_x3f_1018_; lean_object* v_restoreAllArtifacts_x3f_1019_; uint8_t v_libPrefixOnWindows_1020_; uint8_t v_allowImportAll_1021_; uint8_t v_fixedToolchain_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_toWorkspaceConfig_991_ = lean_ctor_get(v_cfg_990_, 0);
v_toLeanConfig_992_ = lean_ctor_get(v_cfg_990_, 1);
v_bootstrap_993_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26);
v_extraDepTargets_994_ = lean_ctor_get(v_cfg_990_, 2);
v_precompileModules_995_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_996_ = lean_ctor_get(v_cfg_990_, 3);
v_srcDir_997_ = lean_ctor_get(v_cfg_990_, 4);
v_buildDir_998_ = lean_ctor_get(v_cfg_990_, 5);
v_leanLibDir_999_ = lean_ctor_get(v_cfg_990_, 6);
v_nativeLibDir_1000_ = lean_ctor_get(v_cfg_990_, 7);
v_irDir_1001_ = lean_ctor_get(v_cfg_990_, 9);
v_releaseRepo_1002_ = lean_ctor_get(v_cfg_990_, 10);
v_buildArchive_1003_ = lean_ctor_get(v_cfg_990_, 11);
v_preferReleaseBuild_1004_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26 + 2);
v_testDriver_1005_ = lean_ctor_get(v_cfg_990_, 12);
v_testDriverArgs_1006_ = lean_ctor_get(v_cfg_990_, 13);
v_lintDriver_1007_ = lean_ctor_get(v_cfg_990_, 14);
v_lintDriverArgs_1008_ = lean_ctor_get(v_cfg_990_, 15);
v_version_1009_ = lean_ctor_get(v_cfg_990_, 16);
v_versionTags_1010_ = lean_ctor_get(v_cfg_990_, 17);
v_description_1011_ = lean_ctor_get(v_cfg_990_, 18);
v_keywords_1012_ = lean_ctor_get(v_cfg_990_, 19);
v_homepage_1013_ = lean_ctor_get(v_cfg_990_, 20);
v_license_1014_ = lean_ctor_get(v_cfg_990_, 21);
v_licenseFiles_1015_ = lean_ctor_get(v_cfg_990_, 22);
v_readmeFile_1016_ = lean_ctor_get(v_cfg_990_, 23);
v_reservoir_1017_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1018_ = lean_ctor_get(v_cfg_990_, 24);
v_restoreAllArtifacts_x3f_1019_ = lean_ctor_get(v_cfg_990_, 25);
v_libPrefixOnWindows_1020_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26 + 4);
v_allowImportAll_1021_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26 + 5);
v_fixedToolchain_1022_ = lean_ctor_get_uint8(v_cfg_990_, sizeof(void*)*26 + 6);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_cfg_990_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_cfg_990_, 8);
lean_dec(v_unused_1030_);
v___x_1024_ = v_cfg_990_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1019_);
lean_inc(v_enableArtifactCache_x3f_1018_);
lean_inc(v_readmeFile_1016_);
lean_inc(v_licenseFiles_1015_);
lean_inc(v_license_1014_);
lean_inc(v_homepage_1013_);
lean_inc(v_keywords_1012_);
lean_inc(v_description_1011_);
lean_inc(v_versionTags_1010_);
lean_inc(v_version_1009_);
lean_inc(v_lintDriverArgs_1008_);
lean_inc(v_lintDriver_1007_);
lean_inc(v_testDriverArgs_1006_);
lean_inc(v_testDriver_1005_);
lean_inc(v_buildArchive_1003_);
lean_inc(v_releaseRepo_1002_);
lean_inc(v_irDir_1001_);
lean_inc(v_nativeLibDir_1000_);
lean_inc(v_leanLibDir_999_);
lean_inc(v_buildDir_998_);
lean_inc(v_srcDir_997_);
lean_inc(v_moreGlobalServerArgs_996_);
lean_inc(v_extraDepTargets_994_);
lean_inc(v_toLeanConfig_992_);
lean_inc(v_toWorkspaceConfig_991_);
lean_dec(v_cfg_990_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 8, v_val_989_);
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_toWorkspaceConfig_991_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_toLeanConfig_992_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_extraDepTargets_994_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_moreGlobalServerArgs_996_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_srcDir_997_);
lean_ctor_set(v_reuseFailAlloc_1028_, 5, v_buildDir_998_);
lean_ctor_set(v_reuseFailAlloc_1028_, 6, v_leanLibDir_999_);
lean_ctor_set(v_reuseFailAlloc_1028_, 7, v_nativeLibDir_1000_);
lean_ctor_set(v_reuseFailAlloc_1028_, 8, v_val_989_);
lean_ctor_set(v_reuseFailAlloc_1028_, 9, v_irDir_1001_);
lean_ctor_set(v_reuseFailAlloc_1028_, 10, v_releaseRepo_1002_);
lean_ctor_set(v_reuseFailAlloc_1028_, 11, v_buildArchive_1003_);
lean_ctor_set(v_reuseFailAlloc_1028_, 12, v_testDriver_1005_);
lean_ctor_set(v_reuseFailAlloc_1028_, 13, v_testDriverArgs_1006_);
lean_ctor_set(v_reuseFailAlloc_1028_, 14, v_lintDriver_1007_);
lean_ctor_set(v_reuseFailAlloc_1028_, 15, v_lintDriverArgs_1008_);
lean_ctor_set(v_reuseFailAlloc_1028_, 16, v_version_1009_);
lean_ctor_set(v_reuseFailAlloc_1028_, 17, v_versionTags_1010_);
lean_ctor_set(v_reuseFailAlloc_1028_, 18, v_description_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 19, v_keywords_1012_);
lean_ctor_set(v_reuseFailAlloc_1028_, 20, v_homepage_1013_);
lean_ctor_set(v_reuseFailAlloc_1028_, 21, v_license_1014_);
lean_ctor_set(v_reuseFailAlloc_1028_, 22, v_licenseFiles_1015_);
lean_ctor_set(v_reuseFailAlloc_1028_, 23, v_readmeFile_1016_);
lean_ctor_set(v_reuseFailAlloc_1028_, 24, v_enableArtifactCache_x3f_1018_);
lean_ctor_set(v_reuseFailAlloc_1028_, 25, v_restoreAllArtifacts_x3f_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26, v_bootstrap_993_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26 + 1, v_precompileModules_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26 + 3, v_reservoir_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26 + 5, v_allowImportAll_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*26 + 6, v_fixedToolchain_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* v_f_1031_, lean_object* v_cfg_1032_){
_start:
{
lean_object* v_toWorkspaceConfig_1033_; lean_object* v_toLeanConfig_1034_; uint8_t v_bootstrap_1035_; lean_object* v_extraDepTargets_1036_; uint8_t v_precompileModules_1037_; lean_object* v_moreGlobalServerArgs_1038_; lean_object* v_srcDir_1039_; lean_object* v_buildDir_1040_; lean_object* v_leanLibDir_1041_; lean_object* v_nativeLibDir_1042_; lean_object* v_binDir_1043_; lean_object* v_irDir_1044_; lean_object* v_releaseRepo_1045_; lean_object* v_buildArchive_1046_; uint8_t v_preferReleaseBuild_1047_; lean_object* v_testDriver_1048_; lean_object* v_testDriverArgs_1049_; lean_object* v_lintDriver_1050_; lean_object* v_lintDriverArgs_1051_; lean_object* v_version_1052_; lean_object* v_versionTags_1053_; lean_object* v_description_1054_; lean_object* v_keywords_1055_; lean_object* v_homepage_1056_; lean_object* v_license_1057_; lean_object* v_licenseFiles_1058_; lean_object* v_readmeFile_1059_; uint8_t v_reservoir_1060_; lean_object* v_enableArtifactCache_x3f_1061_; lean_object* v_restoreAllArtifacts_x3f_1062_; uint8_t v_libPrefixOnWindows_1063_; uint8_t v_allowImportAll_1064_; uint8_t v_fixedToolchain_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
v_toWorkspaceConfig_1033_ = lean_ctor_get(v_cfg_1032_, 0);
v_toLeanConfig_1034_ = lean_ctor_get(v_cfg_1032_, 1);
v_bootstrap_1035_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26);
v_extraDepTargets_1036_ = lean_ctor_get(v_cfg_1032_, 2);
v_precompileModules_1037_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1038_ = lean_ctor_get(v_cfg_1032_, 3);
v_srcDir_1039_ = lean_ctor_get(v_cfg_1032_, 4);
v_buildDir_1040_ = lean_ctor_get(v_cfg_1032_, 5);
v_leanLibDir_1041_ = lean_ctor_get(v_cfg_1032_, 6);
v_nativeLibDir_1042_ = lean_ctor_get(v_cfg_1032_, 7);
v_binDir_1043_ = lean_ctor_get(v_cfg_1032_, 8);
v_irDir_1044_ = lean_ctor_get(v_cfg_1032_, 9);
v_releaseRepo_1045_ = lean_ctor_get(v_cfg_1032_, 10);
v_buildArchive_1046_ = lean_ctor_get(v_cfg_1032_, 11);
v_preferReleaseBuild_1047_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26 + 2);
v_testDriver_1048_ = lean_ctor_get(v_cfg_1032_, 12);
v_testDriverArgs_1049_ = lean_ctor_get(v_cfg_1032_, 13);
v_lintDriver_1050_ = lean_ctor_get(v_cfg_1032_, 14);
v_lintDriverArgs_1051_ = lean_ctor_get(v_cfg_1032_, 15);
v_version_1052_ = lean_ctor_get(v_cfg_1032_, 16);
v_versionTags_1053_ = lean_ctor_get(v_cfg_1032_, 17);
v_description_1054_ = lean_ctor_get(v_cfg_1032_, 18);
v_keywords_1055_ = lean_ctor_get(v_cfg_1032_, 19);
v_homepage_1056_ = lean_ctor_get(v_cfg_1032_, 20);
v_license_1057_ = lean_ctor_get(v_cfg_1032_, 21);
v_licenseFiles_1058_ = lean_ctor_get(v_cfg_1032_, 22);
v_readmeFile_1059_ = lean_ctor_get(v_cfg_1032_, 23);
v_reservoir_1060_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1061_ = lean_ctor_get(v_cfg_1032_, 24);
v_restoreAllArtifacts_x3f_1062_ = lean_ctor_get(v_cfg_1032_, 25);
v_libPrefixOnWindows_1063_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26 + 4);
v_allowImportAll_1064_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26 + 5);
v_fixedToolchain_1065_ = lean_ctor_get_uint8(v_cfg_1032_, sizeof(void*)*26 + 6);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_cfg_1032_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1067_ = v_cfg_1032_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1062_);
lean_inc(v_enableArtifactCache_x3f_1061_);
lean_inc(v_readmeFile_1059_);
lean_inc(v_licenseFiles_1058_);
lean_inc(v_license_1057_);
lean_inc(v_homepage_1056_);
lean_inc(v_keywords_1055_);
lean_inc(v_description_1054_);
lean_inc(v_versionTags_1053_);
lean_inc(v_version_1052_);
lean_inc(v_lintDriverArgs_1051_);
lean_inc(v_lintDriver_1050_);
lean_inc(v_testDriverArgs_1049_);
lean_inc(v_testDriver_1048_);
lean_inc(v_buildArchive_1046_);
lean_inc(v_releaseRepo_1045_);
lean_inc(v_irDir_1044_);
lean_inc(v_binDir_1043_);
lean_inc(v_nativeLibDir_1042_);
lean_inc(v_leanLibDir_1041_);
lean_inc(v_buildDir_1040_);
lean_inc(v_srcDir_1039_);
lean_inc(v_moreGlobalServerArgs_1038_);
lean_inc(v_extraDepTargets_1036_);
lean_inc(v_toLeanConfig_1034_);
lean_inc(v_toWorkspaceConfig_1033_);
lean_dec(v_cfg_1032_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_apply_1(v_f_1031_, v_binDir_1043_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 8, v___x_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_toWorkspaceConfig_1033_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_toLeanConfig_1034_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_extraDepTargets_1036_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v_moreGlobalServerArgs_1038_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_srcDir_1039_);
lean_ctor_set(v_reuseFailAlloc_1072_, 5, v_buildDir_1040_);
lean_ctor_set(v_reuseFailAlloc_1072_, 6, v_leanLibDir_1041_);
lean_ctor_set(v_reuseFailAlloc_1072_, 7, v_nativeLibDir_1042_);
lean_ctor_set(v_reuseFailAlloc_1072_, 8, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1072_, 9, v_irDir_1044_);
lean_ctor_set(v_reuseFailAlloc_1072_, 10, v_releaseRepo_1045_);
lean_ctor_set(v_reuseFailAlloc_1072_, 11, v_buildArchive_1046_);
lean_ctor_set(v_reuseFailAlloc_1072_, 12, v_testDriver_1048_);
lean_ctor_set(v_reuseFailAlloc_1072_, 13, v_testDriverArgs_1049_);
lean_ctor_set(v_reuseFailAlloc_1072_, 14, v_lintDriver_1050_);
lean_ctor_set(v_reuseFailAlloc_1072_, 15, v_lintDriverArgs_1051_);
lean_ctor_set(v_reuseFailAlloc_1072_, 16, v_version_1052_);
lean_ctor_set(v_reuseFailAlloc_1072_, 17, v_versionTags_1053_);
lean_ctor_set(v_reuseFailAlloc_1072_, 18, v_description_1054_);
lean_ctor_set(v_reuseFailAlloc_1072_, 19, v_keywords_1055_);
lean_ctor_set(v_reuseFailAlloc_1072_, 20, v_homepage_1056_);
lean_ctor_set(v_reuseFailAlloc_1072_, 21, v_license_1057_);
lean_ctor_set(v_reuseFailAlloc_1072_, 22, v_licenseFiles_1058_);
lean_ctor_set(v_reuseFailAlloc_1072_, 23, v_readmeFile_1059_);
lean_ctor_set(v_reuseFailAlloc_1072_, 24, v_enableArtifactCache_x3f_1061_);
lean_ctor_set(v_reuseFailAlloc_1072_, 25, v_restoreAllArtifacts_x3f_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26, v_bootstrap_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26 + 1, v_precompileModules_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26 + 3, v_reservoir_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26 + 5, v_allowImportAll_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1072_, sizeof(void*)*26 + 6, v_fixedToolchain_1065_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* v_x_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lake_defaultBinDir;
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* v_x_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lake_PackageConfig_binDir___proj___lam__3(v_x_1076_);
lean_dec_ref(v_x_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1087_, lean_object* v_n_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1090_, lean_object* v_n_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lake_PackageConfig_binDir___proj(v_p_1090_, v_n_1091_);
lean_dec(v_n_1091_);
lean_dec(v_p_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1093_, lean_object* v_n_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lake_PackageConfig_binDir___proj(v_p_1093_, v_n_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1096_, lean_object* v_n_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1096_, v_n_1097_);
lean_dec(v_n_1097_);
lean_dec(v_p_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* v_cfg_1099_){
_start:
{
lean_object* v_irDir_1100_; 
v_irDir_1100_ = lean_ctor_get(v_cfg_1099_, 9);
lean_inc_ref(v_irDir_1100_);
return v_irDir_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* v_cfg_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lake_PackageConfig_irDir___proj___lam__0(v_cfg_1101_);
lean_dec_ref(v_cfg_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* v_val_1103_, lean_object* v_cfg_1104_){
_start:
{
lean_object* v_toWorkspaceConfig_1105_; lean_object* v_toLeanConfig_1106_; uint8_t v_bootstrap_1107_; lean_object* v_extraDepTargets_1108_; uint8_t v_precompileModules_1109_; lean_object* v_moreGlobalServerArgs_1110_; lean_object* v_srcDir_1111_; lean_object* v_buildDir_1112_; lean_object* v_leanLibDir_1113_; lean_object* v_nativeLibDir_1114_; lean_object* v_binDir_1115_; lean_object* v_releaseRepo_1116_; lean_object* v_buildArchive_1117_; uint8_t v_preferReleaseBuild_1118_; lean_object* v_testDriver_1119_; lean_object* v_testDriverArgs_1120_; lean_object* v_lintDriver_1121_; lean_object* v_lintDriverArgs_1122_; lean_object* v_version_1123_; lean_object* v_versionTags_1124_; lean_object* v_description_1125_; lean_object* v_keywords_1126_; lean_object* v_homepage_1127_; lean_object* v_license_1128_; lean_object* v_licenseFiles_1129_; lean_object* v_readmeFile_1130_; uint8_t v_reservoir_1131_; lean_object* v_enableArtifactCache_x3f_1132_; lean_object* v_restoreAllArtifacts_x3f_1133_; uint8_t v_libPrefixOnWindows_1134_; uint8_t v_allowImportAll_1135_; uint8_t v_fixedToolchain_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_toWorkspaceConfig_1105_ = lean_ctor_get(v_cfg_1104_, 0);
v_toLeanConfig_1106_ = lean_ctor_get(v_cfg_1104_, 1);
v_bootstrap_1107_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26);
v_extraDepTargets_1108_ = lean_ctor_get(v_cfg_1104_, 2);
v_precompileModules_1109_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1110_ = lean_ctor_get(v_cfg_1104_, 3);
v_srcDir_1111_ = lean_ctor_get(v_cfg_1104_, 4);
v_buildDir_1112_ = lean_ctor_get(v_cfg_1104_, 5);
v_leanLibDir_1113_ = lean_ctor_get(v_cfg_1104_, 6);
v_nativeLibDir_1114_ = lean_ctor_get(v_cfg_1104_, 7);
v_binDir_1115_ = lean_ctor_get(v_cfg_1104_, 8);
v_releaseRepo_1116_ = lean_ctor_get(v_cfg_1104_, 10);
v_buildArchive_1117_ = lean_ctor_get(v_cfg_1104_, 11);
v_preferReleaseBuild_1118_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26 + 2);
v_testDriver_1119_ = lean_ctor_get(v_cfg_1104_, 12);
v_testDriverArgs_1120_ = lean_ctor_get(v_cfg_1104_, 13);
v_lintDriver_1121_ = lean_ctor_get(v_cfg_1104_, 14);
v_lintDriverArgs_1122_ = lean_ctor_get(v_cfg_1104_, 15);
v_version_1123_ = lean_ctor_get(v_cfg_1104_, 16);
v_versionTags_1124_ = lean_ctor_get(v_cfg_1104_, 17);
v_description_1125_ = lean_ctor_get(v_cfg_1104_, 18);
v_keywords_1126_ = lean_ctor_get(v_cfg_1104_, 19);
v_homepage_1127_ = lean_ctor_get(v_cfg_1104_, 20);
v_license_1128_ = lean_ctor_get(v_cfg_1104_, 21);
v_licenseFiles_1129_ = lean_ctor_get(v_cfg_1104_, 22);
v_readmeFile_1130_ = lean_ctor_get(v_cfg_1104_, 23);
v_reservoir_1131_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1132_ = lean_ctor_get(v_cfg_1104_, 24);
v_restoreAllArtifacts_x3f_1133_ = lean_ctor_get(v_cfg_1104_, 25);
v_libPrefixOnWindows_1134_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26 + 4);
v_allowImportAll_1135_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26 + 5);
v_fixedToolchain_1136_ = lean_ctor_get_uint8(v_cfg_1104_, sizeof(void*)*26 + 6);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_cfg_1104_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_cfg_1104_, 9);
lean_dec(v_unused_1144_);
v___x_1138_ = v_cfg_1104_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1133_);
lean_inc(v_enableArtifactCache_x3f_1132_);
lean_inc(v_readmeFile_1130_);
lean_inc(v_licenseFiles_1129_);
lean_inc(v_license_1128_);
lean_inc(v_homepage_1127_);
lean_inc(v_keywords_1126_);
lean_inc(v_description_1125_);
lean_inc(v_versionTags_1124_);
lean_inc(v_version_1123_);
lean_inc(v_lintDriverArgs_1122_);
lean_inc(v_lintDriver_1121_);
lean_inc(v_testDriverArgs_1120_);
lean_inc(v_testDriver_1119_);
lean_inc(v_buildArchive_1117_);
lean_inc(v_releaseRepo_1116_);
lean_inc(v_binDir_1115_);
lean_inc(v_nativeLibDir_1114_);
lean_inc(v_leanLibDir_1113_);
lean_inc(v_buildDir_1112_);
lean_inc(v_srcDir_1111_);
lean_inc(v_moreGlobalServerArgs_1110_);
lean_inc(v_extraDepTargets_1108_);
lean_inc(v_toLeanConfig_1106_);
lean_inc(v_toWorkspaceConfig_1105_);
lean_dec(v_cfg_1104_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 9, v_val_1103_);
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_toWorkspaceConfig_1105_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_toLeanConfig_1106_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_extraDepTargets_1108_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_moreGlobalServerArgs_1110_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_srcDir_1111_);
lean_ctor_set(v_reuseFailAlloc_1142_, 5, v_buildDir_1112_);
lean_ctor_set(v_reuseFailAlloc_1142_, 6, v_leanLibDir_1113_);
lean_ctor_set(v_reuseFailAlloc_1142_, 7, v_nativeLibDir_1114_);
lean_ctor_set(v_reuseFailAlloc_1142_, 8, v_binDir_1115_);
lean_ctor_set(v_reuseFailAlloc_1142_, 9, v_val_1103_);
lean_ctor_set(v_reuseFailAlloc_1142_, 10, v_releaseRepo_1116_);
lean_ctor_set(v_reuseFailAlloc_1142_, 11, v_buildArchive_1117_);
lean_ctor_set(v_reuseFailAlloc_1142_, 12, v_testDriver_1119_);
lean_ctor_set(v_reuseFailAlloc_1142_, 13, v_testDriverArgs_1120_);
lean_ctor_set(v_reuseFailAlloc_1142_, 14, v_lintDriver_1121_);
lean_ctor_set(v_reuseFailAlloc_1142_, 15, v_lintDriverArgs_1122_);
lean_ctor_set(v_reuseFailAlloc_1142_, 16, v_version_1123_);
lean_ctor_set(v_reuseFailAlloc_1142_, 17, v_versionTags_1124_);
lean_ctor_set(v_reuseFailAlloc_1142_, 18, v_description_1125_);
lean_ctor_set(v_reuseFailAlloc_1142_, 19, v_keywords_1126_);
lean_ctor_set(v_reuseFailAlloc_1142_, 20, v_homepage_1127_);
lean_ctor_set(v_reuseFailAlloc_1142_, 21, v_license_1128_);
lean_ctor_set(v_reuseFailAlloc_1142_, 22, v_licenseFiles_1129_);
lean_ctor_set(v_reuseFailAlloc_1142_, 23, v_readmeFile_1130_);
lean_ctor_set(v_reuseFailAlloc_1142_, 24, v_enableArtifactCache_x3f_1132_);
lean_ctor_set(v_reuseFailAlloc_1142_, 25, v_restoreAllArtifacts_x3f_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26, v_bootstrap_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26 + 1, v_precompileModules_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26 + 3, v_reservoir_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26 + 5, v_allowImportAll_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*26 + 6, v_fixedToolchain_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* v_f_1145_, lean_object* v_cfg_1146_){
_start:
{
lean_object* v_toWorkspaceConfig_1147_; lean_object* v_toLeanConfig_1148_; uint8_t v_bootstrap_1149_; lean_object* v_extraDepTargets_1150_; uint8_t v_precompileModules_1151_; lean_object* v_moreGlobalServerArgs_1152_; lean_object* v_srcDir_1153_; lean_object* v_buildDir_1154_; lean_object* v_leanLibDir_1155_; lean_object* v_nativeLibDir_1156_; lean_object* v_binDir_1157_; lean_object* v_irDir_1158_; lean_object* v_releaseRepo_1159_; lean_object* v_buildArchive_1160_; uint8_t v_preferReleaseBuild_1161_; lean_object* v_testDriver_1162_; lean_object* v_testDriverArgs_1163_; lean_object* v_lintDriver_1164_; lean_object* v_lintDriverArgs_1165_; lean_object* v_version_1166_; lean_object* v_versionTags_1167_; lean_object* v_description_1168_; lean_object* v_keywords_1169_; lean_object* v_homepage_1170_; lean_object* v_license_1171_; lean_object* v_licenseFiles_1172_; lean_object* v_readmeFile_1173_; uint8_t v_reservoir_1174_; lean_object* v_enableArtifactCache_x3f_1175_; lean_object* v_restoreAllArtifacts_x3f_1176_; uint8_t v_libPrefixOnWindows_1177_; uint8_t v_allowImportAll_1178_; uint8_t v_fixedToolchain_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
v_toWorkspaceConfig_1147_ = lean_ctor_get(v_cfg_1146_, 0);
v_toLeanConfig_1148_ = lean_ctor_get(v_cfg_1146_, 1);
v_bootstrap_1149_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26);
v_extraDepTargets_1150_ = lean_ctor_get(v_cfg_1146_, 2);
v_precompileModules_1151_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1152_ = lean_ctor_get(v_cfg_1146_, 3);
v_srcDir_1153_ = lean_ctor_get(v_cfg_1146_, 4);
v_buildDir_1154_ = lean_ctor_get(v_cfg_1146_, 5);
v_leanLibDir_1155_ = lean_ctor_get(v_cfg_1146_, 6);
v_nativeLibDir_1156_ = lean_ctor_get(v_cfg_1146_, 7);
v_binDir_1157_ = lean_ctor_get(v_cfg_1146_, 8);
v_irDir_1158_ = lean_ctor_get(v_cfg_1146_, 9);
v_releaseRepo_1159_ = lean_ctor_get(v_cfg_1146_, 10);
v_buildArchive_1160_ = lean_ctor_get(v_cfg_1146_, 11);
v_preferReleaseBuild_1161_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26 + 2);
v_testDriver_1162_ = lean_ctor_get(v_cfg_1146_, 12);
v_testDriverArgs_1163_ = lean_ctor_get(v_cfg_1146_, 13);
v_lintDriver_1164_ = lean_ctor_get(v_cfg_1146_, 14);
v_lintDriverArgs_1165_ = lean_ctor_get(v_cfg_1146_, 15);
v_version_1166_ = lean_ctor_get(v_cfg_1146_, 16);
v_versionTags_1167_ = lean_ctor_get(v_cfg_1146_, 17);
v_description_1168_ = lean_ctor_get(v_cfg_1146_, 18);
v_keywords_1169_ = lean_ctor_get(v_cfg_1146_, 19);
v_homepage_1170_ = lean_ctor_get(v_cfg_1146_, 20);
v_license_1171_ = lean_ctor_get(v_cfg_1146_, 21);
v_licenseFiles_1172_ = lean_ctor_get(v_cfg_1146_, 22);
v_readmeFile_1173_ = lean_ctor_get(v_cfg_1146_, 23);
v_reservoir_1174_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1175_ = lean_ctor_get(v_cfg_1146_, 24);
v_restoreAllArtifacts_x3f_1176_ = lean_ctor_get(v_cfg_1146_, 25);
v_libPrefixOnWindows_1177_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26 + 4);
v_allowImportAll_1178_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26 + 5);
v_fixedToolchain_1179_ = lean_ctor_get_uint8(v_cfg_1146_, sizeof(void*)*26 + 6);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_cfg_1146_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1181_ = v_cfg_1146_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1176_);
lean_inc(v_enableArtifactCache_x3f_1175_);
lean_inc(v_readmeFile_1173_);
lean_inc(v_licenseFiles_1172_);
lean_inc(v_license_1171_);
lean_inc(v_homepage_1170_);
lean_inc(v_keywords_1169_);
lean_inc(v_description_1168_);
lean_inc(v_versionTags_1167_);
lean_inc(v_version_1166_);
lean_inc(v_lintDriverArgs_1165_);
lean_inc(v_lintDriver_1164_);
lean_inc(v_testDriverArgs_1163_);
lean_inc(v_testDriver_1162_);
lean_inc(v_buildArchive_1160_);
lean_inc(v_releaseRepo_1159_);
lean_inc(v_irDir_1158_);
lean_inc(v_binDir_1157_);
lean_inc(v_nativeLibDir_1156_);
lean_inc(v_leanLibDir_1155_);
lean_inc(v_buildDir_1154_);
lean_inc(v_srcDir_1153_);
lean_inc(v_moreGlobalServerArgs_1152_);
lean_inc(v_extraDepTargets_1150_);
lean_inc(v_toLeanConfig_1148_);
lean_inc(v_toWorkspaceConfig_1147_);
lean_dec(v_cfg_1146_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_apply_1(v_f_1145_, v_irDir_1158_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 9, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_toWorkspaceConfig_1147_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_toLeanConfig_1148_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_extraDepTargets_1150_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_moreGlobalServerArgs_1152_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_srcDir_1153_);
lean_ctor_set(v_reuseFailAlloc_1186_, 5, v_buildDir_1154_);
lean_ctor_set(v_reuseFailAlloc_1186_, 6, v_leanLibDir_1155_);
lean_ctor_set(v_reuseFailAlloc_1186_, 7, v_nativeLibDir_1156_);
lean_ctor_set(v_reuseFailAlloc_1186_, 8, v_binDir_1157_);
lean_ctor_set(v_reuseFailAlloc_1186_, 9, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 10, v_releaseRepo_1159_);
lean_ctor_set(v_reuseFailAlloc_1186_, 11, v_buildArchive_1160_);
lean_ctor_set(v_reuseFailAlloc_1186_, 12, v_testDriver_1162_);
lean_ctor_set(v_reuseFailAlloc_1186_, 13, v_testDriverArgs_1163_);
lean_ctor_set(v_reuseFailAlloc_1186_, 14, v_lintDriver_1164_);
lean_ctor_set(v_reuseFailAlloc_1186_, 15, v_lintDriverArgs_1165_);
lean_ctor_set(v_reuseFailAlloc_1186_, 16, v_version_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 17, v_versionTags_1167_);
lean_ctor_set(v_reuseFailAlloc_1186_, 18, v_description_1168_);
lean_ctor_set(v_reuseFailAlloc_1186_, 19, v_keywords_1169_);
lean_ctor_set(v_reuseFailAlloc_1186_, 20, v_homepage_1170_);
lean_ctor_set(v_reuseFailAlloc_1186_, 21, v_license_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 22, v_licenseFiles_1172_);
lean_ctor_set(v_reuseFailAlloc_1186_, 23, v_readmeFile_1173_);
lean_ctor_set(v_reuseFailAlloc_1186_, 24, v_enableArtifactCache_x3f_1175_);
lean_ctor_set(v_reuseFailAlloc_1186_, 25, v_restoreAllArtifacts_x3f_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26, v_bootstrap_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26 + 1, v_precompileModules_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26 + 3, v_reservoir_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26 + 5, v_allowImportAll_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*26 + 6, v_fixedToolchain_1179_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lake_defaultIrDir;
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* v_x_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lake_PackageConfig_irDir___proj___lam__3(v_x_1190_);
lean_dec_ref(v_x_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1201_, lean_object* v_n_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1204_, lean_object* v_n_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lake_PackageConfig_irDir___proj(v_p_1204_, v_n_1205_);
lean_dec(v_n_1205_);
lean_dec(v_p_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1207_, lean_object* v_n_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lake_PackageConfig_irDir___proj(v_p_1207_, v_n_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1210_, lean_object* v_n_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1210_, v_n_1211_);
lean_dec(v_n_1211_);
lean_dec(v_p_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* v_cfg_1213_){
_start:
{
lean_object* v_releaseRepo_1214_; 
v_releaseRepo_1214_ = lean_ctor_get(v_cfg_1213_, 10);
lean_inc(v_releaseRepo_1214_);
return v_releaseRepo_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* v_cfg_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lake_PackageConfig_releaseRepo___proj___lam__0(v_cfg_1215_);
lean_dec_ref(v_cfg_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* v_val_1217_, lean_object* v_cfg_1218_){
_start:
{
lean_object* v_toWorkspaceConfig_1219_; lean_object* v_toLeanConfig_1220_; uint8_t v_bootstrap_1221_; lean_object* v_extraDepTargets_1222_; uint8_t v_precompileModules_1223_; lean_object* v_moreGlobalServerArgs_1224_; lean_object* v_srcDir_1225_; lean_object* v_buildDir_1226_; lean_object* v_leanLibDir_1227_; lean_object* v_nativeLibDir_1228_; lean_object* v_binDir_1229_; lean_object* v_irDir_1230_; lean_object* v_buildArchive_1231_; uint8_t v_preferReleaseBuild_1232_; lean_object* v_testDriver_1233_; lean_object* v_testDriverArgs_1234_; lean_object* v_lintDriver_1235_; lean_object* v_lintDriverArgs_1236_; lean_object* v_version_1237_; lean_object* v_versionTags_1238_; lean_object* v_description_1239_; lean_object* v_keywords_1240_; lean_object* v_homepage_1241_; lean_object* v_license_1242_; lean_object* v_licenseFiles_1243_; lean_object* v_readmeFile_1244_; uint8_t v_reservoir_1245_; lean_object* v_enableArtifactCache_x3f_1246_; lean_object* v_restoreAllArtifacts_x3f_1247_; uint8_t v_libPrefixOnWindows_1248_; uint8_t v_allowImportAll_1249_; uint8_t v_fixedToolchain_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_toWorkspaceConfig_1219_ = lean_ctor_get(v_cfg_1218_, 0);
v_toLeanConfig_1220_ = lean_ctor_get(v_cfg_1218_, 1);
v_bootstrap_1221_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26);
v_extraDepTargets_1222_ = lean_ctor_get(v_cfg_1218_, 2);
v_precompileModules_1223_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1224_ = lean_ctor_get(v_cfg_1218_, 3);
v_srcDir_1225_ = lean_ctor_get(v_cfg_1218_, 4);
v_buildDir_1226_ = lean_ctor_get(v_cfg_1218_, 5);
v_leanLibDir_1227_ = lean_ctor_get(v_cfg_1218_, 6);
v_nativeLibDir_1228_ = lean_ctor_get(v_cfg_1218_, 7);
v_binDir_1229_ = lean_ctor_get(v_cfg_1218_, 8);
v_irDir_1230_ = lean_ctor_get(v_cfg_1218_, 9);
v_buildArchive_1231_ = lean_ctor_get(v_cfg_1218_, 11);
v_preferReleaseBuild_1232_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26 + 2);
v_testDriver_1233_ = lean_ctor_get(v_cfg_1218_, 12);
v_testDriverArgs_1234_ = lean_ctor_get(v_cfg_1218_, 13);
v_lintDriver_1235_ = lean_ctor_get(v_cfg_1218_, 14);
v_lintDriverArgs_1236_ = lean_ctor_get(v_cfg_1218_, 15);
v_version_1237_ = lean_ctor_get(v_cfg_1218_, 16);
v_versionTags_1238_ = lean_ctor_get(v_cfg_1218_, 17);
v_description_1239_ = lean_ctor_get(v_cfg_1218_, 18);
v_keywords_1240_ = lean_ctor_get(v_cfg_1218_, 19);
v_homepage_1241_ = lean_ctor_get(v_cfg_1218_, 20);
v_license_1242_ = lean_ctor_get(v_cfg_1218_, 21);
v_licenseFiles_1243_ = lean_ctor_get(v_cfg_1218_, 22);
v_readmeFile_1244_ = lean_ctor_get(v_cfg_1218_, 23);
v_reservoir_1245_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1246_ = lean_ctor_get(v_cfg_1218_, 24);
v_restoreAllArtifacts_x3f_1247_ = lean_ctor_get(v_cfg_1218_, 25);
v_libPrefixOnWindows_1248_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26 + 4);
v_allowImportAll_1249_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26 + 5);
v_fixedToolchain_1250_ = lean_ctor_get_uint8(v_cfg_1218_, sizeof(void*)*26 + 6);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_cfg_1218_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_cfg_1218_, 10);
lean_dec(v_unused_1258_);
v___x_1252_ = v_cfg_1218_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1247_);
lean_inc(v_enableArtifactCache_x3f_1246_);
lean_inc(v_readmeFile_1244_);
lean_inc(v_licenseFiles_1243_);
lean_inc(v_license_1242_);
lean_inc(v_homepage_1241_);
lean_inc(v_keywords_1240_);
lean_inc(v_description_1239_);
lean_inc(v_versionTags_1238_);
lean_inc(v_version_1237_);
lean_inc(v_lintDriverArgs_1236_);
lean_inc(v_lintDriver_1235_);
lean_inc(v_testDriverArgs_1234_);
lean_inc(v_testDriver_1233_);
lean_inc(v_buildArchive_1231_);
lean_inc(v_irDir_1230_);
lean_inc(v_binDir_1229_);
lean_inc(v_nativeLibDir_1228_);
lean_inc(v_leanLibDir_1227_);
lean_inc(v_buildDir_1226_);
lean_inc(v_srcDir_1225_);
lean_inc(v_moreGlobalServerArgs_1224_);
lean_inc(v_extraDepTargets_1222_);
lean_inc(v_toLeanConfig_1220_);
lean_inc(v_toWorkspaceConfig_1219_);
lean_dec(v_cfg_1218_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 10, v_val_1217_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_toWorkspaceConfig_1219_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_toLeanConfig_1220_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_extraDepTargets_1222_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_moreGlobalServerArgs_1224_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_srcDir_1225_);
lean_ctor_set(v_reuseFailAlloc_1256_, 5, v_buildDir_1226_);
lean_ctor_set(v_reuseFailAlloc_1256_, 6, v_leanLibDir_1227_);
lean_ctor_set(v_reuseFailAlloc_1256_, 7, v_nativeLibDir_1228_);
lean_ctor_set(v_reuseFailAlloc_1256_, 8, v_binDir_1229_);
lean_ctor_set(v_reuseFailAlloc_1256_, 9, v_irDir_1230_);
lean_ctor_set(v_reuseFailAlloc_1256_, 10, v_val_1217_);
lean_ctor_set(v_reuseFailAlloc_1256_, 11, v_buildArchive_1231_);
lean_ctor_set(v_reuseFailAlloc_1256_, 12, v_testDriver_1233_);
lean_ctor_set(v_reuseFailAlloc_1256_, 13, v_testDriverArgs_1234_);
lean_ctor_set(v_reuseFailAlloc_1256_, 14, v_lintDriver_1235_);
lean_ctor_set(v_reuseFailAlloc_1256_, 15, v_lintDriverArgs_1236_);
lean_ctor_set(v_reuseFailAlloc_1256_, 16, v_version_1237_);
lean_ctor_set(v_reuseFailAlloc_1256_, 17, v_versionTags_1238_);
lean_ctor_set(v_reuseFailAlloc_1256_, 18, v_description_1239_);
lean_ctor_set(v_reuseFailAlloc_1256_, 19, v_keywords_1240_);
lean_ctor_set(v_reuseFailAlloc_1256_, 20, v_homepage_1241_);
lean_ctor_set(v_reuseFailAlloc_1256_, 21, v_license_1242_);
lean_ctor_set(v_reuseFailAlloc_1256_, 22, v_licenseFiles_1243_);
lean_ctor_set(v_reuseFailAlloc_1256_, 23, v_readmeFile_1244_);
lean_ctor_set(v_reuseFailAlloc_1256_, 24, v_enableArtifactCache_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 25, v_restoreAllArtifacts_x3f_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26, v_bootstrap_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26 + 1, v_precompileModules_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26 + 3, v_reservoir_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26 + 5, v_allowImportAll_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*26 + 6, v_fixedToolchain_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* v_f_1259_, lean_object* v_cfg_1260_){
_start:
{
lean_object* v_toWorkspaceConfig_1261_; lean_object* v_toLeanConfig_1262_; uint8_t v_bootstrap_1263_; lean_object* v_extraDepTargets_1264_; uint8_t v_precompileModules_1265_; lean_object* v_moreGlobalServerArgs_1266_; lean_object* v_srcDir_1267_; lean_object* v_buildDir_1268_; lean_object* v_leanLibDir_1269_; lean_object* v_nativeLibDir_1270_; lean_object* v_binDir_1271_; lean_object* v_irDir_1272_; lean_object* v_releaseRepo_1273_; lean_object* v_buildArchive_1274_; uint8_t v_preferReleaseBuild_1275_; lean_object* v_testDriver_1276_; lean_object* v_testDriverArgs_1277_; lean_object* v_lintDriver_1278_; lean_object* v_lintDriverArgs_1279_; lean_object* v_version_1280_; lean_object* v_versionTags_1281_; lean_object* v_description_1282_; lean_object* v_keywords_1283_; lean_object* v_homepage_1284_; lean_object* v_license_1285_; lean_object* v_licenseFiles_1286_; lean_object* v_readmeFile_1287_; uint8_t v_reservoir_1288_; lean_object* v_enableArtifactCache_x3f_1289_; lean_object* v_restoreAllArtifacts_x3f_1290_; uint8_t v_libPrefixOnWindows_1291_; uint8_t v_allowImportAll_1292_; uint8_t v_fixedToolchain_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_toWorkspaceConfig_1261_ = lean_ctor_get(v_cfg_1260_, 0);
v_toLeanConfig_1262_ = lean_ctor_get(v_cfg_1260_, 1);
v_bootstrap_1263_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26);
v_extraDepTargets_1264_ = lean_ctor_get(v_cfg_1260_, 2);
v_precompileModules_1265_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1266_ = lean_ctor_get(v_cfg_1260_, 3);
v_srcDir_1267_ = lean_ctor_get(v_cfg_1260_, 4);
v_buildDir_1268_ = lean_ctor_get(v_cfg_1260_, 5);
v_leanLibDir_1269_ = lean_ctor_get(v_cfg_1260_, 6);
v_nativeLibDir_1270_ = lean_ctor_get(v_cfg_1260_, 7);
v_binDir_1271_ = lean_ctor_get(v_cfg_1260_, 8);
v_irDir_1272_ = lean_ctor_get(v_cfg_1260_, 9);
v_releaseRepo_1273_ = lean_ctor_get(v_cfg_1260_, 10);
v_buildArchive_1274_ = lean_ctor_get(v_cfg_1260_, 11);
v_preferReleaseBuild_1275_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26 + 2);
v_testDriver_1276_ = lean_ctor_get(v_cfg_1260_, 12);
v_testDriverArgs_1277_ = lean_ctor_get(v_cfg_1260_, 13);
v_lintDriver_1278_ = lean_ctor_get(v_cfg_1260_, 14);
v_lintDriverArgs_1279_ = lean_ctor_get(v_cfg_1260_, 15);
v_version_1280_ = lean_ctor_get(v_cfg_1260_, 16);
v_versionTags_1281_ = lean_ctor_get(v_cfg_1260_, 17);
v_description_1282_ = lean_ctor_get(v_cfg_1260_, 18);
v_keywords_1283_ = lean_ctor_get(v_cfg_1260_, 19);
v_homepage_1284_ = lean_ctor_get(v_cfg_1260_, 20);
v_license_1285_ = lean_ctor_get(v_cfg_1260_, 21);
v_licenseFiles_1286_ = lean_ctor_get(v_cfg_1260_, 22);
v_readmeFile_1287_ = lean_ctor_get(v_cfg_1260_, 23);
v_reservoir_1288_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1289_ = lean_ctor_get(v_cfg_1260_, 24);
v_restoreAllArtifacts_x3f_1290_ = lean_ctor_get(v_cfg_1260_, 25);
v_libPrefixOnWindows_1291_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26 + 4);
v_allowImportAll_1292_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26 + 5);
v_fixedToolchain_1293_ = lean_ctor_get_uint8(v_cfg_1260_, sizeof(void*)*26 + 6);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_cfg_1260_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1295_ = v_cfg_1260_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1290_);
lean_inc(v_enableArtifactCache_x3f_1289_);
lean_inc(v_readmeFile_1287_);
lean_inc(v_licenseFiles_1286_);
lean_inc(v_license_1285_);
lean_inc(v_homepage_1284_);
lean_inc(v_keywords_1283_);
lean_inc(v_description_1282_);
lean_inc(v_versionTags_1281_);
lean_inc(v_version_1280_);
lean_inc(v_lintDriverArgs_1279_);
lean_inc(v_lintDriver_1278_);
lean_inc(v_testDriverArgs_1277_);
lean_inc(v_testDriver_1276_);
lean_inc(v_buildArchive_1274_);
lean_inc(v_releaseRepo_1273_);
lean_inc(v_irDir_1272_);
lean_inc(v_binDir_1271_);
lean_inc(v_nativeLibDir_1270_);
lean_inc(v_leanLibDir_1269_);
lean_inc(v_buildDir_1268_);
lean_inc(v_srcDir_1267_);
lean_inc(v_moreGlobalServerArgs_1266_);
lean_inc(v_extraDepTargets_1264_);
lean_inc(v_toLeanConfig_1262_);
lean_inc(v_toWorkspaceConfig_1261_);
lean_dec(v_cfg_1260_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_apply_1(v_f_1259_, v_releaseRepo_1273_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 10, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_toWorkspaceConfig_1261_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_toLeanConfig_1262_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_extraDepTargets_1264_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_moreGlobalServerArgs_1266_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_srcDir_1267_);
lean_ctor_set(v_reuseFailAlloc_1300_, 5, v_buildDir_1268_);
lean_ctor_set(v_reuseFailAlloc_1300_, 6, v_leanLibDir_1269_);
lean_ctor_set(v_reuseFailAlloc_1300_, 7, v_nativeLibDir_1270_);
lean_ctor_set(v_reuseFailAlloc_1300_, 8, v_binDir_1271_);
lean_ctor_set(v_reuseFailAlloc_1300_, 9, v_irDir_1272_);
lean_ctor_set(v_reuseFailAlloc_1300_, 10, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1300_, 11, v_buildArchive_1274_);
lean_ctor_set(v_reuseFailAlloc_1300_, 12, v_testDriver_1276_);
lean_ctor_set(v_reuseFailAlloc_1300_, 13, v_testDriverArgs_1277_);
lean_ctor_set(v_reuseFailAlloc_1300_, 14, v_lintDriver_1278_);
lean_ctor_set(v_reuseFailAlloc_1300_, 15, v_lintDriverArgs_1279_);
lean_ctor_set(v_reuseFailAlloc_1300_, 16, v_version_1280_);
lean_ctor_set(v_reuseFailAlloc_1300_, 17, v_versionTags_1281_);
lean_ctor_set(v_reuseFailAlloc_1300_, 18, v_description_1282_);
lean_ctor_set(v_reuseFailAlloc_1300_, 19, v_keywords_1283_);
lean_ctor_set(v_reuseFailAlloc_1300_, 20, v_homepage_1284_);
lean_ctor_set(v_reuseFailAlloc_1300_, 21, v_license_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 22, v_licenseFiles_1286_);
lean_ctor_set(v_reuseFailAlloc_1300_, 23, v_readmeFile_1287_);
lean_ctor_set(v_reuseFailAlloc_1300_, 24, v_enableArtifactCache_x3f_1289_);
lean_ctor_set(v_reuseFailAlloc_1300_, 25, v_restoreAllArtifacts_x3f_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26, v_bootstrap_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26 + 1, v_precompileModules_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26 + 3, v_reservoir_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26 + 5, v_allowImportAll_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1300_, sizeof(void*)*26 + 6, v_fixedToolchain_1293_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3(lean_object* v_x_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed(lean_object* v_x_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lake_PackageConfig_releaseRepo___proj___lam__3(v_x_1304_);
lean_dec_ref(v_x_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1315_, lean_object* v_n_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__4));
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1318_, lean_object* v_n_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1318_, v_n_1319_);
lean_dec(v_n_1319_);
lean_dec(v_p_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1321_, lean_object* v_n_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1321_, v_n_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1324_, lean_object* v_n_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1324_, v_n_1325_);
lean_dec(v_n_1325_);
lean_dec(v_p_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1327_, lean_object* v_n_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1327_, v_n_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1330_, lean_object* v_n_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1330_, v_n_1331_);
lean_dec(v_n_1331_);
lean_dec(v_p_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* v_cfg_1333_){
_start:
{
lean_object* v_buildArchive_1334_; 
v_buildArchive_1334_ = lean_ctor_get(v_cfg_1333_, 11);
lean_inc(v_buildArchive_1334_);
return v_buildArchive_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* v_cfg_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lake_PackageConfig_buildArchive___proj___lam__0(v_cfg_1335_);
lean_dec_ref(v_cfg_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* v_val_1337_, lean_object* v_cfg_1338_){
_start:
{
lean_object* v_toWorkspaceConfig_1339_; lean_object* v_toLeanConfig_1340_; uint8_t v_bootstrap_1341_; lean_object* v_extraDepTargets_1342_; uint8_t v_precompileModules_1343_; lean_object* v_moreGlobalServerArgs_1344_; lean_object* v_srcDir_1345_; lean_object* v_buildDir_1346_; lean_object* v_leanLibDir_1347_; lean_object* v_nativeLibDir_1348_; lean_object* v_binDir_1349_; lean_object* v_irDir_1350_; lean_object* v_releaseRepo_1351_; uint8_t v_preferReleaseBuild_1352_; lean_object* v_testDriver_1353_; lean_object* v_testDriverArgs_1354_; lean_object* v_lintDriver_1355_; lean_object* v_lintDriverArgs_1356_; lean_object* v_version_1357_; lean_object* v_versionTags_1358_; lean_object* v_description_1359_; lean_object* v_keywords_1360_; lean_object* v_homepage_1361_; lean_object* v_license_1362_; lean_object* v_licenseFiles_1363_; lean_object* v_readmeFile_1364_; uint8_t v_reservoir_1365_; lean_object* v_enableArtifactCache_x3f_1366_; lean_object* v_restoreAllArtifacts_x3f_1367_; uint8_t v_libPrefixOnWindows_1368_; uint8_t v_allowImportAll_1369_; uint8_t v_fixedToolchain_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_toWorkspaceConfig_1339_ = lean_ctor_get(v_cfg_1338_, 0);
v_toLeanConfig_1340_ = lean_ctor_get(v_cfg_1338_, 1);
v_bootstrap_1341_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26);
v_extraDepTargets_1342_ = lean_ctor_get(v_cfg_1338_, 2);
v_precompileModules_1343_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1344_ = lean_ctor_get(v_cfg_1338_, 3);
v_srcDir_1345_ = lean_ctor_get(v_cfg_1338_, 4);
v_buildDir_1346_ = lean_ctor_get(v_cfg_1338_, 5);
v_leanLibDir_1347_ = lean_ctor_get(v_cfg_1338_, 6);
v_nativeLibDir_1348_ = lean_ctor_get(v_cfg_1338_, 7);
v_binDir_1349_ = lean_ctor_get(v_cfg_1338_, 8);
v_irDir_1350_ = lean_ctor_get(v_cfg_1338_, 9);
v_releaseRepo_1351_ = lean_ctor_get(v_cfg_1338_, 10);
v_preferReleaseBuild_1352_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26 + 2);
v_testDriver_1353_ = lean_ctor_get(v_cfg_1338_, 12);
v_testDriverArgs_1354_ = lean_ctor_get(v_cfg_1338_, 13);
v_lintDriver_1355_ = lean_ctor_get(v_cfg_1338_, 14);
v_lintDriverArgs_1356_ = lean_ctor_get(v_cfg_1338_, 15);
v_version_1357_ = lean_ctor_get(v_cfg_1338_, 16);
v_versionTags_1358_ = lean_ctor_get(v_cfg_1338_, 17);
v_description_1359_ = lean_ctor_get(v_cfg_1338_, 18);
v_keywords_1360_ = lean_ctor_get(v_cfg_1338_, 19);
v_homepage_1361_ = lean_ctor_get(v_cfg_1338_, 20);
v_license_1362_ = lean_ctor_get(v_cfg_1338_, 21);
v_licenseFiles_1363_ = lean_ctor_get(v_cfg_1338_, 22);
v_readmeFile_1364_ = lean_ctor_get(v_cfg_1338_, 23);
v_reservoir_1365_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1366_ = lean_ctor_get(v_cfg_1338_, 24);
v_restoreAllArtifacts_x3f_1367_ = lean_ctor_get(v_cfg_1338_, 25);
v_libPrefixOnWindows_1368_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26 + 4);
v_allowImportAll_1369_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26 + 5);
v_fixedToolchain_1370_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*26 + 6);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_cfg_1338_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v_cfg_1338_, 11);
lean_dec(v_unused_1378_);
v___x_1372_ = v_cfg_1338_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1367_);
lean_inc(v_enableArtifactCache_x3f_1366_);
lean_inc(v_readmeFile_1364_);
lean_inc(v_licenseFiles_1363_);
lean_inc(v_license_1362_);
lean_inc(v_homepage_1361_);
lean_inc(v_keywords_1360_);
lean_inc(v_description_1359_);
lean_inc(v_versionTags_1358_);
lean_inc(v_version_1357_);
lean_inc(v_lintDriverArgs_1356_);
lean_inc(v_lintDriver_1355_);
lean_inc(v_testDriverArgs_1354_);
lean_inc(v_testDriver_1353_);
lean_inc(v_releaseRepo_1351_);
lean_inc(v_irDir_1350_);
lean_inc(v_binDir_1349_);
lean_inc(v_nativeLibDir_1348_);
lean_inc(v_leanLibDir_1347_);
lean_inc(v_buildDir_1346_);
lean_inc(v_srcDir_1345_);
lean_inc(v_moreGlobalServerArgs_1344_);
lean_inc(v_extraDepTargets_1342_);
lean_inc(v_toLeanConfig_1340_);
lean_inc(v_toWorkspaceConfig_1339_);
lean_dec(v_cfg_1338_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 11, v_val_1337_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_toWorkspaceConfig_1339_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_toLeanConfig_1340_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_extraDepTargets_1342_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_moreGlobalServerArgs_1344_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_srcDir_1345_);
lean_ctor_set(v_reuseFailAlloc_1376_, 5, v_buildDir_1346_);
lean_ctor_set(v_reuseFailAlloc_1376_, 6, v_leanLibDir_1347_);
lean_ctor_set(v_reuseFailAlloc_1376_, 7, v_nativeLibDir_1348_);
lean_ctor_set(v_reuseFailAlloc_1376_, 8, v_binDir_1349_);
lean_ctor_set(v_reuseFailAlloc_1376_, 9, v_irDir_1350_);
lean_ctor_set(v_reuseFailAlloc_1376_, 10, v_releaseRepo_1351_);
lean_ctor_set(v_reuseFailAlloc_1376_, 11, v_val_1337_);
lean_ctor_set(v_reuseFailAlloc_1376_, 12, v_testDriver_1353_);
lean_ctor_set(v_reuseFailAlloc_1376_, 13, v_testDriverArgs_1354_);
lean_ctor_set(v_reuseFailAlloc_1376_, 14, v_lintDriver_1355_);
lean_ctor_set(v_reuseFailAlloc_1376_, 15, v_lintDriverArgs_1356_);
lean_ctor_set(v_reuseFailAlloc_1376_, 16, v_version_1357_);
lean_ctor_set(v_reuseFailAlloc_1376_, 17, v_versionTags_1358_);
lean_ctor_set(v_reuseFailAlloc_1376_, 18, v_description_1359_);
lean_ctor_set(v_reuseFailAlloc_1376_, 19, v_keywords_1360_);
lean_ctor_set(v_reuseFailAlloc_1376_, 20, v_homepage_1361_);
lean_ctor_set(v_reuseFailAlloc_1376_, 21, v_license_1362_);
lean_ctor_set(v_reuseFailAlloc_1376_, 22, v_licenseFiles_1363_);
lean_ctor_set(v_reuseFailAlloc_1376_, 23, v_readmeFile_1364_);
lean_ctor_set(v_reuseFailAlloc_1376_, 24, v_enableArtifactCache_x3f_1366_);
lean_ctor_set(v_reuseFailAlloc_1376_, 25, v_restoreAllArtifacts_x3f_1367_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26, v_bootstrap_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26 + 1, v_precompileModules_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26 + 3, v_reservoir_1365_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26 + 5, v_allowImportAll_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*26 + 6, v_fixedToolchain_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* v_f_1379_, lean_object* v_cfg_1380_){
_start:
{
lean_object* v_toWorkspaceConfig_1381_; lean_object* v_toLeanConfig_1382_; uint8_t v_bootstrap_1383_; lean_object* v_extraDepTargets_1384_; uint8_t v_precompileModules_1385_; lean_object* v_moreGlobalServerArgs_1386_; lean_object* v_srcDir_1387_; lean_object* v_buildDir_1388_; lean_object* v_leanLibDir_1389_; lean_object* v_nativeLibDir_1390_; lean_object* v_binDir_1391_; lean_object* v_irDir_1392_; lean_object* v_releaseRepo_1393_; lean_object* v_buildArchive_1394_; uint8_t v_preferReleaseBuild_1395_; lean_object* v_testDriver_1396_; lean_object* v_testDriverArgs_1397_; lean_object* v_lintDriver_1398_; lean_object* v_lintDriverArgs_1399_; lean_object* v_version_1400_; lean_object* v_versionTags_1401_; lean_object* v_description_1402_; lean_object* v_keywords_1403_; lean_object* v_homepage_1404_; lean_object* v_license_1405_; lean_object* v_licenseFiles_1406_; lean_object* v_readmeFile_1407_; uint8_t v_reservoir_1408_; lean_object* v_enableArtifactCache_x3f_1409_; lean_object* v_restoreAllArtifacts_x3f_1410_; uint8_t v_libPrefixOnWindows_1411_; uint8_t v_allowImportAll_1412_; uint8_t v_fixedToolchain_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_toWorkspaceConfig_1381_ = lean_ctor_get(v_cfg_1380_, 0);
v_toLeanConfig_1382_ = lean_ctor_get(v_cfg_1380_, 1);
v_bootstrap_1383_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26);
v_extraDepTargets_1384_ = lean_ctor_get(v_cfg_1380_, 2);
v_precompileModules_1385_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1386_ = lean_ctor_get(v_cfg_1380_, 3);
v_srcDir_1387_ = lean_ctor_get(v_cfg_1380_, 4);
v_buildDir_1388_ = lean_ctor_get(v_cfg_1380_, 5);
v_leanLibDir_1389_ = lean_ctor_get(v_cfg_1380_, 6);
v_nativeLibDir_1390_ = lean_ctor_get(v_cfg_1380_, 7);
v_binDir_1391_ = lean_ctor_get(v_cfg_1380_, 8);
v_irDir_1392_ = lean_ctor_get(v_cfg_1380_, 9);
v_releaseRepo_1393_ = lean_ctor_get(v_cfg_1380_, 10);
v_buildArchive_1394_ = lean_ctor_get(v_cfg_1380_, 11);
v_preferReleaseBuild_1395_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26 + 2);
v_testDriver_1396_ = lean_ctor_get(v_cfg_1380_, 12);
v_testDriverArgs_1397_ = lean_ctor_get(v_cfg_1380_, 13);
v_lintDriver_1398_ = lean_ctor_get(v_cfg_1380_, 14);
v_lintDriverArgs_1399_ = lean_ctor_get(v_cfg_1380_, 15);
v_version_1400_ = lean_ctor_get(v_cfg_1380_, 16);
v_versionTags_1401_ = lean_ctor_get(v_cfg_1380_, 17);
v_description_1402_ = lean_ctor_get(v_cfg_1380_, 18);
v_keywords_1403_ = lean_ctor_get(v_cfg_1380_, 19);
v_homepage_1404_ = lean_ctor_get(v_cfg_1380_, 20);
v_license_1405_ = lean_ctor_get(v_cfg_1380_, 21);
v_licenseFiles_1406_ = lean_ctor_get(v_cfg_1380_, 22);
v_readmeFile_1407_ = lean_ctor_get(v_cfg_1380_, 23);
v_reservoir_1408_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1409_ = lean_ctor_get(v_cfg_1380_, 24);
v_restoreAllArtifacts_x3f_1410_ = lean_ctor_get(v_cfg_1380_, 25);
v_libPrefixOnWindows_1411_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26 + 4);
v_allowImportAll_1412_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26 + 5);
v_fixedToolchain_1413_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*26 + 6);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_cfg_1380_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v_cfg_1380_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1410_);
lean_inc(v_enableArtifactCache_x3f_1409_);
lean_inc(v_readmeFile_1407_);
lean_inc(v_licenseFiles_1406_);
lean_inc(v_license_1405_);
lean_inc(v_homepage_1404_);
lean_inc(v_keywords_1403_);
lean_inc(v_description_1402_);
lean_inc(v_versionTags_1401_);
lean_inc(v_version_1400_);
lean_inc(v_lintDriverArgs_1399_);
lean_inc(v_lintDriver_1398_);
lean_inc(v_testDriverArgs_1397_);
lean_inc(v_testDriver_1396_);
lean_inc(v_buildArchive_1394_);
lean_inc(v_releaseRepo_1393_);
lean_inc(v_irDir_1392_);
lean_inc(v_binDir_1391_);
lean_inc(v_nativeLibDir_1390_);
lean_inc(v_leanLibDir_1389_);
lean_inc(v_buildDir_1388_);
lean_inc(v_srcDir_1387_);
lean_inc(v_moreGlobalServerArgs_1386_);
lean_inc(v_extraDepTargets_1384_);
lean_inc(v_toLeanConfig_1382_);
lean_inc(v_toWorkspaceConfig_1381_);
lean_dec(v_cfg_1380_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_apply_1(v_f_1379_, v_buildArchive_1394_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 11, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_toWorkspaceConfig_1381_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_toLeanConfig_1382_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_extraDepTargets_1384_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_moreGlobalServerArgs_1386_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_srcDir_1387_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_buildDir_1388_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_leanLibDir_1389_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v_nativeLibDir_1390_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_binDir_1391_);
lean_ctor_set(v_reuseFailAlloc_1420_, 9, v_irDir_1392_);
lean_ctor_set(v_reuseFailAlloc_1420_, 10, v_releaseRepo_1393_);
lean_ctor_set(v_reuseFailAlloc_1420_, 11, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1420_, 12, v_testDriver_1396_);
lean_ctor_set(v_reuseFailAlloc_1420_, 13, v_testDriverArgs_1397_);
lean_ctor_set(v_reuseFailAlloc_1420_, 14, v_lintDriver_1398_);
lean_ctor_set(v_reuseFailAlloc_1420_, 15, v_lintDriverArgs_1399_);
lean_ctor_set(v_reuseFailAlloc_1420_, 16, v_version_1400_);
lean_ctor_set(v_reuseFailAlloc_1420_, 17, v_versionTags_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 18, v_description_1402_);
lean_ctor_set(v_reuseFailAlloc_1420_, 19, v_keywords_1403_);
lean_ctor_set(v_reuseFailAlloc_1420_, 20, v_homepage_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 21, v_license_1405_);
lean_ctor_set(v_reuseFailAlloc_1420_, 22, v_licenseFiles_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 23, v_readmeFile_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 24, v_enableArtifactCache_x3f_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 25, v_restoreAllArtifacts_x3f_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26, v_bootstrap_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26 + 1, v_precompileModules_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26 + 3, v_reservoir_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26 + 5, v_allowImportAll_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*26 + 6, v_fixedToolchain_1413_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1430_, lean_object* v_n_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1433_, lean_object* v_n_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1433_, v_n_1434_);
lean_dec(v_n_1434_);
lean_dec(v_p_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1436_, lean_object* v_n_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1436_, v_n_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1439_, lean_object* v_n_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1439_, v_n_1440_);
lean_dec(v_n_1440_);
lean_dec(v_p_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1442_, lean_object* v_n_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1442_, v_n_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1445_, lean_object* v_n_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1445_, v_n_1446_);
lean_dec(v_n_1446_);
lean_dec(v_p_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* v_cfg_1448_){
_start:
{
uint8_t v_preferReleaseBuild_1449_; 
v_preferReleaseBuild_1449_ = lean_ctor_get_uint8(v_cfg_1448_, sizeof(void*)*26 + 2);
return v_preferReleaseBuild_1449_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* v_cfg_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(v_cfg_1450_);
lean_dec_ref(v_cfg_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t v_val_1453_, lean_object* v_cfg_1454_){
_start:
{
lean_object* v_toWorkspaceConfig_1455_; lean_object* v_toLeanConfig_1456_; uint8_t v_bootstrap_1457_; lean_object* v_extraDepTargets_1458_; uint8_t v_precompileModules_1459_; lean_object* v_moreGlobalServerArgs_1460_; lean_object* v_srcDir_1461_; lean_object* v_buildDir_1462_; lean_object* v_leanLibDir_1463_; lean_object* v_nativeLibDir_1464_; lean_object* v_binDir_1465_; lean_object* v_irDir_1466_; lean_object* v_releaseRepo_1467_; lean_object* v_buildArchive_1468_; lean_object* v_testDriver_1469_; lean_object* v_testDriverArgs_1470_; lean_object* v_lintDriver_1471_; lean_object* v_lintDriverArgs_1472_; lean_object* v_version_1473_; lean_object* v_versionTags_1474_; lean_object* v_description_1475_; lean_object* v_keywords_1476_; lean_object* v_homepage_1477_; lean_object* v_license_1478_; lean_object* v_licenseFiles_1479_; lean_object* v_readmeFile_1480_; uint8_t v_reservoir_1481_; lean_object* v_enableArtifactCache_x3f_1482_; lean_object* v_restoreAllArtifacts_x3f_1483_; uint8_t v_libPrefixOnWindows_1484_; uint8_t v_allowImportAll_1485_; uint8_t v_fixedToolchain_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_toWorkspaceConfig_1455_ = lean_ctor_get(v_cfg_1454_, 0);
v_toLeanConfig_1456_ = lean_ctor_get(v_cfg_1454_, 1);
v_bootstrap_1457_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*26);
v_extraDepTargets_1458_ = lean_ctor_get(v_cfg_1454_, 2);
v_precompileModules_1459_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1460_ = lean_ctor_get(v_cfg_1454_, 3);
v_srcDir_1461_ = lean_ctor_get(v_cfg_1454_, 4);
v_buildDir_1462_ = lean_ctor_get(v_cfg_1454_, 5);
v_leanLibDir_1463_ = lean_ctor_get(v_cfg_1454_, 6);
v_nativeLibDir_1464_ = lean_ctor_get(v_cfg_1454_, 7);
v_binDir_1465_ = lean_ctor_get(v_cfg_1454_, 8);
v_irDir_1466_ = lean_ctor_get(v_cfg_1454_, 9);
v_releaseRepo_1467_ = lean_ctor_get(v_cfg_1454_, 10);
v_buildArchive_1468_ = lean_ctor_get(v_cfg_1454_, 11);
v_testDriver_1469_ = lean_ctor_get(v_cfg_1454_, 12);
v_testDriverArgs_1470_ = lean_ctor_get(v_cfg_1454_, 13);
v_lintDriver_1471_ = lean_ctor_get(v_cfg_1454_, 14);
v_lintDriverArgs_1472_ = lean_ctor_get(v_cfg_1454_, 15);
v_version_1473_ = lean_ctor_get(v_cfg_1454_, 16);
v_versionTags_1474_ = lean_ctor_get(v_cfg_1454_, 17);
v_description_1475_ = lean_ctor_get(v_cfg_1454_, 18);
v_keywords_1476_ = lean_ctor_get(v_cfg_1454_, 19);
v_homepage_1477_ = lean_ctor_get(v_cfg_1454_, 20);
v_license_1478_ = lean_ctor_get(v_cfg_1454_, 21);
v_licenseFiles_1479_ = lean_ctor_get(v_cfg_1454_, 22);
v_readmeFile_1480_ = lean_ctor_get(v_cfg_1454_, 23);
v_reservoir_1481_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1482_ = lean_ctor_get(v_cfg_1454_, 24);
v_restoreAllArtifacts_x3f_1483_ = lean_ctor_get(v_cfg_1454_, 25);
v_libPrefixOnWindows_1484_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*26 + 4);
v_allowImportAll_1485_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*26 + 5);
v_fixedToolchain_1486_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*26 + 6);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_cfg_1454_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v_cfg_1454_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1483_);
lean_inc(v_enableArtifactCache_x3f_1482_);
lean_inc(v_readmeFile_1480_);
lean_inc(v_licenseFiles_1479_);
lean_inc(v_license_1478_);
lean_inc(v_homepage_1477_);
lean_inc(v_keywords_1476_);
lean_inc(v_description_1475_);
lean_inc(v_versionTags_1474_);
lean_inc(v_version_1473_);
lean_inc(v_lintDriverArgs_1472_);
lean_inc(v_lintDriver_1471_);
lean_inc(v_testDriverArgs_1470_);
lean_inc(v_testDriver_1469_);
lean_inc(v_buildArchive_1468_);
lean_inc(v_releaseRepo_1467_);
lean_inc(v_irDir_1466_);
lean_inc(v_binDir_1465_);
lean_inc(v_nativeLibDir_1464_);
lean_inc(v_leanLibDir_1463_);
lean_inc(v_buildDir_1462_);
lean_inc(v_srcDir_1461_);
lean_inc(v_moreGlobalServerArgs_1460_);
lean_inc(v_extraDepTargets_1458_);
lean_inc(v_toLeanConfig_1456_);
lean_inc(v_toWorkspaceConfig_1455_);
lean_dec(v_cfg_1454_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_toWorkspaceConfig_1455_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_toLeanConfig_1456_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_extraDepTargets_1458_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_moreGlobalServerArgs_1460_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_srcDir_1461_);
lean_ctor_set(v_reuseFailAlloc_1492_, 5, v_buildDir_1462_);
lean_ctor_set(v_reuseFailAlloc_1492_, 6, v_leanLibDir_1463_);
lean_ctor_set(v_reuseFailAlloc_1492_, 7, v_nativeLibDir_1464_);
lean_ctor_set(v_reuseFailAlloc_1492_, 8, v_binDir_1465_);
lean_ctor_set(v_reuseFailAlloc_1492_, 9, v_irDir_1466_);
lean_ctor_set(v_reuseFailAlloc_1492_, 10, v_releaseRepo_1467_);
lean_ctor_set(v_reuseFailAlloc_1492_, 11, v_buildArchive_1468_);
lean_ctor_set(v_reuseFailAlloc_1492_, 12, v_testDriver_1469_);
lean_ctor_set(v_reuseFailAlloc_1492_, 13, v_testDriverArgs_1470_);
lean_ctor_set(v_reuseFailAlloc_1492_, 14, v_lintDriver_1471_);
lean_ctor_set(v_reuseFailAlloc_1492_, 15, v_lintDriverArgs_1472_);
lean_ctor_set(v_reuseFailAlloc_1492_, 16, v_version_1473_);
lean_ctor_set(v_reuseFailAlloc_1492_, 17, v_versionTags_1474_);
lean_ctor_set(v_reuseFailAlloc_1492_, 18, v_description_1475_);
lean_ctor_set(v_reuseFailAlloc_1492_, 19, v_keywords_1476_);
lean_ctor_set(v_reuseFailAlloc_1492_, 20, v_homepage_1477_);
lean_ctor_set(v_reuseFailAlloc_1492_, 21, v_license_1478_);
lean_ctor_set(v_reuseFailAlloc_1492_, 22, v_licenseFiles_1479_);
lean_ctor_set(v_reuseFailAlloc_1492_, 23, v_readmeFile_1480_);
lean_ctor_set(v_reuseFailAlloc_1492_, 24, v_enableArtifactCache_x3f_1482_);
lean_ctor_set(v_reuseFailAlloc_1492_, 25, v_restoreAllArtifacts_x3f_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*26, v_bootstrap_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*26 + 1, v_precompileModules_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*26 + 3, v_reservoir_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*26 + 5, v_allowImportAll_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*26 + 6, v_fixedToolchain_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*26 + 2, v_val_1453_);
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* v_val_1494_, lean_object* v_cfg_1495_){
_start:
{
uint8_t v_val_134__boxed_1496_; lean_object* v_res_1497_; 
v_val_134__boxed_1496_ = lean_unbox(v_val_1494_);
v_res_1497_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(v_val_134__boxed_1496_, v_cfg_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* v_f_1498_, lean_object* v_cfg_1499_){
_start:
{
lean_object* v_toWorkspaceConfig_1500_; lean_object* v_toLeanConfig_1501_; uint8_t v_bootstrap_1502_; lean_object* v_extraDepTargets_1503_; uint8_t v_precompileModules_1504_; lean_object* v_moreGlobalServerArgs_1505_; lean_object* v_srcDir_1506_; lean_object* v_buildDir_1507_; lean_object* v_leanLibDir_1508_; lean_object* v_nativeLibDir_1509_; lean_object* v_binDir_1510_; lean_object* v_irDir_1511_; lean_object* v_releaseRepo_1512_; lean_object* v_buildArchive_1513_; uint8_t v_preferReleaseBuild_1514_; lean_object* v_testDriver_1515_; lean_object* v_testDriverArgs_1516_; lean_object* v_lintDriver_1517_; lean_object* v_lintDriverArgs_1518_; lean_object* v_version_1519_; lean_object* v_versionTags_1520_; lean_object* v_description_1521_; lean_object* v_keywords_1522_; lean_object* v_homepage_1523_; lean_object* v_license_1524_; lean_object* v_licenseFiles_1525_; lean_object* v_readmeFile_1526_; uint8_t v_reservoir_1527_; lean_object* v_enableArtifactCache_x3f_1528_; lean_object* v_restoreAllArtifacts_x3f_1529_; uint8_t v_libPrefixOnWindows_1530_; uint8_t v_allowImportAll_1531_; uint8_t v_fixedToolchain_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1542_; 
v_toWorkspaceConfig_1500_ = lean_ctor_get(v_cfg_1499_, 0);
v_toLeanConfig_1501_ = lean_ctor_get(v_cfg_1499_, 1);
v_bootstrap_1502_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26);
v_extraDepTargets_1503_ = lean_ctor_get(v_cfg_1499_, 2);
v_precompileModules_1504_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1505_ = lean_ctor_get(v_cfg_1499_, 3);
v_srcDir_1506_ = lean_ctor_get(v_cfg_1499_, 4);
v_buildDir_1507_ = lean_ctor_get(v_cfg_1499_, 5);
v_leanLibDir_1508_ = lean_ctor_get(v_cfg_1499_, 6);
v_nativeLibDir_1509_ = lean_ctor_get(v_cfg_1499_, 7);
v_binDir_1510_ = lean_ctor_get(v_cfg_1499_, 8);
v_irDir_1511_ = lean_ctor_get(v_cfg_1499_, 9);
v_releaseRepo_1512_ = lean_ctor_get(v_cfg_1499_, 10);
v_buildArchive_1513_ = lean_ctor_get(v_cfg_1499_, 11);
v_preferReleaseBuild_1514_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26 + 2);
v_testDriver_1515_ = lean_ctor_get(v_cfg_1499_, 12);
v_testDriverArgs_1516_ = lean_ctor_get(v_cfg_1499_, 13);
v_lintDriver_1517_ = lean_ctor_get(v_cfg_1499_, 14);
v_lintDriverArgs_1518_ = lean_ctor_get(v_cfg_1499_, 15);
v_version_1519_ = lean_ctor_get(v_cfg_1499_, 16);
v_versionTags_1520_ = lean_ctor_get(v_cfg_1499_, 17);
v_description_1521_ = lean_ctor_get(v_cfg_1499_, 18);
v_keywords_1522_ = lean_ctor_get(v_cfg_1499_, 19);
v_homepage_1523_ = lean_ctor_get(v_cfg_1499_, 20);
v_license_1524_ = lean_ctor_get(v_cfg_1499_, 21);
v_licenseFiles_1525_ = lean_ctor_get(v_cfg_1499_, 22);
v_readmeFile_1526_ = lean_ctor_get(v_cfg_1499_, 23);
v_reservoir_1527_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1528_ = lean_ctor_get(v_cfg_1499_, 24);
v_restoreAllArtifacts_x3f_1529_ = lean_ctor_get(v_cfg_1499_, 25);
v_libPrefixOnWindows_1530_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26 + 4);
v_allowImportAll_1531_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26 + 5);
v_fixedToolchain_1532_ = lean_ctor_get_uint8(v_cfg_1499_, sizeof(void*)*26 + 6);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_cfg_1499_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1534_ = v_cfg_1499_;
v_isShared_1535_ = v_isSharedCheck_1542_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1529_);
lean_inc(v_enableArtifactCache_x3f_1528_);
lean_inc(v_readmeFile_1526_);
lean_inc(v_licenseFiles_1525_);
lean_inc(v_license_1524_);
lean_inc(v_homepage_1523_);
lean_inc(v_keywords_1522_);
lean_inc(v_description_1521_);
lean_inc(v_versionTags_1520_);
lean_inc(v_version_1519_);
lean_inc(v_lintDriverArgs_1518_);
lean_inc(v_lintDriver_1517_);
lean_inc(v_testDriverArgs_1516_);
lean_inc(v_testDriver_1515_);
lean_inc(v_buildArchive_1513_);
lean_inc(v_releaseRepo_1512_);
lean_inc(v_irDir_1511_);
lean_inc(v_binDir_1510_);
lean_inc(v_nativeLibDir_1509_);
lean_inc(v_leanLibDir_1508_);
lean_inc(v_buildDir_1507_);
lean_inc(v_srcDir_1506_);
lean_inc(v_moreGlobalServerArgs_1505_);
lean_inc(v_extraDepTargets_1503_);
lean_inc(v_toLeanConfig_1501_);
lean_inc(v_toWorkspaceConfig_1500_);
lean_dec(v_cfg_1499_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1542_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1536_ = lean_box(v_preferReleaseBuild_1514_);
v___x_1537_ = lean_apply_1(v_f_1498_, v___x_1536_);
if (v_isShared_1535_ == 0)
{
v___x_1539_ = v___x_1534_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_toWorkspaceConfig_1500_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_toLeanConfig_1501_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_extraDepTargets_1503_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_moreGlobalServerArgs_1505_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_srcDir_1506_);
lean_ctor_set(v_reuseFailAlloc_1541_, 5, v_buildDir_1507_);
lean_ctor_set(v_reuseFailAlloc_1541_, 6, v_leanLibDir_1508_);
lean_ctor_set(v_reuseFailAlloc_1541_, 7, v_nativeLibDir_1509_);
lean_ctor_set(v_reuseFailAlloc_1541_, 8, v_binDir_1510_);
lean_ctor_set(v_reuseFailAlloc_1541_, 9, v_irDir_1511_);
lean_ctor_set(v_reuseFailAlloc_1541_, 10, v_releaseRepo_1512_);
lean_ctor_set(v_reuseFailAlloc_1541_, 11, v_buildArchive_1513_);
lean_ctor_set(v_reuseFailAlloc_1541_, 12, v_testDriver_1515_);
lean_ctor_set(v_reuseFailAlloc_1541_, 13, v_testDriverArgs_1516_);
lean_ctor_set(v_reuseFailAlloc_1541_, 14, v_lintDriver_1517_);
lean_ctor_set(v_reuseFailAlloc_1541_, 15, v_lintDriverArgs_1518_);
lean_ctor_set(v_reuseFailAlloc_1541_, 16, v_version_1519_);
lean_ctor_set(v_reuseFailAlloc_1541_, 17, v_versionTags_1520_);
lean_ctor_set(v_reuseFailAlloc_1541_, 18, v_description_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 19, v_keywords_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 20, v_homepage_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 21, v_license_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 22, v_licenseFiles_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 23, v_readmeFile_1526_);
lean_ctor_set(v_reuseFailAlloc_1541_, 24, v_enableArtifactCache_x3f_1528_);
lean_ctor_set(v_reuseFailAlloc_1541_, 25, v_restoreAllArtifacts_x3f_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*26, v_bootstrap_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*26 + 1, v_precompileModules_1504_);
v___x_1539_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_unbox(v___x_1537_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*26 + 2, v___x_1540_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*26 + 3, v_reservoir_1527_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1530_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*26 + 5, v_allowImportAll_1531_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*26 + 6, v_fixedToolchain_1532_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1551_, lean_object* v_n_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1554_, lean_object* v_n_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1554_, v_n_1555_);
lean_dec(v_n_1555_);
lean_dec(v_p_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1557_, lean_object* v_n_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1557_, v_n_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1560_, lean_object* v_n_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1560_, v_n_1561_);
lean_dec(v_n_1561_);
lean_dec(v_p_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* v_cfg_1563_){
_start:
{
lean_object* v_testDriver_1564_; 
v_testDriver_1564_ = lean_ctor_get(v_cfg_1563_, 12);
lean_inc_ref(v_testDriver_1564_);
return v_testDriver_1564_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* v_cfg_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lake_PackageConfig_testDriver___proj___lam__0(v_cfg_1565_);
lean_dec_ref(v_cfg_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* v_val_1567_, lean_object* v_cfg_1568_){
_start:
{
lean_object* v_toWorkspaceConfig_1569_; lean_object* v_toLeanConfig_1570_; uint8_t v_bootstrap_1571_; lean_object* v_extraDepTargets_1572_; uint8_t v_precompileModules_1573_; lean_object* v_moreGlobalServerArgs_1574_; lean_object* v_srcDir_1575_; lean_object* v_buildDir_1576_; lean_object* v_leanLibDir_1577_; lean_object* v_nativeLibDir_1578_; lean_object* v_binDir_1579_; lean_object* v_irDir_1580_; lean_object* v_releaseRepo_1581_; lean_object* v_buildArchive_1582_; uint8_t v_preferReleaseBuild_1583_; lean_object* v_testDriverArgs_1584_; lean_object* v_lintDriver_1585_; lean_object* v_lintDriverArgs_1586_; lean_object* v_version_1587_; lean_object* v_versionTags_1588_; lean_object* v_description_1589_; lean_object* v_keywords_1590_; lean_object* v_homepage_1591_; lean_object* v_license_1592_; lean_object* v_licenseFiles_1593_; lean_object* v_readmeFile_1594_; uint8_t v_reservoir_1595_; lean_object* v_enableArtifactCache_x3f_1596_; lean_object* v_restoreAllArtifacts_x3f_1597_; uint8_t v_libPrefixOnWindows_1598_; uint8_t v_allowImportAll_1599_; uint8_t v_fixedToolchain_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_toWorkspaceConfig_1569_ = lean_ctor_get(v_cfg_1568_, 0);
v_toLeanConfig_1570_ = lean_ctor_get(v_cfg_1568_, 1);
v_bootstrap_1571_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26);
v_extraDepTargets_1572_ = lean_ctor_get(v_cfg_1568_, 2);
v_precompileModules_1573_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1574_ = lean_ctor_get(v_cfg_1568_, 3);
v_srcDir_1575_ = lean_ctor_get(v_cfg_1568_, 4);
v_buildDir_1576_ = lean_ctor_get(v_cfg_1568_, 5);
v_leanLibDir_1577_ = lean_ctor_get(v_cfg_1568_, 6);
v_nativeLibDir_1578_ = lean_ctor_get(v_cfg_1568_, 7);
v_binDir_1579_ = lean_ctor_get(v_cfg_1568_, 8);
v_irDir_1580_ = lean_ctor_get(v_cfg_1568_, 9);
v_releaseRepo_1581_ = lean_ctor_get(v_cfg_1568_, 10);
v_buildArchive_1582_ = lean_ctor_get(v_cfg_1568_, 11);
v_preferReleaseBuild_1583_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26 + 2);
v_testDriverArgs_1584_ = lean_ctor_get(v_cfg_1568_, 13);
v_lintDriver_1585_ = lean_ctor_get(v_cfg_1568_, 14);
v_lintDriverArgs_1586_ = lean_ctor_get(v_cfg_1568_, 15);
v_version_1587_ = lean_ctor_get(v_cfg_1568_, 16);
v_versionTags_1588_ = lean_ctor_get(v_cfg_1568_, 17);
v_description_1589_ = lean_ctor_get(v_cfg_1568_, 18);
v_keywords_1590_ = lean_ctor_get(v_cfg_1568_, 19);
v_homepage_1591_ = lean_ctor_get(v_cfg_1568_, 20);
v_license_1592_ = lean_ctor_get(v_cfg_1568_, 21);
v_licenseFiles_1593_ = lean_ctor_get(v_cfg_1568_, 22);
v_readmeFile_1594_ = lean_ctor_get(v_cfg_1568_, 23);
v_reservoir_1595_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1596_ = lean_ctor_get(v_cfg_1568_, 24);
v_restoreAllArtifacts_x3f_1597_ = lean_ctor_get(v_cfg_1568_, 25);
v_libPrefixOnWindows_1598_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26 + 4);
v_allowImportAll_1599_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26 + 5);
v_fixedToolchain_1600_ = lean_ctor_get_uint8(v_cfg_1568_, sizeof(void*)*26 + 6);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_cfg_1568_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_cfg_1568_, 12);
lean_dec(v_unused_1608_);
v___x_1602_ = v_cfg_1568_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1597_);
lean_inc(v_enableArtifactCache_x3f_1596_);
lean_inc(v_readmeFile_1594_);
lean_inc(v_licenseFiles_1593_);
lean_inc(v_license_1592_);
lean_inc(v_homepage_1591_);
lean_inc(v_keywords_1590_);
lean_inc(v_description_1589_);
lean_inc(v_versionTags_1588_);
lean_inc(v_version_1587_);
lean_inc(v_lintDriverArgs_1586_);
lean_inc(v_lintDriver_1585_);
lean_inc(v_testDriverArgs_1584_);
lean_inc(v_buildArchive_1582_);
lean_inc(v_releaseRepo_1581_);
lean_inc(v_irDir_1580_);
lean_inc(v_binDir_1579_);
lean_inc(v_nativeLibDir_1578_);
lean_inc(v_leanLibDir_1577_);
lean_inc(v_buildDir_1576_);
lean_inc(v_srcDir_1575_);
lean_inc(v_moreGlobalServerArgs_1574_);
lean_inc(v_extraDepTargets_1572_);
lean_inc(v_toLeanConfig_1570_);
lean_inc(v_toWorkspaceConfig_1569_);
lean_dec(v_cfg_1568_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 12, v_val_1567_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_toWorkspaceConfig_1569_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_toLeanConfig_1570_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_extraDepTargets_1572_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_moreGlobalServerArgs_1574_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_srcDir_1575_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v_buildDir_1576_);
lean_ctor_set(v_reuseFailAlloc_1606_, 6, v_leanLibDir_1577_);
lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_nativeLibDir_1578_);
lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_binDir_1579_);
lean_ctor_set(v_reuseFailAlloc_1606_, 9, v_irDir_1580_);
lean_ctor_set(v_reuseFailAlloc_1606_, 10, v_releaseRepo_1581_);
lean_ctor_set(v_reuseFailAlloc_1606_, 11, v_buildArchive_1582_);
lean_ctor_set(v_reuseFailAlloc_1606_, 12, v_val_1567_);
lean_ctor_set(v_reuseFailAlloc_1606_, 13, v_testDriverArgs_1584_);
lean_ctor_set(v_reuseFailAlloc_1606_, 14, v_lintDriver_1585_);
lean_ctor_set(v_reuseFailAlloc_1606_, 15, v_lintDriverArgs_1586_);
lean_ctor_set(v_reuseFailAlloc_1606_, 16, v_version_1587_);
lean_ctor_set(v_reuseFailAlloc_1606_, 17, v_versionTags_1588_);
lean_ctor_set(v_reuseFailAlloc_1606_, 18, v_description_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 19, v_keywords_1590_);
lean_ctor_set(v_reuseFailAlloc_1606_, 20, v_homepage_1591_);
lean_ctor_set(v_reuseFailAlloc_1606_, 21, v_license_1592_);
lean_ctor_set(v_reuseFailAlloc_1606_, 22, v_licenseFiles_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 23, v_readmeFile_1594_);
lean_ctor_set(v_reuseFailAlloc_1606_, 24, v_enableArtifactCache_x3f_1596_);
lean_ctor_set(v_reuseFailAlloc_1606_, 25, v_restoreAllArtifacts_x3f_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26, v_bootstrap_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26 + 1, v_precompileModules_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26 + 3, v_reservoir_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26 + 5, v_allowImportAll_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*26 + 6, v_fixedToolchain_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* v_f_1609_, lean_object* v_cfg_1610_){
_start:
{
lean_object* v_toWorkspaceConfig_1611_; lean_object* v_toLeanConfig_1612_; uint8_t v_bootstrap_1613_; lean_object* v_extraDepTargets_1614_; uint8_t v_precompileModules_1615_; lean_object* v_moreGlobalServerArgs_1616_; lean_object* v_srcDir_1617_; lean_object* v_buildDir_1618_; lean_object* v_leanLibDir_1619_; lean_object* v_nativeLibDir_1620_; lean_object* v_binDir_1621_; lean_object* v_irDir_1622_; lean_object* v_releaseRepo_1623_; lean_object* v_buildArchive_1624_; uint8_t v_preferReleaseBuild_1625_; lean_object* v_testDriver_1626_; lean_object* v_testDriverArgs_1627_; lean_object* v_lintDriver_1628_; lean_object* v_lintDriverArgs_1629_; lean_object* v_version_1630_; lean_object* v_versionTags_1631_; lean_object* v_description_1632_; lean_object* v_keywords_1633_; lean_object* v_homepage_1634_; lean_object* v_license_1635_; lean_object* v_licenseFiles_1636_; lean_object* v_readmeFile_1637_; uint8_t v_reservoir_1638_; lean_object* v_enableArtifactCache_x3f_1639_; lean_object* v_restoreAllArtifacts_x3f_1640_; uint8_t v_libPrefixOnWindows_1641_; uint8_t v_allowImportAll_1642_; uint8_t v_fixedToolchain_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v_toWorkspaceConfig_1611_ = lean_ctor_get(v_cfg_1610_, 0);
v_toLeanConfig_1612_ = lean_ctor_get(v_cfg_1610_, 1);
v_bootstrap_1613_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26);
v_extraDepTargets_1614_ = lean_ctor_get(v_cfg_1610_, 2);
v_precompileModules_1615_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1616_ = lean_ctor_get(v_cfg_1610_, 3);
v_srcDir_1617_ = lean_ctor_get(v_cfg_1610_, 4);
v_buildDir_1618_ = lean_ctor_get(v_cfg_1610_, 5);
v_leanLibDir_1619_ = lean_ctor_get(v_cfg_1610_, 6);
v_nativeLibDir_1620_ = lean_ctor_get(v_cfg_1610_, 7);
v_binDir_1621_ = lean_ctor_get(v_cfg_1610_, 8);
v_irDir_1622_ = lean_ctor_get(v_cfg_1610_, 9);
v_releaseRepo_1623_ = lean_ctor_get(v_cfg_1610_, 10);
v_buildArchive_1624_ = lean_ctor_get(v_cfg_1610_, 11);
v_preferReleaseBuild_1625_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26 + 2);
v_testDriver_1626_ = lean_ctor_get(v_cfg_1610_, 12);
v_testDriverArgs_1627_ = lean_ctor_get(v_cfg_1610_, 13);
v_lintDriver_1628_ = lean_ctor_get(v_cfg_1610_, 14);
v_lintDriverArgs_1629_ = lean_ctor_get(v_cfg_1610_, 15);
v_version_1630_ = lean_ctor_get(v_cfg_1610_, 16);
v_versionTags_1631_ = lean_ctor_get(v_cfg_1610_, 17);
v_description_1632_ = lean_ctor_get(v_cfg_1610_, 18);
v_keywords_1633_ = lean_ctor_get(v_cfg_1610_, 19);
v_homepage_1634_ = lean_ctor_get(v_cfg_1610_, 20);
v_license_1635_ = lean_ctor_get(v_cfg_1610_, 21);
v_licenseFiles_1636_ = lean_ctor_get(v_cfg_1610_, 22);
v_readmeFile_1637_ = lean_ctor_get(v_cfg_1610_, 23);
v_reservoir_1638_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1639_ = lean_ctor_get(v_cfg_1610_, 24);
v_restoreAllArtifacts_x3f_1640_ = lean_ctor_get(v_cfg_1610_, 25);
v_libPrefixOnWindows_1641_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26 + 4);
v_allowImportAll_1642_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26 + 5);
v_fixedToolchain_1643_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*26 + 6);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_cfg_1610_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v_cfg_1610_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1640_);
lean_inc(v_enableArtifactCache_x3f_1639_);
lean_inc(v_readmeFile_1637_);
lean_inc(v_licenseFiles_1636_);
lean_inc(v_license_1635_);
lean_inc(v_homepage_1634_);
lean_inc(v_keywords_1633_);
lean_inc(v_description_1632_);
lean_inc(v_versionTags_1631_);
lean_inc(v_version_1630_);
lean_inc(v_lintDriverArgs_1629_);
lean_inc(v_lintDriver_1628_);
lean_inc(v_testDriverArgs_1627_);
lean_inc(v_testDriver_1626_);
lean_inc(v_buildArchive_1624_);
lean_inc(v_releaseRepo_1623_);
lean_inc(v_irDir_1622_);
lean_inc(v_binDir_1621_);
lean_inc(v_nativeLibDir_1620_);
lean_inc(v_leanLibDir_1619_);
lean_inc(v_buildDir_1618_);
lean_inc(v_srcDir_1617_);
lean_inc(v_moreGlobalServerArgs_1616_);
lean_inc(v_extraDepTargets_1614_);
lean_inc(v_toLeanConfig_1612_);
lean_inc(v_toWorkspaceConfig_1611_);
lean_dec(v_cfg_1610_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_apply_1(v_f_1609_, v_testDriver_1626_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 12, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_toWorkspaceConfig_1611_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_toLeanConfig_1612_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_extraDepTargets_1614_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_moreGlobalServerArgs_1616_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_srcDir_1617_);
lean_ctor_set(v_reuseFailAlloc_1650_, 5, v_buildDir_1618_);
lean_ctor_set(v_reuseFailAlloc_1650_, 6, v_leanLibDir_1619_);
lean_ctor_set(v_reuseFailAlloc_1650_, 7, v_nativeLibDir_1620_);
lean_ctor_set(v_reuseFailAlloc_1650_, 8, v_binDir_1621_);
lean_ctor_set(v_reuseFailAlloc_1650_, 9, v_irDir_1622_);
lean_ctor_set(v_reuseFailAlloc_1650_, 10, v_releaseRepo_1623_);
lean_ctor_set(v_reuseFailAlloc_1650_, 11, v_buildArchive_1624_);
lean_ctor_set(v_reuseFailAlloc_1650_, 12, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 13, v_testDriverArgs_1627_);
lean_ctor_set(v_reuseFailAlloc_1650_, 14, v_lintDriver_1628_);
lean_ctor_set(v_reuseFailAlloc_1650_, 15, v_lintDriverArgs_1629_);
lean_ctor_set(v_reuseFailAlloc_1650_, 16, v_version_1630_);
lean_ctor_set(v_reuseFailAlloc_1650_, 17, v_versionTags_1631_);
lean_ctor_set(v_reuseFailAlloc_1650_, 18, v_description_1632_);
lean_ctor_set(v_reuseFailAlloc_1650_, 19, v_keywords_1633_);
lean_ctor_set(v_reuseFailAlloc_1650_, 20, v_homepage_1634_);
lean_ctor_set(v_reuseFailAlloc_1650_, 21, v_license_1635_);
lean_ctor_set(v_reuseFailAlloc_1650_, 22, v_licenseFiles_1636_);
lean_ctor_set(v_reuseFailAlloc_1650_, 23, v_readmeFile_1637_);
lean_ctor_set(v_reuseFailAlloc_1650_, 24, v_enableArtifactCache_x3f_1639_);
lean_ctor_set(v_reuseFailAlloc_1650_, 25, v_restoreAllArtifacts_x3f_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26, v_bootstrap_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26 + 1, v_precompileModules_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26 + 3, v_reservoir_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26 + 5, v_allowImportAll_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*26 + 6, v_fixedToolchain_1643_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* v_x_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_PackageConfig_testDriver___proj___lam__3(v_x_1654_);
lean_dec_ref(v_x_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1665_, lean_object* v_n_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1668_, lean_object* v_n_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lake_PackageConfig_testDriver___proj(v_p_1668_, v_n_1669_);
lean_dec(v_n_1669_);
lean_dec(v_p_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1671_, lean_object* v_n_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lake_PackageConfig_testDriver___proj(v_p_1671_, v_n_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1674_, lean_object* v_n_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1674_, v_n_1675_);
lean_dec(v_n_1675_);
lean_dec(v_p_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1677_, lean_object* v_n_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lake_PackageConfig_testDriver___proj(v_p_1677_, v_n_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1680_, lean_object* v_n_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1680_, v_n_1681_);
lean_dec(v_n_1681_);
lean_dec(v_p_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* v_cfg_1683_){
_start:
{
lean_object* v_testDriverArgs_1684_; 
v_testDriverArgs_1684_ = lean_ctor_get(v_cfg_1683_, 13);
lean_inc_ref(v_testDriverArgs_1684_);
return v_testDriverArgs_1684_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(v_cfg_1685_);
lean_dec_ref(v_cfg_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* v_val_1687_, lean_object* v_cfg_1688_){
_start:
{
lean_object* v_toWorkspaceConfig_1689_; lean_object* v_toLeanConfig_1690_; uint8_t v_bootstrap_1691_; lean_object* v_extraDepTargets_1692_; uint8_t v_precompileModules_1693_; lean_object* v_moreGlobalServerArgs_1694_; lean_object* v_srcDir_1695_; lean_object* v_buildDir_1696_; lean_object* v_leanLibDir_1697_; lean_object* v_nativeLibDir_1698_; lean_object* v_binDir_1699_; lean_object* v_irDir_1700_; lean_object* v_releaseRepo_1701_; lean_object* v_buildArchive_1702_; uint8_t v_preferReleaseBuild_1703_; lean_object* v_testDriver_1704_; lean_object* v_lintDriver_1705_; lean_object* v_lintDriverArgs_1706_; lean_object* v_version_1707_; lean_object* v_versionTags_1708_; lean_object* v_description_1709_; lean_object* v_keywords_1710_; lean_object* v_homepage_1711_; lean_object* v_license_1712_; lean_object* v_licenseFiles_1713_; lean_object* v_readmeFile_1714_; uint8_t v_reservoir_1715_; lean_object* v_enableArtifactCache_x3f_1716_; lean_object* v_restoreAllArtifacts_x3f_1717_; uint8_t v_libPrefixOnWindows_1718_; uint8_t v_allowImportAll_1719_; uint8_t v_fixedToolchain_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_toWorkspaceConfig_1689_ = lean_ctor_get(v_cfg_1688_, 0);
v_toLeanConfig_1690_ = lean_ctor_get(v_cfg_1688_, 1);
v_bootstrap_1691_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26);
v_extraDepTargets_1692_ = lean_ctor_get(v_cfg_1688_, 2);
v_precompileModules_1693_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1694_ = lean_ctor_get(v_cfg_1688_, 3);
v_srcDir_1695_ = lean_ctor_get(v_cfg_1688_, 4);
v_buildDir_1696_ = lean_ctor_get(v_cfg_1688_, 5);
v_leanLibDir_1697_ = lean_ctor_get(v_cfg_1688_, 6);
v_nativeLibDir_1698_ = lean_ctor_get(v_cfg_1688_, 7);
v_binDir_1699_ = lean_ctor_get(v_cfg_1688_, 8);
v_irDir_1700_ = lean_ctor_get(v_cfg_1688_, 9);
v_releaseRepo_1701_ = lean_ctor_get(v_cfg_1688_, 10);
v_buildArchive_1702_ = lean_ctor_get(v_cfg_1688_, 11);
v_preferReleaseBuild_1703_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26 + 2);
v_testDriver_1704_ = lean_ctor_get(v_cfg_1688_, 12);
v_lintDriver_1705_ = lean_ctor_get(v_cfg_1688_, 14);
v_lintDriverArgs_1706_ = lean_ctor_get(v_cfg_1688_, 15);
v_version_1707_ = lean_ctor_get(v_cfg_1688_, 16);
v_versionTags_1708_ = lean_ctor_get(v_cfg_1688_, 17);
v_description_1709_ = lean_ctor_get(v_cfg_1688_, 18);
v_keywords_1710_ = lean_ctor_get(v_cfg_1688_, 19);
v_homepage_1711_ = lean_ctor_get(v_cfg_1688_, 20);
v_license_1712_ = lean_ctor_get(v_cfg_1688_, 21);
v_licenseFiles_1713_ = lean_ctor_get(v_cfg_1688_, 22);
v_readmeFile_1714_ = lean_ctor_get(v_cfg_1688_, 23);
v_reservoir_1715_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1716_ = lean_ctor_get(v_cfg_1688_, 24);
v_restoreAllArtifacts_x3f_1717_ = lean_ctor_get(v_cfg_1688_, 25);
v_libPrefixOnWindows_1718_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26 + 4);
v_allowImportAll_1719_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26 + 5);
v_fixedToolchain_1720_ = lean_ctor_get_uint8(v_cfg_1688_, sizeof(void*)*26 + 6);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_cfg_1688_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_cfg_1688_, 13);
lean_dec(v_unused_1728_);
v___x_1722_ = v_cfg_1688_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1717_);
lean_inc(v_enableArtifactCache_x3f_1716_);
lean_inc(v_readmeFile_1714_);
lean_inc(v_licenseFiles_1713_);
lean_inc(v_license_1712_);
lean_inc(v_homepage_1711_);
lean_inc(v_keywords_1710_);
lean_inc(v_description_1709_);
lean_inc(v_versionTags_1708_);
lean_inc(v_version_1707_);
lean_inc(v_lintDriverArgs_1706_);
lean_inc(v_lintDriver_1705_);
lean_inc(v_testDriver_1704_);
lean_inc(v_buildArchive_1702_);
lean_inc(v_releaseRepo_1701_);
lean_inc(v_irDir_1700_);
lean_inc(v_binDir_1699_);
lean_inc(v_nativeLibDir_1698_);
lean_inc(v_leanLibDir_1697_);
lean_inc(v_buildDir_1696_);
lean_inc(v_srcDir_1695_);
lean_inc(v_moreGlobalServerArgs_1694_);
lean_inc(v_extraDepTargets_1692_);
lean_inc(v_toLeanConfig_1690_);
lean_inc(v_toWorkspaceConfig_1689_);
lean_dec(v_cfg_1688_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 13, v_val_1687_);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_toWorkspaceConfig_1689_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_toLeanConfig_1690_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_extraDepTargets_1692_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_moreGlobalServerArgs_1694_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_srcDir_1695_);
lean_ctor_set(v_reuseFailAlloc_1726_, 5, v_buildDir_1696_);
lean_ctor_set(v_reuseFailAlloc_1726_, 6, v_leanLibDir_1697_);
lean_ctor_set(v_reuseFailAlloc_1726_, 7, v_nativeLibDir_1698_);
lean_ctor_set(v_reuseFailAlloc_1726_, 8, v_binDir_1699_);
lean_ctor_set(v_reuseFailAlloc_1726_, 9, v_irDir_1700_);
lean_ctor_set(v_reuseFailAlloc_1726_, 10, v_releaseRepo_1701_);
lean_ctor_set(v_reuseFailAlloc_1726_, 11, v_buildArchive_1702_);
lean_ctor_set(v_reuseFailAlloc_1726_, 12, v_testDriver_1704_);
lean_ctor_set(v_reuseFailAlloc_1726_, 13, v_val_1687_);
lean_ctor_set(v_reuseFailAlloc_1726_, 14, v_lintDriver_1705_);
lean_ctor_set(v_reuseFailAlloc_1726_, 15, v_lintDriverArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1726_, 16, v_version_1707_);
lean_ctor_set(v_reuseFailAlloc_1726_, 17, v_versionTags_1708_);
lean_ctor_set(v_reuseFailAlloc_1726_, 18, v_description_1709_);
lean_ctor_set(v_reuseFailAlloc_1726_, 19, v_keywords_1710_);
lean_ctor_set(v_reuseFailAlloc_1726_, 20, v_homepage_1711_);
lean_ctor_set(v_reuseFailAlloc_1726_, 21, v_license_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 22, v_licenseFiles_1713_);
lean_ctor_set(v_reuseFailAlloc_1726_, 23, v_readmeFile_1714_);
lean_ctor_set(v_reuseFailAlloc_1726_, 24, v_enableArtifactCache_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1726_, 25, v_restoreAllArtifacts_x3f_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26, v_bootstrap_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26 + 1, v_precompileModules_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26 + 3, v_reservoir_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26 + 5, v_allowImportAll_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*26 + 6, v_fixedToolchain_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* v_f_1729_, lean_object* v_cfg_1730_){
_start:
{
lean_object* v_toWorkspaceConfig_1731_; lean_object* v_toLeanConfig_1732_; uint8_t v_bootstrap_1733_; lean_object* v_extraDepTargets_1734_; uint8_t v_precompileModules_1735_; lean_object* v_moreGlobalServerArgs_1736_; lean_object* v_srcDir_1737_; lean_object* v_buildDir_1738_; lean_object* v_leanLibDir_1739_; lean_object* v_nativeLibDir_1740_; lean_object* v_binDir_1741_; lean_object* v_irDir_1742_; lean_object* v_releaseRepo_1743_; lean_object* v_buildArchive_1744_; uint8_t v_preferReleaseBuild_1745_; lean_object* v_testDriver_1746_; lean_object* v_testDriverArgs_1747_; lean_object* v_lintDriver_1748_; lean_object* v_lintDriverArgs_1749_; lean_object* v_version_1750_; lean_object* v_versionTags_1751_; lean_object* v_description_1752_; lean_object* v_keywords_1753_; lean_object* v_homepage_1754_; lean_object* v_license_1755_; lean_object* v_licenseFiles_1756_; lean_object* v_readmeFile_1757_; uint8_t v_reservoir_1758_; lean_object* v_enableArtifactCache_x3f_1759_; lean_object* v_restoreAllArtifacts_x3f_1760_; uint8_t v_libPrefixOnWindows_1761_; uint8_t v_allowImportAll_1762_; uint8_t v_fixedToolchain_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1771_; 
v_toWorkspaceConfig_1731_ = lean_ctor_get(v_cfg_1730_, 0);
v_toLeanConfig_1732_ = lean_ctor_get(v_cfg_1730_, 1);
v_bootstrap_1733_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26);
v_extraDepTargets_1734_ = lean_ctor_get(v_cfg_1730_, 2);
v_precompileModules_1735_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1736_ = lean_ctor_get(v_cfg_1730_, 3);
v_srcDir_1737_ = lean_ctor_get(v_cfg_1730_, 4);
v_buildDir_1738_ = lean_ctor_get(v_cfg_1730_, 5);
v_leanLibDir_1739_ = lean_ctor_get(v_cfg_1730_, 6);
v_nativeLibDir_1740_ = lean_ctor_get(v_cfg_1730_, 7);
v_binDir_1741_ = lean_ctor_get(v_cfg_1730_, 8);
v_irDir_1742_ = lean_ctor_get(v_cfg_1730_, 9);
v_releaseRepo_1743_ = lean_ctor_get(v_cfg_1730_, 10);
v_buildArchive_1744_ = lean_ctor_get(v_cfg_1730_, 11);
v_preferReleaseBuild_1745_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26 + 2);
v_testDriver_1746_ = lean_ctor_get(v_cfg_1730_, 12);
v_testDriverArgs_1747_ = lean_ctor_get(v_cfg_1730_, 13);
v_lintDriver_1748_ = lean_ctor_get(v_cfg_1730_, 14);
v_lintDriverArgs_1749_ = lean_ctor_get(v_cfg_1730_, 15);
v_version_1750_ = lean_ctor_get(v_cfg_1730_, 16);
v_versionTags_1751_ = lean_ctor_get(v_cfg_1730_, 17);
v_description_1752_ = lean_ctor_get(v_cfg_1730_, 18);
v_keywords_1753_ = lean_ctor_get(v_cfg_1730_, 19);
v_homepage_1754_ = lean_ctor_get(v_cfg_1730_, 20);
v_license_1755_ = lean_ctor_get(v_cfg_1730_, 21);
v_licenseFiles_1756_ = lean_ctor_get(v_cfg_1730_, 22);
v_readmeFile_1757_ = lean_ctor_get(v_cfg_1730_, 23);
v_reservoir_1758_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1759_ = lean_ctor_get(v_cfg_1730_, 24);
v_restoreAllArtifacts_x3f_1760_ = lean_ctor_get(v_cfg_1730_, 25);
v_libPrefixOnWindows_1761_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26 + 4);
v_allowImportAll_1762_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26 + 5);
v_fixedToolchain_1763_ = lean_ctor_get_uint8(v_cfg_1730_, sizeof(void*)*26 + 6);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_cfg_1730_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1765_ = v_cfg_1730_;
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1760_);
lean_inc(v_enableArtifactCache_x3f_1759_);
lean_inc(v_readmeFile_1757_);
lean_inc(v_licenseFiles_1756_);
lean_inc(v_license_1755_);
lean_inc(v_homepage_1754_);
lean_inc(v_keywords_1753_);
lean_inc(v_description_1752_);
lean_inc(v_versionTags_1751_);
lean_inc(v_version_1750_);
lean_inc(v_lintDriverArgs_1749_);
lean_inc(v_lintDriver_1748_);
lean_inc(v_testDriverArgs_1747_);
lean_inc(v_testDriver_1746_);
lean_inc(v_buildArchive_1744_);
lean_inc(v_releaseRepo_1743_);
lean_inc(v_irDir_1742_);
lean_inc(v_binDir_1741_);
lean_inc(v_nativeLibDir_1740_);
lean_inc(v_leanLibDir_1739_);
lean_inc(v_buildDir_1738_);
lean_inc(v_srcDir_1737_);
lean_inc(v_moreGlobalServerArgs_1736_);
lean_inc(v_extraDepTargets_1734_);
lean_inc(v_toLeanConfig_1732_);
lean_inc(v_toWorkspaceConfig_1731_);
lean_dec(v_cfg_1730_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_apply_1(v_f_1729_, v_testDriverArgs_1747_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 13, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_toWorkspaceConfig_1731_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_toLeanConfig_1732_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_extraDepTargets_1734_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_moreGlobalServerArgs_1736_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_srcDir_1737_);
lean_ctor_set(v_reuseFailAlloc_1770_, 5, v_buildDir_1738_);
lean_ctor_set(v_reuseFailAlloc_1770_, 6, v_leanLibDir_1739_);
lean_ctor_set(v_reuseFailAlloc_1770_, 7, v_nativeLibDir_1740_);
lean_ctor_set(v_reuseFailAlloc_1770_, 8, v_binDir_1741_);
lean_ctor_set(v_reuseFailAlloc_1770_, 9, v_irDir_1742_);
lean_ctor_set(v_reuseFailAlloc_1770_, 10, v_releaseRepo_1743_);
lean_ctor_set(v_reuseFailAlloc_1770_, 11, v_buildArchive_1744_);
lean_ctor_set(v_reuseFailAlloc_1770_, 12, v_testDriver_1746_);
lean_ctor_set(v_reuseFailAlloc_1770_, 13, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 14, v_lintDriver_1748_);
lean_ctor_set(v_reuseFailAlloc_1770_, 15, v_lintDriverArgs_1749_);
lean_ctor_set(v_reuseFailAlloc_1770_, 16, v_version_1750_);
lean_ctor_set(v_reuseFailAlloc_1770_, 17, v_versionTags_1751_);
lean_ctor_set(v_reuseFailAlloc_1770_, 18, v_description_1752_);
lean_ctor_set(v_reuseFailAlloc_1770_, 19, v_keywords_1753_);
lean_ctor_set(v_reuseFailAlloc_1770_, 20, v_homepage_1754_);
lean_ctor_set(v_reuseFailAlloc_1770_, 21, v_license_1755_);
lean_ctor_set(v_reuseFailAlloc_1770_, 22, v_licenseFiles_1756_);
lean_ctor_set(v_reuseFailAlloc_1770_, 23, v_readmeFile_1757_);
lean_ctor_set(v_reuseFailAlloc_1770_, 24, v_enableArtifactCache_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1770_, 25, v_restoreAllArtifacts_x3f_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26, v_bootstrap_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26 + 1, v_precompileModules_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26 + 3, v_reservoir_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26 + 5, v_allowImportAll_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*26 + 6, v_fixedToolchain_1763_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1780_, lean_object* v_n_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1783_, lean_object* v_n_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1783_, v_n_1784_);
lean_dec(v_n_1784_);
lean_dec(v_p_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_1786_, lean_object* v_n_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1786_, v_n_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_1789_, lean_object* v_n_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_1789_, v_n_1790_);
lean_dec(v_n_1790_);
lean_dec(v_p_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* v_cfg_1792_){
_start:
{
lean_object* v_lintDriver_1793_; 
v_lintDriver_1793_ = lean_ctor_get(v_cfg_1792_, 14);
lean_inc_ref(v_lintDriver_1793_);
return v_lintDriver_1793_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* v_cfg_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lake_PackageConfig_lintDriver___proj___lam__0(v_cfg_1794_);
lean_dec_ref(v_cfg_1794_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* v_val_1796_, lean_object* v_cfg_1797_){
_start:
{
lean_object* v_toWorkspaceConfig_1798_; lean_object* v_toLeanConfig_1799_; uint8_t v_bootstrap_1800_; lean_object* v_extraDepTargets_1801_; uint8_t v_precompileModules_1802_; lean_object* v_moreGlobalServerArgs_1803_; lean_object* v_srcDir_1804_; lean_object* v_buildDir_1805_; lean_object* v_leanLibDir_1806_; lean_object* v_nativeLibDir_1807_; lean_object* v_binDir_1808_; lean_object* v_irDir_1809_; lean_object* v_releaseRepo_1810_; lean_object* v_buildArchive_1811_; uint8_t v_preferReleaseBuild_1812_; lean_object* v_testDriver_1813_; lean_object* v_testDriverArgs_1814_; lean_object* v_lintDriverArgs_1815_; lean_object* v_version_1816_; lean_object* v_versionTags_1817_; lean_object* v_description_1818_; lean_object* v_keywords_1819_; lean_object* v_homepage_1820_; lean_object* v_license_1821_; lean_object* v_licenseFiles_1822_; lean_object* v_readmeFile_1823_; uint8_t v_reservoir_1824_; lean_object* v_enableArtifactCache_x3f_1825_; lean_object* v_restoreAllArtifacts_x3f_1826_; uint8_t v_libPrefixOnWindows_1827_; uint8_t v_allowImportAll_1828_; uint8_t v_fixedToolchain_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_toWorkspaceConfig_1798_ = lean_ctor_get(v_cfg_1797_, 0);
v_toLeanConfig_1799_ = lean_ctor_get(v_cfg_1797_, 1);
v_bootstrap_1800_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26);
v_extraDepTargets_1801_ = lean_ctor_get(v_cfg_1797_, 2);
v_precompileModules_1802_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1803_ = lean_ctor_get(v_cfg_1797_, 3);
v_srcDir_1804_ = lean_ctor_get(v_cfg_1797_, 4);
v_buildDir_1805_ = lean_ctor_get(v_cfg_1797_, 5);
v_leanLibDir_1806_ = lean_ctor_get(v_cfg_1797_, 6);
v_nativeLibDir_1807_ = lean_ctor_get(v_cfg_1797_, 7);
v_binDir_1808_ = lean_ctor_get(v_cfg_1797_, 8);
v_irDir_1809_ = lean_ctor_get(v_cfg_1797_, 9);
v_releaseRepo_1810_ = lean_ctor_get(v_cfg_1797_, 10);
v_buildArchive_1811_ = lean_ctor_get(v_cfg_1797_, 11);
v_preferReleaseBuild_1812_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26 + 2);
v_testDriver_1813_ = lean_ctor_get(v_cfg_1797_, 12);
v_testDriverArgs_1814_ = lean_ctor_get(v_cfg_1797_, 13);
v_lintDriverArgs_1815_ = lean_ctor_get(v_cfg_1797_, 15);
v_version_1816_ = lean_ctor_get(v_cfg_1797_, 16);
v_versionTags_1817_ = lean_ctor_get(v_cfg_1797_, 17);
v_description_1818_ = lean_ctor_get(v_cfg_1797_, 18);
v_keywords_1819_ = lean_ctor_get(v_cfg_1797_, 19);
v_homepage_1820_ = lean_ctor_get(v_cfg_1797_, 20);
v_license_1821_ = lean_ctor_get(v_cfg_1797_, 21);
v_licenseFiles_1822_ = lean_ctor_get(v_cfg_1797_, 22);
v_readmeFile_1823_ = lean_ctor_get(v_cfg_1797_, 23);
v_reservoir_1824_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1825_ = lean_ctor_get(v_cfg_1797_, 24);
v_restoreAllArtifacts_x3f_1826_ = lean_ctor_get(v_cfg_1797_, 25);
v_libPrefixOnWindows_1827_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26 + 4);
v_allowImportAll_1828_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26 + 5);
v_fixedToolchain_1829_ = lean_ctor_get_uint8(v_cfg_1797_, sizeof(void*)*26 + 6);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_cfg_1797_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v_cfg_1797_, 14);
lean_dec(v_unused_1837_);
v___x_1831_ = v_cfg_1797_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1826_);
lean_inc(v_enableArtifactCache_x3f_1825_);
lean_inc(v_readmeFile_1823_);
lean_inc(v_licenseFiles_1822_);
lean_inc(v_license_1821_);
lean_inc(v_homepage_1820_);
lean_inc(v_keywords_1819_);
lean_inc(v_description_1818_);
lean_inc(v_versionTags_1817_);
lean_inc(v_version_1816_);
lean_inc(v_lintDriverArgs_1815_);
lean_inc(v_testDriverArgs_1814_);
lean_inc(v_testDriver_1813_);
lean_inc(v_buildArchive_1811_);
lean_inc(v_releaseRepo_1810_);
lean_inc(v_irDir_1809_);
lean_inc(v_binDir_1808_);
lean_inc(v_nativeLibDir_1807_);
lean_inc(v_leanLibDir_1806_);
lean_inc(v_buildDir_1805_);
lean_inc(v_srcDir_1804_);
lean_inc(v_moreGlobalServerArgs_1803_);
lean_inc(v_extraDepTargets_1801_);
lean_inc(v_toLeanConfig_1799_);
lean_inc(v_toWorkspaceConfig_1798_);
lean_dec(v_cfg_1797_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 14, v_val_1796_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_toWorkspaceConfig_1798_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_toLeanConfig_1799_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_extraDepTargets_1801_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v_moreGlobalServerArgs_1803_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v_srcDir_1804_);
lean_ctor_set(v_reuseFailAlloc_1835_, 5, v_buildDir_1805_);
lean_ctor_set(v_reuseFailAlloc_1835_, 6, v_leanLibDir_1806_);
lean_ctor_set(v_reuseFailAlloc_1835_, 7, v_nativeLibDir_1807_);
lean_ctor_set(v_reuseFailAlloc_1835_, 8, v_binDir_1808_);
lean_ctor_set(v_reuseFailAlloc_1835_, 9, v_irDir_1809_);
lean_ctor_set(v_reuseFailAlloc_1835_, 10, v_releaseRepo_1810_);
lean_ctor_set(v_reuseFailAlloc_1835_, 11, v_buildArchive_1811_);
lean_ctor_set(v_reuseFailAlloc_1835_, 12, v_testDriver_1813_);
lean_ctor_set(v_reuseFailAlloc_1835_, 13, v_testDriverArgs_1814_);
lean_ctor_set(v_reuseFailAlloc_1835_, 14, v_val_1796_);
lean_ctor_set(v_reuseFailAlloc_1835_, 15, v_lintDriverArgs_1815_);
lean_ctor_set(v_reuseFailAlloc_1835_, 16, v_version_1816_);
lean_ctor_set(v_reuseFailAlloc_1835_, 17, v_versionTags_1817_);
lean_ctor_set(v_reuseFailAlloc_1835_, 18, v_description_1818_);
lean_ctor_set(v_reuseFailAlloc_1835_, 19, v_keywords_1819_);
lean_ctor_set(v_reuseFailAlloc_1835_, 20, v_homepage_1820_);
lean_ctor_set(v_reuseFailAlloc_1835_, 21, v_license_1821_);
lean_ctor_set(v_reuseFailAlloc_1835_, 22, v_licenseFiles_1822_);
lean_ctor_set(v_reuseFailAlloc_1835_, 23, v_readmeFile_1823_);
lean_ctor_set(v_reuseFailAlloc_1835_, 24, v_enableArtifactCache_x3f_1825_);
lean_ctor_set(v_reuseFailAlloc_1835_, 25, v_restoreAllArtifacts_x3f_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26, v_bootstrap_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26 + 1, v_precompileModules_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26 + 3, v_reservoir_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26 + 5, v_allowImportAll_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*26 + 6, v_fixedToolchain_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* v_f_1838_, lean_object* v_cfg_1839_){
_start:
{
lean_object* v_toWorkspaceConfig_1840_; lean_object* v_toLeanConfig_1841_; uint8_t v_bootstrap_1842_; lean_object* v_extraDepTargets_1843_; uint8_t v_precompileModules_1844_; lean_object* v_moreGlobalServerArgs_1845_; lean_object* v_srcDir_1846_; lean_object* v_buildDir_1847_; lean_object* v_leanLibDir_1848_; lean_object* v_nativeLibDir_1849_; lean_object* v_binDir_1850_; lean_object* v_irDir_1851_; lean_object* v_releaseRepo_1852_; lean_object* v_buildArchive_1853_; uint8_t v_preferReleaseBuild_1854_; lean_object* v_testDriver_1855_; lean_object* v_testDriverArgs_1856_; lean_object* v_lintDriver_1857_; lean_object* v_lintDriverArgs_1858_; lean_object* v_version_1859_; lean_object* v_versionTags_1860_; lean_object* v_description_1861_; lean_object* v_keywords_1862_; lean_object* v_homepage_1863_; lean_object* v_license_1864_; lean_object* v_licenseFiles_1865_; lean_object* v_readmeFile_1866_; uint8_t v_reservoir_1867_; lean_object* v_enableArtifactCache_x3f_1868_; lean_object* v_restoreAllArtifacts_x3f_1869_; uint8_t v_libPrefixOnWindows_1870_; uint8_t v_allowImportAll_1871_; uint8_t v_fixedToolchain_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
v_toWorkspaceConfig_1840_ = lean_ctor_get(v_cfg_1839_, 0);
v_toLeanConfig_1841_ = lean_ctor_get(v_cfg_1839_, 1);
v_bootstrap_1842_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26);
v_extraDepTargets_1843_ = lean_ctor_get(v_cfg_1839_, 2);
v_precompileModules_1844_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1845_ = lean_ctor_get(v_cfg_1839_, 3);
v_srcDir_1846_ = lean_ctor_get(v_cfg_1839_, 4);
v_buildDir_1847_ = lean_ctor_get(v_cfg_1839_, 5);
v_leanLibDir_1848_ = lean_ctor_get(v_cfg_1839_, 6);
v_nativeLibDir_1849_ = lean_ctor_get(v_cfg_1839_, 7);
v_binDir_1850_ = lean_ctor_get(v_cfg_1839_, 8);
v_irDir_1851_ = lean_ctor_get(v_cfg_1839_, 9);
v_releaseRepo_1852_ = lean_ctor_get(v_cfg_1839_, 10);
v_buildArchive_1853_ = lean_ctor_get(v_cfg_1839_, 11);
v_preferReleaseBuild_1854_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26 + 2);
v_testDriver_1855_ = lean_ctor_get(v_cfg_1839_, 12);
v_testDriverArgs_1856_ = lean_ctor_get(v_cfg_1839_, 13);
v_lintDriver_1857_ = lean_ctor_get(v_cfg_1839_, 14);
v_lintDriverArgs_1858_ = lean_ctor_get(v_cfg_1839_, 15);
v_version_1859_ = lean_ctor_get(v_cfg_1839_, 16);
v_versionTags_1860_ = lean_ctor_get(v_cfg_1839_, 17);
v_description_1861_ = lean_ctor_get(v_cfg_1839_, 18);
v_keywords_1862_ = lean_ctor_get(v_cfg_1839_, 19);
v_homepage_1863_ = lean_ctor_get(v_cfg_1839_, 20);
v_license_1864_ = lean_ctor_get(v_cfg_1839_, 21);
v_licenseFiles_1865_ = lean_ctor_get(v_cfg_1839_, 22);
v_readmeFile_1866_ = lean_ctor_get(v_cfg_1839_, 23);
v_reservoir_1867_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1868_ = lean_ctor_get(v_cfg_1839_, 24);
v_restoreAllArtifacts_x3f_1869_ = lean_ctor_get(v_cfg_1839_, 25);
v_libPrefixOnWindows_1870_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26 + 4);
v_allowImportAll_1871_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26 + 5);
v_fixedToolchain_1872_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*26 + 6);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_cfg_1839_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v_cfg_1839_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1869_);
lean_inc(v_enableArtifactCache_x3f_1868_);
lean_inc(v_readmeFile_1866_);
lean_inc(v_licenseFiles_1865_);
lean_inc(v_license_1864_);
lean_inc(v_homepage_1863_);
lean_inc(v_keywords_1862_);
lean_inc(v_description_1861_);
lean_inc(v_versionTags_1860_);
lean_inc(v_version_1859_);
lean_inc(v_lintDriverArgs_1858_);
lean_inc(v_lintDriver_1857_);
lean_inc(v_testDriverArgs_1856_);
lean_inc(v_testDriver_1855_);
lean_inc(v_buildArchive_1853_);
lean_inc(v_releaseRepo_1852_);
lean_inc(v_irDir_1851_);
lean_inc(v_binDir_1850_);
lean_inc(v_nativeLibDir_1849_);
lean_inc(v_leanLibDir_1848_);
lean_inc(v_buildDir_1847_);
lean_inc(v_srcDir_1846_);
lean_inc(v_moreGlobalServerArgs_1845_);
lean_inc(v_extraDepTargets_1843_);
lean_inc(v_toLeanConfig_1841_);
lean_inc(v_toWorkspaceConfig_1840_);
lean_dec(v_cfg_1839_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_apply_1(v_f_1838_, v_lintDriver_1857_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 14, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_toWorkspaceConfig_1840_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_toLeanConfig_1841_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_extraDepTargets_1843_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_moreGlobalServerArgs_1845_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_srcDir_1846_);
lean_ctor_set(v_reuseFailAlloc_1879_, 5, v_buildDir_1847_);
lean_ctor_set(v_reuseFailAlloc_1879_, 6, v_leanLibDir_1848_);
lean_ctor_set(v_reuseFailAlloc_1879_, 7, v_nativeLibDir_1849_);
lean_ctor_set(v_reuseFailAlloc_1879_, 8, v_binDir_1850_);
lean_ctor_set(v_reuseFailAlloc_1879_, 9, v_irDir_1851_);
lean_ctor_set(v_reuseFailAlloc_1879_, 10, v_releaseRepo_1852_);
lean_ctor_set(v_reuseFailAlloc_1879_, 11, v_buildArchive_1853_);
lean_ctor_set(v_reuseFailAlloc_1879_, 12, v_testDriver_1855_);
lean_ctor_set(v_reuseFailAlloc_1879_, 13, v_testDriverArgs_1856_);
lean_ctor_set(v_reuseFailAlloc_1879_, 14, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1879_, 15, v_lintDriverArgs_1858_);
lean_ctor_set(v_reuseFailAlloc_1879_, 16, v_version_1859_);
lean_ctor_set(v_reuseFailAlloc_1879_, 17, v_versionTags_1860_);
lean_ctor_set(v_reuseFailAlloc_1879_, 18, v_description_1861_);
lean_ctor_set(v_reuseFailAlloc_1879_, 19, v_keywords_1862_);
lean_ctor_set(v_reuseFailAlloc_1879_, 20, v_homepage_1863_);
lean_ctor_set(v_reuseFailAlloc_1879_, 21, v_license_1864_);
lean_ctor_set(v_reuseFailAlloc_1879_, 22, v_licenseFiles_1865_);
lean_ctor_set(v_reuseFailAlloc_1879_, 23, v_readmeFile_1866_);
lean_ctor_set(v_reuseFailAlloc_1879_, 24, v_enableArtifactCache_x3f_1868_);
lean_ctor_set(v_reuseFailAlloc_1879_, 25, v_restoreAllArtifacts_x3f_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26, v_bootstrap_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26 + 1, v_precompileModules_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26 + 3, v_reservoir_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26 + 5, v_allowImportAll_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, sizeof(void*)*26 + 6, v_fixedToolchain_1872_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_1889_, lean_object* v_n_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_1892_, lean_object* v_n_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1892_, v_n_1893_);
lean_dec(v_n_1893_);
lean_dec(v_p_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_1895_, lean_object* v_n_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1895_, v_n_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_1898_, lean_object* v_n_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_1898_, v_n_1899_);
lean_dec(v_n_1899_);
lean_dec(v_p_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* v_cfg_1901_){
_start:
{
lean_object* v_lintDriverArgs_1902_; 
v_lintDriverArgs_1902_ = lean_ctor_get(v_cfg_1901_, 15);
lean_inc_ref(v_lintDriverArgs_1902_);
return v_lintDriverArgs_1902_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(v_cfg_1903_);
lean_dec_ref(v_cfg_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* v_val_1905_, lean_object* v_cfg_1906_){
_start:
{
lean_object* v_toWorkspaceConfig_1907_; lean_object* v_toLeanConfig_1908_; uint8_t v_bootstrap_1909_; lean_object* v_extraDepTargets_1910_; uint8_t v_precompileModules_1911_; lean_object* v_moreGlobalServerArgs_1912_; lean_object* v_srcDir_1913_; lean_object* v_buildDir_1914_; lean_object* v_leanLibDir_1915_; lean_object* v_nativeLibDir_1916_; lean_object* v_binDir_1917_; lean_object* v_irDir_1918_; lean_object* v_releaseRepo_1919_; lean_object* v_buildArchive_1920_; uint8_t v_preferReleaseBuild_1921_; lean_object* v_testDriver_1922_; lean_object* v_testDriverArgs_1923_; lean_object* v_lintDriver_1924_; lean_object* v_version_1925_; lean_object* v_versionTags_1926_; lean_object* v_description_1927_; lean_object* v_keywords_1928_; lean_object* v_homepage_1929_; lean_object* v_license_1930_; lean_object* v_licenseFiles_1931_; lean_object* v_readmeFile_1932_; uint8_t v_reservoir_1933_; lean_object* v_enableArtifactCache_x3f_1934_; lean_object* v_restoreAllArtifacts_x3f_1935_; uint8_t v_libPrefixOnWindows_1936_; uint8_t v_allowImportAll_1937_; uint8_t v_fixedToolchain_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_toWorkspaceConfig_1907_ = lean_ctor_get(v_cfg_1906_, 0);
v_toLeanConfig_1908_ = lean_ctor_get(v_cfg_1906_, 1);
v_bootstrap_1909_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26);
v_extraDepTargets_1910_ = lean_ctor_get(v_cfg_1906_, 2);
v_precompileModules_1911_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1912_ = lean_ctor_get(v_cfg_1906_, 3);
v_srcDir_1913_ = lean_ctor_get(v_cfg_1906_, 4);
v_buildDir_1914_ = lean_ctor_get(v_cfg_1906_, 5);
v_leanLibDir_1915_ = lean_ctor_get(v_cfg_1906_, 6);
v_nativeLibDir_1916_ = lean_ctor_get(v_cfg_1906_, 7);
v_binDir_1917_ = lean_ctor_get(v_cfg_1906_, 8);
v_irDir_1918_ = lean_ctor_get(v_cfg_1906_, 9);
v_releaseRepo_1919_ = lean_ctor_get(v_cfg_1906_, 10);
v_buildArchive_1920_ = lean_ctor_get(v_cfg_1906_, 11);
v_preferReleaseBuild_1921_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26 + 2);
v_testDriver_1922_ = lean_ctor_get(v_cfg_1906_, 12);
v_testDriverArgs_1923_ = lean_ctor_get(v_cfg_1906_, 13);
v_lintDriver_1924_ = lean_ctor_get(v_cfg_1906_, 14);
v_version_1925_ = lean_ctor_get(v_cfg_1906_, 16);
v_versionTags_1926_ = lean_ctor_get(v_cfg_1906_, 17);
v_description_1927_ = lean_ctor_get(v_cfg_1906_, 18);
v_keywords_1928_ = lean_ctor_get(v_cfg_1906_, 19);
v_homepage_1929_ = lean_ctor_get(v_cfg_1906_, 20);
v_license_1930_ = lean_ctor_get(v_cfg_1906_, 21);
v_licenseFiles_1931_ = lean_ctor_get(v_cfg_1906_, 22);
v_readmeFile_1932_ = lean_ctor_get(v_cfg_1906_, 23);
v_reservoir_1933_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1934_ = lean_ctor_get(v_cfg_1906_, 24);
v_restoreAllArtifacts_x3f_1935_ = lean_ctor_get(v_cfg_1906_, 25);
v_libPrefixOnWindows_1936_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26 + 4);
v_allowImportAll_1937_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26 + 5);
v_fixedToolchain_1938_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*26 + 6);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_cfg_1906_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v_cfg_1906_, 15);
lean_dec(v_unused_1946_);
v___x_1940_ = v_cfg_1906_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1935_);
lean_inc(v_enableArtifactCache_x3f_1934_);
lean_inc(v_readmeFile_1932_);
lean_inc(v_licenseFiles_1931_);
lean_inc(v_license_1930_);
lean_inc(v_homepage_1929_);
lean_inc(v_keywords_1928_);
lean_inc(v_description_1927_);
lean_inc(v_versionTags_1926_);
lean_inc(v_version_1925_);
lean_inc(v_lintDriver_1924_);
lean_inc(v_testDriverArgs_1923_);
lean_inc(v_testDriver_1922_);
lean_inc(v_buildArchive_1920_);
lean_inc(v_releaseRepo_1919_);
lean_inc(v_irDir_1918_);
lean_inc(v_binDir_1917_);
lean_inc(v_nativeLibDir_1916_);
lean_inc(v_leanLibDir_1915_);
lean_inc(v_buildDir_1914_);
lean_inc(v_srcDir_1913_);
lean_inc(v_moreGlobalServerArgs_1912_);
lean_inc(v_extraDepTargets_1910_);
lean_inc(v_toLeanConfig_1908_);
lean_inc(v_toWorkspaceConfig_1907_);
lean_dec(v_cfg_1906_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 15, v_val_1905_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_toWorkspaceConfig_1907_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_toLeanConfig_1908_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_extraDepTargets_1910_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_moreGlobalServerArgs_1912_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_srcDir_1913_);
lean_ctor_set(v_reuseFailAlloc_1944_, 5, v_buildDir_1914_);
lean_ctor_set(v_reuseFailAlloc_1944_, 6, v_leanLibDir_1915_);
lean_ctor_set(v_reuseFailAlloc_1944_, 7, v_nativeLibDir_1916_);
lean_ctor_set(v_reuseFailAlloc_1944_, 8, v_binDir_1917_);
lean_ctor_set(v_reuseFailAlloc_1944_, 9, v_irDir_1918_);
lean_ctor_set(v_reuseFailAlloc_1944_, 10, v_releaseRepo_1919_);
lean_ctor_set(v_reuseFailAlloc_1944_, 11, v_buildArchive_1920_);
lean_ctor_set(v_reuseFailAlloc_1944_, 12, v_testDriver_1922_);
lean_ctor_set(v_reuseFailAlloc_1944_, 13, v_testDriverArgs_1923_);
lean_ctor_set(v_reuseFailAlloc_1944_, 14, v_lintDriver_1924_);
lean_ctor_set(v_reuseFailAlloc_1944_, 15, v_val_1905_);
lean_ctor_set(v_reuseFailAlloc_1944_, 16, v_version_1925_);
lean_ctor_set(v_reuseFailAlloc_1944_, 17, v_versionTags_1926_);
lean_ctor_set(v_reuseFailAlloc_1944_, 18, v_description_1927_);
lean_ctor_set(v_reuseFailAlloc_1944_, 19, v_keywords_1928_);
lean_ctor_set(v_reuseFailAlloc_1944_, 20, v_homepage_1929_);
lean_ctor_set(v_reuseFailAlloc_1944_, 21, v_license_1930_);
lean_ctor_set(v_reuseFailAlloc_1944_, 22, v_licenseFiles_1931_);
lean_ctor_set(v_reuseFailAlloc_1944_, 23, v_readmeFile_1932_);
lean_ctor_set(v_reuseFailAlloc_1944_, 24, v_enableArtifactCache_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1944_, 25, v_restoreAllArtifacts_x3f_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26, v_bootstrap_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26 + 1, v_precompileModules_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26 + 3, v_reservoir_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26 + 5, v_allowImportAll_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1944_, sizeof(void*)*26 + 6, v_fixedToolchain_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* v_f_1947_, lean_object* v_cfg_1948_){
_start:
{
lean_object* v_toWorkspaceConfig_1949_; lean_object* v_toLeanConfig_1950_; uint8_t v_bootstrap_1951_; lean_object* v_extraDepTargets_1952_; uint8_t v_precompileModules_1953_; lean_object* v_moreGlobalServerArgs_1954_; lean_object* v_srcDir_1955_; lean_object* v_buildDir_1956_; lean_object* v_leanLibDir_1957_; lean_object* v_nativeLibDir_1958_; lean_object* v_binDir_1959_; lean_object* v_irDir_1960_; lean_object* v_releaseRepo_1961_; lean_object* v_buildArchive_1962_; uint8_t v_preferReleaseBuild_1963_; lean_object* v_testDriver_1964_; lean_object* v_testDriverArgs_1965_; lean_object* v_lintDriver_1966_; lean_object* v_lintDriverArgs_1967_; lean_object* v_version_1968_; lean_object* v_versionTags_1969_; lean_object* v_description_1970_; lean_object* v_keywords_1971_; lean_object* v_homepage_1972_; lean_object* v_license_1973_; lean_object* v_licenseFiles_1974_; lean_object* v_readmeFile_1975_; uint8_t v_reservoir_1976_; lean_object* v_enableArtifactCache_x3f_1977_; lean_object* v_restoreAllArtifacts_x3f_1978_; uint8_t v_libPrefixOnWindows_1979_; uint8_t v_allowImportAll_1980_; uint8_t v_fixedToolchain_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1989_; 
v_toWorkspaceConfig_1949_ = lean_ctor_get(v_cfg_1948_, 0);
v_toLeanConfig_1950_ = lean_ctor_get(v_cfg_1948_, 1);
v_bootstrap_1951_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26);
v_extraDepTargets_1952_ = lean_ctor_get(v_cfg_1948_, 2);
v_precompileModules_1953_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_1954_ = lean_ctor_get(v_cfg_1948_, 3);
v_srcDir_1955_ = lean_ctor_get(v_cfg_1948_, 4);
v_buildDir_1956_ = lean_ctor_get(v_cfg_1948_, 5);
v_leanLibDir_1957_ = lean_ctor_get(v_cfg_1948_, 6);
v_nativeLibDir_1958_ = lean_ctor_get(v_cfg_1948_, 7);
v_binDir_1959_ = lean_ctor_get(v_cfg_1948_, 8);
v_irDir_1960_ = lean_ctor_get(v_cfg_1948_, 9);
v_releaseRepo_1961_ = lean_ctor_get(v_cfg_1948_, 10);
v_buildArchive_1962_ = lean_ctor_get(v_cfg_1948_, 11);
v_preferReleaseBuild_1963_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26 + 2);
v_testDriver_1964_ = lean_ctor_get(v_cfg_1948_, 12);
v_testDriverArgs_1965_ = lean_ctor_get(v_cfg_1948_, 13);
v_lintDriver_1966_ = lean_ctor_get(v_cfg_1948_, 14);
v_lintDriverArgs_1967_ = lean_ctor_get(v_cfg_1948_, 15);
v_version_1968_ = lean_ctor_get(v_cfg_1948_, 16);
v_versionTags_1969_ = lean_ctor_get(v_cfg_1948_, 17);
v_description_1970_ = lean_ctor_get(v_cfg_1948_, 18);
v_keywords_1971_ = lean_ctor_get(v_cfg_1948_, 19);
v_homepage_1972_ = lean_ctor_get(v_cfg_1948_, 20);
v_license_1973_ = lean_ctor_get(v_cfg_1948_, 21);
v_licenseFiles_1974_ = lean_ctor_get(v_cfg_1948_, 22);
v_readmeFile_1975_ = lean_ctor_get(v_cfg_1948_, 23);
v_reservoir_1976_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_1977_ = lean_ctor_get(v_cfg_1948_, 24);
v_restoreAllArtifacts_x3f_1978_ = lean_ctor_get(v_cfg_1948_, 25);
v_libPrefixOnWindows_1979_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26 + 4);
v_allowImportAll_1980_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26 + 5);
v_fixedToolchain_1981_ = lean_ctor_get_uint8(v_cfg_1948_, sizeof(void*)*26 + 6);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_cfg_1948_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1983_ = v_cfg_1948_;
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_1978_);
lean_inc(v_enableArtifactCache_x3f_1977_);
lean_inc(v_readmeFile_1975_);
lean_inc(v_licenseFiles_1974_);
lean_inc(v_license_1973_);
lean_inc(v_homepage_1972_);
lean_inc(v_keywords_1971_);
lean_inc(v_description_1970_);
lean_inc(v_versionTags_1969_);
lean_inc(v_version_1968_);
lean_inc(v_lintDriverArgs_1967_);
lean_inc(v_lintDriver_1966_);
lean_inc(v_testDriverArgs_1965_);
lean_inc(v_testDriver_1964_);
lean_inc(v_buildArchive_1962_);
lean_inc(v_releaseRepo_1961_);
lean_inc(v_irDir_1960_);
lean_inc(v_binDir_1959_);
lean_inc(v_nativeLibDir_1958_);
lean_inc(v_leanLibDir_1957_);
lean_inc(v_buildDir_1956_);
lean_inc(v_srcDir_1955_);
lean_inc(v_moreGlobalServerArgs_1954_);
lean_inc(v_extraDepTargets_1952_);
lean_inc(v_toLeanConfig_1950_);
lean_inc(v_toWorkspaceConfig_1949_);
lean_dec(v_cfg_1948_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_apply_1(v_f_1947_, v_lintDriverArgs_1967_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 15, v___x_1985_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_toWorkspaceConfig_1949_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_toLeanConfig_1950_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_extraDepTargets_1952_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_moreGlobalServerArgs_1954_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_srcDir_1955_);
lean_ctor_set(v_reuseFailAlloc_1988_, 5, v_buildDir_1956_);
lean_ctor_set(v_reuseFailAlloc_1988_, 6, v_leanLibDir_1957_);
lean_ctor_set(v_reuseFailAlloc_1988_, 7, v_nativeLibDir_1958_);
lean_ctor_set(v_reuseFailAlloc_1988_, 8, v_binDir_1959_);
lean_ctor_set(v_reuseFailAlloc_1988_, 9, v_irDir_1960_);
lean_ctor_set(v_reuseFailAlloc_1988_, 10, v_releaseRepo_1961_);
lean_ctor_set(v_reuseFailAlloc_1988_, 11, v_buildArchive_1962_);
lean_ctor_set(v_reuseFailAlloc_1988_, 12, v_testDriver_1964_);
lean_ctor_set(v_reuseFailAlloc_1988_, 13, v_testDriverArgs_1965_);
lean_ctor_set(v_reuseFailAlloc_1988_, 14, v_lintDriver_1966_);
lean_ctor_set(v_reuseFailAlloc_1988_, 15, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1988_, 16, v_version_1968_);
lean_ctor_set(v_reuseFailAlloc_1988_, 17, v_versionTags_1969_);
lean_ctor_set(v_reuseFailAlloc_1988_, 18, v_description_1970_);
lean_ctor_set(v_reuseFailAlloc_1988_, 19, v_keywords_1971_);
lean_ctor_set(v_reuseFailAlloc_1988_, 20, v_homepage_1972_);
lean_ctor_set(v_reuseFailAlloc_1988_, 21, v_license_1973_);
lean_ctor_set(v_reuseFailAlloc_1988_, 22, v_licenseFiles_1974_);
lean_ctor_set(v_reuseFailAlloc_1988_, 23, v_readmeFile_1975_);
lean_ctor_set(v_reuseFailAlloc_1988_, 24, v_enableArtifactCache_x3f_1977_);
lean_ctor_set(v_reuseFailAlloc_1988_, 25, v_restoreAllArtifacts_x3f_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26, v_bootstrap_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26 + 1, v_precompileModules_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26 + 2, v_preferReleaseBuild_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26 + 3, v_reservoir_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26 + 5, v_allowImportAll_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*26 + 6, v_fixedToolchain_1981_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_1998_, lean_object* v_n_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2001_, lean_object* v_n_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2001_, v_n_2002_);
lean_dec(v_n_2002_);
lean_dec(v_p_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2004_, lean_object* v_n_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2004_, v_n_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2007_, lean_object* v_n_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2007_, v_n_2008_);
lean_dec(v_n_2008_);
lean_dec(v_p_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* v_cfg_2010_){
_start:
{
lean_object* v_version_2011_; 
v_version_2011_ = lean_ctor_get(v_cfg_2010_, 16);
lean_inc_ref(v_version_2011_);
return v_version_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* v_cfg_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lake_PackageConfig_version___proj___lam__0(v_cfg_2012_);
lean_dec_ref(v_cfg_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* v_val_2014_, lean_object* v_cfg_2015_){
_start:
{
lean_object* v_toWorkspaceConfig_2016_; lean_object* v_toLeanConfig_2017_; uint8_t v_bootstrap_2018_; lean_object* v_extraDepTargets_2019_; uint8_t v_precompileModules_2020_; lean_object* v_moreGlobalServerArgs_2021_; lean_object* v_srcDir_2022_; lean_object* v_buildDir_2023_; lean_object* v_leanLibDir_2024_; lean_object* v_nativeLibDir_2025_; lean_object* v_binDir_2026_; lean_object* v_irDir_2027_; lean_object* v_releaseRepo_2028_; lean_object* v_buildArchive_2029_; uint8_t v_preferReleaseBuild_2030_; lean_object* v_testDriver_2031_; lean_object* v_testDriverArgs_2032_; lean_object* v_lintDriver_2033_; lean_object* v_lintDriverArgs_2034_; lean_object* v_versionTags_2035_; lean_object* v_description_2036_; lean_object* v_keywords_2037_; lean_object* v_homepage_2038_; lean_object* v_license_2039_; lean_object* v_licenseFiles_2040_; lean_object* v_readmeFile_2041_; uint8_t v_reservoir_2042_; lean_object* v_enableArtifactCache_x3f_2043_; lean_object* v_restoreAllArtifacts_x3f_2044_; uint8_t v_libPrefixOnWindows_2045_; uint8_t v_allowImportAll_2046_; uint8_t v_fixedToolchain_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_toWorkspaceConfig_2016_ = lean_ctor_get(v_cfg_2015_, 0);
v_toLeanConfig_2017_ = lean_ctor_get(v_cfg_2015_, 1);
v_bootstrap_2018_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26);
v_extraDepTargets_2019_ = lean_ctor_get(v_cfg_2015_, 2);
v_precompileModules_2020_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2021_ = lean_ctor_get(v_cfg_2015_, 3);
v_srcDir_2022_ = lean_ctor_get(v_cfg_2015_, 4);
v_buildDir_2023_ = lean_ctor_get(v_cfg_2015_, 5);
v_leanLibDir_2024_ = lean_ctor_get(v_cfg_2015_, 6);
v_nativeLibDir_2025_ = lean_ctor_get(v_cfg_2015_, 7);
v_binDir_2026_ = lean_ctor_get(v_cfg_2015_, 8);
v_irDir_2027_ = lean_ctor_get(v_cfg_2015_, 9);
v_releaseRepo_2028_ = lean_ctor_get(v_cfg_2015_, 10);
v_buildArchive_2029_ = lean_ctor_get(v_cfg_2015_, 11);
v_preferReleaseBuild_2030_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26 + 2);
v_testDriver_2031_ = lean_ctor_get(v_cfg_2015_, 12);
v_testDriverArgs_2032_ = lean_ctor_get(v_cfg_2015_, 13);
v_lintDriver_2033_ = lean_ctor_get(v_cfg_2015_, 14);
v_lintDriverArgs_2034_ = lean_ctor_get(v_cfg_2015_, 15);
v_versionTags_2035_ = lean_ctor_get(v_cfg_2015_, 17);
v_description_2036_ = lean_ctor_get(v_cfg_2015_, 18);
v_keywords_2037_ = lean_ctor_get(v_cfg_2015_, 19);
v_homepage_2038_ = lean_ctor_get(v_cfg_2015_, 20);
v_license_2039_ = lean_ctor_get(v_cfg_2015_, 21);
v_licenseFiles_2040_ = lean_ctor_get(v_cfg_2015_, 22);
v_readmeFile_2041_ = lean_ctor_get(v_cfg_2015_, 23);
v_reservoir_2042_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2043_ = lean_ctor_get(v_cfg_2015_, 24);
v_restoreAllArtifacts_x3f_2044_ = lean_ctor_get(v_cfg_2015_, 25);
v_libPrefixOnWindows_2045_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26 + 4);
v_allowImportAll_2046_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26 + 5);
v_fixedToolchain_2047_ = lean_ctor_get_uint8(v_cfg_2015_, sizeof(void*)*26 + 6);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_cfg_2015_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v_cfg_2015_, 16);
lean_dec(v_unused_2055_);
v___x_2049_ = v_cfg_2015_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2044_);
lean_inc(v_enableArtifactCache_x3f_2043_);
lean_inc(v_readmeFile_2041_);
lean_inc(v_licenseFiles_2040_);
lean_inc(v_license_2039_);
lean_inc(v_homepage_2038_);
lean_inc(v_keywords_2037_);
lean_inc(v_description_2036_);
lean_inc(v_versionTags_2035_);
lean_inc(v_lintDriverArgs_2034_);
lean_inc(v_lintDriver_2033_);
lean_inc(v_testDriverArgs_2032_);
lean_inc(v_testDriver_2031_);
lean_inc(v_buildArchive_2029_);
lean_inc(v_releaseRepo_2028_);
lean_inc(v_irDir_2027_);
lean_inc(v_binDir_2026_);
lean_inc(v_nativeLibDir_2025_);
lean_inc(v_leanLibDir_2024_);
lean_inc(v_buildDir_2023_);
lean_inc(v_srcDir_2022_);
lean_inc(v_moreGlobalServerArgs_2021_);
lean_inc(v_extraDepTargets_2019_);
lean_inc(v_toLeanConfig_2017_);
lean_inc(v_toWorkspaceConfig_2016_);
lean_dec(v_cfg_2015_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 16, v_val_2014_);
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_toWorkspaceConfig_2016_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_toLeanConfig_2017_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_extraDepTargets_2019_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_moreGlobalServerArgs_2021_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_srcDir_2022_);
lean_ctor_set(v_reuseFailAlloc_2053_, 5, v_buildDir_2023_);
lean_ctor_set(v_reuseFailAlloc_2053_, 6, v_leanLibDir_2024_);
lean_ctor_set(v_reuseFailAlloc_2053_, 7, v_nativeLibDir_2025_);
lean_ctor_set(v_reuseFailAlloc_2053_, 8, v_binDir_2026_);
lean_ctor_set(v_reuseFailAlloc_2053_, 9, v_irDir_2027_);
lean_ctor_set(v_reuseFailAlloc_2053_, 10, v_releaseRepo_2028_);
lean_ctor_set(v_reuseFailAlloc_2053_, 11, v_buildArchive_2029_);
lean_ctor_set(v_reuseFailAlloc_2053_, 12, v_testDriver_2031_);
lean_ctor_set(v_reuseFailAlloc_2053_, 13, v_testDriverArgs_2032_);
lean_ctor_set(v_reuseFailAlloc_2053_, 14, v_lintDriver_2033_);
lean_ctor_set(v_reuseFailAlloc_2053_, 15, v_lintDriverArgs_2034_);
lean_ctor_set(v_reuseFailAlloc_2053_, 16, v_val_2014_);
lean_ctor_set(v_reuseFailAlloc_2053_, 17, v_versionTags_2035_);
lean_ctor_set(v_reuseFailAlloc_2053_, 18, v_description_2036_);
lean_ctor_set(v_reuseFailAlloc_2053_, 19, v_keywords_2037_);
lean_ctor_set(v_reuseFailAlloc_2053_, 20, v_homepage_2038_);
lean_ctor_set(v_reuseFailAlloc_2053_, 21, v_license_2039_);
lean_ctor_set(v_reuseFailAlloc_2053_, 22, v_licenseFiles_2040_);
lean_ctor_set(v_reuseFailAlloc_2053_, 23, v_readmeFile_2041_);
lean_ctor_set(v_reuseFailAlloc_2053_, 24, v_enableArtifactCache_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 25, v_restoreAllArtifacts_x3f_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26, v_bootstrap_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26 + 1, v_precompileModules_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26 + 3, v_reservoir_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26 + 5, v_allowImportAll_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*26 + 6, v_fixedToolchain_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* v_f_2056_, lean_object* v_cfg_2057_){
_start:
{
lean_object* v_toWorkspaceConfig_2058_; lean_object* v_toLeanConfig_2059_; uint8_t v_bootstrap_2060_; lean_object* v_extraDepTargets_2061_; uint8_t v_precompileModules_2062_; lean_object* v_moreGlobalServerArgs_2063_; lean_object* v_srcDir_2064_; lean_object* v_buildDir_2065_; lean_object* v_leanLibDir_2066_; lean_object* v_nativeLibDir_2067_; lean_object* v_binDir_2068_; lean_object* v_irDir_2069_; lean_object* v_releaseRepo_2070_; lean_object* v_buildArchive_2071_; uint8_t v_preferReleaseBuild_2072_; lean_object* v_testDriver_2073_; lean_object* v_testDriverArgs_2074_; lean_object* v_lintDriver_2075_; lean_object* v_lintDriverArgs_2076_; lean_object* v_version_2077_; lean_object* v_versionTags_2078_; lean_object* v_description_2079_; lean_object* v_keywords_2080_; lean_object* v_homepage_2081_; lean_object* v_license_2082_; lean_object* v_licenseFiles_2083_; lean_object* v_readmeFile_2084_; uint8_t v_reservoir_2085_; lean_object* v_enableArtifactCache_x3f_2086_; lean_object* v_restoreAllArtifacts_x3f_2087_; uint8_t v_libPrefixOnWindows_2088_; uint8_t v_allowImportAll_2089_; uint8_t v_fixedToolchain_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2098_; 
v_toWorkspaceConfig_2058_ = lean_ctor_get(v_cfg_2057_, 0);
v_toLeanConfig_2059_ = lean_ctor_get(v_cfg_2057_, 1);
v_bootstrap_2060_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26);
v_extraDepTargets_2061_ = lean_ctor_get(v_cfg_2057_, 2);
v_precompileModules_2062_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2063_ = lean_ctor_get(v_cfg_2057_, 3);
v_srcDir_2064_ = lean_ctor_get(v_cfg_2057_, 4);
v_buildDir_2065_ = lean_ctor_get(v_cfg_2057_, 5);
v_leanLibDir_2066_ = lean_ctor_get(v_cfg_2057_, 6);
v_nativeLibDir_2067_ = lean_ctor_get(v_cfg_2057_, 7);
v_binDir_2068_ = lean_ctor_get(v_cfg_2057_, 8);
v_irDir_2069_ = lean_ctor_get(v_cfg_2057_, 9);
v_releaseRepo_2070_ = lean_ctor_get(v_cfg_2057_, 10);
v_buildArchive_2071_ = lean_ctor_get(v_cfg_2057_, 11);
v_preferReleaseBuild_2072_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26 + 2);
v_testDriver_2073_ = lean_ctor_get(v_cfg_2057_, 12);
v_testDriverArgs_2074_ = lean_ctor_get(v_cfg_2057_, 13);
v_lintDriver_2075_ = lean_ctor_get(v_cfg_2057_, 14);
v_lintDriverArgs_2076_ = lean_ctor_get(v_cfg_2057_, 15);
v_version_2077_ = lean_ctor_get(v_cfg_2057_, 16);
v_versionTags_2078_ = lean_ctor_get(v_cfg_2057_, 17);
v_description_2079_ = lean_ctor_get(v_cfg_2057_, 18);
v_keywords_2080_ = lean_ctor_get(v_cfg_2057_, 19);
v_homepage_2081_ = lean_ctor_get(v_cfg_2057_, 20);
v_license_2082_ = lean_ctor_get(v_cfg_2057_, 21);
v_licenseFiles_2083_ = lean_ctor_get(v_cfg_2057_, 22);
v_readmeFile_2084_ = lean_ctor_get(v_cfg_2057_, 23);
v_reservoir_2085_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2086_ = lean_ctor_get(v_cfg_2057_, 24);
v_restoreAllArtifacts_x3f_2087_ = lean_ctor_get(v_cfg_2057_, 25);
v_libPrefixOnWindows_2088_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26 + 4);
v_allowImportAll_2089_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26 + 5);
v_fixedToolchain_2090_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*26 + 6);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_cfg_2057_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2092_ = v_cfg_2057_;
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2087_);
lean_inc(v_enableArtifactCache_x3f_2086_);
lean_inc(v_readmeFile_2084_);
lean_inc(v_licenseFiles_2083_);
lean_inc(v_license_2082_);
lean_inc(v_homepage_2081_);
lean_inc(v_keywords_2080_);
lean_inc(v_description_2079_);
lean_inc(v_versionTags_2078_);
lean_inc(v_version_2077_);
lean_inc(v_lintDriverArgs_2076_);
lean_inc(v_lintDriver_2075_);
lean_inc(v_testDriverArgs_2074_);
lean_inc(v_testDriver_2073_);
lean_inc(v_buildArchive_2071_);
lean_inc(v_releaseRepo_2070_);
lean_inc(v_irDir_2069_);
lean_inc(v_binDir_2068_);
lean_inc(v_nativeLibDir_2067_);
lean_inc(v_leanLibDir_2066_);
lean_inc(v_buildDir_2065_);
lean_inc(v_srcDir_2064_);
lean_inc(v_moreGlobalServerArgs_2063_);
lean_inc(v_extraDepTargets_2061_);
lean_inc(v_toLeanConfig_2059_);
lean_inc(v_toWorkspaceConfig_2058_);
lean_dec(v_cfg_2057_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_apply_1(v_f_2056_, v_version_2077_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 16, v___x_2094_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_toWorkspaceConfig_2058_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_toLeanConfig_2059_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_extraDepTargets_2061_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_moreGlobalServerArgs_2063_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_srcDir_2064_);
lean_ctor_set(v_reuseFailAlloc_2097_, 5, v_buildDir_2065_);
lean_ctor_set(v_reuseFailAlloc_2097_, 6, v_leanLibDir_2066_);
lean_ctor_set(v_reuseFailAlloc_2097_, 7, v_nativeLibDir_2067_);
lean_ctor_set(v_reuseFailAlloc_2097_, 8, v_binDir_2068_);
lean_ctor_set(v_reuseFailAlloc_2097_, 9, v_irDir_2069_);
lean_ctor_set(v_reuseFailAlloc_2097_, 10, v_releaseRepo_2070_);
lean_ctor_set(v_reuseFailAlloc_2097_, 11, v_buildArchive_2071_);
lean_ctor_set(v_reuseFailAlloc_2097_, 12, v_testDriver_2073_);
lean_ctor_set(v_reuseFailAlloc_2097_, 13, v_testDriverArgs_2074_);
lean_ctor_set(v_reuseFailAlloc_2097_, 14, v_lintDriver_2075_);
lean_ctor_set(v_reuseFailAlloc_2097_, 15, v_lintDriverArgs_2076_);
lean_ctor_set(v_reuseFailAlloc_2097_, 16, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2097_, 17, v_versionTags_2078_);
lean_ctor_set(v_reuseFailAlloc_2097_, 18, v_description_2079_);
lean_ctor_set(v_reuseFailAlloc_2097_, 19, v_keywords_2080_);
lean_ctor_set(v_reuseFailAlloc_2097_, 20, v_homepage_2081_);
lean_ctor_set(v_reuseFailAlloc_2097_, 21, v_license_2082_);
lean_ctor_set(v_reuseFailAlloc_2097_, 22, v_licenseFiles_2083_);
lean_ctor_set(v_reuseFailAlloc_2097_, 23, v_readmeFile_2084_);
lean_ctor_set(v_reuseFailAlloc_2097_, 24, v_enableArtifactCache_x3f_2086_);
lean_ctor_set(v_reuseFailAlloc_2097_, 25, v_restoreAllArtifacts_x3f_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26, v_bootstrap_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26 + 1, v_precompileModules_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26 + 3, v_reservoir_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26 + 5, v_allowImportAll_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2097_, sizeof(void*)*26 + 6, v_fixedToolchain_2090_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* v_x_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* v_x_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lake_PackageConfig_version___proj___lam__3(v_x_2101_);
lean_dec_ref(v_x_2101_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2112_, lean_object* v_n_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2115_, lean_object* v_n_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lake_PackageConfig_version___proj(v_p_2115_, v_n_2116_);
lean_dec(v_n_2116_);
lean_dec(v_p_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2118_, lean_object* v_n_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lake_PackageConfig_version___proj(v_p_2118_, v_n_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2121_, lean_object* v_n_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lake_PackageConfig_version_instConfigField(v_p_2121_, v_n_2122_);
lean_dec(v_n_2122_);
lean_dec(v_p_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* v_cfg_2124_){
_start:
{
lean_object* v_versionTags_2125_; 
v_versionTags_2125_ = lean_ctor_get(v_cfg_2124_, 17);
lean_inc_ref(v_versionTags_2125_);
return v_versionTags_2125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* v_cfg_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lake_PackageConfig_versionTags___proj___lam__0(v_cfg_2126_);
lean_dec_ref(v_cfg_2126_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* v_val_2128_, lean_object* v_cfg_2129_){
_start:
{
lean_object* v_toWorkspaceConfig_2130_; lean_object* v_toLeanConfig_2131_; uint8_t v_bootstrap_2132_; lean_object* v_extraDepTargets_2133_; uint8_t v_precompileModules_2134_; lean_object* v_moreGlobalServerArgs_2135_; lean_object* v_srcDir_2136_; lean_object* v_buildDir_2137_; lean_object* v_leanLibDir_2138_; lean_object* v_nativeLibDir_2139_; lean_object* v_binDir_2140_; lean_object* v_irDir_2141_; lean_object* v_releaseRepo_2142_; lean_object* v_buildArchive_2143_; uint8_t v_preferReleaseBuild_2144_; lean_object* v_testDriver_2145_; lean_object* v_testDriverArgs_2146_; lean_object* v_lintDriver_2147_; lean_object* v_lintDriverArgs_2148_; lean_object* v_version_2149_; lean_object* v_description_2150_; lean_object* v_keywords_2151_; lean_object* v_homepage_2152_; lean_object* v_license_2153_; lean_object* v_licenseFiles_2154_; lean_object* v_readmeFile_2155_; uint8_t v_reservoir_2156_; lean_object* v_enableArtifactCache_x3f_2157_; lean_object* v_restoreAllArtifacts_x3f_2158_; uint8_t v_libPrefixOnWindows_2159_; uint8_t v_allowImportAll_2160_; uint8_t v_fixedToolchain_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v_toWorkspaceConfig_2130_ = lean_ctor_get(v_cfg_2129_, 0);
v_toLeanConfig_2131_ = lean_ctor_get(v_cfg_2129_, 1);
v_bootstrap_2132_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26);
v_extraDepTargets_2133_ = lean_ctor_get(v_cfg_2129_, 2);
v_precompileModules_2134_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2135_ = lean_ctor_get(v_cfg_2129_, 3);
v_srcDir_2136_ = lean_ctor_get(v_cfg_2129_, 4);
v_buildDir_2137_ = lean_ctor_get(v_cfg_2129_, 5);
v_leanLibDir_2138_ = lean_ctor_get(v_cfg_2129_, 6);
v_nativeLibDir_2139_ = lean_ctor_get(v_cfg_2129_, 7);
v_binDir_2140_ = lean_ctor_get(v_cfg_2129_, 8);
v_irDir_2141_ = lean_ctor_get(v_cfg_2129_, 9);
v_releaseRepo_2142_ = lean_ctor_get(v_cfg_2129_, 10);
v_buildArchive_2143_ = lean_ctor_get(v_cfg_2129_, 11);
v_preferReleaseBuild_2144_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26 + 2);
v_testDriver_2145_ = lean_ctor_get(v_cfg_2129_, 12);
v_testDriverArgs_2146_ = lean_ctor_get(v_cfg_2129_, 13);
v_lintDriver_2147_ = lean_ctor_get(v_cfg_2129_, 14);
v_lintDriverArgs_2148_ = lean_ctor_get(v_cfg_2129_, 15);
v_version_2149_ = lean_ctor_get(v_cfg_2129_, 16);
v_description_2150_ = lean_ctor_get(v_cfg_2129_, 18);
v_keywords_2151_ = lean_ctor_get(v_cfg_2129_, 19);
v_homepage_2152_ = lean_ctor_get(v_cfg_2129_, 20);
v_license_2153_ = lean_ctor_get(v_cfg_2129_, 21);
v_licenseFiles_2154_ = lean_ctor_get(v_cfg_2129_, 22);
v_readmeFile_2155_ = lean_ctor_get(v_cfg_2129_, 23);
v_reservoir_2156_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2157_ = lean_ctor_get(v_cfg_2129_, 24);
v_restoreAllArtifacts_x3f_2158_ = lean_ctor_get(v_cfg_2129_, 25);
v_libPrefixOnWindows_2159_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26 + 4);
v_allowImportAll_2160_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26 + 5);
v_fixedToolchain_2161_ = lean_ctor_get_uint8(v_cfg_2129_, sizeof(void*)*26 + 6);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_cfg_2129_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_cfg_2129_, 17);
lean_dec(v_unused_2169_);
v___x_2163_ = v_cfg_2129_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2158_);
lean_inc(v_enableArtifactCache_x3f_2157_);
lean_inc(v_readmeFile_2155_);
lean_inc(v_licenseFiles_2154_);
lean_inc(v_license_2153_);
lean_inc(v_homepage_2152_);
lean_inc(v_keywords_2151_);
lean_inc(v_description_2150_);
lean_inc(v_version_2149_);
lean_inc(v_lintDriverArgs_2148_);
lean_inc(v_lintDriver_2147_);
lean_inc(v_testDriverArgs_2146_);
lean_inc(v_testDriver_2145_);
lean_inc(v_buildArchive_2143_);
lean_inc(v_releaseRepo_2142_);
lean_inc(v_irDir_2141_);
lean_inc(v_binDir_2140_);
lean_inc(v_nativeLibDir_2139_);
lean_inc(v_leanLibDir_2138_);
lean_inc(v_buildDir_2137_);
lean_inc(v_srcDir_2136_);
lean_inc(v_moreGlobalServerArgs_2135_);
lean_inc(v_extraDepTargets_2133_);
lean_inc(v_toLeanConfig_2131_);
lean_inc(v_toWorkspaceConfig_2130_);
lean_dec(v_cfg_2129_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 17, v_val_2128_);
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_toWorkspaceConfig_2130_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_toLeanConfig_2131_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_extraDepTargets_2133_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_moreGlobalServerArgs_2135_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_srcDir_2136_);
lean_ctor_set(v_reuseFailAlloc_2167_, 5, v_buildDir_2137_);
lean_ctor_set(v_reuseFailAlloc_2167_, 6, v_leanLibDir_2138_);
lean_ctor_set(v_reuseFailAlloc_2167_, 7, v_nativeLibDir_2139_);
lean_ctor_set(v_reuseFailAlloc_2167_, 8, v_binDir_2140_);
lean_ctor_set(v_reuseFailAlloc_2167_, 9, v_irDir_2141_);
lean_ctor_set(v_reuseFailAlloc_2167_, 10, v_releaseRepo_2142_);
lean_ctor_set(v_reuseFailAlloc_2167_, 11, v_buildArchive_2143_);
lean_ctor_set(v_reuseFailAlloc_2167_, 12, v_testDriver_2145_);
lean_ctor_set(v_reuseFailAlloc_2167_, 13, v_testDriverArgs_2146_);
lean_ctor_set(v_reuseFailAlloc_2167_, 14, v_lintDriver_2147_);
lean_ctor_set(v_reuseFailAlloc_2167_, 15, v_lintDriverArgs_2148_);
lean_ctor_set(v_reuseFailAlloc_2167_, 16, v_version_2149_);
lean_ctor_set(v_reuseFailAlloc_2167_, 17, v_val_2128_);
lean_ctor_set(v_reuseFailAlloc_2167_, 18, v_description_2150_);
lean_ctor_set(v_reuseFailAlloc_2167_, 19, v_keywords_2151_);
lean_ctor_set(v_reuseFailAlloc_2167_, 20, v_homepage_2152_);
lean_ctor_set(v_reuseFailAlloc_2167_, 21, v_license_2153_);
lean_ctor_set(v_reuseFailAlloc_2167_, 22, v_licenseFiles_2154_);
lean_ctor_set(v_reuseFailAlloc_2167_, 23, v_readmeFile_2155_);
lean_ctor_set(v_reuseFailAlloc_2167_, 24, v_enableArtifactCache_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2167_, 25, v_restoreAllArtifacts_x3f_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26, v_bootstrap_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26 + 1, v_precompileModules_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26 + 3, v_reservoir_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26 + 5, v_allowImportAll_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*26 + 6, v_fixedToolchain_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* v_f_2170_, lean_object* v_cfg_2171_){
_start:
{
lean_object* v_toWorkspaceConfig_2172_; lean_object* v_toLeanConfig_2173_; uint8_t v_bootstrap_2174_; lean_object* v_extraDepTargets_2175_; uint8_t v_precompileModules_2176_; lean_object* v_moreGlobalServerArgs_2177_; lean_object* v_srcDir_2178_; lean_object* v_buildDir_2179_; lean_object* v_leanLibDir_2180_; lean_object* v_nativeLibDir_2181_; lean_object* v_binDir_2182_; lean_object* v_irDir_2183_; lean_object* v_releaseRepo_2184_; lean_object* v_buildArchive_2185_; uint8_t v_preferReleaseBuild_2186_; lean_object* v_testDriver_2187_; lean_object* v_testDriverArgs_2188_; lean_object* v_lintDriver_2189_; lean_object* v_lintDriverArgs_2190_; lean_object* v_version_2191_; lean_object* v_versionTags_2192_; lean_object* v_description_2193_; lean_object* v_keywords_2194_; lean_object* v_homepage_2195_; lean_object* v_license_2196_; lean_object* v_licenseFiles_2197_; lean_object* v_readmeFile_2198_; uint8_t v_reservoir_2199_; lean_object* v_enableArtifactCache_x3f_2200_; lean_object* v_restoreAllArtifacts_x3f_2201_; uint8_t v_libPrefixOnWindows_2202_; uint8_t v_allowImportAll_2203_; uint8_t v_fixedToolchain_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
v_toWorkspaceConfig_2172_ = lean_ctor_get(v_cfg_2171_, 0);
v_toLeanConfig_2173_ = lean_ctor_get(v_cfg_2171_, 1);
v_bootstrap_2174_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26);
v_extraDepTargets_2175_ = lean_ctor_get(v_cfg_2171_, 2);
v_precompileModules_2176_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2177_ = lean_ctor_get(v_cfg_2171_, 3);
v_srcDir_2178_ = lean_ctor_get(v_cfg_2171_, 4);
v_buildDir_2179_ = lean_ctor_get(v_cfg_2171_, 5);
v_leanLibDir_2180_ = lean_ctor_get(v_cfg_2171_, 6);
v_nativeLibDir_2181_ = lean_ctor_get(v_cfg_2171_, 7);
v_binDir_2182_ = lean_ctor_get(v_cfg_2171_, 8);
v_irDir_2183_ = lean_ctor_get(v_cfg_2171_, 9);
v_releaseRepo_2184_ = lean_ctor_get(v_cfg_2171_, 10);
v_buildArchive_2185_ = lean_ctor_get(v_cfg_2171_, 11);
v_preferReleaseBuild_2186_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26 + 2);
v_testDriver_2187_ = lean_ctor_get(v_cfg_2171_, 12);
v_testDriverArgs_2188_ = lean_ctor_get(v_cfg_2171_, 13);
v_lintDriver_2189_ = lean_ctor_get(v_cfg_2171_, 14);
v_lintDriverArgs_2190_ = lean_ctor_get(v_cfg_2171_, 15);
v_version_2191_ = lean_ctor_get(v_cfg_2171_, 16);
v_versionTags_2192_ = lean_ctor_get(v_cfg_2171_, 17);
v_description_2193_ = lean_ctor_get(v_cfg_2171_, 18);
v_keywords_2194_ = lean_ctor_get(v_cfg_2171_, 19);
v_homepage_2195_ = lean_ctor_get(v_cfg_2171_, 20);
v_license_2196_ = lean_ctor_get(v_cfg_2171_, 21);
v_licenseFiles_2197_ = lean_ctor_get(v_cfg_2171_, 22);
v_readmeFile_2198_ = lean_ctor_get(v_cfg_2171_, 23);
v_reservoir_2199_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2200_ = lean_ctor_get(v_cfg_2171_, 24);
v_restoreAllArtifacts_x3f_2201_ = lean_ctor_get(v_cfg_2171_, 25);
v_libPrefixOnWindows_2202_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26 + 4);
v_allowImportAll_2203_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26 + 5);
v_fixedToolchain_2204_ = lean_ctor_get_uint8(v_cfg_2171_, sizeof(void*)*26 + 6);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_cfg_2171_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2206_ = v_cfg_2171_;
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2201_);
lean_inc(v_enableArtifactCache_x3f_2200_);
lean_inc(v_readmeFile_2198_);
lean_inc(v_licenseFiles_2197_);
lean_inc(v_license_2196_);
lean_inc(v_homepage_2195_);
lean_inc(v_keywords_2194_);
lean_inc(v_description_2193_);
lean_inc(v_versionTags_2192_);
lean_inc(v_version_2191_);
lean_inc(v_lintDriverArgs_2190_);
lean_inc(v_lintDriver_2189_);
lean_inc(v_testDriverArgs_2188_);
lean_inc(v_testDriver_2187_);
lean_inc(v_buildArchive_2185_);
lean_inc(v_releaseRepo_2184_);
lean_inc(v_irDir_2183_);
lean_inc(v_binDir_2182_);
lean_inc(v_nativeLibDir_2181_);
lean_inc(v_leanLibDir_2180_);
lean_inc(v_buildDir_2179_);
lean_inc(v_srcDir_2178_);
lean_inc(v_moreGlobalServerArgs_2177_);
lean_inc(v_extraDepTargets_2175_);
lean_inc(v_toLeanConfig_2173_);
lean_inc(v_toWorkspaceConfig_2172_);
lean_dec(v_cfg_2171_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_apply_1(v_f_2170_, v_versionTags_2192_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 17, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_toWorkspaceConfig_2172_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_toLeanConfig_2173_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_extraDepTargets_2175_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_moreGlobalServerArgs_2177_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_srcDir_2178_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v_buildDir_2179_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_leanLibDir_2180_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v_nativeLibDir_2181_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v_binDir_2182_);
lean_ctor_set(v_reuseFailAlloc_2211_, 9, v_irDir_2183_);
lean_ctor_set(v_reuseFailAlloc_2211_, 10, v_releaseRepo_2184_);
lean_ctor_set(v_reuseFailAlloc_2211_, 11, v_buildArchive_2185_);
lean_ctor_set(v_reuseFailAlloc_2211_, 12, v_testDriver_2187_);
lean_ctor_set(v_reuseFailAlloc_2211_, 13, v_testDriverArgs_2188_);
lean_ctor_set(v_reuseFailAlloc_2211_, 14, v_lintDriver_2189_);
lean_ctor_set(v_reuseFailAlloc_2211_, 15, v_lintDriverArgs_2190_);
lean_ctor_set(v_reuseFailAlloc_2211_, 16, v_version_2191_);
lean_ctor_set(v_reuseFailAlloc_2211_, 17, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2211_, 18, v_description_2193_);
lean_ctor_set(v_reuseFailAlloc_2211_, 19, v_keywords_2194_);
lean_ctor_set(v_reuseFailAlloc_2211_, 20, v_homepage_2195_);
lean_ctor_set(v_reuseFailAlloc_2211_, 21, v_license_2196_);
lean_ctor_set(v_reuseFailAlloc_2211_, 22, v_licenseFiles_2197_);
lean_ctor_set(v_reuseFailAlloc_2211_, 23, v_readmeFile_2198_);
lean_ctor_set(v_reuseFailAlloc_2211_, 24, v_enableArtifactCache_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2211_, 25, v_restoreAllArtifacts_x3f_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26, v_bootstrap_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26 + 1, v_precompileModules_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26 + 3, v_reservoir_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26 + 5, v_allowImportAll_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*26 + 6, v_fixedToolchain_2204_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* v_x_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lake_defaultVersionTags;
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* v_x_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lake_PackageConfig_versionTags___proj___lam__3(v_x_2215_);
lean_dec_ref(v_x_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2226_, lean_object* v_n_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2229_, lean_object* v_n_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lake_PackageConfig_versionTags___proj(v_p_2229_, v_n_2230_);
lean_dec(v_n_2230_);
lean_dec(v_p_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2232_, lean_object* v_n_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lake_PackageConfig_versionTags___proj(v_p_2232_, v_n_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2235_, lean_object* v_n_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2235_, v_n_2236_);
lean_dec(v_n_2236_);
lean_dec(v_p_2235_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* v_cfg_2238_){
_start:
{
lean_object* v_description_2239_; 
v_description_2239_ = lean_ctor_get(v_cfg_2238_, 18);
lean_inc_ref(v_description_2239_);
return v_description_2239_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* v_cfg_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lake_PackageConfig_description___proj___lam__0(v_cfg_2240_);
lean_dec_ref(v_cfg_2240_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* v_val_2242_, lean_object* v_cfg_2243_){
_start:
{
lean_object* v_toWorkspaceConfig_2244_; lean_object* v_toLeanConfig_2245_; uint8_t v_bootstrap_2246_; lean_object* v_extraDepTargets_2247_; uint8_t v_precompileModules_2248_; lean_object* v_moreGlobalServerArgs_2249_; lean_object* v_srcDir_2250_; lean_object* v_buildDir_2251_; lean_object* v_leanLibDir_2252_; lean_object* v_nativeLibDir_2253_; lean_object* v_binDir_2254_; lean_object* v_irDir_2255_; lean_object* v_releaseRepo_2256_; lean_object* v_buildArchive_2257_; uint8_t v_preferReleaseBuild_2258_; lean_object* v_testDriver_2259_; lean_object* v_testDriverArgs_2260_; lean_object* v_lintDriver_2261_; lean_object* v_lintDriverArgs_2262_; lean_object* v_version_2263_; lean_object* v_versionTags_2264_; lean_object* v_keywords_2265_; lean_object* v_homepage_2266_; lean_object* v_license_2267_; lean_object* v_licenseFiles_2268_; lean_object* v_readmeFile_2269_; uint8_t v_reservoir_2270_; lean_object* v_enableArtifactCache_x3f_2271_; lean_object* v_restoreAllArtifacts_x3f_2272_; uint8_t v_libPrefixOnWindows_2273_; uint8_t v_allowImportAll_2274_; uint8_t v_fixedToolchain_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_toWorkspaceConfig_2244_ = lean_ctor_get(v_cfg_2243_, 0);
v_toLeanConfig_2245_ = lean_ctor_get(v_cfg_2243_, 1);
v_bootstrap_2246_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26);
v_extraDepTargets_2247_ = lean_ctor_get(v_cfg_2243_, 2);
v_precompileModules_2248_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2249_ = lean_ctor_get(v_cfg_2243_, 3);
v_srcDir_2250_ = lean_ctor_get(v_cfg_2243_, 4);
v_buildDir_2251_ = lean_ctor_get(v_cfg_2243_, 5);
v_leanLibDir_2252_ = lean_ctor_get(v_cfg_2243_, 6);
v_nativeLibDir_2253_ = lean_ctor_get(v_cfg_2243_, 7);
v_binDir_2254_ = lean_ctor_get(v_cfg_2243_, 8);
v_irDir_2255_ = lean_ctor_get(v_cfg_2243_, 9);
v_releaseRepo_2256_ = lean_ctor_get(v_cfg_2243_, 10);
v_buildArchive_2257_ = lean_ctor_get(v_cfg_2243_, 11);
v_preferReleaseBuild_2258_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26 + 2);
v_testDriver_2259_ = lean_ctor_get(v_cfg_2243_, 12);
v_testDriverArgs_2260_ = lean_ctor_get(v_cfg_2243_, 13);
v_lintDriver_2261_ = lean_ctor_get(v_cfg_2243_, 14);
v_lintDriverArgs_2262_ = lean_ctor_get(v_cfg_2243_, 15);
v_version_2263_ = lean_ctor_get(v_cfg_2243_, 16);
v_versionTags_2264_ = lean_ctor_get(v_cfg_2243_, 17);
v_keywords_2265_ = lean_ctor_get(v_cfg_2243_, 19);
v_homepage_2266_ = lean_ctor_get(v_cfg_2243_, 20);
v_license_2267_ = lean_ctor_get(v_cfg_2243_, 21);
v_licenseFiles_2268_ = lean_ctor_get(v_cfg_2243_, 22);
v_readmeFile_2269_ = lean_ctor_get(v_cfg_2243_, 23);
v_reservoir_2270_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2271_ = lean_ctor_get(v_cfg_2243_, 24);
v_restoreAllArtifacts_x3f_2272_ = lean_ctor_get(v_cfg_2243_, 25);
v_libPrefixOnWindows_2273_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26 + 4);
v_allowImportAll_2274_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26 + 5);
v_fixedToolchain_2275_ = lean_ctor_get_uint8(v_cfg_2243_, sizeof(void*)*26 + 6);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_cfg_2243_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v_cfg_2243_, 18);
lean_dec(v_unused_2283_);
v___x_2277_ = v_cfg_2243_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2272_);
lean_inc(v_enableArtifactCache_x3f_2271_);
lean_inc(v_readmeFile_2269_);
lean_inc(v_licenseFiles_2268_);
lean_inc(v_license_2267_);
lean_inc(v_homepage_2266_);
lean_inc(v_keywords_2265_);
lean_inc(v_versionTags_2264_);
lean_inc(v_version_2263_);
lean_inc(v_lintDriverArgs_2262_);
lean_inc(v_lintDriver_2261_);
lean_inc(v_testDriverArgs_2260_);
lean_inc(v_testDriver_2259_);
lean_inc(v_buildArchive_2257_);
lean_inc(v_releaseRepo_2256_);
lean_inc(v_irDir_2255_);
lean_inc(v_binDir_2254_);
lean_inc(v_nativeLibDir_2253_);
lean_inc(v_leanLibDir_2252_);
lean_inc(v_buildDir_2251_);
lean_inc(v_srcDir_2250_);
lean_inc(v_moreGlobalServerArgs_2249_);
lean_inc(v_extraDepTargets_2247_);
lean_inc(v_toLeanConfig_2245_);
lean_inc(v_toWorkspaceConfig_2244_);
lean_dec(v_cfg_2243_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 18, v_val_2242_);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_toWorkspaceConfig_2244_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_toLeanConfig_2245_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_extraDepTargets_2247_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_moreGlobalServerArgs_2249_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_srcDir_2250_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_buildDir_2251_);
lean_ctor_set(v_reuseFailAlloc_2281_, 6, v_leanLibDir_2252_);
lean_ctor_set(v_reuseFailAlloc_2281_, 7, v_nativeLibDir_2253_);
lean_ctor_set(v_reuseFailAlloc_2281_, 8, v_binDir_2254_);
lean_ctor_set(v_reuseFailAlloc_2281_, 9, v_irDir_2255_);
lean_ctor_set(v_reuseFailAlloc_2281_, 10, v_releaseRepo_2256_);
lean_ctor_set(v_reuseFailAlloc_2281_, 11, v_buildArchive_2257_);
lean_ctor_set(v_reuseFailAlloc_2281_, 12, v_testDriver_2259_);
lean_ctor_set(v_reuseFailAlloc_2281_, 13, v_testDriverArgs_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 14, v_lintDriver_2261_);
lean_ctor_set(v_reuseFailAlloc_2281_, 15, v_lintDriverArgs_2262_);
lean_ctor_set(v_reuseFailAlloc_2281_, 16, v_version_2263_);
lean_ctor_set(v_reuseFailAlloc_2281_, 17, v_versionTags_2264_);
lean_ctor_set(v_reuseFailAlloc_2281_, 18, v_val_2242_);
lean_ctor_set(v_reuseFailAlloc_2281_, 19, v_keywords_2265_);
lean_ctor_set(v_reuseFailAlloc_2281_, 20, v_homepage_2266_);
lean_ctor_set(v_reuseFailAlloc_2281_, 21, v_license_2267_);
lean_ctor_set(v_reuseFailAlloc_2281_, 22, v_licenseFiles_2268_);
lean_ctor_set(v_reuseFailAlloc_2281_, 23, v_readmeFile_2269_);
lean_ctor_set(v_reuseFailAlloc_2281_, 24, v_enableArtifactCache_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2281_, 25, v_restoreAllArtifacts_x3f_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26, v_bootstrap_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26 + 1, v_precompileModules_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26 + 3, v_reservoir_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26 + 5, v_allowImportAll_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*26 + 6, v_fixedToolchain_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* v_f_2284_, lean_object* v_cfg_2285_){
_start:
{
lean_object* v_toWorkspaceConfig_2286_; lean_object* v_toLeanConfig_2287_; uint8_t v_bootstrap_2288_; lean_object* v_extraDepTargets_2289_; uint8_t v_precompileModules_2290_; lean_object* v_moreGlobalServerArgs_2291_; lean_object* v_srcDir_2292_; lean_object* v_buildDir_2293_; lean_object* v_leanLibDir_2294_; lean_object* v_nativeLibDir_2295_; lean_object* v_binDir_2296_; lean_object* v_irDir_2297_; lean_object* v_releaseRepo_2298_; lean_object* v_buildArchive_2299_; uint8_t v_preferReleaseBuild_2300_; lean_object* v_testDriver_2301_; lean_object* v_testDriverArgs_2302_; lean_object* v_lintDriver_2303_; lean_object* v_lintDriverArgs_2304_; lean_object* v_version_2305_; lean_object* v_versionTags_2306_; lean_object* v_description_2307_; lean_object* v_keywords_2308_; lean_object* v_homepage_2309_; lean_object* v_license_2310_; lean_object* v_licenseFiles_2311_; lean_object* v_readmeFile_2312_; uint8_t v_reservoir_2313_; lean_object* v_enableArtifactCache_x3f_2314_; lean_object* v_restoreAllArtifacts_x3f_2315_; uint8_t v_libPrefixOnWindows_2316_; uint8_t v_allowImportAll_2317_; uint8_t v_fixedToolchain_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
v_toWorkspaceConfig_2286_ = lean_ctor_get(v_cfg_2285_, 0);
v_toLeanConfig_2287_ = lean_ctor_get(v_cfg_2285_, 1);
v_bootstrap_2288_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26);
v_extraDepTargets_2289_ = lean_ctor_get(v_cfg_2285_, 2);
v_precompileModules_2290_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2291_ = lean_ctor_get(v_cfg_2285_, 3);
v_srcDir_2292_ = lean_ctor_get(v_cfg_2285_, 4);
v_buildDir_2293_ = lean_ctor_get(v_cfg_2285_, 5);
v_leanLibDir_2294_ = lean_ctor_get(v_cfg_2285_, 6);
v_nativeLibDir_2295_ = lean_ctor_get(v_cfg_2285_, 7);
v_binDir_2296_ = lean_ctor_get(v_cfg_2285_, 8);
v_irDir_2297_ = lean_ctor_get(v_cfg_2285_, 9);
v_releaseRepo_2298_ = lean_ctor_get(v_cfg_2285_, 10);
v_buildArchive_2299_ = lean_ctor_get(v_cfg_2285_, 11);
v_preferReleaseBuild_2300_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26 + 2);
v_testDriver_2301_ = lean_ctor_get(v_cfg_2285_, 12);
v_testDriverArgs_2302_ = lean_ctor_get(v_cfg_2285_, 13);
v_lintDriver_2303_ = lean_ctor_get(v_cfg_2285_, 14);
v_lintDriverArgs_2304_ = lean_ctor_get(v_cfg_2285_, 15);
v_version_2305_ = lean_ctor_get(v_cfg_2285_, 16);
v_versionTags_2306_ = lean_ctor_get(v_cfg_2285_, 17);
v_description_2307_ = lean_ctor_get(v_cfg_2285_, 18);
v_keywords_2308_ = lean_ctor_get(v_cfg_2285_, 19);
v_homepage_2309_ = lean_ctor_get(v_cfg_2285_, 20);
v_license_2310_ = lean_ctor_get(v_cfg_2285_, 21);
v_licenseFiles_2311_ = lean_ctor_get(v_cfg_2285_, 22);
v_readmeFile_2312_ = lean_ctor_get(v_cfg_2285_, 23);
v_reservoir_2313_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2314_ = lean_ctor_get(v_cfg_2285_, 24);
v_restoreAllArtifacts_x3f_2315_ = lean_ctor_get(v_cfg_2285_, 25);
v_libPrefixOnWindows_2316_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26 + 4);
v_allowImportAll_2317_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26 + 5);
v_fixedToolchain_2318_ = lean_ctor_get_uint8(v_cfg_2285_, sizeof(void*)*26 + 6);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_cfg_2285_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v_cfg_2285_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2315_);
lean_inc(v_enableArtifactCache_x3f_2314_);
lean_inc(v_readmeFile_2312_);
lean_inc(v_licenseFiles_2311_);
lean_inc(v_license_2310_);
lean_inc(v_homepage_2309_);
lean_inc(v_keywords_2308_);
lean_inc(v_description_2307_);
lean_inc(v_versionTags_2306_);
lean_inc(v_version_2305_);
lean_inc(v_lintDriverArgs_2304_);
lean_inc(v_lintDriver_2303_);
lean_inc(v_testDriverArgs_2302_);
lean_inc(v_testDriver_2301_);
lean_inc(v_buildArchive_2299_);
lean_inc(v_releaseRepo_2298_);
lean_inc(v_irDir_2297_);
lean_inc(v_binDir_2296_);
lean_inc(v_nativeLibDir_2295_);
lean_inc(v_leanLibDir_2294_);
lean_inc(v_buildDir_2293_);
lean_inc(v_srcDir_2292_);
lean_inc(v_moreGlobalServerArgs_2291_);
lean_inc(v_extraDepTargets_2289_);
lean_inc(v_toLeanConfig_2287_);
lean_inc(v_toWorkspaceConfig_2286_);
lean_dec(v_cfg_2285_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = lean_apply_1(v_f_2284_, v_description_2307_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 18, v___x_2322_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_toWorkspaceConfig_2286_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_toLeanConfig_2287_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_extraDepTargets_2289_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_moreGlobalServerArgs_2291_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_srcDir_2292_);
lean_ctor_set(v_reuseFailAlloc_2325_, 5, v_buildDir_2293_);
lean_ctor_set(v_reuseFailAlloc_2325_, 6, v_leanLibDir_2294_);
lean_ctor_set(v_reuseFailAlloc_2325_, 7, v_nativeLibDir_2295_);
lean_ctor_set(v_reuseFailAlloc_2325_, 8, v_binDir_2296_);
lean_ctor_set(v_reuseFailAlloc_2325_, 9, v_irDir_2297_);
lean_ctor_set(v_reuseFailAlloc_2325_, 10, v_releaseRepo_2298_);
lean_ctor_set(v_reuseFailAlloc_2325_, 11, v_buildArchive_2299_);
lean_ctor_set(v_reuseFailAlloc_2325_, 12, v_testDriver_2301_);
lean_ctor_set(v_reuseFailAlloc_2325_, 13, v_testDriverArgs_2302_);
lean_ctor_set(v_reuseFailAlloc_2325_, 14, v_lintDriver_2303_);
lean_ctor_set(v_reuseFailAlloc_2325_, 15, v_lintDriverArgs_2304_);
lean_ctor_set(v_reuseFailAlloc_2325_, 16, v_version_2305_);
lean_ctor_set(v_reuseFailAlloc_2325_, 17, v_versionTags_2306_);
lean_ctor_set(v_reuseFailAlloc_2325_, 18, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2325_, 19, v_keywords_2308_);
lean_ctor_set(v_reuseFailAlloc_2325_, 20, v_homepage_2309_);
lean_ctor_set(v_reuseFailAlloc_2325_, 21, v_license_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 22, v_licenseFiles_2311_);
lean_ctor_set(v_reuseFailAlloc_2325_, 23, v_readmeFile_2312_);
lean_ctor_set(v_reuseFailAlloc_2325_, 24, v_enableArtifactCache_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2325_, 25, v_restoreAllArtifacts_x3f_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26, v_bootstrap_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26 + 1, v_precompileModules_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26 + 3, v_reservoir_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26 + 5, v_allowImportAll_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*26 + 6, v_fixedToolchain_2318_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2335_, lean_object* v_n_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2338_, lean_object* v_n_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lake_PackageConfig_description___proj(v_p_2338_, v_n_2339_);
lean_dec(v_n_2339_);
lean_dec(v_p_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2341_, lean_object* v_n_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lake_PackageConfig_description___proj(v_p_2341_, v_n_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2344_, lean_object* v_n_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lake_PackageConfig_description_instConfigField(v_p_2344_, v_n_2345_);
lean_dec(v_n_2345_);
lean_dec(v_p_2344_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* v_cfg_2347_){
_start:
{
lean_object* v_keywords_2348_; 
v_keywords_2348_ = lean_ctor_get(v_cfg_2347_, 19);
lean_inc_ref(v_keywords_2348_);
return v_keywords_2348_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* v_cfg_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lake_PackageConfig_keywords___proj___lam__0(v_cfg_2349_);
lean_dec_ref(v_cfg_2349_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* v_val_2351_, lean_object* v_cfg_2352_){
_start:
{
lean_object* v_toWorkspaceConfig_2353_; lean_object* v_toLeanConfig_2354_; uint8_t v_bootstrap_2355_; lean_object* v_extraDepTargets_2356_; uint8_t v_precompileModules_2357_; lean_object* v_moreGlobalServerArgs_2358_; lean_object* v_srcDir_2359_; lean_object* v_buildDir_2360_; lean_object* v_leanLibDir_2361_; lean_object* v_nativeLibDir_2362_; lean_object* v_binDir_2363_; lean_object* v_irDir_2364_; lean_object* v_releaseRepo_2365_; lean_object* v_buildArchive_2366_; uint8_t v_preferReleaseBuild_2367_; lean_object* v_testDriver_2368_; lean_object* v_testDriverArgs_2369_; lean_object* v_lintDriver_2370_; lean_object* v_lintDriverArgs_2371_; lean_object* v_version_2372_; lean_object* v_versionTags_2373_; lean_object* v_description_2374_; lean_object* v_homepage_2375_; lean_object* v_license_2376_; lean_object* v_licenseFiles_2377_; lean_object* v_readmeFile_2378_; uint8_t v_reservoir_2379_; lean_object* v_enableArtifactCache_x3f_2380_; lean_object* v_restoreAllArtifacts_x3f_2381_; uint8_t v_libPrefixOnWindows_2382_; uint8_t v_allowImportAll_2383_; uint8_t v_fixedToolchain_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_toWorkspaceConfig_2353_ = lean_ctor_get(v_cfg_2352_, 0);
v_toLeanConfig_2354_ = lean_ctor_get(v_cfg_2352_, 1);
v_bootstrap_2355_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26);
v_extraDepTargets_2356_ = lean_ctor_get(v_cfg_2352_, 2);
v_precompileModules_2357_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2358_ = lean_ctor_get(v_cfg_2352_, 3);
v_srcDir_2359_ = lean_ctor_get(v_cfg_2352_, 4);
v_buildDir_2360_ = lean_ctor_get(v_cfg_2352_, 5);
v_leanLibDir_2361_ = lean_ctor_get(v_cfg_2352_, 6);
v_nativeLibDir_2362_ = lean_ctor_get(v_cfg_2352_, 7);
v_binDir_2363_ = lean_ctor_get(v_cfg_2352_, 8);
v_irDir_2364_ = lean_ctor_get(v_cfg_2352_, 9);
v_releaseRepo_2365_ = lean_ctor_get(v_cfg_2352_, 10);
v_buildArchive_2366_ = lean_ctor_get(v_cfg_2352_, 11);
v_preferReleaseBuild_2367_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26 + 2);
v_testDriver_2368_ = lean_ctor_get(v_cfg_2352_, 12);
v_testDriverArgs_2369_ = lean_ctor_get(v_cfg_2352_, 13);
v_lintDriver_2370_ = lean_ctor_get(v_cfg_2352_, 14);
v_lintDriverArgs_2371_ = lean_ctor_get(v_cfg_2352_, 15);
v_version_2372_ = lean_ctor_get(v_cfg_2352_, 16);
v_versionTags_2373_ = lean_ctor_get(v_cfg_2352_, 17);
v_description_2374_ = lean_ctor_get(v_cfg_2352_, 18);
v_homepage_2375_ = lean_ctor_get(v_cfg_2352_, 20);
v_license_2376_ = lean_ctor_get(v_cfg_2352_, 21);
v_licenseFiles_2377_ = lean_ctor_get(v_cfg_2352_, 22);
v_readmeFile_2378_ = lean_ctor_get(v_cfg_2352_, 23);
v_reservoir_2379_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2380_ = lean_ctor_get(v_cfg_2352_, 24);
v_restoreAllArtifacts_x3f_2381_ = lean_ctor_get(v_cfg_2352_, 25);
v_libPrefixOnWindows_2382_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26 + 4);
v_allowImportAll_2383_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26 + 5);
v_fixedToolchain_2384_ = lean_ctor_get_uint8(v_cfg_2352_, sizeof(void*)*26 + 6);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_cfg_2352_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; 
v_unused_2392_ = lean_ctor_get(v_cfg_2352_, 19);
lean_dec(v_unused_2392_);
v___x_2386_ = v_cfg_2352_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2381_);
lean_inc(v_enableArtifactCache_x3f_2380_);
lean_inc(v_readmeFile_2378_);
lean_inc(v_licenseFiles_2377_);
lean_inc(v_license_2376_);
lean_inc(v_homepage_2375_);
lean_inc(v_description_2374_);
lean_inc(v_versionTags_2373_);
lean_inc(v_version_2372_);
lean_inc(v_lintDriverArgs_2371_);
lean_inc(v_lintDriver_2370_);
lean_inc(v_testDriverArgs_2369_);
lean_inc(v_testDriver_2368_);
lean_inc(v_buildArchive_2366_);
lean_inc(v_releaseRepo_2365_);
lean_inc(v_irDir_2364_);
lean_inc(v_binDir_2363_);
lean_inc(v_nativeLibDir_2362_);
lean_inc(v_leanLibDir_2361_);
lean_inc(v_buildDir_2360_);
lean_inc(v_srcDir_2359_);
lean_inc(v_moreGlobalServerArgs_2358_);
lean_inc(v_extraDepTargets_2356_);
lean_inc(v_toLeanConfig_2354_);
lean_inc(v_toWorkspaceConfig_2353_);
lean_dec(v_cfg_2352_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 19, v_val_2351_);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_toWorkspaceConfig_2353_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_toLeanConfig_2354_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_extraDepTargets_2356_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v_moreGlobalServerArgs_2358_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v_srcDir_2359_);
lean_ctor_set(v_reuseFailAlloc_2390_, 5, v_buildDir_2360_);
lean_ctor_set(v_reuseFailAlloc_2390_, 6, v_leanLibDir_2361_);
lean_ctor_set(v_reuseFailAlloc_2390_, 7, v_nativeLibDir_2362_);
lean_ctor_set(v_reuseFailAlloc_2390_, 8, v_binDir_2363_);
lean_ctor_set(v_reuseFailAlloc_2390_, 9, v_irDir_2364_);
lean_ctor_set(v_reuseFailAlloc_2390_, 10, v_releaseRepo_2365_);
lean_ctor_set(v_reuseFailAlloc_2390_, 11, v_buildArchive_2366_);
lean_ctor_set(v_reuseFailAlloc_2390_, 12, v_testDriver_2368_);
lean_ctor_set(v_reuseFailAlloc_2390_, 13, v_testDriverArgs_2369_);
lean_ctor_set(v_reuseFailAlloc_2390_, 14, v_lintDriver_2370_);
lean_ctor_set(v_reuseFailAlloc_2390_, 15, v_lintDriverArgs_2371_);
lean_ctor_set(v_reuseFailAlloc_2390_, 16, v_version_2372_);
lean_ctor_set(v_reuseFailAlloc_2390_, 17, v_versionTags_2373_);
lean_ctor_set(v_reuseFailAlloc_2390_, 18, v_description_2374_);
lean_ctor_set(v_reuseFailAlloc_2390_, 19, v_val_2351_);
lean_ctor_set(v_reuseFailAlloc_2390_, 20, v_homepage_2375_);
lean_ctor_set(v_reuseFailAlloc_2390_, 21, v_license_2376_);
lean_ctor_set(v_reuseFailAlloc_2390_, 22, v_licenseFiles_2377_);
lean_ctor_set(v_reuseFailAlloc_2390_, 23, v_readmeFile_2378_);
lean_ctor_set(v_reuseFailAlloc_2390_, 24, v_enableArtifactCache_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2390_, 25, v_restoreAllArtifacts_x3f_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26, v_bootstrap_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26 + 1, v_precompileModules_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26 + 3, v_reservoir_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26 + 5, v_allowImportAll_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*26 + 6, v_fixedToolchain_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* v_f_2393_, lean_object* v_cfg_2394_){
_start:
{
lean_object* v_toWorkspaceConfig_2395_; lean_object* v_toLeanConfig_2396_; uint8_t v_bootstrap_2397_; lean_object* v_extraDepTargets_2398_; uint8_t v_precompileModules_2399_; lean_object* v_moreGlobalServerArgs_2400_; lean_object* v_srcDir_2401_; lean_object* v_buildDir_2402_; lean_object* v_leanLibDir_2403_; lean_object* v_nativeLibDir_2404_; lean_object* v_binDir_2405_; lean_object* v_irDir_2406_; lean_object* v_releaseRepo_2407_; lean_object* v_buildArchive_2408_; uint8_t v_preferReleaseBuild_2409_; lean_object* v_testDriver_2410_; lean_object* v_testDriverArgs_2411_; lean_object* v_lintDriver_2412_; lean_object* v_lintDriverArgs_2413_; lean_object* v_version_2414_; lean_object* v_versionTags_2415_; lean_object* v_description_2416_; lean_object* v_keywords_2417_; lean_object* v_homepage_2418_; lean_object* v_license_2419_; lean_object* v_licenseFiles_2420_; lean_object* v_readmeFile_2421_; uint8_t v_reservoir_2422_; lean_object* v_enableArtifactCache_x3f_2423_; lean_object* v_restoreAllArtifacts_x3f_2424_; uint8_t v_libPrefixOnWindows_2425_; uint8_t v_allowImportAll_2426_; uint8_t v_fixedToolchain_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_toWorkspaceConfig_2395_ = lean_ctor_get(v_cfg_2394_, 0);
v_toLeanConfig_2396_ = lean_ctor_get(v_cfg_2394_, 1);
v_bootstrap_2397_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26);
v_extraDepTargets_2398_ = lean_ctor_get(v_cfg_2394_, 2);
v_precompileModules_2399_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2400_ = lean_ctor_get(v_cfg_2394_, 3);
v_srcDir_2401_ = lean_ctor_get(v_cfg_2394_, 4);
v_buildDir_2402_ = lean_ctor_get(v_cfg_2394_, 5);
v_leanLibDir_2403_ = lean_ctor_get(v_cfg_2394_, 6);
v_nativeLibDir_2404_ = lean_ctor_get(v_cfg_2394_, 7);
v_binDir_2405_ = lean_ctor_get(v_cfg_2394_, 8);
v_irDir_2406_ = lean_ctor_get(v_cfg_2394_, 9);
v_releaseRepo_2407_ = lean_ctor_get(v_cfg_2394_, 10);
v_buildArchive_2408_ = lean_ctor_get(v_cfg_2394_, 11);
v_preferReleaseBuild_2409_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26 + 2);
v_testDriver_2410_ = lean_ctor_get(v_cfg_2394_, 12);
v_testDriverArgs_2411_ = lean_ctor_get(v_cfg_2394_, 13);
v_lintDriver_2412_ = lean_ctor_get(v_cfg_2394_, 14);
v_lintDriverArgs_2413_ = lean_ctor_get(v_cfg_2394_, 15);
v_version_2414_ = lean_ctor_get(v_cfg_2394_, 16);
v_versionTags_2415_ = lean_ctor_get(v_cfg_2394_, 17);
v_description_2416_ = lean_ctor_get(v_cfg_2394_, 18);
v_keywords_2417_ = lean_ctor_get(v_cfg_2394_, 19);
v_homepage_2418_ = lean_ctor_get(v_cfg_2394_, 20);
v_license_2419_ = lean_ctor_get(v_cfg_2394_, 21);
v_licenseFiles_2420_ = lean_ctor_get(v_cfg_2394_, 22);
v_readmeFile_2421_ = lean_ctor_get(v_cfg_2394_, 23);
v_reservoir_2422_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2423_ = lean_ctor_get(v_cfg_2394_, 24);
v_restoreAllArtifacts_x3f_2424_ = lean_ctor_get(v_cfg_2394_, 25);
v_libPrefixOnWindows_2425_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26 + 4);
v_allowImportAll_2426_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26 + 5);
v_fixedToolchain_2427_ = lean_ctor_get_uint8(v_cfg_2394_, sizeof(void*)*26 + 6);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_cfg_2394_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v_cfg_2394_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2424_);
lean_inc(v_enableArtifactCache_x3f_2423_);
lean_inc(v_readmeFile_2421_);
lean_inc(v_licenseFiles_2420_);
lean_inc(v_license_2419_);
lean_inc(v_homepage_2418_);
lean_inc(v_keywords_2417_);
lean_inc(v_description_2416_);
lean_inc(v_versionTags_2415_);
lean_inc(v_version_2414_);
lean_inc(v_lintDriverArgs_2413_);
lean_inc(v_lintDriver_2412_);
lean_inc(v_testDriverArgs_2411_);
lean_inc(v_testDriver_2410_);
lean_inc(v_buildArchive_2408_);
lean_inc(v_releaseRepo_2407_);
lean_inc(v_irDir_2406_);
lean_inc(v_binDir_2405_);
lean_inc(v_nativeLibDir_2404_);
lean_inc(v_leanLibDir_2403_);
lean_inc(v_buildDir_2402_);
lean_inc(v_srcDir_2401_);
lean_inc(v_moreGlobalServerArgs_2400_);
lean_inc(v_extraDepTargets_2398_);
lean_inc(v_toLeanConfig_2396_);
lean_inc(v_toWorkspaceConfig_2395_);
lean_dec(v_cfg_2394_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_apply_1(v_f_2393_, v_keywords_2417_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 19, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_toWorkspaceConfig_2395_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_toLeanConfig_2396_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_extraDepTargets_2398_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_moreGlobalServerArgs_2400_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v_srcDir_2401_);
lean_ctor_set(v_reuseFailAlloc_2434_, 5, v_buildDir_2402_);
lean_ctor_set(v_reuseFailAlloc_2434_, 6, v_leanLibDir_2403_);
lean_ctor_set(v_reuseFailAlloc_2434_, 7, v_nativeLibDir_2404_);
lean_ctor_set(v_reuseFailAlloc_2434_, 8, v_binDir_2405_);
lean_ctor_set(v_reuseFailAlloc_2434_, 9, v_irDir_2406_);
lean_ctor_set(v_reuseFailAlloc_2434_, 10, v_releaseRepo_2407_);
lean_ctor_set(v_reuseFailAlloc_2434_, 11, v_buildArchive_2408_);
lean_ctor_set(v_reuseFailAlloc_2434_, 12, v_testDriver_2410_);
lean_ctor_set(v_reuseFailAlloc_2434_, 13, v_testDriverArgs_2411_);
lean_ctor_set(v_reuseFailAlloc_2434_, 14, v_lintDriver_2412_);
lean_ctor_set(v_reuseFailAlloc_2434_, 15, v_lintDriverArgs_2413_);
lean_ctor_set(v_reuseFailAlloc_2434_, 16, v_version_2414_);
lean_ctor_set(v_reuseFailAlloc_2434_, 17, v_versionTags_2415_);
lean_ctor_set(v_reuseFailAlloc_2434_, 18, v_description_2416_);
lean_ctor_set(v_reuseFailAlloc_2434_, 19, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2434_, 20, v_homepage_2418_);
lean_ctor_set(v_reuseFailAlloc_2434_, 21, v_license_2419_);
lean_ctor_set(v_reuseFailAlloc_2434_, 22, v_licenseFiles_2420_);
lean_ctor_set(v_reuseFailAlloc_2434_, 23, v_readmeFile_2421_);
lean_ctor_set(v_reuseFailAlloc_2434_, 24, v_enableArtifactCache_x3f_2423_);
lean_ctor_set(v_reuseFailAlloc_2434_, 25, v_restoreAllArtifacts_x3f_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26, v_bootstrap_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26 + 1, v_precompileModules_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26 + 3, v_reservoir_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26 + 5, v_allowImportAll_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2434_, sizeof(void*)*26 + 6, v_fixedToolchain_2427_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2444_, lean_object* v_n_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2447_, lean_object* v_n_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lake_PackageConfig_keywords___proj(v_p_2447_, v_n_2448_);
lean_dec(v_n_2448_);
lean_dec(v_p_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2450_, lean_object* v_n_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lake_PackageConfig_keywords___proj(v_p_2450_, v_n_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2453_, lean_object* v_n_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2453_, v_n_2454_);
lean_dec(v_n_2454_);
lean_dec(v_p_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* v_cfg_2456_){
_start:
{
lean_object* v_homepage_2457_; 
v_homepage_2457_ = lean_ctor_get(v_cfg_2456_, 20);
lean_inc_ref(v_homepage_2457_);
return v_homepage_2457_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* v_cfg_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lake_PackageConfig_homepage___proj___lam__0(v_cfg_2458_);
lean_dec_ref(v_cfg_2458_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* v_val_2460_, lean_object* v_cfg_2461_){
_start:
{
lean_object* v_toWorkspaceConfig_2462_; lean_object* v_toLeanConfig_2463_; uint8_t v_bootstrap_2464_; lean_object* v_extraDepTargets_2465_; uint8_t v_precompileModules_2466_; lean_object* v_moreGlobalServerArgs_2467_; lean_object* v_srcDir_2468_; lean_object* v_buildDir_2469_; lean_object* v_leanLibDir_2470_; lean_object* v_nativeLibDir_2471_; lean_object* v_binDir_2472_; lean_object* v_irDir_2473_; lean_object* v_releaseRepo_2474_; lean_object* v_buildArchive_2475_; uint8_t v_preferReleaseBuild_2476_; lean_object* v_testDriver_2477_; lean_object* v_testDriverArgs_2478_; lean_object* v_lintDriver_2479_; lean_object* v_lintDriverArgs_2480_; lean_object* v_version_2481_; lean_object* v_versionTags_2482_; lean_object* v_description_2483_; lean_object* v_keywords_2484_; lean_object* v_license_2485_; lean_object* v_licenseFiles_2486_; lean_object* v_readmeFile_2487_; uint8_t v_reservoir_2488_; lean_object* v_enableArtifactCache_x3f_2489_; lean_object* v_restoreAllArtifacts_x3f_2490_; uint8_t v_libPrefixOnWindows_2491_; uint8_t v_allowImportAll_2492_; uint8_t v_fixedToolchain_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_toWorkspaceConfig_2462_ = lean_ctor_get(v_cfg_2461_, 0);
v_toLeanConfig_2463_ = lean_ctor_get(v_cfg_2461_, 1);
v_bootstrap_2464_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26);
v_extraDepTargets_2465_ = lean_ctor_get(v_cfg_2461_, 2);
v_precompileModules_2466_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2467_ = lean_ctor_get(v_cfg_2461_, 3);
v_srcDir_2468_ = lean_ctor_get(v_cfg_2461_, 4);
v_buildDir_2469_ = lean_ctor_get(v_cfg_2461_, 5);
v_leanLibDir_2470_ = lean_ctor_get(v_cfg_2461_, 6);
v_nativeLibDir_2471_ = lean_ctor_get(v_cfg_2461_, 7);
v_binDir_2472_ = lean_ctor_get(v_cfg_2461_, 8);
v_irDir_2473_ = lean_ctor_get(v_cfg_2461_, 9);
v_releaseRepo_2474_ = lean_ctor_get(v_cfg_2461_, 10);
v_buildArchive_2475_ = lean_ctor_get(v_cfg_2461_, 11);
v_preferReleaseBuild_2476_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26 + 2);
v_testDriver_2477_ = lean_ctor_get(v_cfg_2461_, 12);
v_testDriverArgs_2478_ = lean_ctor_get(v_cfg_2461_, 13);
v_lintDriver_2479_ = lean_ctor_get(v_cfg_2461_, 14);
v_lintDriverArgs_2480_ = lean_ctor_get(v_cfg_2461_, 15);
v_version_2481_ = lean_ctor_get(v_cfg_2461_, 16);
v_versionTags_2482_ = lean_ctor_get(v_cfg_2461_, 17);
v_description_2483_ = lean_ctor_get(v_cfg_2461_, 18);
v_keywords_2484_ = lean_ctor_get(v_cfg_2461_, 19);
v_license_2485_ = lean_ctor_get(v_cfg_2461_, 21);
v_licenseFiles_2486_ = lean_ctor_get(v_cfg_2461_, 22);
v_readmeFile_2487_ = lean_ctor_get(v_cfg_2461_, 23);
v_reservoir_2488_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2489_ = lean_ctor_get(v_cfg_2461_, 24);
v_restoreAllArtifacts_x3f_2490_ = lean_ctor_get(v_cfg_2461_, 25);
v_libPrefixOnWindows_2491_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26 + 4);
v_allowImportAll_2492_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26 + 5);
v_fixedToolchain_2493_ = lean_ctor_get_uint8(v_cfg_2461_, sizeof(void*)*26 + 6);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_cfg_2461_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_cfg_2461_, 20);
lean_dec(v_unused_2501_);
v___x_2495_ = v_cfg_2461_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2490_);
lean_inc(v_enableArtifactCache_x3f_2489_);
lean_inc(v_readmeFile_2487_);
lean_inc(v_licenseFiles_2486_);
lean_inc(v_license_2485_);
lean_inc(v_keywords_2484_);
lean_inc(v_description_2483_);
lean_inc(v_versionTags_2482_);
lean_inc(v_version_2481_);
lean_inc(v_lintDriverArgs_2480_);
lean_inc(v_lintDriver_2479_);
lean_inc(v_testDriverArgs_2478_);
lean_inc(v_testDriver_2477_);
lean_inc(v_buildArchive_2475_);
lean_inc(v_releaseRepo_2474_);
lean_inc(v_irDir_2473_);
lean_inc(v_binDir_2472_);
lean_inc(v_nativeLibDir_2471_);
lean_inc(v_leanLibDir_2470_);
lean_inc(v_buildDir_2469_);
lean_inc(v_srcDir_2468_);
lean_inc(v_moreGlobalServerArgs_2467_);
lean_inc(v_extraDepTargets_2465_);
lean_inc(v_toLeanConfig_2463_);
lean_inc(v_toWorkspaceConfig_2462_);
lean_dec(v_cfg_2461_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 20, v_val_2460_);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_toWorkspaceConfig_2462_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_toLeanConfig_2463_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_extraDepTargets_2465_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_moreGlobalServerArgs_2467_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v_srcDir_2468_);
lean_ctor_set(v_reuseFailAlloc_2499_, 5, v_buildDir_2469_);
lean_ctor_set(v_reuseFailAlloc_2499_, 6, v_leanLibDir_2470_);
lean_ctor_set(v_reuseFailAlloc_2499_, 7, v_nativeLibDir_2471_);
lean_ctor_set(v_reuseFailAlloc_2499_, 8, v_binDir_2472_);
lean_ctor_set(v_reuseFailAlloc_2499_, 9, v_irDir_2473_);
lean_ctor_set(v_reuseFailAlloc_2499_, 10, v_releaseRepo_2474_);
lean_ctor_set(v_reuseFailAlloc_2499_, 11, v_buildArchive_2475_);
lean_ctor_set(v_reuseFailAlloc_2499_, 12, v_testDriver_2477_);
lean_ctor_set(v_reuseFailAlloc_2499_, 13, v_testDriverArgs_2478_);
lean_ctor_set(v_reuseFailAlloc_2499_, 14, v_lintDriver_2479_);
lean_ctor_set(v_reuseFailAlloc_2499_, 15, v_lintDriverArgs_2480_);
lean_ctor_set(v_reuseFailAlloc_2499_, 16, v_version_2481_);
lean_ctor_set(v_reuseFailAlloc_2499_, 17, v_versionTags_2482_);
lean_ctor_set(v_reuseFailAlloc_2499_, 18, v_description_2483_);
lean_ctor_set(v_reuseFailAlloc_2499_, 19, v_keywords_2484_);
lean_ctor_set(v_reuseFailAlloc_2499_, 20, v_val_2460_);
lean_ctor_set(v_reuseFailAlloc_2499_, 21, v_license_2485_);
lean_ctor_set(v_reuseFailAlloc_2499_, 22, v_licenseFiles_2486_);
lean_ctor_set(v_reuseFailAlloc_2499_, 23, v_readmeFile_2487_);
lean_ctor_set(v_reuseFailAlloc_2499_, 24, v_enableArtifactCache_x3f_2489_);
lean_ctor_set(v_reuseFailAlloc_2499_, 25, v_restoreAllArtifacts_x3f_2490_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26, v_bootstrap_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26 + 1, v_precompileModules_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26 + 3, v_reservoir_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26 + 5, v_allowImportAll_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*26 + 6, v_fixedToolchain_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* v_f_2502_, lean_object* v_cfg_2503_){
_start:
{
lean_object* v_toWorkspaceConfig_2504_; lean_object* v_toLeanConfig_2505_; uint8_t v_bootstrap_2506_; lean_object* v_extraDepTargets_2507_; uint8_t v_precompileModules_2508_; lean_object* v_moreGlobalServerArgs_2509_; lean_object* v_srcDir_2510_; lean_object* v_buildDir_2511_; lean_object* v_leanLibDir_2512_; lean_object* v_nativeLibDir_2513_; lean_object* v_binDir_2514_; lean_object* v_irDir_2515_; lean_object* v_releaseRepo_2516_; lean_object* v_buildArchive_2517_; uint8_t v_preferReleaseBuild_2518_; lean_object* v_testDriver_2519_; lean_object* v_testDriverArgs_2520_; lean_object* v_lintDriver_2521_; lean_object* v_lintDriverArgs_2522_; lean_object* v_version_2523_; lean_object* v_versionTags_2524_; lean_object* v_description_2525_; lean_object* v_keywords_2526_; lean_object* v_homepage_2527_; lean_object* v_license_2528_; lean_object* v_licenseFiles_2529_; lean_object* v_readmeFile_2530_; uint8_t v_reservoir_2531_; lean_object* v_enableArtifactCache_x3f_2532_; lean_object* v_restoreAllArtifacts_x3f_2533_; uint8_t v_libPrefixOnWindows_2534_; uint8_t v_allowImportAll_2535_; uint8_t v_fixedToolchain_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
v_toWorkspaceConfig_2504_ = lean_ctor_get(v_cfg_2503_, 0);
v_toLeanConfig_2505_ = lean_ctor_get(v_cfg_2503_, 1);
v_bootstrap_2506_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26);
v_extraDepTargets_2507_ = lean_ctor_get(v_cfg_2503_, 2);
v_precompileModules_2508_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2509_ = lean_ctor_get(v_cfg_2503_, 3);
v_srcDir_2510_ = lean_ctor_get(v_cfg_2503_, 4);
v_buildDir_2511_ = lean_ctor_get(v_cfg_2503_, 5);
v_leanLibDir_2512_ = lean_ctor_get(v_cfg_2503_, 6);
v_nativeLibDir_2513_ = lean_ctor_get(v_cfg_2503_, 7);
v_binDir_2514_ = lean_ctor_get(v_cfg_2503_, 8);
v_irDir_2515_ = lean_ctor_get(v_cfg_2503_, 9);
v_releaseRepo_2516_ = lean_ctor_get(v_cfg_2503_, 10);
v_buildArchive_2517_ = lean_ctor_get(v_cfg_2503_, 11);
v_preferReleaseBuild_2518_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26 + 2);
v_testDriver_2519_ = lean_ctor_get(v_cfg_2503_, 12);
v_testDriverArgs_2520_ = lean_ctor_get(v_cfg_2503_, 13);
v_lintDriver_2521_ = lean_ctor_get(v_cfg_2503_, 14);
v_lintDriverArgs_2522_ = lean_ctor_get(v_cfg_2503_, 15);
v_version_2523_ = lean_ctor_get(v_cfg_2503_, 16);
v_versionTags_2524_ = lean_ctor_get(v_cfg_2503_, 17);
v_description_2525_ = lean_ctor_get(v_cfg_2503_, 18);
v_keywords_2526_ = lean_ctor_get(v_cfg_2503_, 19);
v_homepage_2527_ = lean_ctor_get(v_cfg_2503_, 20);
v_license_2528_ = lean_ctor_get(v_cfg_2503_, 21);
v_licenseFiles_2529_ = lean_ctor_get(v_cfg_2503_, 22);
v_readmeFile_2530_ = lean_ctor_get(v_cfg_2503_, 23);
v_reservoir_2531_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2532_ = lean_ctor_get(v_cfg_2503_, 24);
v_restoreAllArtifacts_x3f_2533_ = lean_ctor_get(v_cfg_2503_, 25);
v_libPrefixOnWindows_2534_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26 + 4);
v_allowImportAll_2535_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26 + 5);
v_fixedToolchain_2536_ = lean_ctor_get_uint8(v_cfg_2503_, sizeof(void*)*26 + 6);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_cfg_2503_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v_cfg_2503_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2533_);
lean_inc(v_enableArtifactCache_x3f_2532_);
lean_inc(v_readmeFile_2530_);
lean_inc(v_licenseFiles_2529_);
lean_inc(v_license_2528_);
lean_inc(v_homepage_2527_);
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
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = lean_apply_1(v_f_2502_, v_homepage_2527_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 20, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_toWorkspaceConfig_2504_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_toLeanConfig_2505_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_extraDepTargets_2507_);
lean_ctor_set(v_reuseFailAlloc_2543_, 3, v_moreGlobalServerArgs_2509_);
lean_ctor_set(v_reuseFailAlloc_2543_, 4, v_srcDir_2510_);
lean_ctor_set(v_reuseFailAlloc_2543_, 5, v_buildDir_2511_);
lean_ctor_set(v_reuseFailAlloc_2543_, 6, v_leanLibDir_2512_);
lean_ctor_set(v_reuseFailAlloc_2543_, 7, v_nativeLibDir_2513_);
lean_ctor_set(v_reuseFailAlloc_2543_, 8, v_binDir_2514_);
lean_ctor_set(v_reuseFailAlloc_2543_, 9, v_irDir_2515_);
lean_ctor_set(v_reuseFailAlloc_2543_, 10, v_releaseRepo_2516_);
lean_ctor_set(v_reuseFailAlloc_2543_, 11, v_buildArchive_2517_);
lean_ctor_set(v_reuseFailAlloc_2543_, 12, v_testDriver_2519_);
lean_ctor_set(v_reuseFailAlloc_2543_, 13, v_testDriverArgs_2520_);
lean_ctor_set(v_reuseFailAlloc_2543_, 14, v_lintDriver_2521_);
lean_ctor_set(v_reuseFailAlloc_2543_, 15, v_lintDriverArgs_2522_);
lean_ctor_set(v_reuseFailAlloc_2543_, 16, v_version_2523_);
lean_ctor_set(v_reuseFailAlloc_2543_, 17, v_versionTags_2524_);
lean_ctor_set(v_reuseFailAlloc_2543_, 18, v_description_2525_);
lean_ctor_set(v_reuseFailAlloc_2543_, 19, v_keywords_2526_);
lean_ctor_set(v_reuseFailAlloc_2543_, 20, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2543_, 21, v_license_2528_);
lean_ctor_set(v_reuseFailAlloc_2543_, 22, v_licenseFiles_2529_);
lean_ctor_set(v_reuseFailAlloc_2543_, 23, v_readmeFile_2530_);
lean_ctor_set(v_reuseFailAlloc_2543_, 24, v_enableArtifactCache_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2543_, 25, v_restoreAllArtifacts_x3f_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26, v_bootstrap_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26 + 1, v_precompileModules_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26 + 3, v_reservoir_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26 + 5, v_allowImportAll_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*26 + 6, v_fixedToolchain_2536_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2553_, lean_object* v_n_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2556_, lean_object* v_n_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lake_PackageConfig_homepage___proj(v_p_2556_, v_n_2557_);
lean_dec(v_n_2557_);
lean_dec(v_p_2556_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2559_, lean_object* v_n_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lake_PackageConfig_homepage___proj(v_p_2559_, v_n_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2562_, lean_object* v_n_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2562_, v_n_2563_);
lean_dec(v_n_2563_);
lean_dec(v_p_2562_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* v_cfg_2565_){
_start:
{
lean_object* v_license_2566_; 
v_license_2566_ = lean_ctor_get(v_cfg_2565_, 21);
lean_inc_ref(v_license_2566_);
return v_license_2566_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* v_cfg_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lake_PackageConfig_license___proj___lam__0(v_cfg_2567_);
lean_dec_ref(v_cfg_2567_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* v_val_2569_, lean_object* v_cfg_2570_){
_start:
{
lean_object* v_toWorkspaceConfig_2571_; lean_object* v_toLeanConfig_2572_; uint8_t v_bootstrap_2573_; lean_object* v_extraDepTargets_2574_; uint8_t v_precompileModules_2575_; lean_object* v_moreGlobalServerArgs_2576_; lean_object* v_srcDir_2577_; lean_object* v_buildDir_2578_; lean_object* v_leanLibDir_2579_; lean_object* v_nativeLibDir_2580_; lean_object* v_binDir_2581_; lean_object* v_irDir_2582_; lean_object* v_releaseRepo_2583_; lean_object* v_buildArchive_2584_; uint8_t v_preferReleaseBuild_2585_; lean_object* v_testDriver_2586_; lean_object* v_testDriverArgs_2587_; lean_object* v_lintDriver_2588_; lean_object* v_lintDriverArgs_2589_; lean_object* v_version_2590_; lean_object* v_versionTags_2591_; lean_object* v_description_2592_; lean_object* v_keywords_2593_; lean_object* v_homepage_2594_; lean_object* v_licenseFiles_2595_; lean_object* v_readmeFile_2596_; uint8_t v_reservoir_2597_; lean_object* v_enableArtifactCache_x3f_2598_; lean_object* v_restoreAllArtifacts_x3f_2599_; uint8_t v_libPrefixOnWindows_2600_; uint8_t v_allowImportAll_2601_; uint8_t v_fixedToolchain_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_toWorkspaceConfig_2571_ = lean_ctor_get(v_cfg_2570_, 0);
v_toLeanConfig_2572_ = lean_ctor_get(v_cfg_2570_, 1);
v_bootstrap_2573_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26);
v_extraDepTargets_2574_ = lean_ctor_get(v_cfg_2570_, 2);
v_precompileModules_2575_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2576_ = lean_ctor_get(v_cfg_2570_, 3);
v_srcDir_2577_ = lean_ctor_get(v_cfg_2570_, 4);
v_buildDir_2578_ = lean_ctor_get(v_cfg_2570_, 5);
v_leanLibDir_2579_ = lean_ctor_get(v_cfg_2570_, 6);
v_nativeLibDir_2580_ = lean_ctor_get(v_cfg_2570_, 7);
v_binDir_2581_ = lean_ctor_get(v_cfg_2570_, 8);
v_irDir_2582_ = lean_ctor_get(v_cfg_2570_, 9);
v_releaseRepo_2583_ = lean_ctor_get(v_cfg_2570_, 10);
v_buildArchive_2584_ = lean_ctor_get(v_cfg_2570_, 11);
v_preferReleaseBuild_2585_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26 + 2);
v_testDriver_2586_ = lean_ctor_get(v_cfg_2570_, 12);
v_testDriverArgs_2587_ = lean_ctor_get(v_cfg_2570_, 13);
v_lintDriver_2588_ = lean_ctor_get(v_cfg_2570_, 14);
v_lintDriverArgs_2589_ = lean_ctor_get(v_cfg_2570_, 15);
v_version_2590_ = lean_ctor_get(v_cfg_2570_, 16);
v_versionTags_2591_ = lean_ctor_get(v_cfg_2570_, 17);
v_description_2592_ = lean_ctor_get(v_cfg_2570_, 18);
v_keywords_2593_ = lean_ctor_get(v_cfg_2570_, 19);
v_homepage_2594_ = lean_ctor_get(v_cfg_2570_, 20);
v_licenseFiles_2595_ = lean_ctor_get(v_cfg_2570_, 22);
v_readmeFile_2596_ = lean_ctor_get(v_cfg_2570_, 23);
v_reservoir_2597_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2598_ = lean_ctor_get(v_cfg_2570_, 24);
v_restoreAllArtifacts_x3f_2599_ = lean_ctor_get(v_cfg_2570_, 25);
v_libPrefixOnWindows_2600_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26 + 4);
v_allowImportAll_2601_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26 + 5);
v_fixedToolchain_2602_ = lean_ctor_get_uint8(v_cfg_2570_, sizeof(void*)*26 + 6);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_cfg_2570_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v_cfg_2570_, 21);
lean_dec(v_unused_2610_);
v___x_2604_ = v_cfg_2570_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2599_);
lean_inc(v_enableArtifactCache_x3f_2598_);
lean_inc(v_readmeFile_2596_);
lean_inc(v_licenseFiles_2595_);
lean_inc(v_homepage_2594_);
lean_inc(v_keywords_2593_);
lean_inc(v_description_2592_);
lean_inc(v_versionTags_2591_);
lean_inc(v_version_2590_);
lean_inc(v_lintDriverArgs_2589_);
lean_inc(v_lintDriver_2588_);
lean_inc(v_testDriverArgs_2587_);
lean_inc(v_testDriver_2586_);
lean_inc(v_buildArchive_2584_);
lean_inc(v_releaseRepo_2583_);
lean_inc(v_irDir_2582_);
lean_inc(v_binDir_2581_);
lean_inc(v_nativeLibDir_2580_);
lean_inc(v_leanLibDir_2579_);
lean_inc(v_buildDir_2578_);
lean_inc(v_srcDir_2577_);
lean_inc(v_moreGlobalServerArgs_2576_);
lean_inc(v_extraDepTargets_2574_);
lean_inc(v_toLeanConfig_2572_);
lean_inc(v_toWorkspaceConfig_2571_);
lean_dec(v_cfg_2570_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 21, v_val_2569_);
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_toWorkspaceConfig_2571_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_toLeanConfig_2572_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_extraDepTargets_2574_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_moreGlobalServerArgs_2576_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_srcDir_2577_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v_buildDir_2578_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_leanLibDir_2579_);
lean_ctor_set(v_reuseFailAlloc_2608_, 7, v_nativeLibDir_2580_);
lean_ctor_set(v_reuseFailAlloc_2608_, 8, v_binDir_2581_);
lean_ctor_set(v_reuseFailAlloc_2608_, 9, v_irDir_2582_);
lean_ctor_set(v_reuseFailAlloc_2608_, 10, v_releaseRepo_2583_);
lean_ctor_set(v_reuseFailAlloc_2608_, 11, v_buildArchive_2584_);
lean_ctor_set(v_reuseFailAlloc_2608_, 12, v_testDriver_2586_);
lean_ctor_set(v_reuseFailAlloc_2608_, 13, v_testDriverArgs_2587_);
lean_ctor_set(v_reuseFailAlloc_2608_, 14, v_lintDriver_2588_);
lean_ctor_set(v_reuseFailAlloc_2608_, 15, v_lintDriverArgs_2589_);
lean_ctor_set(v_reuseFailAlloc_2608_, 16, v_version_2590_);
lean_ctor_set(v_reuseFailAlloc_2608_, 17, v_versionTags_2591_);
lean_ctor_set(v_reuseFailAlloc_2608_, 18, v_description_2592_);
lean_ctor_set(v_reuseFailAlloc_2608_, 19, v_keywords_2593_);
lean_ctor_set(v_reuseFailAlloc_2608_, 20, v_homepage_2594_);
lean_ctor_set(v_reuseFailAlloc_2608_, 21, v_val_2569_);
lean_ctor_set(v_reuseFailAlloc_2608_, 22, v_licenseFiles_2595_);
lean_ctor_set(v_reuseFailAlloc_2608_, 23, v_readmeFile_2596_);
lean_ctor_set(v_reuseFailAlloc_2608_, 24, v_enableArtifactCache_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2608_, 25, v_restoreAllArtifacts_x3f_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26, v_bootstrap_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26 + 1, v_precompileModules_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26 + 3, v_reservoir_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26 + 5, v_allowImportAll_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*26 + 6, v_fixedToolchain_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* v_f_2611_, lean_object* v_cfg_2612_){
_start:
{
lean_object* v_toWorkspaceConfig_2613_; lean_object* v_toLeanConfig_2614_; uint8_t v_bootstrap_2615_; lean_object* v_extraDepTargets_2616_; uint8_t v_precompileModules_2617_; lean_object* v_moreGlobalServerArgs_2618_; lean_object* v_srcDir_2619_; lean_object* v_buildDir_2620_; lean_object* v_leanLibDir_2621_; lean_object* v_nativeLibDir_2622_; lean_object* v_binDir_2623_; lean_object* v_irDir_2624_; lean_object* v_releaseRepo_2625_; lean_object* v_buildArchive_2626_; uint8_t v_preferReleaseBuild_2627_; lean_object* v_testDriver_2628_; lean_object* v_testDriverArgs_2629_; lean_object* v_lintDriver_2630_; lean_object* v_lintDriverArgs_2631_; lean_object* v_version_2632_; lean_object* v_versionTags_2633_; lean_object* v_description_2634_; lean_object* v_keywords_2635_; lean_object* v_homepage_2636_; lean_object* v_license_2637_; lean_object* v_licenseFiles_2638_; lean_object* v_readmeFile_2639_; uint8_t v_reservoir_2640_; lean_object* v_enableArtifactCache_x3f_2641_; lean_object* v_restoreAllArtifacts_x3f_2642_; uint8_t v_libPrefixOnWindows_2643_; uint8_t v_allowImportAll_2644_; uint8_t v_fixedToolchain_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2653_; 
v_toWorkspaceConfig_2613_ = lean_ctor_get(v_cfg_2612_, 0);
v_toLeanConfig_2614_ = lean_ctor_get(v_cfg_2612_, 1);
v_bootstrap_2615_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26);
v_extraDepTargets_2616_ = lean_ctor_get(v_cfg_2612_, 2);
v_precompileModules_2617_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2618_ = lean_ctor_get(v_cfg_2612_, 3);
v_srcDir_2619_ = lean_ctor_get(v_cfg_2612_, 4);
v_buildDir_2620_ = lean_ctor_get(v_cfg_2612_, 5);
v_leanLibDir_2621_ = lean_ctor_get(v_cfg_2612_, 6);
v_nativeLibDir_2622_ = lean_ctor_get(v_cfg_2612_, 7);
v_binDir_2623_ = lean_ctor_get(v_cfg_2612_, 8);
v_irDir_2624_ = lean_ctor_get(v_cfg_2612_, 9);
v_releaseRepo_2625_ = lean_ctor_get(v_cfg_2612_, 10);
v_buildArchive_2626_ = lean_ctor_get(v_cfg_2612_, 11);
v_preferReleaseBuild_2627_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26 + 2);
v_testDriver_2628_ = lean_ctor_get(v_cfg_2612_, 12);
v_testDriverArgs_2629_ = lean_ctor_get(v_cfg_2612_, 13);
v_lintDriver_2630_ = lean_ctor_get(v_cfg_2612_, 14);
v_lintDriverArgs_2631_ = lean_ctor_get(v_cfg_2612_, 15);
v_version_2632_ = lean_ctor_get(v_cfg_2612_, 16);
v_versionTags_2633_ = lean_ctor_get(v_cfg_2612_, 17);
v_description_2634_ = lean_ctor_get(v_cfg_2612_, 18);
v_keywords_2635_ = lean_ctor_get(v_cfg_2612_, 19);
v_homepage_2636_ = lean_ctor_get(v_cfg_2612_, 20);
v_license_2637_ = lean_ctor_get(v_cfg_2612_, 21);
v_licenseFiles_2638_ = lean_ctor_get(v_cfg_2612_, 22);
v_readmeFile_2639_ = lean_ctor_get(v_cfg_2612_, 23);
v_reservoir_2640_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2641_ = lean_ctor_get(v_cfg_2612_, 24);
v_restoreAllArtifacts_x3f_2642_ = lean_ctor_get(v_cfg_2612_, 25);
v_libPrefixOnWindows_2643_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26 + 4);
v_allowImportAll_2644_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26 + 5);
v_fixedToolchain_2645_ = lean_ctor_get_uint8(v_cfg_2612_, sizeof(void*)*26 + 6);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_cfg_2612_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2647_ = v_cfg_2612_;
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2642_);
lean_inc(v_enableArtifactCache_x3f_2641_);
lean_inc(v_readmeFile_2639_);
lean_inc(v_licenseFiles_2638_);
lean_inc(v_license_2637_);
lean_inc(v_homepage_2636_);
lean_inc(v_keywords_2635_);
lean_inc(v_description_2634_);
lean_inc(v_versionTags_2633_);
lean_inc(v_version_2632_);
lean_inc(v_lintDriverArgs_2631_);
lean_inc(v_lintDriver_2630_);
lean_inc(v_testDriverArgs_2629_);
lean_inc(v_testDriver_2628_);
lean_inc(v_buildArchive_2626_);
lean_inc(v_releaseRepo_2625_);
lean_inc(v_irDir_2624_);
lean_inc(v_binDir_2623_);
lean_inc(v_nativeLibDir_2622_);
lean_inc(v_leanLibDir_2621_);
lean_inc(v_buildDir_2620_);
lean_inc(v_srcDir_2619_);
lean_inc(v_moreGlobalServerArgs_2618_);
lean_inc(v_extraDepTargets_2616_);
lean_inc(v_toLeanConfig_2614_);
lean_inc(v_toWorkspaceConfig_2613_);
lean_dec(v_cfg_2612_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_apply_1(v_f_2611_, v_license_2637_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 21, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_toWorkspaceConfig_2613_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_toLeanConfig_2614_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_extraDepTargets_2616_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_moreGlobalServerArgs_2618_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_srcDir_2619_);
lean_ctor_set(v_reuseFailAlloc_2652_, 5, v_buildDir_2620_);
lean_ctor_set(v_reuseFailAlloc_2652_, 6, v_leanLibDir_2621_);
lean_ctor_set(v_reuseFailAlloc_2652_, 7, v_nativeLibDir_2622_);
lean_ctor_set(v_reuseFailAlloc_2652_, 8, v_binDir_2623_);
lean_ctor_set(v_reuseFailAlloc_2652_, 9, v_irDir_2624_);
lean_ctor_set(v_reuseFailAlloc_2652_, 10, v_releaseRepo_2625_);
lean_ctor_set(v_reuseFailAlloc_2652_, 11, v_buildArchive_2626_);
lean_ctor_set(v_reuseFailAlloc_2652_, 12, v_testDriver_2628_);
lean_ctor_set(v_reuseFailAlloc_2652_, 13, v_testDriverArgs_2629_);
lean_ctor_set(v_reuseFailAlloc_2652_, 14, v_lintDriver_2630_);
lean_ctor_set(v_reuseFailAlloc_2652_, 15, v_lintDriverArgs_2631_);
lean_ctor_set(v_reuseFailAlloc_2652_, 16, v_version_2632_);
lean_ctor_set(v_reuseFailAlloc_2652_, 17, v_versionTags_2633_);
lean_ctor_set(v_reuseFailAlloc_2652_, 18, v_description_2634_);
lean_ctor_set(v_reuseFailAlloc_2652_, 19, v_keywords_2635_);
lean_ctor_set(v_reuseFailAlloc_2652_, 20, v_homepage_2636_);
lean_ctor_set(v_reuseFailAlloc_2652_, 21, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2652_, 22, v_licenseFiles_2638_);
lean_ctor_set(v_reuseFailAlloc_2652_, 23, v_readmeFile_2639_);
lean_ctor_set(v_reuseFailAlloc_2652_, 24, v_enableArtifactCache_x3f_2641_);
lean_ctor_set(v_reuseFailAlloc_2652_, 25, v_restoreAllArtifacts_x3f_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26, v_bootstrap_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26 + 1, v_precompileModules_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26 + 3, v_reservoir_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26 + 5, v_allowImportAll_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*26 + 6, v_fixedToolchain_2645_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2662_, lean_object* v_n_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2665_, lean_object* v_n_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lake_PackageConfig_license___proj(v_p_2665_, v_n_2666_);
lean_dec(v_n_2666_);
lean_dec(v_p_2665_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2668_, lean_object* v_n_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lake_PackageConfig_license___proj(v_p_2668_, v_n_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2671_, lean_object* v_n_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lake_PackageConfig_license_instConfigField(v_p_2671_, v_n_2672_);
lean_dec(v_n_2672_);
lean_dec(v_p_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* v_cfg_2674_){
_start:
{
lean_object* v_licenseFiles_2675_; 
v_licenseFiles_2675_ = lean_ctor_get(v_cfg_2674_, 22);
lean_inc_ref(v_licenseFiles_2675_);
return v_licenseFiles_2675_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* v_cfg_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lake_PackageConfig_licenseFiles___proj___lam__0(v_cfg_2676_);
lean_dec_ref(v_cfg_2676_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* v_val_2678_, lean_object* v_cfg_2679_){
_start:
{
lean_object* v_toWorkspaceConfig_2680_; lean_object* v_toLeanConfig_2681_; uint8_t v_bootstrap_2682_; lean_object* v_extraDepTargets_2683_; uint8_t v_precompileModules_2684_; lean_object* v_moreGlobalServerArgs_2685_; lean_object* v_srcDir_2686_; lean_object* v_buildDir_2687_; lean_object* v_leanLibDir_2688_; lean_object* v_nativeLibDir_2689_; lean_object* v_binDir_2690_; lean_object* v_irDir_2691_; lean_object* v_releaseRepo_2692_; lean_object* v_buildArchive_2693_; uint8_t v_preferReleaseBuild_2694_; lean_object* v_testDriver_2695_; lean_object* v_testDriverArgs_2696_; lean_object* v_lintDriver_2697_; lean_object* v_lintDriverArgs_2698_; lean_object* v_version_2699_; lean_object* v_versionTags_2700_; lean_object* v_description_2701_; lean_object* v_keywords_2702_; lean_object* v_homepage_2703_; lean_object* v_license_2704_; lean_object* v_readmeFile_2705_; uint8_t v_reservoir_2706_; lean_object* v_enableArtifactCache_x3f_2707_; lean_object* v_restoreAllArtifacts_x3f_2708_; uint8_t v_libPrefixOnWindows_2709_; uint8_t v_allowImportAll_2710_; uint8_t v_fixedToolchain_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
v_toWorkspaceConfig_2680_ = lean_ctor_get(v_cfg_2679_, 0);
v_toLeanConfig_2681_ = lean_ctor_get(v_cfg_2679_, 1);
v_bootstrap_2682_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26);
v_extraDepTargets_2683_ = lean_ctor_get(v_cfg_2679_, 2);
v_precompileModules_2684_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2685_ = lean_ctor_get(v_cfg_2679_, 3);
v_srcDir_2686_ = lean_ctor_get(v_cfg_2679_, 4);
v_buildDir_2687_ = lean_ctor_get(v_cfg_2679_, 5);
v_leanLibDir_2688_ = lean_ctor_get(v_cfg_2679_, 6);
v_nativeLibDir_2689_ = lean_ctor_get(v_cfg_2679_, 7);
v_binDir_2690_ = lean_ctor_get(v_cfg_2679_, 8);
v_irDir_2691_ = lean_ctor_get(v_cfg_2679_, 9);
v_releaseRepo_2692_ = lean_ctor_get(v_cfg_2679_, 10);
v_buildArchive_2693_ = lean_ctor_get(v_cfg_2679_, 11);
v_preferReleaseBuild_2694_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26 + 2);
v_testDriver_2695_ = lean_ctor_get(v_cfg_2679_, 12);
v_testDriverArgs_2696_ = lean_ctor_get(v_cfg_2679_, 13);
v_lintDriver_2697_ = lean_ctor_get(v_cfg_2679_, 14);
v_lintDriverArgs_2698_ = lean_ctor_get(v_cfg_2679_, 15);
v_version_2699_ = lean_ctor_get(v_cfg_2679_, 16);
v_versionTags_2700_ = lean_ctor_get(v_cfg_2679_, 17);
v_description_2701_ = lean_ctor_get(v_cfg_2679_, 18);
v_keywords_2702_ = lean_ctor_get(v_cfg_2679_, 19);
v_homepage_2703_ = lean_ctor_get(v_cfg_2679_, 20);
v_license_2704_ = lean_ctor_get(v_cfg_2679_, 21);
v_readmeFile_2705_ = lean_ctor_get(v_cfg_2679_, 23);
v_reservoir_2706_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2707_ = lean_ctor_get(v_cfg_2679_, 24);
v_restoreAllArtifacts_x3f_2708_ = lean_ctor_get(v_cfg_2679_, 25);
v_libPrefixOnWindows_2709_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26 + 4);
v_allowImportAll_2710_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26 + 5);
v_fixedToolchain_2711_ = lean_ctor_get_uint8(v_cfg_2679_, sizeof(void*)*26 + 6);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_cfg_2679_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_cfg_2679_, 22);
lean_dec(v_unused_2719_);
v___x_2713_ = v_cfg_2679_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2708_);
lean_inc(v_enableArtifactCache_x3f_2707_);
lean_inc(v_readmeFile_2705_);
lean_inc(v_license_2704_);
lean_inc(v_homepage_2703_);
lean_inc(v_keywords_2702_);
lean_inc(v_description_2701_);
lean_inc(v_versionTags_2700_);
lean_inc(v_version_2699_);
lean_inc(v_lintDriverArgs_2698_);
lean_inc(v_lintDriver_2697_);
lean_inc(v_testDriverArgs_2696_);
lean_inc(v_testDriver_2695_);
lean_inc(v_buildArchive_2693_);
lean_inc(v_releaseRepo_2692_);
lean_inc(v_irDir_2691_);
lean_inc(v_binDir_2690_);
lean_inc(v_nativeLibDir_2689_);
lean_inc(v_leanLibDir_2688_);
lean_inc(v_buildDir_2687_);
lean_inc(v_srcDir_2686_);
lean_inc(v_moreGlobalServerArgs_2685_);
lean_inc(v_extraDepTargets_2683_);
lean_inc(v_toLeanConfig_2681_);
lean_inc(v_toWorkspaceConfig_2680_);
lean_dec(v_cfg_2679_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 22, v_val_2678_);
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_toWorkspaceConfig_2680_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_toLeanConfig_2681_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_extraDepTargets_2683_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_moreGlobalServerArgs_2685_);
lean_ctor_set(v_reuseFailAlloc_2717_, 4, v_srcDir_2686_);
lean_ctor_set(v_reuseFailAlloc_2717_, 5, v_buildDir_2687_);
lean_ctor_set(v_reuseFailAlloc_2717_, 6, v_leanLibDir_2688_);
lean_ctor_set(v_reuseFailAlloc_2717_, 7, v_nativeLibDir_2689_);
lean_ctor_set(v_reuseFailAlloc_2717_, 8, v_binDir_2690_);
lean_ctor_set(v_reuseFailAlloc_2717_, 9, v_irDir_2691_);
lean_ctor_set(v_reuseFailAlloc_2717_, 10, v_releaseRepo_2692_);
lean_ctor_set(v_reuseFailAlloc_2717_, 11, v_buildArchive_2693_);
lean_ctor_set(v_reuseFailAlloc_2717_, 12, v_testDriver_2695_);
lean_ctor_set(v_reuseFailAlloc_2717_, 13, v_testDriverArgs_2696_);
lean_ctor_set(v_reuseFailAlloc_2717_, 14, v_lintDriver_2697_);
lean_ctor_set(v_reuseFailAlloc_2717_, 15, v_lintDriverArgs_2698_);
lean_ctor_set(v_reuseFailAlloc_2717_, 16, v_version_2699_);
lean_ctor_set(v_reuseFailAlloc_2717_, 17, v_versionTags_2700_);
lean_ctor_set(v_reuseFailAlloc_2717_, 18, v_description_2701_);
lean_ctor_set(v_reuseFailAlloc_2717_, 19, v_keywords_2702_);
lean_ctor_set(v_reuseFailAlloc_2717_, 20, v_homepage_2703_);
lean_ctor_set(v_reuseFailAlloc_2717_, 21, v_license_2704_);
lean_ctor_set(v_reuseFailAlloc_2717_, 22, v_val_2678_);
lean_ctor_set(v_reuseFailAlloc_2717_, 23, v_readmeFile_2705_);
lean_ctor_set(v_reuseFailAlloc_2717_, 24, v_enableArtifactCache_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2717_, 25, v_restoreAllArtifacts_x3f_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26, v_bootstrap_2682_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26 + 1, v_precompileModules_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26 + 3, v_reservoir_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26 + 5, v_allowImportAll_2710_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*26 + 6, v_fixedToolchain_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* v_f_2720_, lean_object* v_cfg_2721_){
_start:
{
lean_object* v_toWorkspaceConfig_2722_; lean_object* v_toLeanConfig_2723_; uint8_t v_bootstrap_2724_; lean_object* v_extraDepTargets_2725_; uint8_t v_precompileModules_2726_; lean_object* v_moreGlobalServerArgs_2727_; lean_object* v_srcDir_2728_; lean_object* v_buildDir_2729_; lean_object* v_leanLibDir_2730_; lean_object* v_nativeLibDir_2731_; lean_object* v_binDir_2732_; lean_object* v_irDir_2733_; lean_object* v_releaseRepo_2734_; lean_object* v_buildArchive_2735_; uint8_t v_preferReleaseBuild_2736_; lean_object* v_testDriver_2737_; lean_object* v_testDriverArgs_2738_; lean_object* v_lintDriver_2739_; lean_object* v_lintDriverArgs_2740_; lean_object* v_version_2741_; lean_object* v_versionTags_2742_; lean_object* v_description_2743_; lean_object* v_keywords_2744_; lean_object* v_homepage_2745_; lean_object* v_license_2746_; lean_object* v_licenseFiles_2747_; lean_object* v_readmeFile_2748_; uint8_t v_reservoir_2749_; lean_object* v_enableArtifactCache_x3f_2750_; lean_object* v_restoreAllArtifacts_x3f_2751_; uint8_t v_libPrefixOnWindows_2752_; uint8_t v_allowImportAll_2753_; uint8_t v_fixedToolchain_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
v_toWorkspaceConfig_2722_ = lean_ctor_get(v_cfg_2721_, 0);
v_toLeanConfig_2723_ = lean_ctor_get(v_cfg_2721_, 1);
v_bootstrap_2724_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26);
v_extraDepTargets_2725_ = lean_ctor_get(v_cfg_2721_, 2);
v_precompileModules_2726_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2727_ = lean_ctor_get(v_cfg_2721_, 3);
v_srcDir_2728_ = lean_ctor_get(v_cfg_2721_, 4);
v_buildDir_2729_ = lean_ctor_get(v_cfg_2721_, 5);
v_leanLibDir_2730_ = lean_ctor_get(v_cfg_2721_, 6);
v_nativeLibDir_2731_ = lean_ctor_get(v_cfg_2721_, 7);
v_binDir_2732_ = lean_ctor_get(v_cfg_2721_, 8);
v_irDir_2733_ = lean_ctor_get(v_cfg_2721_, 9);
v_releaseRepo_2734_ = lean_ctor_get(v_cfg_2721_, 10);
v_buildArchive_2735_ = lean_ctor_get(v_cfg_2721_, 11);
v_preferReleaseBuild_2736_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26 + 2);
v_testDriver_2737_ = lean_ctor_get(v_cfg_2721_, 12);
v_testDriverArgs_2738_ = lean_ctor_get(v_cfg_2721_, 13);
v_lintDriver_2739_ = lean_ctor_get(v_cfg_2721_, 14);
v_lintDriverArgs_2740_ = lean_ctor_get(v_cfg_2721_, 15);
v_version_2741_ = lean_ctor_get(v_cfg_2721_, 16);
v_versionTags_2742_ = lean_ctor_get(v_cfg_2721_, 17);
v_description_2743_ = lean_ctor_get(v_cfg_2721_, 18);
v_keywords_2744_ = lean_ctor_get(v_cfg_2721_, 19);
v_homepage_2745_ = lean_ctor_get(v_cfg_2721_, 20);
v_license_2746_ = lean_ctor_get(v_cfg_2721_, 21);
v_licenseFiles_2747_ = lean_ctor_get(v_cfg_2721_, 22);
v_readmeFile_2748_ = lean_ctor_get(v_cfg_2721_, 23);
v_reservoir_2749_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2750_ = lean_ctor_get(v_cfg_2721_, 24);
v_restoreAllArtifacts_x3f_2751_ = lean_ctor_get(v_cfg_2721_, 25);
v_libPrefixOnWindows_2752_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26 + 4);
v_allowImportAll_2753_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26 + 5);
v_fixedToolchain_2754_ = lean_ctor_get_uint8(v_cfg_2721_, sizeof(void*)*26 + 6);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_cfg_2721_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2756_ = v_cfg_2721_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2751_);
lean_inc(v_enableArtifactCache_x3f_2750_);
lean_inc(v_readmeFile_2748_);
lean_inc(v_licenseFiles_2747_);
lean_inc(v_license_2746_);
lean_inc(v_homepage_2745_);
lean_inc(v_keywords_2744_);
lean_inc(v_description_2743_);
lean_inc(v_versionTags_2742_);
lean_inc(v_version_2741_);
lean_inc(v_lintDriverArgs_2740_);
lean_inc(v_lintDriver_2739_);
lean_inc(v_testDriverArgs_2738_);
lean_inc(v_testDriver_2737_);
lean_inc(v_buildArchive_2735_);
lean_inc(v_releaseRepo_2734_);
lean_inc(v_irDir_2733_);
lean_inc(v_binDir_2732_);
lean_inc(v_nativeLibDir_2731_);
lean_inc(v_leanLibDir_2730_);
lean_inc(v_buildDir_2729_);
lean_inc(v_srcDir_2728_);
lean_inc(v_moreGlobalServerArgs_2727_);
lean_inc(v_extraDepTargets_2725_);
lean_inc(v_toLeanConfig_2723_);
lean_inc(v_toWorkspaceConfig_2722_);
lean_dec(v_cfg_2721_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2758_ = lean_apply_1(v_f_2720_, v_licenseFiles_2747_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 22, v___x_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_toWorkspaceConfig_2722_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_toLeanConfig_2723_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_extraDepTargets_2725_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v_moreGlobalServerArgs_2727_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v_srcDir_2728_);
lean_ctor_set(v_reuseFailAlloc_2761_, 5, v_buildDir_2729_);
lean_ctor_set(v_reuseFailAlloc_2761_, 6, v_leanLibDir_2730_);
lean_ctor_set(v_reuseFailAlloc_2761_, 7, v_nativeLibDir_2731_);
lean_ctor_set(v_reuseFailAlloc_2761_, 8, v_binDir_2732_);
lean_ctor_set(v_reuseFailAlloc_2761_, 9, v_irDir_2733_);
lean_ctor_set(v_reuseFailAlloc_2761_, 10, v_releaseRepo_2734_);
lean_ctor_set(v_reuseFailAlloc_2761_, 11, v_buildArchive_2735_);
lean_ctor_set(v_reuseFailAlloc_2761_, 12, v_testDriver_2737_);
lean_ctor_set(v_reuseFailAlloc_2761_, 13, v_testDriverArgs_2738_);
lean_ctor_set(v_reuseFailAlloc_2761_, 14, v_lintDriver_2739_);
lean_ctor_set(v_reuseFailAlloc_2761_, 15, v_lintDriverArgs_2740_);
lean_ctor_set(v_reuseFailAlloc_2761_, 16, v_version_2741_);
lean_ctor_set(v_reuseFailAlloc_2761_, 17, v_versionTags_2742_);
lean_ctor_set(v_reuseFailAlloc_2761_, 18, v_description_2743_);
lean_ctor_set(v_reuseFailAlloc_2761_, 19, v_keywords_2744_);
lean_ctor_set(v_reuseFailAlloc_2761_, 20, v_homepage_2745_);
lean_ctor_set(v_reuseFailAlloc_2761_, 21, v_license_2746_);
lean_ctor_set(v_reuseFailAlloc_2761_, 22, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2761_, 23, v_readmeFile_2748_);
lean_ctor_set(v_reuseFailAlloc_2761_, 24, v_enableArtifactCache_x3f_2750_);
lean_ctor_set(v_reuseFailAlloc_2761_, 25, v_restoreAllArtifacts_x3f_2751_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26, v_bootstrap_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26 + 1, v_precompileModules_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26 + 3, v_reservoir_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2752_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26 + 5, v_allowImportAll_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*26 + 6, v_fixedToolchain_2754_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* v_x_2763_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = lean_unsigned_to_nat(1u);
v___x_2765_ = lean_mk_empty_array_with_capacity(v___x_2764_);
lean_dec_ref(v___x_2765_);
v___x_2766_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* v_x_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lake_PackageConfig_licenseFiles___proj___lam__3(v_x_2767_);
lean_dec_ref(v_x_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_2778_, lean_object* v_n_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_2781_, lean_object* v_n_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2781_, v_n_2782_);
lean_dec(v_n_2782_);
lean_dec(v_p_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_2784_, lean_object* v_n_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2784_, v_n_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_2787_, lean_object* v_n_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_2787_, v_n_2788_);
lean_dec(v_n_2788_);
lean_dec(v_p_2787_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* v_cfg_2790_){
_start:
{
lean_object* v_readmeFile_2791_; 
v_readmeFile_2791_ = lean_ctor_get(v_cfg_2790_, 23);
lean_inc_ref(v_readmeFile_2791_);
return v_readmeFile_2791_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* v_cfg_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lake_PackageConfig_readmeFile___proj___lam__0(v_cfg_2792_);
lean_dec_ref(v_cfg_2792_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* v_val_2794_, lean_object* v_cfg_2795_){
_start:
{
lean_object* v_toWorkspaceConfig_2796_; lean_object* v_toLeanConfig_2797_; uint8_t v_bootstrap_2798_; lean_object* v_extraDepTargets_2799_; uint8_t v_precompileModules_2800_; lean_object* v_moreGlobalServerArgs_2801_; lean_object* v_srcDir_2802_; lean_object* v_buildDir_2803_; lean_object* v_leanLibDir_2804_; lean_object* v_nativeLibDir_2805_; lean_object* v_binDir_2806_; lean_object* v_irDir_2807_; lean_object* v_releaseRepo_2808_; lean_object* v_buildArchive_2809_; uint8_t v_preferReleaseBuild_2810_; lean_object* v_testDriver_2811_; lean_object* v_testDriverArgs_2812_; lean_object* v_lintDriver_2813_; lean_object* v_lintDriverArgs_2814_; lean_object* v_version_2815_; lean_object* v_versionTags_2816_; lean_object* v_description_2817_; lean_object* v_keywords_2818_; lean_object* v_homepage_2819_; lean_object* v_license_2820_; lean_object* v_licenseFiles_2821_; uint8_t v_reservoir_2822_; lean_object* v_enableArtifactCache_x3f_2823_; lean_object* v_restoreAllArtifacts_x3f_2824_; uint8_t v_libPrefixOnWindows_2825_; uint8_t v_allowImportAll_2826_; uint8_t v_fixedToolchain_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
v_toWorkspaceConfig_2796_ = lean_ctor_get(v_cfg_2795_, 0);
v_toLeanConfig_2797_ = lean_ctor_get(v_cfg_2795_, 1);
v_bootstrap_2798_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26);
v_extraDepTargets_2799_ = lean_ctor_get(v_cfg_2795_, 2);
v_precompileModules_2800_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2801_ = lean_ctor_get(v_cfg_2795_, 3);
v_srcDir_2802_ = lean_ctor_get(v_cfg_2795_, 4);
v_buildDir_2803_ = lean_ctor_get(v_cfg_2795_, 5);
v_leanLibDir_2804_ = lean_ctor_get(v_cfg_2795_, 6);
v_nativeLibDir_2805_ = lean_ctor_get(v_cfg_2795_, 7);
v_binDir_2806_ = lean_ctor_get(v_cfg_2795_, 8);
v_irDir_2807_ = lean_ctor_get(v_cfg_2795_, 9);
v_releaseRepo_2808_ = lean_ctor_get(v_cfg_2795_, 10);
v_buildArchive_2809_ = lean_ctor_get(v_cfg_2795_, 11);
v_preferReleaseBuild_2810_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26 + 2);
v_testDriver_2811_ = lean_ctor_get(v_cfg_2795_, 12);
v_testDriverArgs_2812_ = lean_ctor_get(v_cfg_2795_, 13);
v_lintDriver_2813_ = lean_ctor_get(v_cfg_2795_, 14);
v_lintDriverArgs_2814_ = lean_ctor_get(v_cfg_2795_, 15);
v_version_2815_ = lean_ctor_get(v_cfg_2795_, 16);
v_versionTags_2816_ = lean_ctor_get(v_cfg_2795_, 17);
v_description_2817_ = lean_ctor_get(v_cfg_2795_, 18);
v_keywords_2818_ = lean_ctor_get(v_cfg_2795_, 19);
v_homepage_2819_ = lean_ctor_get(v_cfg_2795_, 20);
v_license_2820_ = lean_ctor_get(v_cfg_2795_, 21);
v_licenseFiles_2821_ = lean_ctor_get(v_cfg_2795_, 22);
v_reservoir_2822_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2823_ = lean_ctor_get(v_cfg_2795_, 24);
v_restoreAllArtifacts_x3f_2824_ = lean_ctor_get(v_cfg_2795_, 25);
v_libPrefixOnWindows_2825_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26 + 4);
v_allowImportAll_2826_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26 + 5);
v_fixedToolchain_2827_ = lean_ctor_get_uint8(v_cfg_2795_, sizeof(void*)*26 + 6);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_cfg_2795_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; 
v_unused_2835_ = lean_ctor_get(v_cfg_2795_, 23);
lean_dec(v_unused_2835_);
v___x_2829_ = v_cfg_2795_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2824_);
lean_inc(v_enableArtifactCache_x3f_2823_);
lean_inc(v_licenseFiles_2821_);
lean_inc(v_license_2820_);
lean_inc(v_homepage_2819_);
lean_inc(v_keywords_2818_);
lean_inc(v_description_2817_);
lean_inc(v_versionTags_2816_);
lean_inc(v_version_2815_);
lean_inc(v_lintDriverArgs_2814_);
lean_inc(v_lintDriver_2813_);
lean_inc(v_testDriverArgs_2812_);
lean_inc(v_testDriver_2811_);
lean_inc(v_buildArchive_2809_);
lean_inc(v_releaseRepo_2808_);
lean_inc(v_irDir_2807_);
lean_inc(v_binDir_2806_);
lean_inc(v_nativeLibDir_2805_);
lean_inc(v_leanLibDir_2804_);
lean_inc(v_buildDir_2803_);
lean_inc(v_srcDir_2802_);
lean_inc(v_moreGlobalServerArgs_2801_);
lean_inc(v_extraDepTargets_2799_);
lean_inc(v_toLeanConfig_2797_);
lean_inc(v_toWorkspaceConfig_2796_);
lean_dec(v_cfg_2795_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 23, v_val_2794_);
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_toWorkspaceConfig_2796_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_toLeanConfig_2797_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_extraDepTargets_2799_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_moreGlobalServerArgs_2801_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_srcDir_2802_);
lean_ctor_set(v_reuseFailAlloc_2833_, 5, v_buildDir_2803_);
lean_ctor_set(v_reuseFailAlloc_2833_, 6, v_leanLibDir_2804_);
lean_ctor_set(v_reuseFailAlloc_2833_, 7, v_nativeLibDir_2805_);
lean_ctor_set(v_reuseFailAlloc_2833_, 8, v_binDir_2806_);
lean_ctor_set(v_reuseFailAlloc_2833_, 9, v_irDir_2807_);
lean_ctor_set(v_reuseFailAlloc_2833_, 10, v_releaseRepo_2808_);
lean_ctor_set(v_reuseFailAlloc_2833_, 11, v_buildArchive_2809_);
lean_ctor_set(v_reuseFailAlloc_2833_, 12, v_testDriver_2811_);
lean_ctor_set(v_reuseFailAlloc_2833_, 13, v_testDriverArgs_2812_);
lean_ctor_set(v_reuseFailAlloc_2833_, 14, v_lintDriver_2813_);
lean_ctor_set(v_reuseFailAlloc_2833_, 15, v_lintDriverArgs_2814_);
lean_ctor_set(v_reuseFailAlloc_2833_, 16, v_version_2815_);
lean_ctor_set(v_reuseFailAlloc_2833_, 17, v_versionTags_2816_);
lean_ctor_set(v_reuseFailAlloc_2833_, 18, v_description_2817_);
lean_ctor_set(v_reuseFailAlloc_2833_, 19, v_keywords_2818_);
lean_ctor_set(v_reuseFailAlloc_2833_, 20, v_homepage_2819_);
lean_ctor_set(v_reuseFailAlloc_2833_, 21, v_license_2820_);
lean_ctor_set(v_reuseFailAlloc_2833_, 22, v_licenseFiles_2821_);
lean_ctor_set(v_reuseFailAlloc_2833_, 23, v_val_2794_);
lean_ctor_set(v_reuseFailAlloc_2833_, 24, v_enableArtifactCache_x3f_2823_);
lean_ctor_set(v_reuseFailAlloc_2833_, 25, v_restoreAllArtifacts_x3f_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26, v_bootstrap_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26 + 1, v_precompileModules_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26 + 3, v_reservoir_2822_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2825_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26 + 5, v_allowImportAll_2826_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*26 + 6, v_fixedToolchain_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* v_f_2836_, lean_object* v_cfg_2837_){
_start:
{
lean_object* v_toWorkspaceConfig_2838_; lean_object* v_toLeanConfig_2839_; uint8_t v_bootstrap_2840_; lean_object* v_extraDepTargets_2841_; uint8_t v_precompileModules_2842_; lean_object* v_moreGlobalServerArgs_2843_; lean_object* v_srcDir_2844_; lean_object* v_buildDir_2845_; lean_object* v_leanLibDir_2846_; lean_object* v_nativeLibDir_2847_; lean_object* v_binDir_2848_; lean_object* v_irDir_2849_; lean_object* v_releaseRepo_2850_; lean_object* v_buildArchive_2851_; uint8_t v_preferReleaseBuild_2852_; lean_object* v_testDriver_2853_; lean_object* v_testDriverArgs_2854_; lean_object* v_lintDriver_2855_; lean_object* v_lintDriverArgs_2856_; lean_object* v_version_2857_; lean_object* v_versionTags_2858_; lean_object* v_description_2859_; lean_object* v_keywords_2860_; lean_object* v_homepage_2861_; lean_object* v_license_2862_; lean_object* v_licenseFiles_2863_; lean_object* v_readmeFile_2864_; uint8_t v_reservoir_2865_; lean_object* v_enableArtifactCache_x3f_2866_; lean_object* v_restoreAllArtifacts_x3f_2867_; uint8_t v_libPrefixOnWindows_2868_; uint8_t v_allowImportAll_2869_; uint8_t v_fixedToolchain_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2878_; 
v_toWorkspaceConfig_2838_ = lean_ctor_get(v_cfg_2837_, 0);
v_toLeanConfig_2839_ = lean_ctor_get(v_cfg_2837_, 1);
v_bootstrap_2840_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26);
v_extraDepTargets_2841_ = lean_ctor_get(v_cfg_2837_, 2);
v_precompileModules_2842_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2843_ = lean_ctor_get(v_cfg_2837_, 3);
v_srcDir_2844_ = lean_ctor_get(v_cfg_2837_, 4);
v_buildDir_2845_ = lean_ctor_get(v_cfg_2837_, 5);
v_leanLibDir_2846_ = lean_ctor_get(v_cfg_2837_, 6);
v_nativeLibDir_2847_ = lean_ctor_get(v_cfg_2837_, 7);
v_binDir_2848_ = lean_ctor_get(v_cfg_2837_, 8);
v_irDir_2849_ = lean_ctor_get(v_cfg_2837_, 9);
v_releaseRepo_2850_ = lean_ctor_get(v_cfg_2837_, 10);
v_buildArchive_2851_ = lean_ctor_get(v_cfg_2837_, 11);
v_preferReleaseBuild_2852_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26 + 2);
v_testDriver_2853_ = lean_ctor_get(v_cfg_2837_, 12);
v_testDriverArgs_2854_ = lean_ctor_get(v_cfg_2837_, 13);
v_lintDriver_2855_ = lean_ctor_get(v_cfg_2837_, 14);
v_lintDriverArgs_2856_ = lean_ctor_get(v_cfg_2837_, 15);
v_version_2857_ = lean_ctor_get(v_cfg_2837_, 16);
v_versionTags_2858_ = lean_ctor_get(v_cfg_2837_, 17);
v_description_2859_ = lean_ctor_get(v_cfg_2837_, 18);
v_keywords_2860_ = lean_ctor_get(v_cfg_2837_, 19);
v_homepage_2861_ = lean_ctor_get(v_cfg_2837_, 20);
v_license_2862_ = lean_ctor_get(v_cfg_2837_, 21);
v_licenseFiles_2863_ = lean_ctor_get(v_cfg_2837_, 22);
v_readmeFile_2864_ = lean_ctor_get(v_cfg_2837_, 23);
v_reservoir_2865_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2866_ = lean_ctor_get(v_cfg_2837_, 24);
v_restoreAllArtifacts_x3f_2867_ = lean_ctor_get(v_cfg_2837_, 25);
v_libPrefixOnWindows_2868_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26 + 4);
v_allowImportAll_2869_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26 + 5);
v_fixedToolchain_2870_ = lean_ctor_get_uint8(v_cfg_2837_, sizeof(void*)*26 + 6);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_cfg_2837_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2872_ = v_cfg_2837_;
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2867_);
lean_inc(v_enableArtifactCache_x3f_2866_);
lean_inc(v_readmeFile_2864_);
lean_inc(v_licenseFiles_2863_);
lean_inc(v_license_2862_);
lean_inc(v_homepage_2861_);
lean_inc(v_keywords_2860_);
lean_inc(v_description_2859_);
lean_inc(v_versionTags_2858_);
lean_inc(v_version_2857_);
lean_inc(v_lintDriverArgs_2856_);
lean_inc(v_lintDriver_2855_);
lean_inc(v_testDriverArgs_2854_);
lean_inc(v_testDriver_2853_);
lean_inc(v_buildArchive_2851_);
lean_inc(v_releaseRepo_2850_);
lean_inc(v_irDir_2849_);
lean_inc(v_binDir_2848_);
lean_inc(v_nativeLibDir_2847_);
lean_inc(v_leanLibDir_2846_);
lean_inc(v_buildDir_2845_);
lean_inc(v_srcDir_2844_);
lean_inc(v_moreGlobalServerArgs_2843_);
lean_inc(v_extraDepTargets_2841_);
lean_inc(v_toLeanConfig_2839_);
lean_inc(v_toWorkspaceConfig_2838_);
lean_dec(v_cfg_2837_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = lean_apply_1(v_f_2836_, v_readmeFile_2864_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 23, v___x_2874_);
v___x_2876_ = v___x_2872_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_toWorkspaceConfig_2838_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_toLeanConfig_2839_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_extraDepTargets_2841_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_moreGlobalServerArgs_2843_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_srcDir_2844_);
lean_ctor_set(v_reuseFailAlloc_2877_, 5, v_buildDir_2845_);
lean_ctor_set(v_reuseFailAlloc_2877_, 6, v_leanLibDir_2846_);
lean_ctor_set(v_reuseFailAlloc_2877_, 7, v_nativeLibDir_2847_);
lean_ctor_set(v_reuseFailAlloc_2877_, 8, v_binDir_2848_);
lean_ctor_set(v_reuseFailAlloc_2877_, 9, v_irDir_2849_);
lean_ctor_set(v_reuseFailAlloc_2877_, 10, v_releaseRepo_2850_);
lean_ctor_set(v_reuseFailAlloc_2877_, 11, v_buildArchive_2851_);
lean_ctor_set(v_reuseFailAlloc_2877_, 12, v_testDriver_2853_);
lean_ctor_set(v_reuseFailAlloc_2877_, 13, v_testDriverArgs_2854_);
lean_ctor_set(v_reuseFailAlloc_2877_, 14, v_lintDriver_2855_);
lean_ctor_set(v_reuseFailAlloc_2877_, 15, v_lintDriverArgs_2856_);
lean_ctor_set(v_reuseFailAlloc_2877_, 16, v_version_2857_);
lean_ctor_set(v_reuseFailAlloc_2877_, 17, v_versionTags_2858_);
lean_ctor_set(v_reuseFailAlloc_2877_, 18, v_description_2859_);
lean_ctor_set(v_reuseFailAlloc_2877_, 19, v_keywords_2860_);
lean_ctor_set(v_reuseFailAlloc_2877_, 20, v_homepage_2861_);
lean_ctor_set(v_reuseFailAlloc_2877_, 21, v_license_2862_);
lean_ctor_set(v_reuseFailAlloc_2877_, 22, v_licenseFiles_2863_);
lean_ctor_set(v_reuseFailAlloc_2877_, 23, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2877_, 24, v_enableArtifactCache_x3f_2866_);
lean_ctor_set(v_reuseFailAlloc_2877_, 25, v_restoreAllArtifacts_x3f_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26, v_bootstrap_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26 + 1, v_precompileModules_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26 + 3, v_reservoir_2865_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2868_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26 + 5, v_allowImportAll_2869_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*26 + 6, v_fixedToolchain_2870_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* v_x_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* v_x_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lake_PackageConfig_readmeFile___proj___lam__3(v_x_2881_);
lean_dec_ref(v_x_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_2892_, lean_object* v_n_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_2895_, lean_object* v_n_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2895_, v_n_2896_);
lean_dec(v_n_2896_);
lean_dec(v_p_2895_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_2898_, lean_object* v_n_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2898_, v_n_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_2901_, lean_object* v_n_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_2901_, v_n_2902_);
lean_dec(v_n_2902_);
lean_dec(v_p_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* v_cfg_2904_){
_start:
{
uint8_t v_reservoir_2905_; 
v_reservoir_2905_ = lean_ctor_get_uint8(v_cfg_2904_, sizeof(void*)*26 + 3);
return v_reservoir_2905_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* v_cfg_2906_){
_start:
{
uint8_t v_res_2907_; lean_object* v_r_2908_; 
v_res_2907_ = l_Lake_PackageConfig_reservoir___proj___lam__0(v_cfg_2906_);
lean_dec_ref(v_cfg_2906_);
v_r_2908_ = lean_box(v_res_2907_);
return v_r_2908_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t v_val_2909_, lean_object* v_cfg_2910_){
_start:
{
lean_object* v_toWorkspaceConfig_2911_; lean_object* v_toLeanConfig_2912_; uint8_t v_bootstrap_2913_; lean_object* v_extraDepTargets_2914_; uint8_t v_precompileModules_2915_; lean_object* v_moreGlobalServerArgs_2916_; lean_object* v_srcDir_2917_; lean_object* v_buildDir_2918_; lean_object* v_leanLibDir_2919_; lean_object* v_nativeLibDir_2920_; lean_object* v_binDir_2921_; lean_object* v_irDir_2922_; lean_object* v_releaseRepo_2923_; lean_object* v_buildArchive_2924_; uint8_t v_preferReleaseBuild_2925_; lean_object* v_testDriver_2926_; lean_object* v_testDriverArgs_2927_; lean_object* v_lintDriver_2928_; lean_object* v_lintDriverArgs_2929_; lean_object* v_version_2930_; lean_object* v_versionTags_2931_; lean_object* v_description_2932_; lean_object* v_keywords_2933_; lean_object* v_homepage_2934_; lean_object* v_license_2935_; lean_object* v_licenseFiles_2936_; lean_object* v_readmeFile_2937_; lean_object* v_enableArtifactCache_x3f_2938_; lean_object* v_restoreAllArtifacts_x3f_2939_; uint8_t v_libPrefixOnWindows_2940_; uint8_t v_allowImportAll_2941_; uint8_t v_fixedToolchain_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_toWorkspaceConfig_2911_ = lean_ctor_get(v_cfg_2910_, 0);
v_toLeanConfig_2912_ = lean_ctor_get(v_cfg_2910_, 1);
v_bootstrap_2913_ = lean_ctor_get_uint8(v_cfg_2910_, sizeof(void*)*26);
v_extraDepTargets_2914_ = lean_ctor_get(v_cfg_2910_, 2);
v_precompileModules_2915_ = lean_ctor_get_uint8(v_cfg_2910_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2916_ = lean_ctor_get(v_cfg_2910_, 3);
v_srcDir_2917_ = lean_ctor_get(v_cfg_2910_, 4);
v_buildDir_2918_ = lean_ctor_get(v_cfg_2910_, 5);
v_leanLibDir_2919_ = lean_ctor_get(v_cfg_2910_, 6);
v_nativeLibDir_2920_ = lean_ctor_get(v_cfg_2910_, 7);
v_binDir_2921_ = lean_ctor_get(v_cfg_2910_, 8);
v_irDir_2922_ = lean_ctor_get(v_cfg_2910_, 9);
v_releaseRepo_2923_ = lean_ctor_get(v_cfg_2910_, 10);
v_buildArchive_2924_ = lean_ctor_get(v_cfg_2910_, 11);
v_preferReleaseBuild_2925_ = lean_ctor_get_uint8(v_cfg_2910_, sizeof(void*)*26 + 2);
v_testDriver_2926_ = lean_ctor_get(v_cfg_2910_, 12);
v_testDriverArgs_2927_ = lean_ctor_get(v_cfg_2910_, 13);
v_lintDriver_2928_ = lean_ctor_get(v_cfg_2910_, 14);
v_lintDriverArgs_2929_ = lean_ctor_get(v_cfg_2910_, 15);
v_version_2930_ = lean_ctor_get(v_cfg_2910_, 16);
v_versionTags_2931_ = lean_ctor_get(v_cfg_2910_, 17);
v_description_2932_ = lean_ctor_get(v_cfg_2910_, 18);
v_keywords_2933_ = lean_ctor_get(v_cfg_2910_, 19);
v_homepage_2934_ = lean_ctor_get(v_cfg_2910_, 20);
v_license_2935_ = lean_ctor_get(v_cfg_2910_, 21);
v_licenseFiles_2936_ = lean_ctor_get(v_cfg_2910_, 22);
v_readmeFile_2937_ = lean_ctor_get(v_cfg_2910_, 23);
v_enableArtifactCache_x3f_2938_ = lean_ctor_get(v_cfg_2910_, 24);
v_restoreAllArtifacts_x3f_2939_ = lean_ctor_get(v_cfg_2910_, 25);
v_libPrefixOnWindows_2940_ = lean_ctor_get_uint8(v_cfg_2910_, sizeof(void*)*26 + 4);
v_allowImportAll_2941_ = lean_ctor_get_uint8(v_cfg_2910_, sizeof(void*)*26 + 5);
v_fixedToolchain_2942_ = lean_ctor_get_uint8(v_cfg_2910_, sizeof(void*)*26 + 6);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_cfg_2910_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v_cfg_2910_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2939_);
lean_inc(v_enableArtifactCache_x3f_2938_);
lean_inc(v_readmeFile_2937_);
lean_inc(v_licenseFiles_2936_);
lean_inc(v_license_2935_);
lean_inc(v_homepage_2934_);
lean_inc(v_keywords_2933_);
lean_inc(v_description_2932_);
lean_inc(v_versionTags_2931_);
lean_inc(v_version_2930_);
lean_inc(v_lintDriverArgs_2929_);
lean_inc(v_lintDriver_2928_);
lean_inc(v_testDriverArgs_2927_);
lean_inc(v_testDriver_2926_);
lean_inc(v_buildArchive_2924_);
lean_inc(v_releaseRepo_2923_);
lean_inc(v_irDir_2922_);
lean_inc(v_binDir_2921_);
lean_inc(v_nativeLibDir_2920_);
lean_inc(v_leanLibDir_2919_);
lean_inc(v_buildDir_2918_);
lean_inc(v_srcDir_2917_);
lean_inc(v_moreGlobalServerArgs_2916_);
lean_inc(v_extraDepTargets_2914_);
lean_inc(v_toLeanConfig_2912_);
lean_inc(v_toWorkspaceConfig_2911_);
lean_dec(v_cfg_2910_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_toWorkspaceConfig_2911_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_toLeanConfig_2912_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v_extraDepTargets_2914_);
lean_ctor_set(v_reuseFailAlloc_2948_, 3, v_moreGlobalServerArgs_2916_);
lean_ctor_set(v_reuseFailAlloc_2948_, 4, v_srcDir_2917_);
lean_ctor_set(v_reuseFailAlloc_2948_, 5, v_buildDir_2918_);
lean_ctor_set(v_reuseFailAlloc_2948_, 6, v_leanLibDir_2919_);
lean_ctor_set(v_reuseFailAlloc_2948_, 7, v_nativeLibDir_2920_);
lean_ctor_set(v_reuseFailAlloc_2948_, 8, v_binDir_2921_);
lean_ctor_set(v_reuseFailAlloc_2948_, 9, v_irDir_2922_);
lean_ctor_set(v_reuseFailAlloc_2948_, 10, v_releaseRepo_2923_);
lean_ctor_set(v_reuseFailAlloc_2948_, 11, v_buildArchive_2924_);
lean_ctor_set(v_reuseFailAlloc_2948_, 12, v_testDriver_2926_);
lean_ctor_set(v_reuseFailAlloc_2948_, 13, v_testDriverArgs_2927_);
lean_ctor_set(v_reuseFailAlloc_2948_, 14, v_lintDriver_2928_);
lean_ctor_set(v_reuseFailAlloc_2948_, 15, v_lintDriverArgs_2929_);
lean_ctor_set(v_reuseFailAlloc_2948_, 16, v_version_2930_);
lean_ctor_set(v_reuseFailAlloc_2948_, 17, v_versionTags_2931_);
lean_ctor_set(v_reuseFailAlloc_2948_, 18, v_description_2932_);
lean_ctor_set(v_reuseFailAlloc_2948_, 19, v_keywords_2933_);
lean_ctor_set(v_reuseFailAlloc_2948_, 20, v_homepage_2934_);
lean_ctor_set(v_reuseFailAlloc_2948_, 21, v_license_2935_);
lean_ctor_set(v_reuseFailAlloc_2948_, 22, v_licenseFiles_2936_);
lean_ctor_set(v_reuseFailAlloc_2948_, 23, v_readmeFile_2937_);
lean_ctor_set(v_reuseFailAlloc_2948_, 24, v_enableArtifactCache_x3f_2938_);
lean_ctor_set(v_reuseFailAlloc_2948_, 25, v_restoreAllArtifacts_x3f_2939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*26, v_bootstrap_2913_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*26 + 1, v_precompileModules_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*26 + 5, v_allowImportAll_2941_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*26 + 6, v_fixedToolchain_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*26 + 3, v_val_2909_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* v_val_2950_, lean_object* v_cfg_2951_){
_start:
{
uint8_t v_val_134__boxed_2952_; lean_object* v_res_2953_; 
v_val_134__boxed_2952_ = lean_unbox(v_val_2950_);
v_res_2953_ = l_Lake_PackageConfig_reservoir___proj___lam__1(v_val_134__boxed_2952_, v_cfg_2951_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* v_f_2954_, lean_object* v_cfg_2955_){
_start:
{
lean_object* v_toWorkspaceConfig_2956_; lean_object* v_toLeanConfig_2957_; uint8_t v_bootstrap_2958_; lean_object* v_extraDepTargets_2959_; uint8_t v_precompileModules_2960_; lean_object* v_moreGlobalServerArgs_2961_; lean_object* v_srcDir_2962_; lean_object* v_buildDir_2963_; lean_object* v_leanLibDir_2964_; lean_object* v_nativeLibDir_2965_; lean_object* v_binDir_2966_; lean_object* v_irDir_2967_; lean_object* v_releaseRepo_2968_; lean_object* v_buildArchive_2969_; uint8_t v_preferReleaseBuild_2970_; lean_object* v_testDriver_2971_; lean_object* v_testDriverArgs_2972_; lean_object* v_lintDriver_2973_; lean_object* v_lintDriverArgs_2974_; lean_object* v_version_2975_; lean_object* v_versionTags_2976_; lean_object* v_description_2977_; lean_object* v_keywords_2978_; lean_object* v_homepage_2979_; lean_object* v_license_2980_; lean_object* v_licenseFiles_2981_; lean_object* v_readmeFile_2982_; uint8_t v_reservoir_2983_; lean_object* v_enableArtifactCache_x3f_2984_; lean_object* v_restoreAllArtifacts_x3f_2985_; uint8_t v_libPrefixOnWindows_2986_; uint8_t v_allowImportAll_2987_; uint8_t v_fixedToolchain_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2998_; 
v_toWorkspaceConfig_2956_ = lean_ctor_get(v_cfg_2955_, 0);
v_toLeanConfig_2957_ = lean_ctor_get(v_cfg_2955_, 1);
v_bootstrap_2958_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26);
v_extraDepTargets_2959_ = lean_ctor_get(v_cfg_2955_, 2);
v_precompileModules_2960_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_2961_ = lean_ctor_get(v_cfg_2955_, 3);
v_srcDir_2962_ = lean_ctor_get(v_cfg_2955_, 4);
v_buildDir_2963_ = lean_ctor_get(v_cfg_2955_, 5);
v_leanLibDir_2964_ = lean_ctor_get(v_cfg_2955_, 6);
v_nativeLibDir_2965_ = lean_ctor_get(v_cfg_2955_, 7);
v_binDir_2966_ = lean_ctor_get(v_cfg_2955_, 8);
v_irDir_2967_ = lean_ctor_get(v_cfg_2955_, 9);
v_releaseRepo_2968_ = lean_ctor_get(v_cfg_2955_, 10);
v_buildArchive_2969_ = lean_ctor_get(v_cfg_2955_, 11);
v_preferReleaseBuild_2970_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26 + 2);
v_testDriver_2971_ = lean_ctor_get(v_cfg_2955_, 12);
v_testDriverArgs_2972_ = lean_ctor_get(v_cfg_2955_, 13);
v_lintDriver_2973_ = lean_ctor_get(v_cfg_2955_, 14);
v_lintDriverArgs_2974_ = lean_ctor_get(v_cfg_2955_, 15);
v_version_2975_ = lean_ctor_get(v_cfg_2955_, 16);
v_versionTags_2976_ = lean_ctor_get(v_cfg_2955_, 17);
v_description_2977_ = lean_ctor_get(v_cfg_2955_, 18);
v_keywords_2978_ = lean_ctor_get(v_cfg_2955_, 19);
v_homepage_2979_ = lean_ctor_get(v_cfg_2955_, 20);
v_license_2980_ = lean_ctor_get(v_cfg_2955_, 21);
v_licenseFiles_2981_ = lean_ctor_get(v_cfg_2955_, 22);
v_readmeFile_2982_ = lean_ctor_get(v_cfg_2955_, 23);
v_reservoir_2983_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_2984_ = lean_ctor_get(v_cfg_2955_, 24);
v_restoreAllArtifacts_x3f_2985_ = lean_ctor_get(v_cfg_2955_, 25);
v_libPrefixOnWindows_2986_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26 + 4);
v_allowImportAll_2987_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26 + 5);
v_fixedToolchain_2988_ = lean_ctor_get_uint8(v_cfg_2955_, sizeof(void*)*26 + 6);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_cfg_2955_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2990_ = v_cfg_2955_;
v_isShared_2991_ = v_isSharedCheck_2998_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_2985_);
lean_inc(v_enableArtifactCache_x3f_2984_);
lean_inc(v_readmeFile_2982_);
lean_inc(v_licenseFiles_2981_);
lean_inc(v_license_2980_);
lean_inc(v_homepage_2979_);
lean_inc(v_keywords_2978_);
lean_inc(v_description_2977_);
lean_inc(v_versionTags_2976_);
lean_inc(v_version_2975_);
lean_inc(v_lintDriverArgs_2974_);
lean_inc(v_lintDriver_2973_);
lean_inc(v_testDriverArgs_2972_);
lean_inc(v_testDriver_2971_);
lean_inc(v_buildArchive_2969_);
lean_inc(v_releaseRepo_2968_);
lean_inc(v_irDir_2967_);
lean_inc(v_binDir_2966_);
lean_inc(v_nativeLibDir_2965_);
lean_inc(v_leanLibDir_2964_);
lean_inc(v_buildDir_2963_);
lean_inc(v_srcDir_2962_);
lean_inc(v_moreGlobalServerArgs_2961_);
lean_inc(v_extraDepTargets_2959_);
lean_inc(v_toLeanConfig_2957_);
lean_inc(v_toWorkspaceConfig_2956_);
lean_dec(v_cfg_2955_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2998_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2992_ = lean_box(v_reservoir_2983_);
v___x_2993_ = lean_apply_1(v_f_2954_, v___x_2992_);
if (v_isShared_2991_ == 0)
{
v___x_2995_ = v___x_2990_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_toWorkspaceConfig_2956_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_toLeanConfig_2957_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_extraDepTargets_2959_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v_moreGlobalServerArgs_2961_);
lean_ctor_set(v_reuseFailAlloc_2997_, 4, v_srcDir_2962_);
lean_ctor_set(v_reuseFailAlloc_2997_, 5, v_buildDir_2963_);
lean_ctor_set(v_reuseFailAlloc_2997_, 6, v_leanLibDir_2964_);
lean_ctor_set(v_reuseFailAlloc_2997_, 7, v_nativeLibDir_2965_);
lean_ctor_set(v_reuseFailAlloc_2997_, 8, v_binDir_2966_);
lean_ctor_set(v_reuseFailAlloc_2997_, 9, v_irDir_2967_);
lean_ctor_set(v_reuseFailAlloc_2997_, 10, v_releaseRepo_2968_);
lean_ctor_set(v_reuseFailAlloc_2997_, 11, v_buildArchive_2969_);
lean_ctor_set(v_reuseFailAlloc_2997_, 12, v_testDriver_2971_);
lean_ctor_set(v_reuseFailAlloc_2997_, 13, v_testDriverArgs_2972_);
lean_ctor_set(v_reuseFailAlloc_2997_, 14, v_lintDriver_2973_);
lean_ctor_set(v_reuseFailAlloc_2997_, 15, v_lintDriverArgs_2974_);
lean_ctor_set(v_reuseFailAlloc_2997_, 16, v_version_2975_);
lean_ctor_set(v_reuseFailAlloc_2997_, 17, v_versionTags_2976_);
lean_ctor_set(v_reuseFailAlloc_2997_, 18, v_description_2977_);
lean_ctor_set(v_reuseFailAlloc_2997_, 19, v_keywords_2978_);
lean_ctor_set(v_reuseFailAlloc_2997_, 20, v_homepage_2979_);
lean_ctor_set(v_reuseFailAlloc_2997_, 21, v_license_2980_);
lean_ctor_set(v_reuseFailAlloc_2997_, 22, v_licenseFiles_2981_);
lean_ctor_set(v_reuseFailAlloc_2997_, 23, v_readmeFile_2982_);
lean_ctor_set(v_reuseFailAlloc_2997_, 24, v_enableArtifactCache_x3f_2984_);
lean_ctor_set(v_reuseFailAlloc_2997_, 25, v_restoreAllArtifacts_x3f_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2997_, sizeof(void*)*26, v_bootstrap_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_2997_, sizeof(void*)*26 + 1, v_precompileModules_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_2997_, sizeof(void*)*26 + 2, v_preferReleaseBuild_2970_);
v___x_2995_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_unbox(v___x_2993_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*26 + 3, v___x_2996_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_2986_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*26 + 5, v_allowImportAll_2987_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*26 + 6, v_fixedToolchain_2988_);
return v___x_2995_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* v_x_2999_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = 1;
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* v_x_3001_){
_start:
{
uint8_t v_res_3002_; lean_object* v_r_3003_; 
v_res_3002_ = l_Lake_PackageConfig_reservoir___proj___lam__3(v_x_3001_);
lean_dec_ref(v_x_3001_);
v_r_3003_ = lean_box(v_res_3002_);
return v_r_3003_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3013_, lean_object* v_n_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3016_, lean_object* v_n_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lake_PackageConfig_reservoir___proj(v_p_3016_, v_n_3017_);
lean_dec(v_n_3017_);
lean_dec(v_p_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3019_, lean_object* v_n_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lake_PackageConfig_reservoir___proj(v_p_3019_, v_n_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3022_, lean_object* v_n_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3022_, v_n_3023_);
lean_dec(v_n_3023_);
lean_dec(v_p_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* v_cfg_3025_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3026_; 
v_enableArtifactCache_x3f_3026_ = lean_ctor_get(v_cfg_3025_, 24);
lean_inc(v_enableArtifactCache_x3f_3026_);
return v_enableArtifactCache_x3f_3026_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* v_cfg_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(v_cfg_3027_);
lean_dec_ref(v_cfg_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* v_val_3029_, lean_object* v_cfg_3030_){
_start:
{
lean_object* v_toWorkspaceConfig_3031_; lean_object* v_toLeanConfig_3032_; uint8_t v_bootstrap_3033_; lean_object* v_extraDepTargets_3034_; uint8_t v_precompileModules_3035_; lean_object* v_moreGlobalServerArgs_3036_; lean_object* v_srcDir_3037_; lean_object* v_buildDir_3038_; lean_object* v_leanLibDir_3039_; lean_object* v_nativeLibDir_3040_; lean_object* v_binDir_3041_; lean_object* v_irDir_3042_; lean_object* v_releaseRepo_3043_; lean_object* v_buildArchive_3044_; uint8_t v_preferReleaseBuild_3045_; lean_object* v_testDriver_3046_; lean_object* v_testDriverArgs_3047_; lean_object* v_lintDriver_3048_; lean_object* v_lintDriverArgs_3049_; lean_object* v_version_3050_; lean_object* v_versionTags_3051_; lean_object* v_description_3052_; lean_object* v_keywords_3053_; lean_object* v_homepage_3054_; lean_object* v_license_3055_; lean_object* v_licenseFiles_3056_; lean_object* v_readmeFile_3057_; uint8_t v_reservoir_3058_; lean_object* v_restoreAllArtifacts_x3f_3059_; uint8_t v_libPrefixOnWindows_3060_; uint8_t v_allowImportAll_3061_; uint8_t v_fixedToolchain_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
v_toWorkspaceConfig_3031_ = lean_ctor_get(v_cfg_3030_, 0);
v_toLeanConfig_3032_ = lean_ctor_get(v_cfg_3030_, 1);
v_bootstrap_3033_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26);
v_extraDepTargets_3034_ = lean_ctor_get(v_cfg_3030_, 2);
v_precompileModules_3035_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3036_ = lean_ctor_get(v_cfg_3030_, 3);
v_srcDir_3037_ = lean_ctor_get(v_cfg_3030_, 4);
v_buildDir_3038_ = lean_ctor_get(v_cfg_3030_, 5);
v_leanLibDir_3039_ = lean_ctor_get(v_cfg_3030_, 6);
v_nativeLibDir_3040_ = lean_ctor_get(v_cfg_3030_, 7);
v_binDir_3041_ = lean_ctor_get(v_cfg_3030_, 8);
v_irDir_3042_ = lean_ctor_get(v_cfg_3030_, 9);
v_releaseRepo_3043_ = lean_ctor_get(v_cfg_3030_, 10);
v_buildArchive_3044_ = lean_ctor_get(v_cfg_3030_, 11);
v_preferReleaseBuild_3045_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26 + 2);
v_testDriver_3046_ = lean_ctor_get(v_cfg_3030_, 12);
v_testDriverArgs_3047_ = lean_ctor_get(v_cfg_3030_, 13);
v_lintDriver_3048_ = lean_ctor_get(v_cfg_3030_, 14);
v_lintDriverArgs_3049_ = lean_ctor_get(v_cfg_3030_, 15);
v_version_3050_ = lean_ctor_get(v_cfg_3030_, 16);
v_versionTags_3051_ = lean_ctor_get(v_cfg_3030_, 17);
v_description_3052_ = lean_ctor_get(v_cfg_3030_, 18);
v_keywords_3053_ = lean_ctor_get(v_cfg_3030_, 19);
v_homepage_3054_ = lean_ctor_get(v_cfg_3030_, 20);
v_license_3055_ = lean_ctor_get(v_cfg_3030_, 21);
v_licenseFiles_3056_ = lean_ctor_get(v_cfg_3030_, 22);
v_readmeFile_3057_ = lean_ctor_get(v_cfg_3030_, 23);
v_reservoir_3058_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26 + 3);
v_restoreAllArtifacts_x3f_3059_ = lean_ctor_get(v_cfg_3030_, 25);
v_libPrefixOnWindows_3060_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26 + 4);
v_allowImportAll_3061_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26 + 5);
v_fixedToolchain_3062_ = lean_ctor_get_uint8(v_cfg_3030_, sizeof(void*)*26 + 6);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_cfg_3030_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v_cfg_3030_, 24);
lean_dec(v_unused_3070_);
v___x_3064_ = v_cfg_3030_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3059_);
lean_inc(v_readmeFile_3057_);
lean_inc(v_licenseFiles_3056_);
lean_inc(v_license_3055_);
lean_inc(v_homepage_3054_);
lean_inc(v_keywords_3053_);
lean_inc(v_description_3052_);
lean_inc(v_versionTags_3051_);
lean_inc(v_version_3050_);
lean_inc(v_lintDriverArgs_3049_);
lean_inc(v_lintDriver_3048_);
lean_inc(v_testDriverArgs_3047_);
lean_inc(v_testDriver_3046_);
lean_inc(v_buildArchive_3044_);
lean_inc(v_releaseRepo_3043_);
lean_inc(v_irDir_3042_);
lean_inc(v_binDir_3041_);
lean_inc(v_nativeLibDir_3040_);
lean_inc(v_leanLibDir_3039_);
lean_inc(v_buildDir_3038_);
lean_inc(v_srcDir_3037_);
lean_inc(v_moreGlobalServerArgs_3036_);
lean_inc(v_extraDepTargets_3034_);
lean_inc(v_toLeanConfig_3032_);
lean_inc(v_toWorkspaceConfig_3031_);
lean_dec(v_cfg_3030_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 24, v_val_3029_);
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_toWorkspaceConfig_3031_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_toLeanConfig_3032_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_extraDepTargets_3034_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_moreGlobalServerArgs_3036_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_srcDir_3037_);
lean_ctor_set(v_reuseFailAlloc_3068_, 5, v_buildDir_3038_);
lean_ctor_set(v_reuseFailAlloc_3068_, 6, v_leanLibDir_3039_);
lean_ctor_set(v_reuseFailAlloc_3068_, 7, v_nativeLibDir_3040_);
lean_ctor_set(v_reuseFailAlloc_3068_, 8, v_binDir_3041_);
lean_ctor_set(v_reuseFailAlloc_3068_, 9, v_irDir_3042_);
lean_ctor_set(v_reuseFailAlloc_3068_, 10, v_releaseRepo_3043_);
lean_ctor_set(v_reuseFailAlloc_3068_, 11, v_buildArchive_3044_);
lean_ctor_set(v_reuseFailAlloc_3068_, 12, v_testDriver_3046_);
lean_ctor_set(v_reuseFailAlloc_3068_, 13, v_testDriverArgs_3047_);
lean_ctor_set(v_reuseFailAlloc_3068_, 14, v_lintDriver_3048_);
lean_ctor_set(v_reuseFailAlloc_3068_, 15, v_lintDriverArgs_3049_);
lean_ctor_set(v_reuseFailAlloc_3068_, 16, v_version_3050_);
lean_ctor_set(v_reuseFailAlloc_3068_, 17, v_versionTags_3051_);
lean_ctor_set(v_reuseFailAlloc_3068_, 18, v_description_3052_);
lean_ctor_set(v_reuseFailAlloc_3068_, 19, v_keywords_3053_);
lean_ctor_set(v_reuseFailAlloc_3068_, 20, v_homepage_3054_);
lean_ctor_set(v_reuseFailAlloc_3068_, 21, v_license_3055_);
lean_ctor_set(v_reuseFailAlloc_3068_, 22, v_licenseFiles_3056_);
lean_ctor_set(v_reuseFailAlloc_3068_, 23, v_readmeFile_3057_);
lean_ctor_set(v_reuseFailAlloc_3068_, 24, v_val_3029_);
lean_ctor_set(v_reuseFailAlloc_3068_, 25, v_restoreAllArtifacts_x3f_3059_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26, v_bootstrap_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26 + 1, v_precompileModules_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3045_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26 + 3, v_reservoir_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26 + 5, v_allowImportAll_3061_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*26 + 6, v_fixedToolchain_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* v_f_3071_, lean_object* v_cfg_3072_){
_start:
{
lean_object* v_toWorkspaceConfig_3073_; lean_object* v_toLeanConfig_3074_; uint8_t v_bootstrap_3075_; lean_object* v_extraDepTargets_3076_; uint8_t v_precompileModules_3077_; lean_object* v_moreGlobalServerArgs_3078_; lean_object* v_srcDir_3079_; lean_object* v_buildDir_3080_; lean_object* v_leanLibDir_3081_; lean_object* v_nativeLibDir_3082_; lean_object* v_binDir_3083_; lean_object* v_irDir_3084_; lean_object* v_releaseRepo_3085_; lean_object* v_buildArchive_3086_; uint8_t v_preferReleaseBuild_3087_; lean_object* v_testDriver_3088_; lean_object* v_testDriverArgs_3089_; lean_object* v_lintDriver_3090_; lean_object* v_lintDriverArgs_3091_; lean_object* v_version_3092_; lean_object* v_versionTags_3093_; lean_object* v_description_3094_; lean_object* v_keywords_3095_; lean_object* v_homepage_3096_; lean_object* v_license_3097_; lean_object* v_licenseFiles_3098_; lean_object* v_readmeFile_3099_; uint8_t v_reservoir_3100_; lean_object* v_enableArtifactCache_x3f_3101_; lean_object* v_restoreAllArtifacts_x3f_3102_; uint8_t v_libPrefixOnWindows_3103_; uint8_t v_allowImportAll_3104_; uint8_t v_fixedToolchain_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3113_; 
v_toWorkspaceConfig_3073_ = lean_ctor_get(v_cfg_3072_, 0);
v_toLeanConfig_3074_ = lean_ctor_get(v_cfg_3072_, 1);
v_bootstrap_3075_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26);
v_extraDepTargets_3076_ = lean_ctor_get(v_cfg_3072_, 2);
v_precompileModules_3077_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3078_ = lean_ctor_get(v_cfg_3072_, 3);
v_srcDir_3079_ = lean_ctor_get(v_cfg_3072_, 4);
v_buildDir_3080_ = lean_ctor_get(v_cfg_3072_, 5);
v_leanLibDir_3081_ = lean_ctor_get(v_cfg_3072_, 6);
v_nativeLibDir_3082_ = lean_ctor_get(v_cfg_3072_, 7);
v_binDir_3083_ = lean_ctor_get(v_cfg_3072_, 8);
v_irDir_3084_ = lean_ctor_get(v_cfg_3072_, 9);
v_releaseRepo_3085_ = lean_ctor_get(v_cfg_3072_, 10);
v_buildArchive_3086_ = lean_ctor_get(v_cfg_3072_, 11);
v_preferReleaseBuild_3087_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26 + 2);
v_testDriver_3088_ = lean_ctor_get(v_cfg_3072_, 12);
v_testDriverArgs_3089_ = lean_ctor_get(v_cfg_3072_, 13);
v_lintDriver_3090_ = lean_ctor_get(v_cfg_3072_, 14);
v_lintDriverArgs_3091_ = lean_ctor_get(v_cfg_3072_, 15);
v_version_3092_ = lean_ctor_get(v_cfg_3072_, 16);
v_versionTags_3093_ = lean_ctor_get(v_cfg_3072_, 17);
v_description_3094_ = lean_ctor_get(v_cfg_3072_, 18);
v_keywords_3095_ = lean_ctor_get(v_cfg_3072_, 19);
v_homepage_3096_ = lean_ctor_get(v_cfg_3072_, 20);
v_license_3097_ = lean_ctor_get(v_cfg_3072_, 21);
v_licenseFiles_3098_ = lean_ctor_get(v_cfg_3072_, 22);
v_readmeFile_3099_ = lean_ctor_get(v_cfg_3072_, 23);
v_reservoir_3100_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3101_ = lean_ctor_get(v_cfg_3072_, 24);
v_restoreAllArtifacts_x3f_3102_ = lean_ctor_get(v_cfg_3072_, 25);
v_libPrefixOnWindows_3103_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26 + 4);
v_allowImportAll_3104_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26 + 5);
v_fixedToolchain_3105_ = lean_ctor_get_uint8(v_cfg_3072_, sizeof(void*)*26 + 6);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_cfg_3072_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3107_ = v_cfg_3072_;
v_isShared_3108_ = v_isSharedCheck_3113_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3102_);
lean_inc(v_enableArtifactCache_x3f_3101_);
lean_inc(v_readmeFile_3099_);
lean_inc(v_licenseFiles_3098_);
lean_inc(v_license_3097_);
lean_inc(v_homepage_3096_);
lean_inc(v_keywords_3095_);
lean_inc(v_description_3094_);
lean_inc(v_versionTags_3093_);
lean_inc(v_version_3092_);
lean_inc(v_lintDriverArgs_3091_);
lean_inc(v_lintDriver_3090_);
lean_inc(v_testDriverArgs_3089_);
lean_inc(v_testDriver_3088_);
lean_inc(v_buildArchive_3086_);
lean_inc(v_releaseRepo_3085_);
lean_inc(v_irDir_3084_);
lean_inc(v_binDir_3083_);
lean_inc(v_nativeLibDir_3082_);
lean_inc(v_leanLibDir_3081_);
lean_inc(v_buildDir_3080_);
lean_inc(v_srcDir_3079_);
lean_inc(v_moreGlobalServerArgs_3078_);
lean_inc(v_extraDepTargets_3076_);
lean_inc(v_toLeanConfig_3074_);
lean_inc(v_toWorkspaceConfig_3073_);
lean_dec(v_cfg_3072_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3113_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_apply_1(v_f_3071_, v_enableArtifactCache_x3f_3101_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 24, v___x_3109_);
v___x_3111_ = v___x_3107_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_toWorkspaceConfig_3073_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_toLeanConfig_3074_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_extraDepTargets_3076_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_moreGlobalServerArgs_3078_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_srcDir_3079_);
lean_ctor_set(v_reuseFailAlloc_3112_, 5, v_buildDir_3080_);
lean_ctor_set(v_reuseFailAlloc_3112_, 6, v_leanLibDir_3081_);
lean_ctor_set(v_reuseFailAlloc_3112_, 7, v_nativeLibDir_3082_);
lean_ctor_set(v_reuseFailAlloc_3112_, 8, v_binDir_3083_);
lean_ctor_set(v_reuseFailAlloc_3112_, 9, v_irDir_3084_);
lean_ctor_set(v_reuseFailAlloc_3112_, 10, v_releaseRepo_3085_);
lean_ctor_set(v_reuseFailAlloc_3112_, 11, v_buildArchive_3086_);
lean_ctor_set(v_reuseFailAlloc_3112_, 12, v_testDriver_3088_);
lean_ctor_set(v_reuseFailAlloc_3112_, 13, v_testDriverArgs_3089_);
lean_ctor_set(v_reuseFailAlloc_3112_, 14, v_lintDriver_3090_);
lean_ctor_set(v_reuseFailAlloc_3112_, 15, v_lintDriverArgs_3091_);
lean_ctor_set(v_reuseFailAlloc_3112_, 16, v_version_3092_);
lean_ctor_set(v_reuseFailAlloc_3112_, 17, v_versionTags_3093_);
lean_ctor_set(v_reuseFailAlloc_3112_, 18, v_description_3094_);
lean_ctor_set(v_reuseFailAlloc_3112_, 19, v_keywords_3095_);
lean_ctor_set(v_reuseFailAlloc_3112_, 20, v_homepage_3096_);
lean_ctor_set(v_reuseFailAlloc_3112_, 21, v_license_3097_);
lean_ctor_set(v_reuseFailAlloc_3112_, 22, v_licenseFiles_3098_);
lean_ctor_set(v_reuseFailAlloc_3112_, 23, v_readmeFile_3099_);
lean_ctor_set(v_reuseFailAlloc_3112_, 24, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3112_, 25, v_restoreAllArtifacts_x3f_3102_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26, v_bootstrap_3075_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26 + 1, v_precompileModules_3077_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26 + 3, v_reservoir_3100_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3103_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26 + 5, v_allowImportAll_3104_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*26 + 6, v_fixedToolchain_3105_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* v_x_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_box(0);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* v_x_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(v_x_3116_);
lean_dec_ref(v_x_3116_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3127_, lean_object* v_n_3128_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3130_, lean_object* v_n_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3130_, v_n_3131_);
lean_dec(v_n_3131_);
lean_dec(v_p_3130_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3133_, lean_object* v_n_3134_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3133_, v_n_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3136_, lean_object* v_n_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3136_, v_n_3137_);
lean_dec(v_n_3137_);
lean_dec(v_p_3136_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3139_, lean_object* v_n_3140_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3139_, v_n_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3142_, lean_object* v_n_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3142_, v_n_3143_);
lean_dec(v_n_3143_);
lean_dec(v_p_3142_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object* v_cfg_3145_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3146_; 
v_restoreAllArtifacts_x3f_3146_ = lean_ctor_get(v_cfg_3145_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3146_);
return v_restoreAllArtifacts_x3f_3146_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object* v_cfg_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(v_cfg_3147_);
lean_dec_ref(v_cfg_3147_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object* v_val_3149_, lean_object* v_cfg_3150_){
_start:
{
lean_object* v_toWorkspaceConfig_3151_; lean_object* v_toLeanConfig_3152_; uint8_t v_bootstrap_3153_; lean_object* v_extraDepTargets_3154_; uint8_t v_precompileModules_3155_; lean_object* v_moreGlobalServerArgs_3156_; lean_object* v_srcDir_3157_; lean_object* v_buildDir_3158_; lean_object* v_leanLibDir_3159_; lean_object* v_nativeLibDir_3160_; lean_object* v_binDir_3161_; lean_object* v_irDir_3162_; lean_object* v_releaseRepo_3163_; lean_object* v_buildArchive_3164_; uint8_t v_preferReleaseBuild_3165_; lean_object* v_testDriver_3166_; lean_object* v_testDriverArgs_3167_; lean_object* v_lintDriver_3168_; lean_object* v_lintDriverArgs_3169_; lean_object* v_version_3170_; lean_object* v_versionTags_3171_; lean_object* v_description_3172_; lean_object* v_keywords_3173_; lean_object* v_homepage_3174_; lean_object* v_license_3175_; lean_object* v_licenseFiles_3176_; lean_object* v_readmeFile_3177_; uint8_t v_reservoir_3178_; lean_object* v_enableArtifactCache_x3f_3179_; uint8_t v_libPrefixOnWindows_3180_; uint8_t v_allowImportAll_3181_; uint8_t v_fixedToolchain_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
v_toWorkspaceConfig_3151_ = lean_ctor_get(v_cfg_3150_, 0);
v_toLeanConfig_3152_ = lean_ctor_get(v_cfg_3150_, 1);
v_bootstrap_3153_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26);
v_extraDepTargets_3154_ = lean_ctor_get(v_cfg_3150_, 2);
v_precompileModules_3155_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3156_ = lean_ctor_get(v_cfg_3150_, 3);
v_srcDir_3157_ = lean_ctor_get(v_cfg_3150_, 4);
v_buildDir_3158_ = lean_ctor_get(v_cfg_3150_, 5);
v_leanLibDir_3159_ = lean_ctor_get(v_cfg_3150_, 6);
v_nativeLibDir_3160_ = lean_ctor_get(v_cfg_3150_, 7);
v_binDir_3161_ = lean_ctor_get(v_cfg_3150_, 8);
v_irDir_3162_ = lean_ctor_get(v_cfg_3150_, 9);
v_releaseRepo_3163_ = lean_ctor_get(v_cfg_3150_, 10);
v_buildArchive_3164_ = lean_ctor_get(v_cfg_3150_, 11);
v_preferReleaseBuild_3165_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26 + 2);
v_testDriver_3166_ = lean_ctor_get(v_cfg_3150_, 12);
v_testDriverArgs_3167_ = lean_ctor_get(v_cfg_3150_, 13);
v_lintDriver_3168_ = lean_ctor_get(v_cfg_3150_, 14);
v_lintDriverArgs_3169_ = lean_ctor_get(v_cfg_3150_, 15);
v_version_3170_ = lean_ctor_get(v_cfg_3150_, 16);
v_versionTags_3171_ = lean_ctor_get(v_cfg_3150_, 17);
v_description_3172_ = lean_ctor_get(v_cfg_3150_, 18);
v_keywords_3173_ = lean_ctor_get(v_cfg_3150_, 19);
v_homepage_3174_ = lean_ctor_get(v_cfg_3150_, 20);
v_license_3175_ = lean_ctor_get(v_cfg_3150_, 21);
v_licenseFiles_3176_ = lean_ctor_get(v_cfg_3150_, 22);
v_readmeFile_3177_ = lean_ctor_get(v_cfg_3150_, 23);
v_reservoir_3178_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3179_ = lean_ctor_get(v_cfg_3150_, 24);
v_libPrefixOnWindows_3180_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26 + 4);
v_allowImportAll_3181_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26 + 5);
v_fixedToolchain_3182_ = lean_ctor_get_uint8(v_cfg_3150_, sizeof(void*)*26 + 6);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_cfg_3150_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v_cfg_3150_, 25);
lean_dec(v_unused_3190_);
v___x_3184_ = v_cfg_3150_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_enableArtifactCache_x3f_3179_);
lean_inc(v_readmeFile_3177_);
lean_inc(v_licenseFiles_3176_);
lean_inc(v_license_3175_);
lean_inc(v_homepage_3174_);
lean_inc(v_keywords_3173_);
lean_inc(v_description_3172_);
lean_inc(v_versionTags_3171_);
lean_inc(v_version_3170_);
lean_inc(v_lintDriverArgs_3169_);
lean_inc(v_lintDriver_3168_);
lean_inc(v_testDriverArgs_3167_);
lean_inc(v_testDriver_3166_);
lean_inc(v_buildArchive_3164_);
lean_inc(v_releaseRepo_3163_);
lean_inc(v_irDir_3162_);
lean_inc(v_binDir_3161_);
lean_inc(v_nativeLibDir_3160_);
lean_inc(v_leanLibDir_3159_);
lean_inc(v_buildDir_3158_);
lean_inc(v_srcDir_3157_);
lean_inc(v_moreGlobalServerArgs_3156_);
lean_inc(v_extraDepTargets_3154_);
lean_inc(v_toLeanConfig_3152_);
lean_inc(v_toWorkspaceConfig_3151_);
lean_dec(v_cfg_3150_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 25, v_val_3149_);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_toWorkspaceConfig_3151_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_toLeanConfig_3152_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_extraDepTargets_3154_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_moreGlobalServerArgs_3156_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_srcDir_3157_);
lean_ctor_set(v_reuseFailAlloc_3188_, 5, v_buildDir_3158_);
lean_ctor_set(v_reuseFailAlloc_3188_, 6, v_leanLibDir_3159_);
lean_ctor_set(v_reuseFailAlloc_3188_, 7, v_nativeLibDir_3160_);
lean_ctor_set(v_reuseFailAlloc_3188_, 8, v_binDir_3161_);
lean_ctor_set(v_reuseFailAlloc_3188_, 9, v_irDir_3162_);
lean_ctor_set(v_reuseFailAlloc_3188_, 10, v_releaseRepo_3163_);
lean_ctor_set(v_reuseFailAlloc_3188_, 11, v_buildArchive_3164_);
lean_ctor_set(v_reuseFailAlloc_3188_, 12, v_testDriver_3166_);
lean_ctor_set(v_reuseFailAlloc_3188_, 13, v_testDriverArgs_3167_);
lean_ctor_set(v_reuseFailAlloc_3188_, 14, v_lintDriver_3168_);
lean_ctor_set(v_reuseFailAlloc_3188_, 15, v_lintDriverArgs_3169_);
lean_ctor_set(v_reuseFailAlloc_3188_, 16, v_version_3170_);
lean_ctor_set(v_reuseFailAlloc_3188_, 17, v_versionTags_3171_);
lean_ctor_set(v_reuseFailAlloc_3188_, 18, v_description_3172_);
lean_ctor_set(v_reuseFailAlloc_3188_, 19, v_keywords_3173_);
lean_ctor_set(v_reuseFailAlloc_3188_, 20, v_homepage_3174_);
lean_ctor_set(v_reuseFailAlloc_3188_, 21, v_license_3175_);
lean_ctor_set(v_reuseFailAlloc_3188_, 22, v_licenseFiles_3176_);
lean_ctor_set(v_reuseFailAlloc_3188_, 23, v_readmeFile_3177_);
lean_ctor_set(v_reuseFailAlloc_3188_, 24, v_enableArtifactCache_x3f_3179_);
lean_ctor_set(v_reuseFailAlloc_3188_, 25, v_val_3149_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26, v_bootstrap_3153_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26 + 1, v_precompileModules_3155_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26 + 3, v_reservoir_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26 + 5, v_allowImportAll_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*26 + 6, v_fixedToolchain_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object* v_f_3191_, lean_object* v_cfg_3192_){
_start:
{
lean_object* v_toWorkspaceConfig_3193_; lean_object* v_toLeanConfig_3194_; uint8_t v_bootstrap_3195_; lean_object* v_extraDepTargets_3196_; uint8_t v_precompileModules_3197_; lean_object* v_moreGlobalServerArgs_3198_; lean_object* v_srcDir_3199_; lean_object* v_buildDir_3200_; lean_object* v_leanLibDir_3201_; lean_object* v_nativeLibDir_3202_; lean_object* v_binDir_3203_; lean_object* v_irDir_3204_; lean_object* v_releaseRepo_3205_; lean_object* v_buildArchive_3206_; uint8_t v_preferReleaseBuild_3207_; lean_object* v_testDriver_3208_; lean_object* v_testDriverArgs_3209_; lean_object* v_lintDriver_3210_; lean_object* v_lintDriverArgs_3211_; lean_object* v_version_3212_; lean_object* v_versionTags_3213_; lean_object* v_description_3214_; lean_object* v_keywords_3215_; lean_object* v_homepage_3216_; lean_object* v_license_3217_; lean_object* v_licenseFiles_3218_; lean_object* v_readmeFile_3219_; uint8_t v_reservoir_3220_; lean_object* v_enableArtifactCache_x3f_3221_; lean_object* v_restoreAllArtifacts_x3f_3222_; uint8_t v_libPrefixOnWindows_3223_; uint8_t v_allowImportAll_3224_; uint8_t v_fixedToolchain_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3233_; 
v_toWorkspaceConfig_3193_ = lean_ctor_get(v_cfg_3192_, 0);
v_toLeanConfig_3194_ = lean_ctor_get(v_cfg_3192_, 1);
v_bootstrap_3195_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26);
v_extraDepTargets_3196_ = lean_ctor_get(v_cfg_3192_, 2);
v_precompileModules_3197_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3198_ = lean_ctor_get(v_cfg_3192_, 3);
v_srcDir_3199_ = lean_ctor_get(v_cfg_3192_, 4);
v_buildDir_3200_ = lean_ctor_get(v_cfg_3192_, 5);
v_leanLibDir_3201_ = lean_ctor_get(v_cfg_3192_, 6);
v_nativeLibDir_3202_ = lean_ctor_get(v_cfg_3192_, 7);
v_binDir_3203_ = lean_ctor_get(v_cfg_3192_, 8);
v_irDir_3204_ = lean_ctor_get(v_cfg_3192_, 9);
v_releaseRepo_3205_ = lean_ctor_get(v_cfg_3192_, 10);
v_buildArchive_3206_ = lean_ctor_get(v_cfg_3192_, 11);
v_preferReleaseBuild_3207_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26 + 2);
v_testDriver_3208_ = lean_ctor_get(v_cfg_3192_, 12);
v_testDriverArgs_3209_ = lean_ctor_get(v_cfg_3192_, 13);
v_lintDriver_3210_ = lean_ctor_get(v_cfg_3192_, 14);
v_lintDriverArgs_3211_ = lean_ctor_get(v_cfg_3192_, 15);
v_version_3212_ = lean_ctor_get(v_cfg_3192_, 16);
v_versionTags_3213_ = lean_ctor_get(v_cfg_3192_, 17);
v_description_3214_ = lean_ctor_get(v_cfg_3192_, 18);
v_keywords_3215_ = lean_ctor_get(v_cfg_3192_, 19);
v_homepage_3216_ = lean_ctor_get(v_cfg_3192_, 20);
v_license_3217_ = lean_ctor_get(v_cfg_3192_, 21);
v_licenseFiles_3218_ = lean_ctor_get(v_cfg_3192_, 22);
v_readmeFile_3219_ = lean_ctor_get(v_cfg_3192_, 23);
v_reservoir_3220_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3221_ = lean_ctor_get(v_cfg_3192_, 24);
v_restoreAllArtifacts_x3f_3222_ = lean_ctor_get(v_cfg_3192_, 25);
v_libPrefixOnWindows_3223_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26 + 4);
v_allowImportAll_3224_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26 + 5);
v_fixedToolchain_3225_ = lean_ctor_get_uint8(v_cfg_3192_, sizeof(void*)*26 + 6);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_cfg_3192_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3227_ = v_cfg_3192_;
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3222_);
lean_inc(v_enableArtifactCache_x3f_3221_);
lean_inc(v_readmeFile_3219_);
lean_inc(v_licenseFiles_3218_);
lean_inc(v_license_3217_);
lean_inc(v_homepage_3216_);
lean_inc(v_keywords_3215_);
lean_inc(v_description_3214_);
lean_inc(v_versionTags_3213_);
lean_inc(v_version_3212_);
lean_inc(v_lintDriverArgs_3211_);
lean_inc(v_lintDriver_3210_);
lean_inc(v_testDriverArgs_3209_);
lean_inc(v_testDriver_3208_);
lean_inc(v_buildArchive_3206_);
lean_inc(v_releaseRepo_3205_);
lean_inc(v_irDir_3204_);
lean_inc(v_binDir_3203_);
lean_inc(v_nativeLibDir_3202_);
lean_inc(v_leanLibDir_3201_);
lean_inc(v_buildDir_3200_);
lean_inc(v_srcDir_3199_);
lean_inc(v_moreGlobalServerArgs_3198_);
lean_inc(v_extraDepTargets_3196_);
lean_inc(v_toLeanConfig_3194_);
lean_inc(v_toWorkspaceConfig_3193_);
lean_dec(v_cfg_3192_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_apply_1(v_f_3191_, v_restoreAllArtifacts_x3f_3222_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 25, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_toWorkspaceConfig_3193_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_toLeanConfig_3194_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_extraDepTargets_3196_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_moreGlobalServerArgs_3198_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v_srcDir_3199_);
lean_ctor_set(v_reuseFailAlloc_3232_, 5, v_buildDir_3200_);
lean_ctor_set(v_reuseFailAlloc_3232_, 6, v_leanLibDir_3201_);
lean_ctor_set(v_reuseFailAlloc_3232_, 7, v_nativeLibDir_3202_);
lean_ctor_set(v_reuseFailAlloc_3232_, 8, v_binDir_3203_);
lean_ctor_set(v_reuseFailAlloc_3232_, 9, v_irDir_3204_);
lean_ctor_set(v_reuseFailAlloc_3232_, 10, v_releaseRepo_3205_);
lean_ctor_set(v_reuseFailAlloc_3232_, 11, v_buildArchive_3206_);
lean_ctor_set(v_reuseFailAlloc_3232_, 12, v_testDriver_3208_);
lean_ctor_set(v_reuseFailAlloc_3232_, 13, v_testDriverArgs_3209_);
lean_ctor_set(v_reuseFailAlloc_3232_, 14, v_lintDriver_3210_);
lean_ctor_set(v_reuseFailAlloc_3232_, 15, v_lintDriverArgs_3211_);
lean_ctor_set(v_reuseFailAlloc_3232_, 16, v_version_3212_);
lean_ctor_set(v_reuseFailAlloc_3232_, 17, v_versionTags_3213_);
lean_ctor_set(v_reuseFailAlloc_3232_, 18, v_description_3214_);
lean_ctor_set(v_reuseFailAlloc_3232_, 19, v_keywords_3215_);
lean_ctor_set(v_reuseFailAlloc_3232_, 20, v_homepage_3216_);
lean_ctor_set(v_reuseFailAlloc_3232_, 21, v_license_3217_);
lean_ctor_set(v_reuseFailAlloc_3232_, 22, v_licenseFiles_3218_);
lean_ctor_set(v_reuseFailAlloc_3232_, 23, v_readmeFile_3219_);
lean_ctor_set(v_reuseFailAlloc_3232_, 24, v_enableArtifactCache_x3f_3221_);
lean_ctor_set(v_reuseFailAlloc_3232_, 25, v___x_3229_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26, v_bootstrap_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26 + 1, v_precompileModules_3197_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3207_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26 + 3, v_reservoir_3220_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26 + 5, v_allowImportAll_3224_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*26 + 6, v_fixedToolchain_3225_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3242_, lean_object* v_n_3243_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3));
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3245_, lean_object* v_n_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3245_, v_n_3246_);
lean_dec(v_n_3246_);
lean_dec(v_p_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3248_, lean_object* v_n_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3248_, v_n_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3251_, lean_object* v_n_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3251_, v_n_3252_);
lean_dec(v_n_3252_);
lean_dec(v_p_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3254_, lean_object* v_n_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3254_, v_n_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3257_, lean_object* v_n_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3257_, v_n_3258_);
lean_dec(v_n_3258_);
lean_dec(v_p_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_3260_){
_start:
{
uint8_t v_libPrefixOnWindows_3261_; 
v_libPrefixOnWindows_3261_ = lean_ctor_get_uint8(v_cfg_3260_, sizeof(void*)*26 + 4);
return v_libPrefixOnWindows_3261_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_3262_){
_start:
{
uint8_t v_res_3263_; lean_object* v_r_3264_; 
v_res_3263_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(v_cfg_3262_);
lean_dec_ref(v_cfg_3262_);
v_r_3264_ = lean_box(v_res_3263_);
return v_r_3264_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_3265_, lean_object* v_cfg_3266_){
_start:
{
lean_object* v_toWorkspaceConfig_3267_; lean_object* v_toLeanConfig_3268_; uint8_t v_bootstrap_3269_; lean_object* v_extraDepTargets_3270_; uint8_t v_precompileModules_3271_; lean_object* v_moreGlobalServerArgs_3272_; lean_object* v_srcDir_3273_; lean_object* v_buildDir_3274_; lean_object* v_leanLibDir_3275_; lean_object* v_nativeLibDir_3276_; lean_object* v_binDir_3277_; lean_object* v_irDir_3278_; lean_object* v_releaseRepo_3279_; lean_object* v_buildArchive_3280_; uint8_t v_preferReleaseBuild_3281_; lean_object* v_testDriver_3282_; lean_object* v_testDriverArgs_3283_; lean_object* v_lintDriver_3284_; lean_object* v_lintDriverArgs_3285_; lean_object* v_version_3286_; lean_object* v_versionTags_3287_; lean_object* v_description_3288_; lean_object* v_keywords_3289_; lean_object* v_homepage_3290_; lean_object* v_license_3291_; lean_object* v_licenseFiles_3292_; lean_object* v_readmeFile_3293_; uint8_t v_reservoir_3294_; lean_object* v_enableArtifactCache_x3f_3295_; lean_object* v_restoreAllArtifacts_x3f_3296_; uint8_t v_allowImportAll_3297_; uint8_t v_fixedToolchain_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
v_toWorkspaceConfig_3267_ = lean_ctor_get(v_cfg_3266_, 0);
v_toLeanConfig_3268_ = lean_ctor_get(v_cfg_3266_, 1);
v_bootstrap_3269_ = lean_ctor_get_uint8(v_cfg_3266_, sizeof(void*)*26);
v_extraDepTargets_3270_ = lean_ctor_get(v_cfg_3266_, 2);
v_precompileModules_3271_ = lean_ctor_get_uint8(v_cfg_3266_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3272_ = lean_ctor_get(v_cfg_3266_, 3);
v_srcDir_3273_ = lean_ctor_get(v_cfg_3266_, 4);
v_buildDir_3274_ = lean_ctor_get(v_cfg_3266_, 5);
v_leanLibDir_3275_ = lean_ctor_get(v_cfg_3266_, 6);
v_nativeLibDir_3276_ = lean_ctor_get(v_cfg_3266_, 7);
v_binDir_3277_ = lean_ctor_get(v_cfg_3266_, 8);
v_irDir_3278_ = lean_ctor_get(v_cfg_3266_, 9);
v_releaseRepo_3279_ = lean_ctor_get(v_cfg_3266_, 10);
v_buildArchive_3280_ = lean_ctor_get(v_cfg_3266_, 11);
v_preferReleaseBuild_3281_ = lean_ctor_get_uint8(v_cfg_3266_, sizeof(void*)*26 + 2);
v_testDriver_3282_ = lean_ctor_get(v_cfg_3266_, 12);
v_testDriverArgs_3283_ = lean_ctor_get(v_cfg_3266_, 13);
v_lintDriver_3284_ = lean_ctor_get(v_cfg_3266_, 14);
v_lintDriverArgs_3285_ = lean_ctor_get(v_cfg_3266_, 15);
v_version_3286_ = lean_ctor_get(v_cfg_3266_, 16);
v_versionTags_3287_ = lean_ctor_get(v_cfg_3266_, 17);
v_description_3288_ = lean_ctor_get(v_cfg_3266_, 18);
v_keywords_3289_ = lean_ctor_get(v_cfg_3266_, 19);
v_homepage_3290_ = lean_ctor_get(v_cfg_3266_, 20);
v_license_3291_ = lean_ctor_get(v_cfg_3266_, 21);
v_licenseFiles_3292_ = lean_ctor_get(v_cfg_3266_, 22);
v_readmeFile_3293_ = lean_ctor_get(v_cfg_3266_, 23);
v_reservoir_3294_ = lean_ctor_get_uint8(v_cfg_3266_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3295_ = lean_ctor_get(v_cfg_3266_, 24);
v_restoreAllArtifacts_x3f_3296_ = lean_ctor_get(v_cfg_3266_, 25);
v_allowImportAll_3297_ = lean_ctor_get_uint8(v_cfg_3266_, sizeof(void*)*26 + 5);
v_fixedToolchain_3298_ = lean_ctor_get_uint8(v_cfg_3266_, sizeof(void*)*26 + 6);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_cfg_3266_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v_cfg_3266_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3296_);
lean_inc(v_enableArtifactCache_x3f_3295_);
lean_inc(v_readmeFile_3293_);
lean_inc(v_licenseFiles_3292_);
lean_inc(v_license_3291_);
lean_inc(v_homepage_3290_);
lean_inc(v_keywords_3289_);
lean_inc(v_description_3288_);
lean_inc(v_versionTags_3287_);
lean_inc(v_version_3286_);
lean_inc(v_lintDriverArgs_3285_);
lean_inc(v_lintDriver_3284_);
lean_inc(v_testDriverArgs_3283_);
lean_inc(v_testDriver_3282_);
lean_inc(v_buildArchive_3280_);
lean_inc(v_releaseRepo_3279_);
lean_inc(v_irDir_3278_);
lean_inc(v_binDir_3277_);
lean_inc(v_nativeLibDir_3276_);
lean_inc(v_leanLibDir_3275_);
lean_inc(v_buildDir_3274_);
lean_inc(v_srcDir_3273_);
lean_inc(v_moreGlobalServerArgs_3272_);
lean_inc(v_extraDepTargets_3270_);
lean_inc(v_toLeanConfig_3268_);
lean_inc(v_toWorkspaceConfig_3267_);
lean_dec(v_cfg_3266_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_toWorkspaceConfig_3267_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_toLeanConfig_3268_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_extraDepTargets_3270_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_moreGlobalServerArgs_3272_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_srcDir_3273_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v_buildDir_3274_);
lean_ctor_set(v_reuseFailAlloc_3304_, 6, v_leanLibDir_3275_);
lean_ctor_set(v_reuseFailAlloc_3304_, 7, v_nativeLibDir_3276_);
lean_ctor_set(v_reuseFailAlloc_3304_, 8, v_binDir_3277_);
lean_ctor_set(v_reuseFailAlloc_3304_, 9, v_irDir_3278_);
lean_ctor_set(v_reuseFailAlloc_3304_, 10, v_releaseRepo_3279_);
lean_ctor_set(v_reuseFailAlloc_3304_, 11, v_buildArchive_3280_);
lean_ctor_set(v_reuseFailAlloc_3304_, 12, v_testDriver_3282_);
lean_ctor_set(v_reuseFailAlloc_3304_, 13, v_testDriverArgs_3283_);
lean_ctor_set(v_reuseFailAlloc_3304_, 14, v_lintDriver_3284_);
lean_ctor_set(v_reuseFailAlloc_3304_, 15, v_lintDriverArgs_3285_);
lean_ctor_set(v_reuseFailAlloc_3304_, 16, v_version_3286_);
lean_ctor_set(v_reuseFailAlloc_3304_, 17, v_versionTags_3287_);
lean_ctor_set(v_reuseFailAlloc_3304_, 18, v_description_3288_);
lean_ctor_set(v_reuseFailAlloc_3304_, 19, v_keywords_3289_);
lean_ctor_set(v_reuseFailAlloc_3304_, 20, v_homepage_3290_);
lean_ctor_set(v_reuseFailAlloc_3304_, 21, v_license_3291_);
lean_ctor_set(v_reuseFailAlloc_3304_, 22, v_licenseFiles_3292_);
lean_ctor_set(v_reuseFailAlloc_3304_, 23, v_readmeFile_3293_);
lean_ctor_set(v_reuseFailAlloc_3304_, 24, v_enableArtifactCache_x3f_3295_);
lean_ctor_set(v_reuseFailAlloc_3304_, 25, v_restoreAllArtifacts_x3f_3296_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*26, v_bootstrap_3269_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*26 + 1, v_precompileModules_3271_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3281_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*26 + 3, v_reservoir_3294_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*26 + 5, v_allowImportAll_3297_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*26 + 6, v_fixedToolchain_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*26 + 4, v_val_3265_);
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_3306_, lean_object* v_cfg_3307_){
_start:
{
uint8_t v_val_134__boxed_3308_; lean_object* v_res_3309_; 
v_val_134__boxed_3308_ = lean_unbox(v_val_3306_);
v_res_3309_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(v_val_134__boxed_3308_, v_cfg_3307_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_3310_, lean_object* v_cfg_3311_){
_start:
{
lean_object* v_toWorkspaceConfig_3312_; lean_object* v_toLeanConfig_3313_; uint8_t v_bootstrap_3314_; lean_object* v_extraDepTargets_3315_; uint8_t v_precompileModules_3316_; lean_object* v_moreGlobalServerArgs_3317_; lean_object* v_srcDir_3318_; lean_object* v_buildDir_3319_; lean_object* v_leanLibDir_3320_; lean_object* v_nativeLibDir_3321_; lean_object* v_binDir_3322_; lean_object* v_irDir_3323_; lean_object* v_releaseRepo_3324_; lean_object* v_buildArchive_3325_; uint8_t v_preferReleaseBuild_3326_; lean_object* v_testDriver_3327_; lean_object* v_testDriverArgs_3328_; lean_object* v_lintDriver_3329_; lean_object* v_lintDriverArgs_3330_; lean_object* v_version_3331_; lean_object* v_versionTags_3332_; lean_object* v_description_3333_; lean_object* v_keywords_3334_; lean_object* v_homepage_3335_; lean_object* v_license_3336_; lean_object* v_licenseFiles_3337_; lean_object* v_readmeFile_3338_; uint8_t v_reservoir_3339_; lean_object* v_enableArtifactCache_x3f_3340_; lean_object* v_restoreAllArtifacts_x3f_3341_; uint8_t v_libPrefixOnWindows_3342_; uint8_t v_allowImportAll_3343_; uint8_t v_fixedToolchain_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3354_; 
v_toWorkspaceConfig_3312_ = lean_ctor_get(v_cfg_3311_, 0);
v_toLeanConfig_3313_ = lean_ctor_get(v_cfg_3311_, 1);
v_bootstrap_3314_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26);
v_extraDepTargets_3315_ = lean_ctor_get(v_cfg_3311_, 2);
v_precompileModules_3316_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3317_ = lean_ctor_get(v_cfg_3311_, 3);
v_srcDir_3318_ = lean_ctor_get(v_cfg_3311_, 4);
v_buildDir_3319_ = lean_ctor_get(v_cfg_3311_, 5);
v_leanLibDir_3320_ = lean_ctor_get(v_cfg_3311_, 6);
v_nativeLibDir_3321_ = lean_ctor_get(v_cfg_3311_, 7);
v_binDir_3322_ = lean_ctor_get(v_cfg_3311_, 8);
v_irDir_3323_ = lean_ctor_get(v_cfg_3311_, 9);
v_releaseRepo_3324_ = lean_ctor_get(v_cfg_3311_, 10);
v_buildArchive_3325_ = lean_ctor_get(v_cfg_3311_, 11);
v_preferReleaseBuild_3326_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26 + 2);
v_testDriver_3327_ = lean_ctor_get(v_cfg_3311_, 12);
v_testDriverArgs_3328_ = lean_ctor_get(v_cfg_3311_, 13);
v_lintDriver_3329_ = lean_ctor_get(v_cfg_3311_, 14);
v_lintDriverArgs_3330_ = lean_ctor_get(v_cfg_3311_, 15);
v_version_3331_ = lean_ctor_get(v_cfg_3311_, 16);
v_versionTags_3332_ = lean_ctor_get(v_cfg_3311_, 17);
v_description_3333_ = lean_ctor_get(v_cfg_3311_, 18);
v_keywords_3334_ = lean_ctor_get(v_cfg_3311_, 19);
v_homepage_3335_ = lean_ctor_get(v_cfg_3311_, 20);
v_license_3336_ = lean_ctor_get(v_cfg_3311_, 21);
v_licenseFiles_3337_ = lean_ctor_get(v_cfg_3311_, 22);
v_readmeFile_3338_ = lean_ctor_get(v_cfg_3311_, 23);
v_reservoir_3339_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3340_ = lean_ctor_get(v_cfg_3311_, 24);
v_restoreAllArtifacts_x3f_3341_ = lean_ctor_get(v_cfg_3311_, 25);
v_libPrefixOnWindows_3342_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26 + 4);
v_allowImportAll_3343_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26 + 5);
v_fixedToolchain_3344_ = lean_ctor_get_uint8(v_cfg_3311_, sizeof(void*)*26 + 6);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_cfg_3311_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3346_ = v_cfg_3311_;
v_isShared_3347_ = v_isSharedCheck_3354_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3341_);
lean_inc(v_enableArtifactCache_x3f_3340_);
lean_inc(v_readmeFile_3338_);
lean_inc(v_licenseFiles_3337_);
lean_inc(v_license_3336_);
lean_inc(v_homepage_3335_);
lean_inc(v_keywords_3334_);
lean_inc(v_description_3333_);
lean_inc(v_versionTags_3332_);
lean_inc(v_version_3331_);
lean_inc(v_lintDriverArgs_3330_);
lean_inc(v_lintDriver_3329_);
lean_inc(v_testDriverArgs_3328_);
lean_inc(v_testDriver_3327_);
lean_inc(v_buildArchive_3325_);
lean_inc(v_releaseRepo_3324_);
lean_inc(v_irDir_3323_);
lean_inc(v_binDir_3322_);
lean_inc(v_nativeLibDir_3321_);
lean_inc(v_leanLibDir_3320_);
lean_inc(v_buildDir_3319_);
lean_inc(v_srcDir_3318_);
lean_inc(v_moreGlobalServerArgs_3317_);
lean_inc(v_extraDepTargets_3315_);
lean_inc(v_toLeanConfig_3313_);
lean_inc(v_toWorkspaceConfig_3312_);
lean_dec(v_cfg_3311_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3354_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3348_ = lean_box(v_libPrefixOnWindows_3342_);
v___x_3349_ = lean_apply_1(v_f_3310_, v___x_3348_);
if (v_isShared_3347_ == 0)
{
v___x_3351_ = v___x_3346_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_toWorkspaceConfig_3312_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_toLeanConfig_3313_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_extraDepTargets_3315_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v_moreGlobalServerArgs_3317_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_srcDir_3318_);
lean_ctor_set(v_reuseFailAlloc_3353_, 5, v_buildDir_3319_);
lean_ctor_set(v_reuseFailAlloc_3353_, 6, v_leanLibDir_3320_);
lean_ctor_set(v_reuseFailAlloc_3353_, 7, v_nativeLibDir_3321_);
lean_ctor_set(v_reuseFailAlloc_3353_, 8, v_binDir_3322_);
lean_ctor_set(v_reuseFailAlloc_3353_, 9, v_irDir_3323_);
lean_ctor_set(v_reuseFailAlloc_3353_, 10, v_releaseRepo_3324_);
lean_ctor_set(v_reuseFailAlloc_3353_, 11, v_buildArchive_3325_);
lean_ctor_set(v_reuseFailAlloc_3353_, 12, v_testDriver_3327_);
lean_ctor_set(v_reuseFailAlloc_3353_, 13, v_testDriverArgs_3328_);
lean_ctor_set(v_reuseFailAlloc_3353_, 14, v_lintDriver_3329_);
lean_ctor_set(v_reuseFailAlloc_3353_, 15, v_lintDriverArgs_3330_);
lean_ctor_set(v_reuseFailAlloc_3353_, 16, v_version_3331_);
lean_ctor_set(v_reuseFailAlloc_3353_, 17, v_versionTags_3332_);
lean_ctor_set(v_reuseFailAlloc_3353_, 18, v_description_3333_);
lean_ctor_set(v_reuseFailAlloc_3353_, 19, v_keywords_3334_);
lean_ctor_set(v_reuseFailAlloc_3353_, 20, v_homepage_3335_);
lean_ctor_set(v_reuseFailAlloc_3353_, 21, v_license_3336_);
lean_ctor_set(v_reuseFailAlloc_3353_, 22, v_licenseFiles_3337_);
lean_ctor_set(v_reuseFailAlloc_3353_, 23, v_readmeFile_3338_);
lean_ctor_set(v_reuseFailAlloc_3353_, 24, v_enableArtifactCache_x3f_3340_);
lean_ctor_set(v_reuseFailAlloc_3353_, 25, v_restoreAllArtifacts_x3f_3341_);
lean_ctor_set_uint8(v_reuseFailAlloc_3353_, sizeof(void*)*26, v_bootstrap_3314_);
lean_ctor_set_uint8(v_reuseFailAlloc_3353_, sizeof(void*)*26 + 1, v_precompileModules_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3353_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3353_, sizeof(void*)*26 + 3, v_reservoir_3339_);
v___x_3351_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
uint8_t v___x_3352_; 
v___x_3352_ = lean_unbox(v___x_3349_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*26 + 4, v___x_3352_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*26 + 5, v_allowImportAll_3343_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*26 + 6, v_fixedToolchain_3344_);
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3363_, lean_object* v_n_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3366_, lean_object* v_n_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3366_, v_n_3367_);
lean_dec(v_n_3367_);
lean_dec(v_p_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3369_, lean_object* v_n_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3369_, v_n_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3372_, lean_object* v_n_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3372_, v_n_3373_);
lean_dec(v_n_3373_);
lean_dec(v_p_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_3375_){
_start:
{
uint8_t v_allowImportAll_3376_; 
v_allowImportAll_3376_ = lean_ctor_get_uint8(v_cfg_3375_, sizeof(void*)*26 + 5);
return v_allowImportAll_3376_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_3377_){
_start:
{
uint8_t v_res_3378_; lean_object* v_r_3379_; 
v_res_3378_ = l_Lake_PackageConfig_allowImportAll___proj___lam__0(v_cfg_3377_);
lean_dec_ref(v_cfg_3377_);
v_r_3379_ = lean_box(v_res_3378_);
return v_r_3379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t v_val_3380_, lean_object* v_cfg_3381_){
_start:
{
lean_object* v_toWorkspaceConfig_3382_; lean_object* v_toLeanConfig_3383_; uint8_t v_bootstrap_3384_; lean_object* v_extraDepTargets_3385_; uint8_t v_precompileModules_3386_; lean_object* v_moreGlobalServerArgs_3387_; lean_object* v_srcDir_3388_; lean_object* v_buildDir_3389_; lean_object* v_leanLibDir_3390_; lean_object* v_nativeLibDir_3391_; lean_object* v_binDir_3392_; lean_object* v_irDir_3393_; lean_object* v_releaseRepo_3394_; lean_object* v_buildArchive_3395_; uint8_t v_preferReleaseBuild_3396_; lean_object* v_testDriver_3397_; lean_object* v_testDriverArgs_3398_; lean_object* v_lintDriver_3399_; lean_object* v_lintDriverArgs_3400_; lean_object* v_version_3401_; lean_object* v_versionTags_3402_; lean_object* v_description_3403_; lean_object* v_keywords_3404_; lean_object* v_homepage_3405_; lean_object* v_license_3406_; lean_object* v_licenseFiles_3407_; lean_object* v_readmeFile_3408_; uint8_t v_reservoir_3409_; lean_object* v_enableArtifactCache_x3f_3410_; lean_object* v_restoreAllArtifacts_x3f_3411_; uint8_t v_libPrefixOnWindows_3412_; uint8_t v_fixedToolchain_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
v_toWorkspaceConfig_3382_ = lean_ctor_get(v_cfg_3381_, 0);
v_toLeanConfig_3383_ = lean_ctor_get(v_cfg_3381_, 1);
v_bootstrap_3384_ = lean_ctor_get_uint8(v_cfg_3381_, sizeof(void*)*26);
v_extraDepTargets_3385_ = lean_ctor_get(v_cfg_3381_, 2);
v_precompileModules_3386_ = lean_ctor_get_uint8(v_cfg_3381_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3387_ = lean_ctor_get(v_cfg_3381_, 3);
v_srcDir_3388_ = lean_ctor_get(v_cfg_3381_, 4);
v_buildDir_3389_ = lean_ctor_get(v_cfg_3381_, 5);
v_leanLibDir_3390_ = lean_ctor_get(v_cfg_3381_, 6);
v_nativeLibDir_3391_ = lean_ctor_get(v_cfg_3381_, 7);
v_binDir_3392_ = lean_ctor_get(v_cfg_3381_, 8);
v_irDir_3393_ = lean_ctor_get(v_cfg_3381_, 9);
v_releaseRepo_3394_ = lean_ctor_get(v_cfg_3381_, 10);
v_buildArchive_3395_ = lean_ctor_get(v_cfg_3381_, 11);
v_preferReleaseBuild_3396_ = lean_ctor_get_uint8(v_cfg_3381_, sizeof(void*)*26 + 2);
v_testDriver_3397_ = lean_ctor_get(v_cfg_3381_, 12);
v_testDriverArgs_3398_ = lean_ctor_get(v_cfg_3381_, 13);
v_lintDriver_3399_ = lean_ctor_get(v_cfg_3381_, 14);
v_lintDriverArgs_3400_ = lean_ctor_get(v_cfg_3381_, 15);
v_version_3401_ = lean_ctor_get(v_cfg_3381_, 16);
v_versionTags_3402_ = lean_ctor_get(v_cfg_3381_, 17);
v_description_3403_ = lean_ctor_get(v_cfg_3381_, 18);
v_keywords_3404_ = lean_ctor_get(v_cfg_3381_, 19);
v_homepage_3405_ = lean_ctor_get(v_cfg_3381_, 20);
v_license_3406_ = lean_ctor_get(v_cfg_3381_, 21);
v_licenseFiles_3407_ = lean_ctor_get(v_cfg_3381_, 22);
v_readmeFile_3408_ = lean_ctor_get(v_cfg_3381_, 23);
v_reservoir_3409_ = lean_ctor_get_uint8(v_cfg_3381_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3410_ = lean_ctor_get(v_cfg_3381_, 24);
v_restoreAllArtifacts_x3f_3411_ = lean_ctor_get(v_cfg_3381_, 25);
v_libPrefixOnWindows_3412_ = lean_ctor_get_uint8(v_cfg_3381_, sizeof(void*)*26 + 4);
v_fixedToolchain_3413_ = lean_ctor_get_uint8(v_cfg_3381_, sizeof(void*)*26 + 6);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_cfg_3381_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v_cfg_3381_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3411_);
lean_inc(v_enableArtifactCache_x3f_3410_);
lean_inc(v_readmeFile_3408_);
lean_inc(v_licenseFiles_3407_);
lean_inc(v_license_3406_);
lean_inc(v_homepage_3405_);
lean_inc(v_keywords_3404_);
lean_inc(v_description_3403_);
lean_inc(v_versionTags_3402_);
lean_inc(v_version_3401_);
lean_inc(v_lintDriverArgs_3400_);
lean_inc(v_lintDriver_3399_);
lean_inc(v_testDriverArgs_3398_);
lean_inc(v_testDriver_3397_);
lean_inc(v_buildArchive_3395_);
lean_inc(v_releaseRepo_3394_);
lean_inc(v_irDir_3393_);
lean_inc(v_binDir_3392_);
lean_inc(v_nativeLibDir_3391_);
lean_inc(v_leanLibDir_3390_);
lean_inc(v_buildDir_3389_);
lean_inc(v_srcDir_3388_);
lean_inc(v_moreGlobalServerArgs_3387_);
lean_inc(v_extraDepTargets_3385_);
lean_inc(v_toLeanConfig_3383_);
lean_inc(v_toWorkspaceConfig_3382_);
lean_dec(v_cfg_3381_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_toWorkspaceConfig_3382_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_toLeanConfig_3383_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_extraDepTargets_3385_);
lean_ctor_set(v_reuseFailAlloc_3419_, 3, v_moreGlobalServerArgs_3387_);
lean_ctor_set(v_reuseFailAlloc_3419_, 4, v_srcDir_3388_);
lean_ctor_set(v_reuseFailAlloc_3419_, 5, v_buildDir_3389_);
lean_ctor_set(v_reuseFailAlloc_3419_, 6, v_leanLibDir_3390_);
lean_ctor_set(v_reuseFailAlloc_3419_, 7, v_nativeLibDir_3391_);
lean_ctor_set(v_reuseFailAlloc_3419_, 8, v_binDir_3392_);
lean_ctor_set(v_reuseFailAlloc_3419_, 9, v_irDir_3393_);
lean_ctor_set(v_reuseFailAlloc_3419_, 10, v_releaseRepo_3394_);
lean_ctor_set(v_reuseFailAlloc_3419_, 11, v_buildArchive_3395_);
lean_ctor_set(v_reuseFailAlloc_3419_, 12, v_testDriver_3397_);
lean_ctor_set(v_reuseFailAlloc_3419_, 13, v_testDriverArgs_3398_);
lean_ctor_set(v_reuseFailAlloc_3419_, 14, v_lintDriver_3399_);
lean_ctor_set(v_reuseFailAlloc_3419_, 15, v_lintDriverArgs_3400_);
lean_ctor_set(v_reuseFailAlloc_3419_, 16, v_version_3401_);
lean_ctor_set(v_reuseFailAlloc_3419_, 17, v_versionTags_3402_);
lean_ctor_set(v_reuseFailAlloc_3419_, 18, v_description_3403_);
lean_ctor_set(v_reuseFailAlloc_3419_, 19, v_keywords_3404_);
lean_ctor_set(v_reuseFailAlloc_3419_, 20, v_homepage_3405_);
lean_ctor_set(v_reuseFailAlloc_3419_, 21, v_license_3406_);
lean_ctor_set(v_reuseFailAlloc_3419_, 22, v_licenseFiles_3407_);
lean_ctor_set(v_reuseFailAlloc_3419_, 23, v_readmeFile_3408_);
lean_ctor_set(v_reuseFailAlloc_3419_, 24, v_enableArtifactCache_x3f_3410_);
lean_ctor_set(v_reuseFailAlloc_3419_, 25, v_restoreAllArtifacts_x3f_3411_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*26, v_bootstrap_3384_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*26 + 1, v_precompileModules_3386_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3396_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*26 + 3, v_reservoir_3409_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3412_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*26 + 6, v_fixedToolchain_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_ctor_set_uint8(v___x_3418_, sizeof(void*)*26 + 5, v_val_3380_);
return v___x_3418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_3421_, lean_object* v_cfg_3422_){
_start:
{
uint8_t v_val_134__boxed_3423_; lean_object* v_res_3424_; 
v_val_134__boxed_3423_ = lean_unbox(v_val_3421_);
v_res_3424_ = l_Lake_PackageConfig_allowImportAll___proj___lam__1(v_val_134__boxed_3423_, v_cfg_3422_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* v_f_3425_, lean_object* v_cfg_3426_){
_start:
{
lean_object* v_toWorkspaceConfig_3427_; lean_object* v_toLeanConfig_3428_; uint8_t v_bootstrap_3429_; lean_object* v_extraDepTargets_3430_; uint8_t v_precompileModules_3431_; lean_object* v_moreGlobalServerArgs_3432_; lean_object* v_srcDir_3433_; lean_object* v_buildDir_3434_; lean_object* v_leanLibDir_3435_; lean_object* v_nativeLibDir_3436_; lean_object* v_binDir_3437_; lean_object* v_irDir_3438_; lean_object* v_releaseRepo_3439_; lean_object* v_buildArchive_3440_; uint8_t v_preferReleaseBuild_3441_; lean_object* v_testDriver_3442_; lean_object* v_testDriverArgs_3443_; lean_object* v_lintDriver_3444_; lean_object* v_lintDriverArgs_3445_; lean_object* v_version_3446_; lean_object* v_versionTags_3447_; lean_object* v_description_3448_; lean_object* v_keywords_3449_; lean_object* v_homepage_3450_; lean_object* v_license_3451_; lean_object* v_licenseFiles_3452_; lean_object* v_readmeFile_3453_; uint8_t v_reservoir_3454_; lean_object* v_enableArtifactCache_x3f_3455_; lean_object* v_restoreAllArtifacts_x3f_3456_; uint8_t v_libPrefixOnWindows_3457_; uint8_t v_allowImportAll_3458_; uint8_t v_fixedToolchain_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3469_; 
v_toWorkspaceConfig_3427_ = lean_ctor_get(v_cfg_3426_, 0);
v_toLeanConfig_3428_ = lean_ctor_get(v_cfg_3426_, 1);
v_bootstrap_3429_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26);
v_extraDepTargets_3430_ = lean_ctor_get(v_cfg_3426_, 2);
v_precompileModules_3431_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3432_ = lean_ctor_get(v_cfg_3426_, 3);
v_srcDir_3433_ = lean_ctor_get(v_cfg_3426_, 4);
v_buildDir_3434_ = lean_ctor_get(v_cfg_3426_, 5);
v_leanLibDir_3435_ = lean_ctor_get(v_cfg_3426_, 6);
v_nativeLibDir_3436_ = lean_ctor_get(v_cfg_3426_, 7);
v_binDir_3437_ = lean_ctor_get(v_cfg_3426_, 8);
v_irDir_3438_ = lean_ctor_get(v_cfg_3426_, 9);
v_releaseRepo_3439_ = lean_ctor_get(v_cfg_3426_, 10);
v_buildArchive_3440_ = lean_ctor_get(v_cfg_3426_, 11);
v_preferReleaseBuild_3441_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26 + 2);
v_testDriver_3442_ = lean_ctor_get(v_cfg_3426_, 12);
v_testDriverArgs_3443_ = lean_ctor_get(v_cfg_3426_, 13);
v_lintDriver_3444_ = lean_ctor_get(v_cfg_3426_, 14);
v_lintDriverArgs_3445_ = lean_ctor_get(v_cfg_3426_, 15);
v_version_3446_ = lean_ctor_get(v_cfg_3426_, 16);
v_versionTags_3447_ = lean_ctor_get(v_cfg_3426_, 17);
v_description_3448_ = lean_ctor_get(v_cfg_3426_, 18);
v_keywords_3449_ = lean_ctor_get(v_cfg_3426_, 19);
v_homepage_3450_ = lean_ctor_get(v_cfg_3426_, 20);
v_license_3451_ = lean_ctor_get(v_cfg_3426_, 21);
v_licenseFiles_3452_ = lean_ctor_get(v_cfg_3426_, 22);
v_readmeFile_3453_ = lean_ctor_get(v_cfg_3426_, 23);
v_reservoir_3454_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3455_ = lean_ctor_get(v_cfg_3426_, 24);
v_restoreAllArtifacts_x3f_3456_ = lean_ctor_get(v_cfg_3426_, 25);
v_libPrefixOnWindows_3457_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26 + 4);
v_allowImportAll_3458_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26 + 5);
v_fixedToolchain_3459_ = lean_ctor_get_uint8(v_cfg_3426_, sizeof(void*)*26 + 6);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_cfg_3426_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3461_ = v_cfg_3426_;
v_isShared_3462_ = v_isSharedCheck_3469_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3456_);
lean_inc(v_enableArtifactCache_x3f_3455_);
lean_inc(v_readmeFile_3453_);
lean_inc(v_licenseFiles_3452_);
lean_inc(v_license_3451_);
lean_inc(v_homepage_3450_);
lean_inc(v_keywords_3449_);
lean_inc(v_description_3448_);
lean_inc(v_versionTags_3447_);
lean_inc(v_version_3446_);
lean_inc(v_lintDriverArgs_3445_);
lean_inc(v_lintDriver_3444_);
lean_inc(v_testDriverArgs_3443_);
lean_inc(v_testDriver_3442_);
lean_inc(v_buildArchive_3440_);
lean_inc(v_releaseRepo_3439_);
lean_inc(v_irDir_3438_);
lean_inc(v_binDir_3437_);
lean_inc(v_nativeLibDir_3436_);
lean_inc(v_leanLibDir_3435_);
lean_inc(v_buildDir_3434_);
lean_inc(v_srcDir_3433_);
lean_inc(v_moreGlobalServerArgs_3432_);
lean_inc(v_extraDepTargets_3430_);
lean_inc(v_toLeanConfig_3428_);
lean_inc(v_toWorkspaceConfig_3427_);
lean_dec(v_cfg_3426_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3469_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = lean_box(v_allowImportAll_3458_);
v___x_3464_ = lean_apply_1(v_f_3425_, v___x_3463_);
if (v_isShared_3462_ == 0)
{
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_toWorkspaceConfig_3427_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_toLeanConfig_3428_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_extraDepTargets_3430_);
lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_moreGlobalServerArgs_3432_);
lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_srcDir_3433_);
lean_ctor_set(v_reuseFailAlloc_3468_, 5, v_buildDir_3434_);
lean_ctor_set(v_reuseFailAlloc_3468_, 6, v_leanLibDir_3435_);
lean_ctor_set(v_reuseFailAlloc_3468_, 7, v_nativeLibDir_3436_);
lean_ctor_set(v_reuseFailAlloc_3468_, 8, v_binDir_3437_);
lean_ctor_set(v_reuseFailAlloc_3468_, 9, v_irDir_3438_);
lean_ctor_set(v_reuseFailAlloc_3468_, 10, v_releaseRepo_3439_);
lean_ctor_set(v_reuseFailAlloc_3468_, 11, v_buildArchive_3440_);
lean_ctor_set(v_reuseFailAlloc_3468_, 12, v_testDriver_3442_);
lean_ctor_set(v_reuseFailAlloc_3468_, 13, v_testDriverArgs_3443_);
lean_ctor_set(v_reuseFailAlloc_3468_, 14, v_lintDriver_3444_);
lean_ctor_set(v_reuseFailAlloc_3468_, 15, v_lintDriverArgs_3445_);
lean_ctor_set(v_reuseFailAlloc_3468_, 16, v_version_3446_);
lean_ctor_set(v_reuseFailAlloc_3468_, 17, v_versionTags_3447_);
lean_ctor_set(v_reuseFailAlloc_3468_, 18, v_description_3448_);
lean_ctor_set(v_reuseFailAlloc_3468_, 19, v_keywords_3449_);
lean_ctor_set(v_reuseFailAlloc_3468_, 20, v_homepage_3450_);
lean_ctor_set(v_reuseFailAlloc_3468_, 21, v_license_3451_);
lean_ctor_set(v_reuseFailAlloc_3468_, 22, v_licenseFiles_3452_);
lean_ctor_set(v_reuseFailAlloc_3468_, 23, v_readmeFile_3453_);
lean_ctor_set(v_reuseFailAlloc_3468_, 24, v_enableArtifactCache_x3f_3455_);
lean_ctor_set(v_reuseFailAlloc_3468_, 25, v_restoreAllArtifacts_x3f_3456_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*26, v_bootstrap_3429_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*26 + 1, v_precompileModules_3431_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3441_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*26 + 3, v_reservoir_3454_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3457_);
v___x_3466_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_unbox(v___x_3464_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*26 + 5, v___x_3467_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*26 + 6, v_fixedToolchain_3459_);
return v___x_3466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3478_, lean_object* v_n_3479_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3481_, lean_object* v_n_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3481_, v_n_3482_);
lean_dec(v_n_3482_);
lean_dec(v_p_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3484_, lean_object* v_n_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3484_, v_n_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3487_, lean_object* v_n_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3487_, v_n_3488_);
lean_dec(v_n_3488_);
lean_dec(v_p_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___lam__0(lean_object* v_cfg_3490_){
_start:
{
uint8_t v_fixedToolchain_3491_; 
v_fixedToolchain_3491_ = lean_ctor_get_uint8(v_cfg_3490_, sizeof(void*)*26 + 6);
return v_fixedToolchain_3491_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed(lean_object* v_cfg_3492_){
_start:
{
uint8_t v_res_3493_; lean_object* v_r_3494_; 
v_res_3493_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__0(v_cfg_3492_);
lean_dec_ref(v_cfg_3492_);
v_r_3494_ = lean_box(v_res_3493_);
return v_r_3494_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1(uint8_t v_val_3495_, lean_object* v_cfg_3496_){
_start:
{
lean_object* v_toWorkspaceConfig_3497_; lean_object* v_toLeanConfig_3498_; uint8_t v_bootstrap_3499_; lean_object* v_extraDepTargets_3500_; uint8_t v_precompileModules_3501_; lean_object* v_moreGlobalServerArgs_3502_; lean_object* v_srcDir_3503_; lean_object* v_buildDir_3504_; lean_object* v_leanLibDir_3505_; lean_object* v_nativeLibDir_3506_; lean_object* v_binDir_3507_; lean_object* v_irDir_3508_; lean_object* v_releaseRepo_3509_; lean_object* v_buildArchive_3510_; uint8_t v_preferReleaseBuild_3511_; lean_object* v_testDriver_3512_; lean_object* v_testDriverArgs_3513_; lean_object* v_lintDriver_3514_; lean_object* v_lintDriverArgs_3515_; lean_object* v_version_3516_; lean_object* v_versionTags_3517_; lean_object* v_description_3518_; lean_object* v_keywords_3519_; lean_object* v_homepage_3520_; lean_object* v_license_3521_; lean_object* v_licenseFiles_3522_; lean_object* v_readmeFile_3523_; uint8_t v_reservoir_3524_; lean_object* v_enableArtifactCache_x3f_3525_; lean_object* v_restoreAllArtifacts_x3f_3526_; uint8_t v_libPrefixOnWindows_3527_; uint8_t v_allowImportAll_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_toWorkspaceConfig_3497_ = lean_ctor_get(v_cfg_3496_, 0);
v_toLeanConfig_3498_ = lean_ctor_get(v_cfg_3496_, 1);
v_bootstrap_3499_ = lean_ctor_get_uint8(v_cfg_3496_, sizeof(void*)*26);
v_extraDepTargets_3500_ = lean_ctor_get(v_cfg_3496_, 2);
v_precompileModules_3501_ = lean_ctor_get_uint8(v_cfg_3496_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3502_ = lean_ctor_get(v_cfg_3496_, 3);
v_srcDir_3503_ = lean_ctor_get(v_cfg_3496_, 4);
v_buildDir_3504_ = lean_ctor_get(v_cfg_3496_, 5);
v_leanLibDir_3505_ = lean_ctor_get(v_cfg_3496_, 6);
v_nativeLibDir_3506_ = lean_ctor_get(v_cfg_3496_, 7);
v_binDir_3507_ = lean_ctor_get(v_cfg_3496_, 8);
v_irDir_3508_ = lean_ctor_get(v_cfg_3496_, 9);
v_releaseRepo_3509_ = lean_ctor_get(v_cfg_3496_, 10);
v_buildArchive_3510_ = lean_ctor_get(v_cfg_3496_, 11);
v_preferReleaseBuild_3511_ = lean_ctor_get_uint8(v_cfg_3496_, sizeof(void*)*26 + 2);
v_testDriver_3512_ = lean_ctor_get(v_cfg_3496_, 12);
v_testDriverArgs_3513_ = lean_ctor_get(v_cfg_3496_, 13);
v_lintDriver_3514_ = lean_ctor_get(v_cfg_3496_, 14);
v_lintDriverArgs_3515_ = lean_ctor_get(v_cfg_3496_, 15);
v_version_3516_ = lean_ctor_get(v_cfg_3496_, 16);
v_versionTags_3517_ = lean_ctor_get(v_cfg_3496_, 17);
v_description_3518_ = lean_ctor_get(v_cfg_3496_, 18);
v_keywords_3519_ = lean_ctor_get(v_cfg_3496_, 19);
v_homepage_3520_ = lean_ctor_get(v_cfg_3496_, 20);
v_license_3521_ = lean_ctor_get(v_cfg_3496_, 21);
v_licenseFiles_3522_ = lean_ctor_get(v_cfg_3496_, 22);
v_readmeFile_3523_ = lean_ctor_get(v_cfg_3496_, 23);
v_reservoir_3524_ = lean_ctor_get_uint8(v_cfg_3496_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3525_ = lean_ctor_get(v_cfg_3496_, 24);
v_restoreAllArtifacts_x3f_3526_ = lean_ctor_get(v_cfg_3496_, 25);
v_libPrefixOnWindows_3527_ = lean_ctor_get_uint8(v_cfg_3496_, sizeof(void*)*26 + 4);
v_allowImportAll_3528_ = lean_ctor_get_uint8(v_cfg_3496_, sizeof(void*)*26 + 5);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_cfg_3496_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v_cfg_3496_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3526_);
lean_inc(v_enableArtifactCache_x3f_3525_);
lean_inc(v_readmeFile_3523_);
lean_inc(v_licenseFiles_3522_);
lean_inc(v_license_3521_);
lean_inc(v_homepage_3520_);
lean_inc(v_keywords_3519_);
lean_inc(v_description_3518_);
lean_inc(v_versionTags_3517_);
lean_inc(v_version_3516_);
lean_inc(v_lintDriverArgs_3515_);
lean_inc(v_lintDriver_3514_);
lean_inc(v_testDriverArgs_3513_);
lean_inc(v_testDriver_3512_);
lean_inc(v_buildArchive_3510_);
lean_inc(v_releaseRepo_3509_);
lean_inc(v_irDir_3508_);
lean_inc(v_binDir_3507_);
lean_inc(v_nativeLibDir_3506_);
lean_inc(v_leanLibDir_3505_);
lean_inc(v_buildDir_3504_);
lean_inc(v_srcDir_3503_);
lean_inc(v_moreGlobalServerArgs_3502_);
lean_inc(v_extraDepTargets_3500_);
lean_inc(v_toLeanConfig_3498_);
lean_inc(v_toWorkspaceConfig_3497_);
lean_dec(v_cfg_3496_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_toWorkspaceConfig_3497_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_toLeanConfig_3498_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_extraDepTargets_3500_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_moreGlobalServerArgs_3502_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_srcDir_3503_);
lean_ctor_set(v_reuseFailAlloc_3534_, 5, v_buildDir_3504_);
lean_ctor_set(v_reuseFailAlloc_3534_, 6, v_leanLibDir_3505_);
lean_ctor_set(v_reuseFailAlloc_3534_, 7, v_nativeLibDir_3506_);
lean_ctor_set(v_reuseFailAlloc_3534_, 8, v_binDir_3507_);
lean_ctor_set(v_reuseFailAlloc_3534_, 9, v_irDir_3508_);
lean_ctor_set(v_reuseFailAlloc_3534_, 10, v_releaseRepo_3509_);
lean_ctor_set(v_reuseFailAlloc_3534_, 11, v_buildArchive_3510_);
lean_ctor_set(v_reuseFailAlloc_3534_, 12, v_testDriver_3512_);
lean_ctor_set(v_reuseFailAlloc_3534_, 13, v_testDriverArgs_3513_);
lean_ctor_set(v_reuseFailAlloc_3534_, 14, v_lintDriver_3514_);
lean_ctor_set(v_reuseFailAlloc_3534_, 15, v_lintDriverArgs_3515_);
lean_ctor_set(v_reuseFailAlloc_3534_, 16, v_version_3516_);
lean_ctor_set(v_reuseFailAlloc_3534_, 17, v_versionTags_3517_);
lean_ctor_set(v_reuseFailAlloc_3534_, 18, v_description_3518_);
lean_ctor_set(v_reuseFailAlloc_3534_, 19, v_keywords_3519_);
lean_ctor_set(v_reuseFailAlloc_3534_, 20, v_homepage_3520_);
lean_ctor_set(v_reuseFailAlloc_3534_, 21, v_license_3521_);
lean_ctor_set(v_reuseFailAlloc_3534_, 22, v_licenseFiles_3522_);
lean_ctor_set(v_reuseFailAlloc_3534_, 23, v_readmeFile_3523_);
lean_ctor_set(v_reuseFailAlloc_3534_, 24, v_enableArtifactCache_x3f_3525_);
lean_ctor_set(v_reuseFailAlloc_3534_, 25, v_restoreAllArtifacts_x3f_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*26, v_bootstrap_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*26 + 1, v_precompileModules_3501_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*26 + 3, v_reservoir_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*26 + 5, v_allowImportAll_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_ctor_set_uint8(v___x_3533_, sizeof(void*)*26 + 6, v_val_3495_);
return v___x_3533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed(lean_object* v_val_3536_, lean_object* v_cfg_3537_){
_start:
{
uint8_t v_val_134__boxed_3538_; lean_object* v_res_3539_; 
v_val_134__boxed_3538_ = lean_unbox(v_val_3536_);
v_res_3539_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__1(v_val_134__boxed_3538_, v_cfg_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__2(lean_object* v_f_3540_, lean_object* v_cfg_3541_){
_start:
{
lean_object* v_toWorkspaceConfig_3542_; lean_object* v_toLeanConfig_3543_; uint8_t v_bootstrap_3544_; lean_object* v_extraDepTargets_3545_; uint8_t v_precompileModules_3546_; lean_object* v_moreGlobalServerArgs_3547_; lean_object* v_srcDir_3548_; lean_object* v_buildDir_3549_; lean_object* v_leanLibDir_3550_; lean_object* v_nativeLibDir_3551_; lean_object* v_binDir_3552_; lean_object* v_irDir_3553_; lean_object* v_releaseRepo_3554_; lean_object* v_buildArchive_3555_; uint8_t v_preferReleaseBuild_3556_; lean_object* v_testDriver_3557_; lean_object* v_testDriverArgs_3558_; lean_object* v_lintDriver_3559_; lean_object* v_lintDriverArgs_3560_; lean_object* v_version_3561_; lean_object* v_versionTags_3562_; lean_object* v_description_3563_; lean_object* v_keywords_3564_; lean_object* v_homepage_3565_; lean_object* v_license_3566_; lean_object* v_licenseFiles_3567_; lean_object* v_readmeFile_3568_; uint8_t v_reservoir_3569_; lean_object* v_enableArtifactCache_x3f_3570_; lean_object* v_restoreAllArtifacts_x3f_3571_; uint8_t v_libPrefixOnWindows_3572_; uint8_t v_allowImportAll_3573_; uint8_t v_fixedToolchain_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3584_; 
v_toWorkspaceConfig_3542_ = lean_ctor_get(v_cfg_3541_, 0);
v_toLeanConfig_3543_ = lean_ctor_get(v_cfg_3541_, 1);
v_bootstrap_3544_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26);
v_extraDepTargets_3545_ = lean_ctor_get(v_cfg_3541_, 2);
v_precompileModules_3546_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3547_ = lean_ctor_get(v_cfg_3541_, 3);
v_srcDir_3548_ = lean_ctor_get(v_cfg_3541_, 4);
v_buildDir_3549_ = lean_ctor_get(v_cfg_3541_, 5);
v_leanLibDir_3550_ = lean_ctor_get(v_cfg_3541_, 6);
v_nativeLibDir_3551_ = lean_ctor_get(v_cfg_3541_, 7);
v_binDir_3552_ = lean_ctor_get(v_cfg_3541_, 8);
v_irDir_3553_ = lean_ctor_get(v_cfg_3541_, 9);
v_releaseRepo_3554_ = lean_ctor_get(v_cfg_3541_, 10);
v_buildArchive_3555_ = lean_ctor_get(v_cfg_3541_, 11);
v_preferReleaseBuild_3556_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26 + 2);
v_testDriver_3557_ = lean_ctor_get(v_cfg_3541_, 12);
v_testDriverArgs_3558_ = lean_ctor_get(v_cfg_3541_, 13);
v_lintDriver_3559_ = lean_ctor_get(v_cfg_3541_, 14);
v_lintDriverArgs_3560_ = lean_ctor_get(v_cfg_3541_, 15);
v_version_3561_ = lean_ctor_get(v_cfg_3541_, 16);
v_versionTags_3562_ = lean_ctor_get(v_cfg_3541_, 17);
v_description_3563_ = lean_ctor_get(v_cfg_3541_, 18);
v_keywords_3564_ = lean_ctor_get(v_cfg_3541_, 19);
v_homepage_3565_ = lean_ctor_get(v_cfg_3541_, 20);
v_license_3566_ = lean_ctor_get(v_cfg_3541_, 21);
v_licenseFiles_3567_ = lean_ctor_get(v_cfg_3541_, 22);
v_readmeFile_3568_ = lean_ctor_get(v_cfg_3541_, 23);
v_reservoir_3569_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3570_ = lean_ctor_get(v_cfg_3541_, 24);
v_restoreAllArtifacts_x3f_3571_ = lean_ctor_get(v_cfg_3541_, 25);
v_libPrefixOnWindows_3572_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26 + 4);
v_allowImportAll_3573_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26 + 5);
v_fixedToolchain_3574_ = lean_ctor_get_uint8(v_cfg_3541_, sizeof(void*)*26 + 6);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_cfg_3541_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3576_ = v_cfg_3541_;
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3571_);
lean_inc(v_enableArtifactCache_x3f_3570_);
lean_inc(v_readmeFile_3568_);
lean_inc(v_licenseFiles_3567_);
lean_inc(v_license_3566_);
lean_inc(v_homepage_3565_);
lean_inc(v_keywords_3564_);
lean_inc(v_description_3563_);
lean_inc(v_versionTags_3562_);
lean_inc(v_version_3561_);
lean_inc(v_lintDriverArgs_3560_);
lean_inc(v_lintDriver_3559_);
lean_inc(v_testDriverArgs_3558_);
lean_inc(v_testDriver_3557_);
lean_inc(v_buildArchive_3555_);
lean_inc(v_releaseRepo_3554_);
lean_inc(v_irDir_3553_);
lean_inc(v_binDir_3552_);
lean_inc(v_nativeLibDir_3551_);
lean_inc(v_leanLibDir_3550_);
lean_inc(v_buildDir_3549_);
lean_inc(v_srcDir_3548_);
lean_inc(v_moreGlobalServerArgs_3547_);
lean_inc(v_extraDepTargets_3545_);
lean_inc(v_toLeanConfig_3543_);
lean_inc(v_toWorkspaceConfig_3542_);
lean_dec(v_cfg_3541_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3578_ = lean_box(v_fixedToolchain_3574_);
v___x_3579_ = lean_apply_1(v_f_3540_, v___x_3578_);
if (v_isShared_3577_ == 0)
{
v___x_3581_ = v___x_3576_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_toWorkspaceConfig_3542_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_toLeanConfig_3543_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_extraDepTargets_3545_);
lean_ctor_set(v_reuseFailAlloc_3583_, 3, v_moreGlobalServerArgs_3547_);
lean_ctor_set(v_reuseFailAlloc_3583_, 4, v_srcDir_3548_);
lean_ctor_set(v_reuseFailAlloc_3583_, 5, v_buildDir_3549_);
lean_ctor_set(v_reuseFailAlloc_3583_, 6, v_leanLibDir_3550_);
lean_ctor_set(v_reuseFailAlloc_3583_, 7, v_nativeLibDir_3551_);
lean_ctor_set(v_reuseFailAlloc_3583_, 8, v_binDir_3552_);
lean_ctor_set(v_reuseFailAlloc_3583_, 9, v_irDir_3553_);
lean_ctor_set(v_reuseFailAlloc_3583_, 10, v_releaseRepo_3554_);
lean_ctor_set(v_reuseFailAlloc_3583_, 11, v_buildArchive_3555_);
lean_ctor_set(v_reuseFailAlloc_3583_, 12, v_testDriver_3557_);
lean_ctor_set(v_reuseFailAlloc_3583_, 13, v_testDriverArgs_3558_);
lean_ctor_set(v_reuseFailAlloc_3583_, 14, v_lintDriver_3559_);
lean_ctor_set(v_reuseFailAlloc_3583_, 15, v_lintDriverArgs_3560_);
lean_ctor_set(v_reuseFailAlloc_3583_, 16, v_version_3561_);
lean_ctor_set(v_reuseFailAlloc_3583_, 17, v_versionTags_3562_);
lean_ctor_set(v_reuseFailAlloc_3583_, 18, v_description_3563_);
lean_ctor_set(v_reuseFailAlloc_3583_, 19, v_keywords_3564_);
lean_ctor_set(v_reuseFailAlloc_3583_, 20, v_homepage_3565_);
lean_ctor_set(v_reuseFailAlloc_3583_, 21, v_license_3566_);
lean_ctor_set(v_reuseFailAlloc_3583_, 22, v_licenseFiles_3567_);
lean_ctor_set(v_reuseFailAlloc_3583_, 23, v_readmeFile_3568_);
lean_ctor_set(v_reuseFailAlloc_3583_, 24, v_enableArtifactCache_x3f_3570_);
lean_ctor_set(v_reuseFailAlloc_3583_, 25, v_restoreAllArtifacts_x3f_3571_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*26, v_bootstrap_3544_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*26 + 1, v_precompileModules_3546_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3556_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*26 + 3, v_reservoir_3569_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3572_);
lean_ctor_set_uint8(v_reuseFailAlloc_3583_, sizeof(void*)*26 + 5, v_allowImportAll_3573_);
v___x_3581_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_unbox(v___x_3579_);
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*26 + 6, v___x_3582_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_3593_, lean_object* v_n_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___closed__3));
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_3596_, lean_object* v_n_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3596_, v_n_3597_);
lean_dec(v_n_3597_);
lean_dec(v_p_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_3599_, lean_object* v_n_3600_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3599_, v_n_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_3602_, lean_object* v_n_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_3602_, v_n_3603_);
lean_dec(v_n_3603_);
lean_dec(v_p_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* v_cfg_3605_){
_start:
{
lean_object* v_toWorkspaceConfig_3606_; 
v_toWorkspaceConfig_3606_ = lean_ctor_get(v_cfg_3605_, 0);
lean_inc_ref(v_toWorkspaceConfig_3606_);
return v_toWorkspaceConfig_3606_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* v_cfg_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(v_cfg_3607_);
lean_dec_ref(v_cfg_3607_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* v_val_3609_, lean_object* v_cfg_3610_){
_start:
{
lean_object* v_toLeanConfig_3611_; uint8_t v_bootstrap_3612_; lean_object* v_extraDepTargets_3613_; uint8_t v_precompileModules_3614_; lean_object* v_moreGlobalServerArgs_3615_; lean_object* v_srcDir_3616_; lean_object* v_buildDir_3617_; lean_object* v_leanLibDir_3618_; lean_object* v_nativeLibDir_3619_; lean_object* v_binDir_3620_; lean_object* v_irDir_3621_; lean_object* v_releaseRepo_3622_; lean_object* v_buildArchive_3623_; uint8_t v_preferReleaseBuild_3624_; lean_object* v_testDriver_3625_; lean_object* v_testDriverArgs_3626_; lean_object* v_lintDriver_3627_; lean_object* v_lintDriverArgs_3628_; lean_object* v_version_3629_; lean_object* v_versionTags_3630_; lean_object* v_description_3631_; lean_object* v_keywords_3632_; lean_object* v_homepage_3633_; lean_object* v_license_3634_; lean_object* v_licenseFiles_3635_; lean_object* v_readmeFile_3636_; uint8_t v_reservoir_3637_; lean_object* v_enableArtifactCache_x3f_3638_; lean_object* v_restoreAllArtifacts_x3f_3639_; uint8_t v_libPrefixOnWindows_3640_; uint8_t v_allowImportAll_3641_; uint8_t v_fixedToolchain_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v_toLeanConfig_3611_ = lean_ctor_get(v_cfg_3610_, 1);
v_bootstrap_3612_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26);
v_extraDepTargets_3613_ = lean_ctor_get(v_cfg_3610_, 2);
v_precompileModules_3614_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3615_ = lean_ctor_get(v_cfg_3610_, 3);
v_srcDir_3616_ = lean_ctor_get(v_cfg_3610_, 4);
v_buildDir_3617_ = lean_ctor_get(v_cfg_3610_, 5);
v_leanLibDir_3618_ = lean_ctor_get(v_cfg_3610_, 6);
v_nativeLibDir_3619_ = lean_ctor_get(v_cfg_3610_, 7);
v_binDir_3620_ = lean_ctor_get(v_cfg_3610_, 8);
v_irDir_3621_ = lean_ctor_get(v_cfg_3610_, 9);
v_releaseRepo_3622_ = lean_ctor_get(v_cfg_3610_, 10);
v_buildArchive_3623_ = lean_ctor_get(v_cfg_3610_, 11);
v_preferReleaseBuild_3624_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26 + 2);
v_testDriver_3625_ = lean_ctor_get(v_cfg_3610_, 12);
v_testDriverArgs_3626_ = lean_ctor_get(v_cfg_3610_, 13);
v_lintDriver_3627_ = lean_ctor_get(v_cfg_3610_, 14);
v_lintDriverArgs_3628_ = lean_ctor_get(v_cfg_3610_, 15);
v_version_3629_ = lean_ctor_get(v_cfg_3610_, 16);
v_versionTags_3630_ = lean_ctor_get(v_cfg_3610_, 17);
v_description_3631_ = lean_ctor_get(v_cfg_3610_, 18);
v_keywords_3632_ = lean_ctor_get(v_cfg_3610_, 19);
v_homepage_3633_ = lean_ctor_get(v_cfg_3610_, 20);
v_license_3634_ = lean_ctor_get(v_cfg_3610_, 21);
v_licenseFiles_3635_ = lean_ctor_get(v_cfg_3610_, 22);
v_readmeFile_3636_ = lean_ctor_get(v_cfg_3610_, 23);
v_reservoir_3637_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3638_ = lean_ctor_get(v_cfg_3610_, 24);
v_restoreAllArtifacts_x3f_3639_ = lean_ctor_get(v_cfg_3610_, 25);
v_libPrefixOnWindows_3640_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26 + 4);
v_allowImportAll_3641_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26 + 5);
v_fixedToolchain_3642_ = lean_ctor_get_uint8(v_cfg_3610_, sizeof(void*)*26 + 6);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_cfg_3610_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; 
v_unused_3650_ = lean_ctor_get(v_cfg_3610_, 0);
lean_dec(v_unused_3650_);
v___x_3644_ = v_cfg_3610_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3639_);
lean_inc(v_enableArtifactCache_x3f_3638_);
lean_inc(v_readmeFile_3636_);
lean_inc(v_licenseFiles_3635_);
lean_inc(v_license_3634_);
lean_inc(v_homepage_3633_);
lean_inc(v_keywords_3632_);
lean_inc(v_description_3631_);
lean_inc(v_versionTags_3630_);
lean_inc(v_version_3629_);
lean_inc(v_lintDriverArgs_3628_);
lean_inc(v_lintDriver_3627_);
lean_inc(v_testDriverArgs_3626_);
lean_inc(v_testDriver_3625_);
lean_inc(v_buildArchive_3623_);
lean_inc(v_releaseRepo_3622_);
lean_inc(v_irDir_3621_);
lean_inc(v_binDir_3620_);
lean_inc(v_nativeLibDir_3619_);
lean_inc(v_leanLibDir_3618_);
lean_inc(v_buildDir_3617_);
lean_inc(v_srcDir_3616_);
lean_inc(v_moreGlobalServerArgs_3615_);
lean_inc(v_extraDepTargets_3613_);
lean_inc(v_toLeanConfig_3611_);
lean_dec(v_cfg_3610_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_val_3609_);
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_val_3609_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_toLeanConfig_3611_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_extraDepTargets_3613_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_moreGlobalServerArgs_3615_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_srcDir_3616_);
lean_ctor_set(v_reuseFailAlloc_3648_, 5, v_buildDir_3617_);
lean_ctor_set(v_reuseFailAlloc_3648_, 6, v_leanLibDir_3618_);
lean_ctor_set(v_reuseFailAlloc_3648_, 7, v_nativeLibDir_3619_);
lean_ctor_set(v_reuseFailAlloc_3648_, 8, v_binDir_3620_);
lean_ctor_set(v_reuseFailAlloc_3648_, 9, v_irDir_3621_);
lean_ctor_set(v_reuseFailAlloc_3648_, 10, v_releaseRepo_3622_);
lean_ctor_set(v_reuseFailAlloc_3648_, 11, v_buildArchive_3623_);
lean_ctor_set(v_reuseFailAlloc_3648_, 12, v_testDriver_3625_);
lean_ctor_set(v_reuseFailAlloc_3648_, 13, v_testDriverArgs_3626_);
lean_ctor_set(v_reuseFailAlloc_3648_, 14, v_lintDriver_3627_);
lean_ctor_set(v_reuseFailAlloc_3648_, 15, v_lintDriverArgs_3628_);
lean_ctor_set(v_reuseFailAlloc_3648_, 16, v_version_3629_);
lean_ctor_set(v_reuseFailAlloc_3648_, 17, v_versionTags_3630_);
lean_ctor_set(v_reuseFailAlloc_3648_, 18, v_description_3631_);
lean_ctor_set(v_reuseFailAlloc_3648_, 19, v_keywords_3632_);
lean_ctor_set(v_reuseFailAlloc_3648_, 20, v_homepage_3633_);
lean_ctor_set(v_reuseFailAlloc_3648_, 21, v_license_3634_);
lean_ctor_set(v_reuseFailAlloc_3648_, 22, v_licenseFiles_3635_);
lean_ctor_set(v_reuseFailAlloc_3648_, 23, v_readmeFile_3636_);
lean_ctor_set(v_reuseFailAlloc_3648_, 24, v_enableArtifactCache_x3f_3638_);
lean_ctor_set(v_reuseFailAlloc_3648_, 25, v_restoreAllArtifacts_x3f_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26, v_bootstrap_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26 + 1, v_precompileModules_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26 + 3, v_reservoir_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26 + 5, v_allowImportAll_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, sizeof(void*)*26 + 6, v_fixedToolchain_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* v_f_3651_, lean_object* v_cfg_3652_){
_start:
{
lean_object* v_toWorkspaceConfig_3653_; lean_object* v_toLeanConfig_3654_; uint8_t v_bootstrap_3655_; lean_object* v_extraDepTargets_3656_; uint8_t v_precompileModules_3657_; lean_object* v_moreGlobalServerArgs_3658_; lean_object* v_srcDir_3659_; lean_object* v_buildDir_3660_; lean_object* v_leanLibDir_3661_; lean_object* v_nativeLibDir_3662_; lean_object* v_binDir_3663_; lean_object* v_irDir_3664_; lean_object* v_releaseRepo_3665_; lean_object* v_buildArchive_3666_; uint8_t v_preferReleaseBuild_3667_; lean_object* v_testDriver_3668_; lean_object* v_testDriverArgs_3669_; lean_object* v_lintDriver_3670_; lean_object* v_lintDriverArgs_3671_; lean_object* v_version_3672_; lean_object* v_versionTags_3673_; lean_object* v_description_3674_; lean_object* v_keywords_3675_; lean_object* v_homepage_3676_; lean_object* v_license_3677_; lean_object* v_licenseFiles_3678_; lean_object* v_readmeFile_3679_; uint8_t v_reservoir_3680_; lean_object* v_enableArtifactCache_x3f_3681_; lean_object* v_restoreAllArtifacts_x3f_3682_; uint8_t v_libPrefixOnWindows_3683_; uint8_t v_allowImportAll_3684_; uint8_t v_fixedToolchain_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3693_; 
v_toWorkspaceConfig_3653_ = lean_ctor_get(v_cfg_3652_, 0);
v_toLeanConfig_3654_ = lean_ctor_get(v_cfg_3652_, 1);
v_bootstrap_3655_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26);
v_extraDepTargets_3656_ = lean_ctor_get(v_cfg_3652_, 2);
v_precompileModules_3657_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3658_ = lean_ctor_get(v_cfg_3652_, 3);
v_srcDir_3659_ = lean_ctor_get(v_cfg_3652_, 4);
v_buildDir_3660_ = lean_ctor_get(v_cfg_3652_, 5);
v_leanLibDir_3661_ = lean_ctor_get(v_cfg_3652_, 6);
v_nativeLibDir_3662_ = lean_ctor_get(v_cfg_3652_, 7);
v_binDir_3663_ = lean_ctor_get(v_cfg_3652_, 8);
v_irDir_3664_ = lean_ctor_get(v_cfg_3652_, 9);
v_releaseRepo_3665_ = lean_ctor_get(v_cfg_3652_, 10);
v_buildArchive_3666_ = lean_ctor_get(v_cfg_3652_, 11);
v_preferReleaseBuild_3667_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26 + 2);
v_testDriver_3668_ = lean_ctor_get(v_cfg_3652_, 12);
v_testDriverArgs_3669_ = lean_ctor_get(v_cfg_3652_, 13);
v_lintDriver_3670_ = lean_ctor_get(v_cfg_3652_, 14);
v_lintDriverArgs_3671_ = lean_ctor_get(v_cfg_3652_, 15);
v_version_3672_ = lean_ctor_get(v_cfg_3652_, 16);
v_versionTags_3673_ = lean_ctor_get(v_cfg_3652_, 17);
v_description_3674_ = lean_ctor_get(v_cfg_3652_, 18);
v_keywords_3675_ = lean_ctor_get(v_cfg_3652_, 19);
v_homepage_3676_ = lean_ctor_get(v_cfg_3652_, 20);
v_license_3677_ = lean_ctor_get(v_cfg_3652_, 21);
v_licenseFiles_3678_ = lean_ctor_get(v_cfg_3652_, 22);
v_readmeFile_3679_ = lean_ctor_get(v_cfg_3652_, 23);
v_reservoir_3680_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3681_ = lean_ctor_get(v_cfg_3652_, 24);
v_restoreAllArtifacts_x3f_3682_ = lean_ctor_get(v_cfg_3652_, 25);
v_libPrefixOnWindows_3683_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26 + 4);
v_allowImportAll_3684_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26 + 5);
v_fixedToolchain_3685_ = lean_ctor_get_uint8(v_cfg_3652_, sizeof(void*)*26 + 6);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_cfg_3652_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3687_ = v_cfg_3652_;
v_isShared_3688_ = v_isSharedCheck_3693_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3682_);
lean_inc(v_enableArtifactCache_x3f_3681_);
lean_inc(v_readmeFile_3679_);
lean_inc(v_licenseFiles_3678_);
lean_inc(v_license_3677_);
lean_inc(v_homepage_3676_);
lean_inc(v_keywords_3675_);
lean_inc(v_description_3674_);
lean_inc(v_versionTags_3673_);
lean_inc(v_version_3672_);
lean_inc(v_lintDriverArgs_3671_);
lean_inc(v_lintDriver_3670_);
lean_inc(v_testDriverArgs_3669_);
lean_inc(v_testDriver_3668_);
lean_inc(v_buildArchive_3666_);
lean_inc(v_releaseRepo_3665_);
lean_inc(v_irDir_3664_);
lean_inc(v_binDir_3663_);
lean_inc(v_nativeLibDir_3662_);
lean_inc(v_leanLibDir_3661_);
lean_inc(v_buildDir_3660_);
lean_inc(v_srcDir_3659_);
lean_inc(v_moreGlobalServerArgs_3658_);
lean_inc(v_extraDepTargets_3656_);
lean_inc(v_toLeanConfig_3654_);
lean_inc(v_toWorkspaceConfig_3653_);
lean_dec(v_cfg_3652_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3693_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_apply_1(v_f_3651_, v_toWorkspaceConfig_3653_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3689_);
v___x_3691_ = v___x_3687_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_toLeanConfig_3654_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_extraDepTargets_3656_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_moreGlobalServerArgs_3658_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_srcDir_3659_);
lean_ctor_set(v_reuseFailAlloc_3692_, 5, v_buildDir_3660_);
lean_ctor_set(v_reuseFailAlloc_3692_, 6, v_leanLibDir_3661_);
lean_ctor_set(v_reuseFailAlloc_3692_, 7, v_nativeLibDir_3662_);
lean_ctor_set(v_reuseFailAlloc_3692_, 8, v_binDir_3663_);
lean_ctor_set(v_reuseFailAlloc_3692_, 9, v_irDir_3664_);
lean_ctor_set(v_reuseFailAlloc_3692_, 10, v_releaseRepo_3665_);
lean_ctor_set(v_reuseFailAlloc_3692_, 11, v_buildArchive_3666_);
lean_ctor_set(v_reuseFailAlloc_3692_, 12, v_testDriver_3668_);
lean_ctor_set(v_reuseFailAlloc_3692_, 13, v_testDriverArgs_3669_);
lean_ctor_set(v_reuseFailAlloc_3692_, 14, v_lintDriver_3670_);
lean_ctor_set(v_reuseFailAlloc_3692_, 15, v_lintDriverArgs_3671_);
lean_ctor_set(v_reuseFailAlloc_3692_, 16, v_version_3672_);
lean_ctor_set(v_reuseFailAlloc_3692_, 17, v_versionTags_3673_);
lean_ctor_set(v_reuseFailAlloc_3692_, 18, v_description_3674_);
lean_ctor_set(v_reuseFailAlloc_3692_, 19, v_keywords_3675_);
lean_ctor_set(v_reuseFailAlloc_3692_, 20, v_homepage_3676_);
lean_ctor_set(v_reuseFailAlloc_3692_, 21, v_license_3677_);
lean_ctor_set(v_reuseFailAlloc_3692_, 22, v_licenseFiles_3678_);
lean_ctor_set(v_reuseFailAlloc_3692_, 23, v_readmeFile_3679_);
lean_ctor_set(v_reuseFailAlloc_3692_, 24, v_enableArtifactCache_x3f_3681_);
lean_ctor_set(v_reuseFailAlloc_3692_, 25, v_restoreAllArtifacts_x3f_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26, v_bootstrap_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26 + 1, v_precompileModules_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26 + 3, v_reservoir_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26 + 5, v_allowImportAll_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*26 + 6, v_fixedToolchain_3685_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* v_x_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lake_defaultPackagesDir;
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* v_x_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(v_x_3696_);
lean_dec_ref(v_x_3696_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_3707_, lean_object* v_n_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_3710_, lean_object* v_n_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3710_, v_n_3711_);
lean_dec(v_n_3711_);
lean_dec(v_p_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_3713_, lean_object* v_n_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_3713_, v_n_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_3716_, lean_object* v_n_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_3716_, v_n_3717_);
lean_dec(v_n_3717_);
lean_dec(v_p_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_3719_){
_start:
{
lean_object* v_toLeanConfig_3720_; 
v_toLeanConfig_3720_ = lean_ctor_get(v_cfg_3719_, 1);
lean_inc_ref(v_toLeanConfig_3720_);
return v_toLeanConfig_3720_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(v_cfg_3721_);
lean_dec_ref(v_cfg_3721_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* v_val_3723_, lean_object* v_cfg_3724_){
_start:
{
lean_object* v_toWorkspaceConfig_3725_; uint8_t v_bootstrap_3726_; lean_object* v_extraDepTargets_3727_; uint8_t v_precompileModules_3728_; lean_object* v_moreGlobalServerArgs_3729_; lean_object* v_srcDir_3730_; lean_object* v_buildDir_3731_; lean_object* v_leanLibDir_3732_; lean_object* v_nativeLibDir_3733_; lean_object* v_binDir_3734_; lean_object* v_irDir_3735_; lean_object* v_releaseRepo_3736_; lean_object* v_buildArchive_3737_; uint8_t v_preferReleaseBuild_3738_; lean_object* v_testDriver_3739_; lean_object* v_testDriverArgs_3740_; lean_object* v_lintDriver_3741_; lean_object* v_lintDriverArgs_3742_; lean_object* v_version_3743_; lean_object* v_versionTags_3744_; lean_object* v_description_3745_; lean_object* v_keywords_3746_; lean_object* v_homepage_3747_; lean_object* v_license_3748_; lean_object* v_licenseFiles_3749_; lean_object* v_readmeFile_3750_; uint8_t v_reservoir_3751_; lean_object* v_enableArtifactCache_x3f_3752_; lean_object* v_restoreAllArtifacts_x3f_3753_; uint8_t v_libPrefixOnWindows_3754_; uint8_t v_allowImportAll_3755_; uint8_t v_fixedToolchain_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_toWorkspaceConfig_3725_ = lean_ctor_get(v_cfg_3724_, 0);
v_bootstrap_3726_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26);
v_extraDepTargets_3727_ = lean_ctor_get(v_cfg_3724_, 2);
v_precompileModules_3728_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3729_ = lean_ctor_get(v_cfg_3724_, 3);
v_srcDir_3730_ = lean_ctor_get(v_cfg_3724_, 4);
v_buildDir_3731_ = lean_ctor_get(v_cfg_3724_, 5);
v_leanLibDir_3732_ = lean_ctor_get(v_cfg_3724_, 6);
v_nativeLibDir_3733_ = lean_ctor_get(v_cfg_3724_, 7);
v_binDir_3734_ = lean_ctor_get(v_cfg_3724_, 8);
v_irDir_3735_ = lean_ctor_get(v_cfg_3724_, 9);
v_releaseRepo_3736_ = lean_ctor_get(v_cfg_3724_, 10);
v_buildArchive_3737_ = lean_ctor_get(v_cfg_3724_, 11);
v_preferReleaseBuild_3738_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26 + 2);
v_testDriver_3739_ = lean_ctor_get(v_cfg_3724_, 12);
v_testDriverArgs_3740_ = lean_ctor_get(v_cfg_3724_, 13);
v_lintDriver_3741_ = lean_ctor_get(v_cfg_3724_, 14);
v_lintDriverArgs_3742_ = lean_ctor_get(v_cfg_3724_, 15);
v_version_3743_ = lean_ctor_get(v_cfg_3724_, 16);
v_versionTags_3744_ = lean_ctor_get(v_cfg_3724_, 17);
v_description_3745_ = lean_ctor_get(v_cfg_3724_, 18);
v_keywords_3746_ = lean_ctor_get(v_cfg_3724_, 19);
v_homepage_3747_ = lean_ctor_get(v_cfg_3724_, 20);
v_license_3748_ = lean_ctor_get(v_cfg_3724_, 21);
v_licenseFiles_3749_ = lean_ctor_get(v_cfg_3724_, 22);
v_readmeFile_3750_ = lean_ctor_get(v_cfg_3724_, 23);
v_reservoir_3751_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3752_ = lean_ctor_get(v_cfg_3724_, 24);
v_restoreAllArtifacts_x3f_3753_ = lean_ctor_get(v_cfg_3724_, 25);
v_libPrefixOnWindows_3754_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26 + 4);
v_allowImportAll_3755_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26 + 5);
v_fixedToolchain_3756_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*26 + 6);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_cfg_3724_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v_cfg_3724_, 1);
lean_dec(v_unused_3764_);
v___x_3758_ = v_cfg_3724_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3753_);
lean_inc(v_enableArtifactCache_x3f_3752_);
lean_inc(v_readmeFile_3750_);
lean_inc(v_licenseFiles_3749_);
lean_inc(v_license_3748_);
lean_inc(v_homepage_3747_);
lean_inc(v_keywords_3746_);
lean_inc(v_description_3745_);
lean_inc(v_versionTags_3744_);
lean_inc(v_version_3743_);
lean_inc(v_lintDriverArgs_3742_);
lean_inc(v_lintDriver_3741_);
lean_inc(v_testDriverArgs_3740_);
lean_inc(v_testDriver_3739_);
lean_inc(v_buildArchive_3737_);
lean_inc(v_releaseRepo_3736_);
lean_inc(v_irDir_3735_);
lean_inc(v_binDir_3734_);
lean_inc(v_nativeLibDir_3733_);
lean_inc(v_leanLibDir_3732_);
lean_inc(v_buildDir_3731_);
lean_inc(v_srcDir_3730_);
lean_inc(v_moreGlobalServerArgs_3729_);
lean_inc(v_extraDepTargets_3727_);
lean_inc(v_toWorkspaceConfig_3725_);
lean_dec(v_cfg_3724_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 1, v_val_3723_);
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_toWorkspaceConfig_3725_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_val_3723_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_extraDepTargets_3727_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_moreGlobalServerArgs_3729_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_srcDir_3730_);
lean_ctor_set(v_reuseFailAlloc_3762_, 5, v_buildDir_3731_);
lean_ctor_set(v_reuseFailAlloc_3762_, 6, v_leanLibDir_3732_);
lean_ctor_set(v_reuseFailAlloc_3762_, 7, v_nativeLibDir_3733_);
lean_ctor_set(v_reuseFailAlloc_3762_, 8, v_binDir_3734_);
lean_ctor_set(v_reuseFailAlloc_3762_, 9, v_irDir_3735_);
lean_ctor_set(v_reuseFailAlloc_3762_, 10, v_releaseRepo_3736_);
lean_ctor_set(v_reuseFailAlloc_3762_, 11, v_buildArchive_3737_);
lean_ctor_set(v_reuseFailAlloc_3762_, 12, v_testDriver_3739_);
lean_ctor_set(v_reuseFailAlloc_3762_, 13, v_testDriverArgs_3740_);
lean_ctor_set(v_reuseFailAlloc_3762_, 14, v_lintDriver_3741_);
lean_ctor_set(v_reuseFailAlloc_3762_, 15, v_lintDriverArgs_3742_);
lean_ctor_set(v_reuseFailAlloc_3762_, 16, v_version_3743_);
lean_ctor_set(v_reuseFailAlloc_3762_, 17, v_versionTags_3744_);
lean_ctor_set(v_reuseFailAlloc_3762_, 18, v_description_3745_);
lean_ctor_set(v_reuseFailAlloc_3762_, 19, v_keywords_3746_);
lean_ctor_set(v_reuseFailAlloc_3762_, 20, v_homepage_3747_);
lean_ctor_set(v_reuseFailAlloc_3762_, 21, v_license_3748_);
lean_ctor_set(v_reuseFailAlloc_3762_, 22, v_licenseFiles_3749_);
lean_ctor_set(v_reuseFailAlloc_3762_, 23, v_readmeFile_3750_);
lean_ctor_set(v_reuseFailAlloc_3762_, 24, v_enableArtifactCache_x3f_3752_);
lean_ctor_set(v_reuseFailAlloc_3762_, 25, v_restoreAllArtifacts_x3f_3753_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26, v_bootstrap_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26 + 1, v_precompileModules_3728_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26 + 3, v_reservoir_3751_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3754_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26 + 5, v_allowImportAll_3755_);
lean_ctor_set_uint8(v_reuseFailAlloc_3762_, sizeof(void*)*26 + 6, v_fixedToolchain_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* v_f_3765_, lean_object* v_cfg_3766_){
_start:
{
lean_object* v_toWorkspaceConfig_3767_; lean_object* v_toLeanConfig_3768_; uint8_t v_bootstrap_3769_; lean_object* v_extraDepTargets_3770_; uint8_t v_precompileModules_3771_; lean_object* v_moreGlobalServerArgs_3772_; lean_object* v_srcDir_3773_; lean_object* v_buildDir_3774_; lean_object* v_leanLibDir_3775_; lean_object* v_nativeLibDir_3776_; lean_object* v_binDir_3777_; lean_object* v_irDir_3778_; lean_object* v_releaseRepo_3779_; lean_object* v_buildArchive_3780_; uint8_t v_preferReleaseBuild_3781_; lean_object* v_testDriver_3782_; lean_object* v_testDriverArgs_3783_; lean_object* v_lintDriver_3784_; lean_object* v_lintDriverArgs_3785_; lean_object* v_version_3786_; lean_object* v_versionTags_3787_; lean_object* v_description_3788_; lean_object* v_keywords_3789_; lean_object* v_homepage_3790_; lean_object* v_license_3791_; lean_object* v_licenseFiles_3792_; lean_object* v_readmeFile_3793_; uint8_t v_reservoir_3794_; lean_object* v_enableArtifactCache_x3f_3795_; lean_object* v_restoreAllArtifacts_x3f_3796_; uint8_t v_libPrefixOnWindows_3797_; uint8_t v_allowImportAll_3798_; uint8_t v_fixedToolchain_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
v_toWorkspaceConfig_3767_ = lean_ctor_get(v_cfg_3766_, 0);
v_toLeanConfig_3768_ = lean_ctor_get(v_cfg_3766_, 1);
v_bootstrap_3769_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26);
v_extraDepTargets_3770_ = lean_ctor_get(v_cfg_3766_, 2);
v_precompileModules_3771_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26 + 1);
v_moreGlobalServerArgs_3772_ = lean_ctor_get(v_cfg_3766_, 3);
v_srcDir_3773_ = lean_ctor_get(v_cfg_3766_, 4);
v_buildDir_3774_ = lean_ctor_get(v_cfg_3766_, 5);
v_leanLibDir_3775_ = lean_ctor_get(v_cfg_3766_, 6);
v_nativeLibDir_3776_ = lean_ctor_get(v_cfg_3766_, 7);
v_binDir_3777_ = lean_ctor_get(v_cfg_3766_, 8);
v_irDir_3778_ = lean_ctor_get(v_cfg_3766_, 9);
v_releaseRepo_3779_ = lean_ctor_get(v_cfg_3766_, 10);
v_buildArchive_3780_ = lean_ctor_get(v_cfg_3766_, 11);
v_preferReleaseBuild_3781_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26 + 2);
v_testDriver_3782_ = lean_ctor_get(v_cfg_3766_, 12);
v_testDriverArgs_3783_ = lean_ctor_get(v_cfg_3766_, 13);
v_lintDriver_3784_ = lean_ctor_get(v_cfg_3766_, 14);
v_lintDriverArgs_3785_ = lean_ctor_get(v_cfg_3766_, 15);
v_version_3786_ = lean_ctor_get(v_cfg_3766_, 16);
v_versionTags_3787_ = lean_ctor_get(v_cfg_3766_, 17);
v_description_3788_ = lean_ctor_get(v_cfg_3766_, 18);
v_keywords_3789_ = lean_ctor_get(v_cfg_3766_, 19);
v_homepage_3790_ = lean_ctor_get(v_cfg_3766_, 20);
v_license_3791_ = lean_ctor_get(v_cfg_3766_, 21);
v_licenseFiles_3792_ = lean_ctor_get(v_cfg_3766_, 22);
v_readmeFile_3793_ = lean_ctor_get(v_cfg_3766_, 23);
v_reservoir_3794_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26 + 3);
v_enableArtifactCache_x3f_3795_ = lean_ctor_get(v_cfg_3766_, 24);
v_restoreAllArtifacts_x3f_3796_ = lean_ctor_get(v_cfg_3766_, 25);
v_libPrefixOnWindows_3797_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26 + 4);
v_allowImportAll_3798_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26 + 5);
v_fixedToolchain_3799_ = lean_ctor_get_uint8(v_cfg_3766_, sizeof(void*)*26 + 6);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_cfg_3766_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3801_ = v_cfg_3766_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_restoreAllArtifacts_x3f_3796_);
lean_inc(v_enableArtifactCache_x3f_3795_);
lean_inc(v_readmeFile_3793_);
lean_inc(v_licenseFiles_3792_);
lean_inc(v_license_3791_);
lean_inc(v_homepage_3790_);
lean_inc(v_keywords_3789_);
lean_inc(v_description_3788_);
lean_inc(v_versionTags_3787_);
lean_inc(v_version_3786_);
lean_inc(v_lintDriverArgs_3785_);
lean_inc(v_lintDriver_3784_);
lean_inc(v_testDriverArgs_3783_);
lean_inc(v_testDriver_3782_);
lean_inc(v_buildArchive_3780_);
lean_inc(v_releaseRepo_3779_);
lean_inc(v_irDir_3778_);
lean_inc(v_binDir_3777_);
lean_inc(v_nativeLibDir_3776_);
lean_inc(v_leanLibDir_3775_);
lean_inc(v_buildDir_3774_);
lean_inc(v_srcDir_3773_);
lean_inc(v_moreGlobalServerArgs_3772_);
lean_inc(v_extraDepTargets_3770_);
lean_inc(v_toLeanConfig_3768_);
lean_inc(v_toWorkspaceConfig_3767_);
lean_dec(v_cfg_3766_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_apply_1(v_f_3765_, v_toLeanConfig_3768_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_toWorkspaceConfig_3767_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_extraDepTargets_3770_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_moreGlobalServerArgs_3772_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v_srcDir_3773_);
lean_ctor_set(v_reuseFailAlloc_3806_, 5, v_buildDir_3774_);
lean_ctor_set(v_reuseFailAlloc_3806_, 6, v_leanLibDir_3775_);
lean_ctor_set(v_reuseFailAlloc_3806_, 7, v_nativeLibDir_3776_);
lean_ctor_set(v_reuseFailAlloc_3806_, 8, v_binDir_3777_);
lean_ctor_set(v_reuseFailAlloc_3806_, 9, v_irDir_3778_);
lean_ctor_set(v_reuseFailAlloc_3806_, 10, v_releaseRepo_3779_);
lean_ctor_set(v_reuseFailAlloc_3806_, 11, v_buildArchive_3780_);
lean_ctor_set(v_reuseFailAlloc_3806_, 12, v_testDriver_3782_);
lean_ctor_set(v_reuseFailAlloc_3806_, 13, v_testDriverArgs_3783_);
lean_ctor_set(v_reuseFailAlloc_3806_, 14, v_lintDriver_3784_);
lean_ctor_set(v_reuseFailAlloc_3806_, 15, v_lintDriverArgs_3785_);
lean_ctor_set(v_reuseFailAlloc_3806_, 16, v_version_3786_);
lean_ctor_set(v_reuseFailAlloc_3806_, 17, v_versionTags_3787_);
lean_ctor_set(v_reuseFailAlloc_3806_, 18, v_description_3788_);
lean_ctor_set(v_reuseFailAlloc_3806_, 19, v_keywords_3789_);
lean_ctor_set(v_reuseFailAlloc_3806_, 20, v_homepage_3790_);
lean_ctor_set(v_reuseFailAlloc_3806_, 21, v_license_3791_);
lean_ctor_set(v_reuseFailAlloc_3806_, 22, v_licenseFiles_3792_);
lean_ctor_set(v_reuseFailAlloc_3806_, 23, v_readmeFile_3793_);
lean_ctor_set(v_reuseFailAlloc_3806_, 24, v_enableArtifactCache_x3f_3795_);
lean_ctor_set(v_reuseFailAlloc_3806_, 25, v_restoreAllArtifacts_x3f_3796_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26, v_bootstrap_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26 + 1, v_precompileModules_3771_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26 + 2, v_preferReleaseBuild_3781_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26 + 3, v_reservoir_3794_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26 + 4, v_libPrefixOnWindows_3797_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26 + 5, v_allowImportAll_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*26 + 6, v_fixedToolchain_3799_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* v_x_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__3(v_x_3817_);
lean_dec_ref(v_x_3817_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_3828_, lean_object* v_n_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___closed__4));
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_3831_, lean_object* v_n_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_3831_, v_n_3832_);
lean_dec(v_n_3832_);
lean_dec(v_p_3831_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_3834_, lean_object* v_n_3835_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_3834_, v_n_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_3837_, lean_object* v_n_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_3837_, v_n_3838_);
lean_dec(v_n_3838_);
lean_dec(v_p_3837_);
return v_res_3839_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_3850_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_3851_ = lean_array_push(v___x_3850_, v___x_3849_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_3860_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_3861_ = lean_array_push(v___x_3860_, v___x_3859_);
return v___x_3861_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3869_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_3870_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_3871_ = lean_array_push(v___x_3870_, v___x_3869_);
return v___x_3871_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_3880_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_3881_ = lean_array_push(v___x_3880_, v___x_3879_);
return v___x_3881_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_3890_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_3891_ = lean_array_push(v___x_3890_, v___x_3889_);
return v___x_3891_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_3900_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_3901_ = lean_array_push(v___x_3900_, v___x_3899_);
return v___x_3901_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_3910_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_3911_ = lean_array_push(v___x_3910_, v___x_3909_);
return v___x_3911_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_3920_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_3921_ = lean_array_push(v___x_3920_, v___x_3919_);
return v___x_3921_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_3930_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_3931_ = lean_array_push(v___x_3930_, v___x_3929_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_3940_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_3941_ = lean_array_push(v___x_3940_, v___x_3939_);
return v___x_3941_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_3950_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_3951_ = lean_array_push(v___x_3950_, v___x_3949_);
return v___x_3951_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_3960_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_3961_ = lean_array_push(v___x_3960_, v___x_3959_);
return v___x_3961_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_3970_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_3971_ = lean_array_push(v___x_3970_, v___x_3969_);
return v___x_3971_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_3980_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_3981_ = lean_array_push(v___x_3980_, v___x_3979_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_3990_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_3991_ = lean_array_push(v___x_3990_, v___x_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_4000_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_4001_ = lean_array_push(v___x_4000_, v___x_3999_);
return v___x_4001_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4009_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__67));
v___x_4010_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4011_ = lean_array_push(v___x_4010_, v___x_4009_);
return v___x_4011_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4020_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4021_ = lean_array_push(v___x_4020_, v___x_4019_);
return v___x_4021_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4029_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4030_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4031_ = lean_array_push(v___x_4030_, v___x_4029_);
return v___x_4031_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4040_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4041_ = lean_array_push(v___x_4040_, v___x_4039_);
return v___x_4041_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4050_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4051_ = lean_array_push(v___x_4050_, v___x_4049_);
return v___x_4051_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4060_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4061_ = lean_array_push(v___x_4060_, v___x_4059_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4069_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4070_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4071_ = lean_array_push(v___x_4070_, v___x_4069_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_4080_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4081_ = lean_array_push(v___x_4080_, v___x_4079_);
return v___x_4081_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_4090_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4091_ = lean_array_push(v___x_4090_, v___x_4089_);
return v___x_4091_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_4100_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4101_ = lean_array_push(v___x_4100_, v___x_4099_);
return v___x_4101_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_4110_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4111_ = lean_array_push(v___x_4110_, v___x_4109_);
return v___x_4111_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4119_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_4120_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4121_ = lean_array_push(v___x_4120_, v___x_4119_);
return v___x_4121_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_4130_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4131_ = lean_array_push(v___x_4130_, v___x_4129_);
return v___x_4131_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4139_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_4140_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4141_ = lean_array_push(v___x_4140_, v___x_4139_);
return v___x_4141_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_4150_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4151_ = lean_array_push(v___x_4150_, v___x_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_4160_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4161_ = lean_array_push(v___x_4160_, v___x_4159_);
return v___x_4161_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4169_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4170_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4171_ = lean_array_push(v___x_4170_, v___x_4169_);
return v___x_4171_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4179_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_4180_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4181_ = lean_array_push(v___x_4180_, v___x_4179_);
return v___x_4181_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_4190_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_4191_ = lean_array_push(v___x_4190_, v___x_4189_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_4200_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_4201_ = lean_array_push(v___x_4200_, v___x_4199_);
return v___x_4201_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_4210_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_4211_ = lean_array_push(v___x_4210_, v___x_4209_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__149(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = l_Lake_WorkspaceConfig___fields;
v___x_4213_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_4214_ = l_Array_append___redArg(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__153(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4222_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__152));
v___x_4223_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__149, &l_Lake_PackageConfig___fields___closed__149_once, _init_l_Lake_PackageConfig___fields___closed__149);
v___x_4224_ = lean_array_push(v___x_4223_, v___x_4222_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__154(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = l_Lake_LeanConfig___fields;
v___x_4226_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__153, &l_Lake_PackageConfig___fields___closed__153_once, _init_l_Lake_PackageConfig___fields___closed__153);
v___x_4227_ = l_Array_append___redArg(v___x_4226_, v___x_4225_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__158(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__157));
v___x_4236_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__154, &l_Lake_PackageConfig___fields___closed__154_once, _init_l_Lake_PackageConfig___fields___closed__154);
v___x_4237_ = lean_array_push(v___x_4236_, v___x_4235_);
return v___x_4237_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__158, &l_Lake_PackageConfig___fields___closed__158_once, _init_l_Lake_PackageConfig___fields___closed__158);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_4239_, lean_object* v_n_4240_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lake_PackageConfig___fields;
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_4242_, lean_object* v_n_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lake_PackageConfig_instConfigFields(v_p_4242_, v_n_4243_);
lean_dec(v_n_4243_);
lean_dec(v_p_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_4245_, lean_object* v_x2_4246_){
_start:
{
lean_object* v_name_4247_; lean_object* v___x_4248_; 
v_name_4247_ = lean_ctor_get(v_x2_4246_, 0);
lean_inc(v_name_4247_);
v___x_4248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_4247_, v_x2_4246_, v_x1_4245_);
return v___x_4248_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = l_Lake_PackageConfig___fields;
v___x_4250_ = lean_array_get_size(v___x_4249_);
return v___x_4250_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v___x_4270_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4271_ = lean_unsigned_to_nat(0u);
v___x_4272_ = lean_nat_dec_lt(v___x_4271_, v___x_4270_);
return v___x_4272_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_4274_; uint8_t v___x_4275_; 
v___x_4274_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4275_ = lean_nat_dec_le(v___x_4274_, v___x_4274_);
return v___x_4275_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_4276_; size_t v___x_4277_; 
v___x_4276_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4277_ = lean_usize_of_nat(v___x_4276_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_4278_; size_t v___x_4279_; size_t v___x_4280_; lean_object* v___x_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4278_ = lean_box(1);
v___x_4279_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_4280_ = ((size_t)0ULL);
v___x_4281_ = l_Lake_PackageConfig___fields;
v___f_4282_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_4283_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4283_, v___f_4282_, v___x_4281_, v___x_4280_, v___x_4279_, v___x_4278_);
return v___x_4284_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___y_4287_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4285_ = l_Lake_PackageConfig___fields;
v___x_4290_ = lean_box(1);
v___x_4291_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_4291_ == 0)
{
v___y_4287_ = v___x_4290_;
goto v___jp_4286_;
}
else
{
uint8_t v___x_4292_; 
v___x_4292_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_4292_ == 0)
{
if (v___x_4291_ == 0)
{
v___y_4287_ = v___x_4290_;
goto v___jp_4286_;
}
else
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4287_ = v___x_4293_;
goto v___jp_4286_;
}
}
else
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4287_ = v___x_4294_;
goto v___jp_4286_;
}
}
v___jp_4286_:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_4287_);
v___x_4289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4285_);
lean_ctor_set(v___x_4289_, 1, v___y_4287_);
lean_ctor_set(v___x_4289_, 2, v___x_4288_);
return v___x_4289_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
uint8_t v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4295_ = 1;
v___x_4296_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
v___x_4297_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
v___x_4298_ = l_Lake_defaultVersionTags;
v___x_4299_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
v___x_4300_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
v___x_4301_ = lean_box(0);
v___x_4302_ = l_Lake_defaultIrDir;
v___x_4303_ = l_Lake_defaultBinDir;
v___x_4304_ = l_Lake_defaultNativeLibDir;
v___x_4305_ = l_Lake_defaultLeanLibDir;
v___x_4306_ = l_Lake_defaultBuildDir;
v___x_4307_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_4308_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_4309_ = 0;
v___x_4310_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_4311_ = l_Lake_defaultPackagesDir;
v___x_4312_ = lean_alloc_ctor(0, 26, 7);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
lean_ctor_set(v___x_4312_, 1, v___x_4310_);
lean_ctor_set(v___x_4312_, 2, v___x_4308_);
lean_ctor_set(v___x_4312_, 3, v___x_4308_);
lean_ctor_set(v___x_4312_, 4, v___x_4307_);
lean_ctor_set(v___x_4312_, 5, v___x_4306_);
lean_ctor_set(v___x_4312_, 6, v___x_4305_);
lean_ctor_set(v___x_4312_, 7, v___x_4304_);
lean_ctor_set(v___x_4312_, 8, v___x_4303_);
lean_ctor_set(v___x_4312_, 9, v___x_4302_);
lean_ctor_set(v___x_4312_, 10, v___x_4301_);
lean_ctor_set(v___x_4312_, 11, v___x_4301_);
lean_ctor_set(v___x_4312_, 12, v___x_4300_);
lean_ctor_set(v___x_4312_, 13, v___x_4308_);
lean_ctor_set(v___x_4312_, 14, v___x_4300_);
lean_ctor_set(v___x_4312_, 15, v___x_4308_);
lean_ctor_set(v___x_4312_, 16, v___x_4299_);
lean_ctor_set(v___x_4312_, 17, v___x_4298_);
lean_ctor_set(v___x_4312_, 18, v___x_4300_);
lean_ctor_set(v___x_4312_, 19, v___x_4308_);
lean_ctor_set(v___x_4312_, 20, v___x_4300_);
lean_ctor_set(v___x_4312_, 21, v___x_4300_);
lean_ctor_set(v___x_4312_, 22, v___x_4297_);
lean_ctor_set(v___x_4312_, 23, v___x_4296_);
lean_ctor_set(v___x_4312_, 24, v___x_4301_);
lean_ctor_set(v___x_4312_, 25, v___x_4301_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26, v___x_4309_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26 + 1, v___x_4309_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26 + 2, v___x_4309_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26 + 3, v___x_4295_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26 + 4, v___x_4309_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26 + 5, v___x_4309_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*26 + 6, v___x_4309_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_4313_, lean_object* v_n_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_4316_, lean_object* v_n_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Lake_PackageConfig_instEmptyCollection(v_p_4316_, v_n_4317_);
lean_dec(v_n_4317_);
lean_dec(v_p_4316_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_4319_){
_start:
{
lean_inc(v_n_4319_);
return v_n_4319_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Lake_PackageConfig_origName___redArg(v_n_4320_);
lean_dec(v_n_4320_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_4322_, lean_object* v_n_4323_, lean_object* v_x_4324_){
_start:
{
lean_inc(v_n_4323_);
return v_n_4323_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_4325_, lean_object* v_n_4326_, lean_object* v_x_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Lake_PackageConfig_origName(v_p_4325_, v_n_4326_, v_x_4327_);
lean_dec_ref(v_x_4327_);
lean_dec(v_n_4326_);
lean_dec(v_p_4325_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_4336_){
_start:
{
lean_object* v_keyName_4337_; 
v_keyName_4337_ = lean_ctor_get(v_self_4336_, 1);
lean_inc(v_keyName_4337_);
return v_keyName_4337_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lake_PackageDecl_name(v_self_4338_);
lean_dec_ref(v_self_4338_);
return v_res_4339_;
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
