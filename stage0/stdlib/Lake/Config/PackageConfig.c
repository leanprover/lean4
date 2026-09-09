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
extern lean_object* l_Lake_LeanConfig___fields;
extern lean_object* l_Lake_WorkspaceConfig___fields;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_checks___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_checks___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_checks___proj___closed__0 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_checks___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_checks___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_checks___proj___closed__1 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_checks___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_checks___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_checks___proj___closed__2 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_checks___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_checks___proj___closed__0_value),((lean_object*)&l_Lake_PackageConfig_checks___proj___closed__1_value),((lean_object*)&l_Lake_PackageConfig_checks___proj___closed__2_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_checks___proj___closed__3 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_PackageConfig___fields___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "checks"};
static const lean_object* l_Lake_PackageConfig___fields___closed__153 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__153_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__153_value),LEAN_SCALAR_PTR_LITERAL(26, 43, 61, 84, 108, 97, 184, 96)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__154 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__154_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__154_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__154_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__155 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__155_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__156;
static const lean_string_object l_Lake_PackageConfig___fields___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fixedToolchain"};
static const lean_object* l_Lake_PackageConfig___fields___closed__157 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__157_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__157_value),LEAN_SCALAR_PTR_LITERAL(248, 4, 88, 39, 97, 195, 130, 156)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__158 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__158_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__158_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__158_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__159 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__159_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__160_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__160;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__161_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__161;
static const lean_string_object l_Lake_PackageConfig___fields___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toWorkspaceConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__162 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__162_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__162_value),LEAN_SCALAR_PTR_LITERAL(135, 228, 155, 156, 156, 252, 46, 118)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__163 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__163_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__163_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__163_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__164 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__164_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__165_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__165;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__166_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__166;
static const lean_string_object l_Lake_PackageConfig___fields___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__167 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__167_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__167_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__168 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__168_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__168_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__168_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__169 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__169_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__170_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__170;
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
v___x_44_ = lean_alloc_ctor(0, 28, 7);
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
lean_ctor_set(v___x_44_, 27, v___x_40_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28 + 1, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28 + 2, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28 + 3, v___x_27_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28 + 4, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28 + 5, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*28 + 6, v___x_41_);
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
v_bootstrap_58_ = lean_ctor_get_uint8(v_cfg_57_, sizeof(void*)*28);
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
lean_object* v_toWorkspaceConfig_64_; lean_object* v_toLeanConfig_65_; lean_object* v_extraDepTargets_66_; uint8_t v_precompileModules_67_; lean_object* v_moreGlobalServerArgs_68_; lean_object* v_srcDir_69_; lean_object* v_buildDir_70_; lean_object* v_leanLibDir_71_; lean_object* v_nativeLibDir_72_; lean_object* v_binDir_73_; lean_object* v_irDir_74_; lean_object* v_releaseRepo_75_; lean_object* v_buildArchive_76_; uint8_t v_preferReleaseBuild_77_; lean_object* v_testDriver_78_; lean_object* v_testDriverArgs_79_; lean_object* v_lintDriver_80_; lean_object* v_lintDriverArgs_81_; lean_object* v_version_82_; lean_object* v_versionTags_83_; lean_object* v_description_84_; lean_object* v_keywords_85_; lean_object* v_homepage_86_; lean_object* v_license_87_; lean_object* v_licenseFiles_88_; lean_object* v_readmeFile_89_; uint8_t v_reservoir_90_; lean_object* v_enableArtifactCache_x3f_91_; lean_object* v_restoreAllArtifacts_x3f_92_; uint8_t v_libPrefixOnWindows_93_; uint8_t v_allowImportAll_94_; lean_object* v_builtinLint_x3f_95_; lean_object* v_checks_96_; uint8_t v_fixedToolchain_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_toWorkspaceConfig_64_ = lean_ctor_get(v_cfg_63_, 0);
v_toLeanConfig_65_ = lean_ctor_get(v_cfg_63_, 1);
v_extraDepTargets_66_ = lean_ctor_get(v_cfg_63_, 2);
v_precompileModules_67_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_68_ = lean_ctor_get(v_cfg_63_, 3);
v_srcDir_69_ = lean_ctor_get(v_cfg_63_, 4);
v_buildDir_70_ = lean_ctor_get(v_cfg_63_, 5);
v_leanLibDir_71_ = lean_ctor_get(v_cfg_63_, 6);
v_nativeLibDir_72_ = lean_ctor_get(v_cfg_63_, 7);
v_binDir_73_ = lean_ctor_get(v_cfg_63_, 8);
v_irDir_74_ = lean_ctor_get(v_cfg_63_, 9);
v_releaseRepo_75_ = lean_ctor_get(v_cfg_63_, 10);
v_buildArchive_76_ = lean_ctor_get(v_cfg_63_, 11);
v_preferReleaseBuild_77_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*28 + 2);
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
v_reservoir_90_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_91_ = lean_ctor_get(v_cfg_63_, 24);
v_restoreAllArtifacts_x3f_92_ = lean_ctor_get(v_cfg_63_, 25);
v_libPrefixOnWindows_93_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*28 + 4);
v_allowImportAll_94_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_95_ = lean_ctor_get(v_cfg_63_, 26);
v_checks_96_ = lean_ctor_get(v_cfg_63_, 27);
v_fixedToolchain_97_ = lean_ctor_get_uint8(v_cfg_63_, sizeof(void*)*28 + 6);
v_isSharedCheck_104_ = !lean_is_exclusive(v_cfg_63_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v_cfg_63_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_checks_96_);
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
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_toWorkspaceConfig_64_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_toLeanConfig_65_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_extraDepTargets_66_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_moreGlobalServerArgs_68_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v_srcDir_69_);
lean_ctor_set(v_reuseFailAlloc_103_, 5, v_buildDir_70_);
lean_ctor_set(v_reuseFailAlloc_103_, 6, v_leanLibDir_71_);
lean_ctor_set(v_reuseFailAlloc_103_, 7, v_nativeLibDir_72_);
lean_ctor_set(v_reuseFailAlloc_103_, 8, v_binDir_73_);
lean_ctor_set(v_reuseFailAlloc_103_, 9, v_irDir_74_);
lean_ctor_set(v_reuseFailAlloc_103_, 10, v_releaseRepo_75_);
lean_ctor_set(v_reuseFailAlloc_103_, 11, v_buildArchive_76_);
lean_ctor_set(v_reuseFailAlloc_103_, 12, v_testDriver_78_);
lean_ctor_set(v_reuseFailAlloc_103_, 13, v_testDriverArgs_79_);
lean_ctor_set(v_reuseFailAlloc_103_, 14, v_lintDriver_80_);
lean_ctor_set(v_reuseFailAlloc_103_, 15, v_lintDriverArgs_81_);
lean_ctor_set(v_reuseFailAlloc_103_, 16, v_version_82_);
lean_ctor_set(v_reuseFailAlloc_103_, 17, v_versionTags_83_);
lean_ctor_set(v_reuseFailAlloc_103_, 18, v_description_84_);
lean_ctor_set(v_reuseFailAlloc_103_, 19, v_keywords_85_);
lean_ctor_set(v_reuseFailAlloc_103_, 20, v_homepage_86_);
lean_ctor_set(v_reuseFailAlloc_103_, 21, v_license_87_);
lean_ctor_set(v_reuseFailAlloc_103_, 22, v_licenseFiles_88_);
lean_ctor_set(v_reuseFailAlloc_103_, 23, v_readmeFile_89_);
lean_ctor_set(v_reuseFailAlloc_103_, 24, v_enableArtifactCache_x3f_91_);
lean_ctor_set(v_reuseFailAlloc_103_, 25, v_restoreAllArtifacts_x3f_92_);
lean_ctor_set(v_reuseFailAlloc_103_, 26, v_builtinLint_x3f_95_);
lean_ctor_set(v_reuseFailAlloc_103_, 27, v_checks_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*28 + 1, v_precompileModules_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*28 + 2, v_preferReleaseBuild_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*28 + 3, v_reservoir_90_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*28 + 5, v_allowImportAll_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*28 + 6, v_fixedToolchain_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*28, v_val_62_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__1___boxed(lean_object* v_val_105_, lean_object* v_cfg_106_){
_start:
{
uint8_t v_val_140__boxed_107_; lean_object* v_res_108_; 
v_val_140__boxed_107_ = lean_unbox(v_val_105_);
v_res_108_ = l_Lake_PackageConfig_bootstrap___proj___lam__1(v_val_140__boxed_107_, v_cfg_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__2(lean_object* v_f_109_, lean_object* v_cfg_110_){
_start:
{
lean_object* v_toWorkspaceConfig_111_; lean_object* v_toLeanConfig_112_; uint8_t v_bootstrap_113_; lean_object* v_extraDepTargets_114_; uint8_t v_precompileModules_115_; lean_object* v_moreGlobalServerArgs_116_; lean_object* v_srcDir_117_; lean_object* v_buildDir_118_; lean_object* v_leanLibDir_119_; lean_object* v_nativeLibDir_120_; lean_object* v_binDir_121_; lean_object* v_irDir_122_; lean_object* v_releaseRepo_123_; lean_object* v_buildArchive_124_; uint8_t v_preferReleaseBuild_125_; lean_object* v_testDriver_126_; lean_object* v_testDriverArgs_127_; lean_object* v_lintDriver_128_; lean_object* v_lintDriverArgs_129_; lean_object* v_version_130_; lean_object* v_versionTags_131_; lean_object* v_description_132_; lean_object* v_keywords_133_; lean_object* v_homepage_134_; lean_object* v_license_135_; lean_object* v_licenseFiles_136_; lean_object* v_readmeFile_137_; uint8_t v_reservoir_138_; lean_object* v_enableArtifactCache_x3f_139_; lean_object* v_restoreAllArtifacts_x3f_140_; uint8_t v_libPrefixOnWindows_141_; uint8_t v_allowImportAll_142_; lean_object* v_builtinLint_x3f_143_; lean_object* v_checks_144_; uint8_t v_fixedToolchain_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_155_; 
v_toWorkspaceConfig_111_ = lean_ctor_get(v_cfg_110_, 0);
v_toLeanConfig_112_ = lean_ctor_get(v_cfg_110_, 1);
v_bootstrap_113_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28);
v_extraDepTargets_114_ = lean_ctor_get(v_cfg_110_, 2);
v_precompileModules_115_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_116_ = lean_ctor_get(v_cfg_110_, 3);
v_srcDir_117_ = lean_ctor_get(v_cfg_110_, 4);
v_buildDir_118_ = lean_ctor_get(v_cfg_110_, 5);
v_leanLibDir_119_ = lean_ctor_get(v_cfg_110_, 6);
v_nativeLibDir_120_ = lean_ctor_get(v_cfg_110_, 7);
v_binDir_121_ = lean_ctor_get(v_cfg_110_, 8);
v_irDir_122_ = lean_ctor_get(v_cfg_110_, 9);
v_releaseRepo_123_ = lean_ctor_get(v_cfg_110_, 10);
v_buildArchive_124_ = lean_ctor_get(v_cfg_110_, 11);
v_preferReleaseBuild_125_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28 + 2);
v_testDriver_126_ = lean_ctor_get(v_cfg_110_, 12);
v_testDriverArgs_127_ = lean_ctor_get(v_cfg_110_, 13);
v_lintDriver_128_ = lean_ctor_get(v_cfg_110_, 14);
v_lintDriverArgs_129_ = lean_ctor_get(v_cfg_110_, 15);
v_version_130_ = lean_ctor_get(v_cfg_110_, 16);
v_versionTags_131_ = lean_ctor_get(v_cfg_110_, 17);
v_description_132_ = lean_ctor_get(v_cfg_110_, 18);
v_keywords_133_ = lean_ctor_get(v_cfg_110_, 19);
v_homepage_134_ = lean_ctor_get(v_cfg_110_, 20);
v_license_135_ = lean_ctor_get(v_cfg_110_, 21);
v_licenseFiles_136_ = lean_ctor_get(v_cfg_110_, 22);
v_readmeFile_137_ = lean_ctor_get(v_cfg_110_, 23);
v_reservoir_138_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_139_ = lean_ctor_get(v_cfg_110_, 24);
v_restoreAllArtifacts_x3f_140_ = lean_ctor_get(v_cfg_110_, 25);
v_libPrefixOnWindows_141_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28 + 4);
v_allowImportAll_142_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_143_ = lean_ctor_get(v_cfg_110_, 26);
v_checks_144_ = lean_ctor_get(v_cfg_110_, 27);
v_fixedToolchain_145_ = lean_ctor_get_uint8(v_cfg_110_, sizeof(void*)*28 + 6);
v_isSharedCheck_155_ = !lean_is_exclusive(v_cfg_110_);
if (v_isSharedCheck_155_ == 0)
{
v___x_147_ = v_cfg_110_;
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_checks_144_);
lean_inc(v_builtinLint_x3f_143_);
lean_inc(v_restoreAllArtifacts_x3f_140_);
lean_inc(v_enableArtifactCache_x3f_139_);
lean_inc(v_readmeFile_137_);
lean_inc(v_licenseFiles_136_);
lean_inc(v_license_135_);
lean_inc(v_homepage_134_);
lean_inc(v_keywords_133_);
lean_inc(v_description_132_);
lean_inc(v_versionTags_131_);
lean_inc(v_version_130_);
lean_inc(v_lintDriverArgs_129_);
lean_inc(v_lintDriver_128_);
lean_inc(v_testDriverArgs_127_);
lean_inc(v_testDriver_126_);
lean_inc(v_buildArchive_124_);
lean_inc(v_releaseRepo_123_);
lean_inc(v_irDir_122_);
lean_inc(v_binDir_121_);
lean_inc(v_nativeLibDir_120_);
lean_inc(v_leanLibDir_119_);
lean_inc(v_buildDir_118_);
lean_inc(v_srcDir_117_);
lean_inc(v_moreGlobalServerArgs_116_);
lean_inc(v_extraDepTargets_114_);
lean_inc(v_toLeanConfig_112_);
lean_inc(v_toWorkspaceConfig_111_);
lean_dec(v_cfg_110_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_149_ = lean_box(v_bootstrap_113_);
v___x_150_ = lean_apply_1(v_f_109_, v___x_149_);
if (v_isShared_148_ == 0)
{
v___x_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_toWorkspaceConfig_111_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_toLeanConfig_112_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_extraDepTargets_114_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_moreGlobalServerArgs_116_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_srcDir_117_);
lean_ctor_set(v_reuseFailAlloc_154_, 5, v_buildDir_118_);
lean_ctor_set(v_reuseFailAlloc_154_, 6, v_leanLibDir_119_);
lean_ctor_set(v_reuseFailAlloc_154_, 7, v_nativeLibDir_120_);
lean_ctor_set(v_reuseFailAlloc_154_, 8, v_binDir_121_);
lean_ctor_set(v_reuseFailAlloc_154_, 9, v_irDir_122_);
lean_ctor_set(v_reuseFailAlloc_154_, 10, v_releaseRepo_123_);
lean_ctor_set(v_reuseFailAlloc_154_, 11, v_buildArchive_124_);
lean_ctor_set(v_reuseFailAlloc_154_, 12, v_testDriver_126_);
lean_ctor_set(v_reuseFailAlloc_154_, 13, v_testDriverArgs_127_);
lean_ctor_set(v_reuseFailAlloc_154_, 14, v_lintDriver_128_);
lean_ctor_set(v_reuseFailAlloc_154_, 15, v_lintDriverArgs_129_);
lean_ctor_set(v_reuseFailAlloc_154_, 16, v_version_130_);
lean_ctor_set(v_reuseFailAlloc_154_, 17, v_versionTags_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 18, v_description_132_);
lean_ctor_set(v_reuseFailAlloc_154_, 19, v_keywords_133_);
lean_ctor_set(v_reuseFailAlloc_154_, 20, v_homepage_134_);
lean_ctor_set(v_reuseFailAlloc_154_, 21, v_license_135_);
lean_ctor_set(v_reuseFailAlloc_154_, 22, v_licenseFiles_136_);
lean_ctor_set(v_reuseFailAlloc_154_, 23, v_readmeFile_137_);
lean_ctor_set(v_reuseFailAlloc_154_, 24, v_enableArtifactCache_x3f_139_);
lean_ctor_set(v_reuseFailAlloc_154_, 25, v_restoreAllArtifacts_x3f_140_);
lean_ctor_set(v_reuseFailAlloc_154_, 26, v_builtinLint_x3f_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 27, v_checks_144_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
uint8_t v___x_153_; 
v___x_153_ = lean_unbox(v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28, v___x_153_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28 + 1, v_precompileModules_115_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28 + 2, v_preferReleaseBuild_125_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28 + 3, v_reservoir_138_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_141_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28 + 5, v_allowImportAll_142_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*28 + 6, v_fixedToolchain_145_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___lam__3(lean_object* v_x_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___lam__3___boxed(lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lake_PackageConfig_bootstrap___proj___lam__3(v_x_158_);
lean_dec_ref(v_x_158_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_170_, lean_object* v_n_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___closed__4));
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_173_, lean_object* v_n_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lake_PackageConfig_bootstrap___proj(v_p_173_, v_n_174_);
lean_dec(v_n_174_);
lean_dec(v_p_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_176_, lean_object* v_n_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lake_PackageConfig_bootstrap___proj(v_p_176_, v_n_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_179_, lean_object* v_n_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_179_, v_n_180_);
lean_dec(v_n_180_);
lean_dec(v_p_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0(lean_object* v_cfg_182_){
_start:
{
lean_object* v_extraDepTargets_183_; 
v_extraDepTargets_183_ = lean_ctor_get(v_cfg_182_, 2);
lean_inc_ref(v_extraDepTargets_183_);
return v_extraDepTargets_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__0___boxed(lean_object* v_cfg_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__0(v_cfg_184_);
lean_dec_ref(v_cfg_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__1(lean_object* v_val_186_, lean_object* v_cfg_187_){
_start:
{
lean_object* v_toWorkspaceConfig_188_; lean_object* v_toLeanConfig_189_; uint8_t v_bootstrap_190_; uint8_t v_precompileModules_191_; lean_object* v_moreGlobalServerArgs_192_; lean_object* v_srcDir_193_; lean_object* v_buildDir_194_; lean_object* v_leanLibDir_195_; lean_object* v_nativeLibDir_196_; lean_object* v_binDir_197_; lean_object* v_irDir_198_; lean_object* v_releaseRepo_199_; lean_object* v_buildArchive_200_; uint8_t v_preferReleaseBuild_201_; lean_object* v_testDriver_202_; lean_object* v_testDriverArgs_203_; lean_object* v_lintDriver_204_; lean_object* v_lintDriverArgs_205_; lean_object* v_version_206_; lean_object* v_versionTags_207_; lean_object* v_description_208_; lean_object* v_keywords_209_; lean_object* v_homepage_210_; lean_object* v_license_211_; lean_object* v_licenseFiles_212_; lean_object* v_readmeFile_213_; uint8_t v_reservoir_214_; lean_object* v_enableArtifactCache_x3f_215_; lean_object* v_restoreAllArtifacts_x3f_216_; uint8_t v_libPrefixOnWindows_217_; uint8_t v_allowImportAll_218_; lean_object* v_builtinLint_x3f_219_; lean_object* v_checks_220_; uint8_t v_fixedToolchain_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_toWorkspaceConfig_188_ = lean_ctor_get(v_cfg_187_, 0);
v_toLeanConfig_189_ = lean_ctor_get(v_cfg_187_, 1);
v_bootstrap_190_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28);
v_precompileModules_191_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_192_ = lean_ctor_get(v_cfg_187_, 3);
v_srcDir_193_ = lean_ctor_get(v_cfg_187_, 4);
v_buildDir_194_ = lean_ctor_get(v_cfg_187_, 5);
v_leanLibDir_195_ = lean_ctor_get(v_cfg_187_, 6);
v_nativeLibDir_196_ = lean_ctor_get(v_cfg_187_, 7);
v_binDir_197_ = lean_ctor_get(v_cfg_187_, 8);
v_irDir_198_ = lean_ctor_get(v_cfg_187_, 9);
v_releaseRepo_199_ = lean_ctor_get(v_cfg_187_, 10);
v_buildArchive_200_ = lean_ctor_get(v_cfg_187_, 11);
v_preferReleaseBuild_201_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28 + 2);
v_testDriver_202_ = lean_ctor_get(v_cfg_187_, 12);
v_testDriverArgs_203_ = lean_ctor_get(v_cfg_187_, 13);
v_lintDriver_204_ = lean_ctor_get(v_cfg_187_, 14);
v_lintDriverArgs_205_ = lean_ctor_get(v_cfg_187_, 15);
v_version_206_ = lean_ctor_get(v_cfg_187_, 16);
v_versionTags_207_ = lean_ctor_get(v_cfg_187_, 17);
v_description_208_ = lean_ctor_get(v_cfg_187_, 18);
v_keywords_209_ = lean_ctor_get(v_cfg_187_, 19);
v_homepage_210_ = lean_ctor_get(v_cfg_187_, 20);
v_license_211_ = lean_ctor_get(v_cfg_187_, 21);
v_licenseFiles_212_ = lean_ctor_get(v_cfg_187_, 22);
v_readmeFile_213_ = lean_ctor_get(v_cfg_187_, 23);
v_reservoir_214_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_215_ = lean_ctor_get(v_cfg_187_, 24);
v_restoreAllArtifacts_x3f_216_ = lean_ctor_get(v_cfg_187_, 25);
v_libPrefixOnWindows_217_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28 + 4);
v_allowImportAll_218_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_219_ = lean_ctor_get(v_cfg_187_, 26);
v_checks_220_ = lean_ctor_get(v_cfg_187_, 27);
v_fixedToolchain_221_ = lean_ctor_get_uint8(v_cfg_187_, sizeof(void*)*28 + 6);
v_isSharedCheck_228_ = !lean_is_exclusive(v_cfg_187_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_cfg_187_, 2);
lean_dec(v_unused_229_);
v___x_223_ = v_cfg_187_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_checks_220_);
lean_inc(v_builtinLint_x3f_219_);
lean_inc(v_restoreAllArtifacts_x3f_216_);
lean_inc(v_enableArtifactCache_x3f_215_);
lean_inc(v_readmeFile_213_);
lean_inc(v_licenseFiles_212_);
lean_inc(v_license_211_);
lean_inc(v_homepage_210_);
lean_inc(v_keywords_209_);
lean_inc(v_description_208_);
lean_inc(v_versionTags_207_);
lean_inc(v_version_206_);
lean_inc(v_lintDriverArgs_205_);
lean_inc(v_lintDriver_204_);
lean_inc(v_testDriverArgs_203_);
lean_inc(v_testDriver_202_);
lean_inc(v_buildArchive_200_);
lean_inc(v_releaseRepo_199_);
lean_inc(v_irDir_198_);
lean_inc(v_binDir_197_);
lean_inc(v_nativeLibDir_196_);
lean_inc(v_leanLibDir_195_);
lean_inc(v_buildDir_194_);
lean_inc(v_srcDir_193_);
lean_inc(v_moreGlobalServerArgs_192_);
lean_inc(v_toLeanConfig_189_);
lean_inc(v_toWorkspaceConfig_188_);
lean_dec(v_cfg_187_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 2, v_val_186_);
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_toWorkspaceConfig_188_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_toLeanConfig_189_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_val_186_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_moreGlobalServerArgs_192_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_srcDir_193_);
lean_ctor_set(v_reuseFailAlloc_227_, 5, v_buildDir_194_);
lean_ctor_set(v_reuseFailAlloc_227_, 6, v_leanLibDir_195_);
lean_ctor_set(v_reuseFailAlloc_227_, 7, v_nativeLibDir_196_);
lean_ctor_set(v_reuseFailAlloc_227_, 8, v_binDir_197_);
lean_ctor_set(v_reuseFailAlloc_227_, 9, v_irDir_198_);
lean_ctor_set(v_reuseFailAlloc_227_, 10, v_releaseRepo_199_);
lean_ctor_set(v_reuseFailAlloc_227_, 11, v_buildArchive_200_);
lean_ctor_set(v_reuseFailAlloc_227_, 12, v_testDriver_202_);
lean_ctor_set(v_reuseFailAlloc_227_, 13, v_testDriverArgs_203_);
lean_ctor_set(v_reuseFailAlloc_227_, 14, v_lintDriver_204_);
lean_ctor_set(v_reuseFailAlloc_227_, 15, v_lintDriverArgs_205_);
lean_ctor_set(v_reuseFailAlloc_227_, 16, v_version_206_);
lean_ctor_set(v_reuseFailAlloc_227_, 17, v_versionTags_207_);
lean_ctor_set(v_reuseFailAlloc_227_, 18, v_description_208_);
lean_ctor_set(v_reuseFailAlloc_227_, 19, v_keywords_209_);
lean_ctor_set(v_reuseFailAlloc_227_, 20, v_homepage_210_);
lean_ctor_set(v_reuseFailAlloc_227_, 21, v_license_211_);
lean_ctor_set(v_reuseFailAlloc_227_, 22, v_licenseFiles_212_);
lean_ctor_set(v_reuseFailAlloc_227_, 23, v_readmeFile_213_);
lean_ctor_set(v_reuseFailAlloc_227_, 24, v_enableArtifactCache_x3f_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 25, v_restoreAllArtifacts_x3f_216_);
lean_ctor_set(v_reuseFailAlloc_227_, 26, v_builtinLint_x3f_219_);
lean_ctor_set(v_reuseFailAlloc_227_, 27, v_checks_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28, v_bootstrap_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28 + 1, v_precompileModules_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28 + 2, v_preferReleaseBuild_201_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28 + 3, v_reservoir_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28 + 5, v_allowImportAll_218_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*28 + 6, v_fixedToolchain_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__2(lean_object* v_f_230_, lean_object* v_cfg_231_){
_start:
{
lean_object* v_toWorkspaceConfig_232_; lean_object* v_toLeanConfig_233_; uint8_t v_bootstrap_234_; lean_object* v_extraDepTargets_235_; uint8_t v_precompileModules_236_; lean_object* v_moreGlobalServerArgs_237_; lean_object* v_srcDir_238_; lean_object* v_buildDir_239_; lean_object* v_leanLibDir_240_; lean_object* v_nativeLibDir_241_; lean_object* v_binDir_242_; lean_object* v_irDir_243_; lean_object* v_releaseRepo_244_; lean_object* v_buildArchive_245_; uint8_t v_preferReleaseBuild_246_; lean_object* v_testDriver_247_; lean_object* v_testDriverArgs_248_; lean_object* v_lintDriver_249_; lean_object* v_lintDriverArgs_250_; lean_object* v_version_251_; lean_object* v_versionTags_252_; lean_object* v_description_253_; lean_object* v_keywords_254_; lean_object* v_homepage_255_; lean_object* v_license_256_; lean_object* v_licenseFiles_257_; lean_object* v_readmeFile_258_; uint8_t v_reservoir_259_; lean_object* v_enableArtifactCache_x3f_260_; lean_object* v_restoreAllArtifacts_x3f_261_; uint8_t v_libPrefixOnWindows_262_; uint8_t v_allowImportAll_263_; lean_object* v_builtinLint_x3f_264_; lean_object* v_checks_265_; uint8_t v_fixedToolchain_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_toWorkspaceConfig_232_ = lean_ctor_get(v_cfg_231_, 0);
v_toLeanConfig_233_ = lean_ctor_get(v_cfg_231_, 1);
v_bootstrap_234_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28);
v_extraDepTargets_235_ = lean_ctor_get(v_cfg_231_, 2);
v_precompileModules_236_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_237_ = lean_ctor_get(v_cfg_231_, 3);
v_srcDir_238_ = lean_ctor_get(v_cfg_231_, 4);
v_buildDir_239_ = lean_ctor_get(v_cfg_231_, 5);
v_leanLibDir_240_ = lean_ctor_get(v_cfg_231_, 6);
v_nativeLibDir_241_ = lean_ctor_get(v_cfg_231_, 7);
v_binDir_242_ = lean_ctor_get(v_cfg_231_, 8);
v_irDir_243_ = lean_ctor_get(v_cfg_231_, 9);
v_releaseRepo_244_ = lean_ctor_get(v_cfg_231_, 10);
v_buildArchive_245_ = lean_ctor_get(v_cfg_231_, 11);
v_preferReleaseBuild_246_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28 + 2);
v_testDriver_247_ = lean_ctor_get(v_cfg_231_, 12);
v_testDriverArgs_248_ = lean_ctor_get(v_cfg_231_, 13);
v_lintDriver_249_ = lean_ctor_get(v_cfg_231_, 14);
v_lintDriverArgs_250_ = lean_ctor_get(v_cfg_231_, 15);
v_version_251_ = lean_ctor_get(v_cfg_231_, 16);
v_versionTags_252_ = lean_ctor_get(v_cfg_231_, 17);
v_description_253_ = lean_ctor_get(v_cfg_231_, 18);
v_keywords_254_ = lean_ctor_get(v_cfg_231_, 19);
v_homepage_255_ = lean_ctor_get(v_cfg_231_, 20);
v_license_256_ = lean_ctor_get(v_cfg_231_, 21);
v_licenseFiles_257_ = lean_ctor_get(v_cfg_231_, 22);
v_readmeFile_258_ = lean_ctor_get(v_cfg_231_, 23);
v_reservoir_259_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_260_ = lean_ctor_get(v_cfg_231_, 24);
v_restoreAllArtifacts_x3f_261_ = lean_ctor_get(v_cfg_231_, 25);
v_libPrefixOnWindows_262_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28 + 4);
v_allowImportAll_263_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_264_ = lean_ctor_get(v_cfg_231_, 26);
v_checks_265_ = lean_ctor_get(v_cfg_231_, 27);
v_fixedToolchain_266_ = lean_ctor_get_uint8(v_cfg_231_, sizeof(void*)*28 + 6);
v_isSharedCheck_274_ = !lean_is_exclusive(v_cfg_231_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v_cfg_231_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_checks_265_);
lean_inc(v_builtinLint_x3f_264_);
lean_inc(v_restoreAllArtifacts_x3f_261_);
lean_inc(v_enableArtifactCache_x3f_260_);
lean_inc(v_readmeFile_258_);
lean_inc(v_licenseFiles_257_);
lean_inc(v_license_256_);
lean_inc(v_homepage_255_);
lean_inc(v_keywords_254_);
lean_inc(v_description_253_);
lean_inc(v_versionTags_252_);
lean_inc(v_version_251_);
lean_inc(v_lintDriverArgs_250_);
lean_inc(v_lintDriver_249_);
lean_inc(v_testDriverArgs_248_);
lean_inc(v_testDriver_247_);
lean_inc(v_buildArchive_245_);
lean_inc(v_releaseRepo_244_);
lean_inc(v_irDir_243_);
lean_inc(v_binDir_242_);
lean_inc(v_nativeLibDir_241_);
lean_inc(v_leanLibDir_240_);
lean_inc(v_buildDir_239_);
lean_inc(v_srcDir_238_);
lean_inc(v_moreGlobalServerArgs_237_);
lean_inc(v_extraDepTargets_235_);
lean_inc(v_toLeanConfig_233_);
lean_inc(v_toWorkspaceConfig_232_);
lean_dec(v_cfg_231_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_apply_1(v_f_230_, v_extraDepTargets_235_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 2, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_toWorkspaceConfig_232_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_toLeanConfig_233_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_moreGlobalServerArgs_237_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_srcDir_238_);
lean_ctor_set(v_reuseFailAlloc_273_, 5, v_buildDir_239_);
lean_ctor_set(v_reuseFailAlloc_273_, 6, v_leanLibDir_240_);
lean_ctor_set(v_reuseFailAlloc_273_, 7, v_nativeLibDir_241_);
lean_ctor_set(v_reuseFailAlloc_273_, 8, v_binDir_242_);
lean_ctor_set(v_reuseFailAlloc_273_, 9, v_irDir_243_);
lean_ctor_set(v_reuseFailAlloc_273_, 10, v_releaseRepo_244_);
lean_ctor_set(v_reuseFailAlloc_273_, 11, v_buildArchive_245_);
lean_ctor_set(v_reuseFailAlloc_273_, 12, v_testDriver_247_);
lean_ctor_set(v_reuseFailAlloc_273_, 13, v_testDriverArgs_248_);
lean_ctor_set(v_reuseFailAlloc_273_, 14, v_lintDriver_249_);
lean_ctor_set(v_reuseFailAlloc_273_, 15, v_lintDriverArgs_250_);
lean_ctor_set(v_reuseFailAlloc_273_, 16, v_version_251_);
lean_ctor_set(v_reuseFailAlloc_273_, 17, v_versionTags_252_);
lean_ctor_set(v_reuseFailAlloc_273_, 18, v_description_253_);
lean_ctor_set(v_reuseFailAlloc_273_, 19, v_keywords_254_);
lean_ctor_set(v_reuseFailAlloc_273_, 20, v_homepage_255_);
lean_ctor_set(v_reuseFailAlloc_273_, 21, v_license_256_);
lean_ctor_set(v_reuseFailAlloc_273_, 22, v_licenseFiles_257_);
lean_ctor_set(v_reuseFailAlloc_273_, 23, v_readmeFile_258_);
lean_ctor_set(v_reuseFailAlloc_273_, 24, v_enableArtifactCache_x3f_260_);
lean_ctor_set(v_reuseFailAlloc_273_, 25, v_restoreAllArtifacts_x3f_261_);
lean_ctor_set(v_reuseFailAlloc_273_, 26, v_builtinLint_x3f_264_);
lean_ctor_set(v_reuseFailAlloc_273_, 27, v_checks_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28, v_bootstrap_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28 + 1, v_precompileModules_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28 + 2, v_preferReleaseBuild_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28 + 3, v_reservoir_259_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_262_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28 + 5, v_allowImportAll_263_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*28 + 6, v_fixedToolchain_266_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3(lean_object* v_x_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__0));
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___lam__3___boxed(lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lake_PackageConfig_extraDepTargets___proj___lam__3(v_x_277_);
lean_dec_ref(v_x_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_288_, lean_object* v_n_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___closed__4));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_291_, lean_object* v_n_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_291_, v_n_292_);
lean_dec(v_n_292_);
lean_dec(v_p_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_294_, lean_object* v_n_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_294_, v_n_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_297_, lean_object* v_n_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_297_, v_n_298_);
lean_dec(v_n_298_);
lean_dec(v_p_297_);
return v_res_299_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___lam__0(lean_object* v_cfg_300_){
_start:
{
uint8_t v_precompileModules_301_; 
v_precompileModules_301_ = lean_ctor_get_uint8(v_cfg_300_, sizeof(void*)*28 + 1);
return v_precompileModules_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__0___boxed(lean_object* v_cfg_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lake_PackageConfig_precompileModules___proj___lam__0(v_cfg_302_);
lean_dec_ref(v_cfg_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1(uint8_t v_val_305_, lean_object* v_cfg_306_){
_start:
{
lean_object* v_toWorkspaceConfig_307_; lean_object* v_toLeanConfig_308_; uint8_t v_bootstrap_309_; lean_object* v_extraDepTargets_310_; lean_object* v_moreGlobalServerArgs_311_; lean_object* v_srcDir_312_; lean_object* v_buildDir_313_; lean_object* v_leanLibDir_314_; lean_object* v_nativeLibDir_315_; lean_object* v_binDir_316_; lean_object* v_irDir_317_; lean_object* v_releaseRepo_318_; lean_object* v_buildArchive_319_; uint8_t v_preferReleaseBuild_320_; lean_object* v_testDriver_321_; lean_object* v_testDriverArgs_322_; lean_object* v_lintDriver_323_; lean_object* v_lintDriverArgs_324_; lean_object* v_version_325_; lean_object* v_versionTags_326_; lean_object* v_description_327_; lean_object* v_keywords_328_; lean_object* v_homepage_329_; lean_object* v_license_330_; lean_object* v_licenseFiles_331_; lean_object* v_readmeFile_332_; uint8_t v_reservoir_333_; lean_object* v_enableArtifactCache_x3f_334_; lean_object* v_restoreAllArtifacts_x3f_335_; uint8_t v_libPrefixOnWindows_336_; uint8_t v_allowImportAll_337_; lean_object* v_builtinLint_x3f_338_; lean_object* v_checks_339_; uint8_t v_fixedToolchain_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_toWorkspaceConfig_307_ = lean_ctor_get(v_cfg_306_, 0);
v_toLeanConfig_308_ = lean_ctor_get(v_cfg_306_, 1);
v_bootstrap_309_ = lean_ctor_get_uint8(v_cfg_306_, sizeof(void*)*28);
v_extraDepTargets_310_ = lean_ctor_get(v_cfg_306_, 2);
v_moreGlobalServerArgs_311_ = lean_ctor_get(v_cfg_306_, 3);
v_srcDir_312_ = lean_ctor_get(v_cfg_306_, 4);
v_buildDir_313_ = lean_ctor_get(v_cfg_306_, 5);
v_leanLibDir_314_ = lean_ctor_get(v_cfg_306_, 6);
v_nativeLibDir_315_ = lean_ctor_get(v_cfg_306_, 7);
v_binDir_316_ = lean_ctor_get(v_cfg_306_, 8);
v_irDir_317_ = lean_ctor_get(v_cfg_306_, 9);
v_releaseRepo_318_ = lean_ctor_get(v_cfg_306_, 10);
v_buildArchive_319_ = lean_ctor_get(v_cfg_306_, 11);
v_preferReleaseBuild_320_ = lean_ctor_get_uint8(v_cfg_306_, sizeof(void*)*28 + 2);
v_testDriver_321_ = lean_ctor_get(v_cfg_306_, 12);
v_testDriverArgs_322_ = lean_ctor_get(v_cfg_306_, 13);
v_lintDriver_323_ = lean_ctor_get(v_cfg_306_, 14);
v_lintDriverArgs_324_ = lean_ctor_get(v_cfg_306_, 15);
v_version_325_ = lean_ctor_get(v_cfg_306_, 16);
v_versionTags_326_ = lean_ctor_get(v_cfg_306_, 17);
v_description_327_ = lean_ctor_get(v_cfg_306_, 18);
v_keywords_328_ = lean_ctor_get(v_cfg_306_, 19);
v_homepage_329_ = lean_ctor_get(v_cfg_306_, 20);
v_license_330_ = lean_ctor_get(v_cfg_306_, 21);
v_licenseFiles_331_ = lean_ctor_get(v_cfg_306_, 22);
v_readmeFile_332_ = lean_ctor_get(v_cfg_306_, 23);
v_reservoir_333_ = lean_ctor_get_uint8(v_cfg_306_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_334_ = lean_ctor_get(v_cfg_306_, 24);
v_restoreAllArtifacts_x3f_335_ = lean_ctor_get(v_cfg_306_, 25);
v_libPrefixOnWindows_336_ = lean_ctor_get_uint8(v_cfg_306_, sizeof(void*)*28 + 4);
v_allowImportAll_337_ = lean_ctor_get_uint8(v_cfg_306_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_338_ = lean_ctor_get(v_cfg_306_, 26);
v_checks_339_ = lean_ctor_get(v_cfg_306_, 27);
v_fixedToolchain_340_ = lean_ctor_get_uint8(v_cfg_306_, sizeof(void*)*28 + 6);
v_isSharedCheck_347_ = !lean_is_exclusive(v_cfg_306_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v_cfg_306_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_checks_339_);
lean_inc(v_builtinLint_x3f_338_);
lean_inc(v_restoreAllArtifacts_x3f_335_);
lean_inc(v_enableArtifactCache_x3f_334_);
lean_inc(v_readmeFile_332_);
lean_inc(v_licenseFiles_331_);
lean_inc(v_license_330_);
lean_inc(v_homepage_329_);
lean_inc(v_keywords_328_);
lean_inc(v_description_327_);
lean_inc(v_versionTags_326_);
lean_inc(v_version_325_);
lean_inc(v_lintDriverArgs_324_);
lean_inc(v_lintDriver_323_);
lean_inc(v_testDriverArgs_322_);
lean_inc(v_testDriver_321_);
lean_inc(v_buildArchive_319_);
lean_inc(v_releaseRepo_318_);
lean_inc(v_irDir_317_);
lean_inc(v_binDir_316_);
lean_inc(v_nativeLibDir_315_);
lean_inc(v_leanLibDir_314_);
lean_inc(v_buildDir_313_);
lean_inc(v_srcDir_312_);
lean_inc(v_moreGlobalServerArgs_311_);
lean_inc(v_extraDepTargets_310_);
lean_inc(v_toLeanConfig_308_);
lean_inc(v_toWorkspaceConfig_307_);
lean_dec(v_cfg_306_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_toWorkspaceConfig_307_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_toLeanConfig_308_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_extraDepTargets_310_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_moreGlobalServerArgs_311_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_srcDir_312_);
lean_ctor_set(v_reuseFailAlloc_346_, 5, v_buildDir_313_);
lean_ctor_set(v_reuseFailAlloc_346_, 6, v_leanLibDir_314_);
lean_ctor_set(v_reuseFailAlloc_346_, 7, v_nativeLibDir_315_);
lean_ctor_set(v_reuseFailAlloc_346_, 8, v_binDir_316_);
lean_ctor_set(v_reuseFailAlloc_346_, 9, v_irDir_317_);
lean_ctor_set(v_reuseFailAlloc_346_, 10, v_releaseRepo_318_);
lean_ctor_set(v_reuseFailAlloc_346_, 11, v_buildArchive_319_);
lean_ctor_set(v_reuseFailAlloc_346_, 12, v_testDriver_321_);
lean_ctor_set(v_reuseFailAlloc_346_, 13, v_testDriverArgs_322_);
lean_ctor_set(v_reuseFailAlloc_346_, 14, v_lintDriver_323_);
lean_ctor_set(v_reuseFailAlloc_346_, 15, v_lintDriverArgs_324_);
lean_ctor_set(v_reuseFailAlloc_346_, 16, v_version_325_);
lean_ctor_set(v_reuseFailAlloc_346_, 17, v_versionTags_326_);
lean_ctor_set(v_reuseFailAlloc_346_, 18, v_description_327_);
lean_ctor_set(v_reuseFailAlloc_346_, 19, v_keywords_328_);
lean_ctor_set(v_reuseFailAlloc_346_, 20, v_homepage_329_);
lean_ctor_set(v_reuseFailAlloc_346_, 21, v_license_330_);
lean_ctor_set(v_reuseFailAlloc_346_, 22, v_licenseFiles_331_);
lean_ctor_set(v_reuseFailAlloc_346_, 23, v_readmeFile_332_);
lean_ctor_set(v_reuseFailAlloc_346_, 24, v_enableArtifactCache_x3f_334_);
lean_ctor_set(v_reuseFailAlloc_346_, 25, v_restoreAllArtifacts_x3f_335_);
lean_ctor_set(v_reuseFailAlloc_346_, 26, v_builtinLint_x3f_338_);
lean_ctor_set(v_reuseFailAlloc_346_, 27, v_checks_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*28, v_bootstrap_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*28 + 2, v_preferReleaseBuild_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*28 + 3, v_reservoir_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*28 + 5, v_allowImportAll_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*28 + 6, v_fixedToolchain_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*28 + 1, v_val_305_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__1___boxed(lean_object* v_val_348_, lean_object* v_cfg_349_){
_start:
{
uint8_t v_val_140__boxed_350_; lean_object* v_res_351_; 
v_val_140__boxed_350_ = lean_unbox(v_val_348_);
v_res_351_ = l_Lake_PackageConfig_precompileModules___proj___lam__1(v_val_140__boxed_350_, v_cfg_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___lam__2(lean_object* v_f_352_, lean_object* v_cfg_353_){
_start:
{
lean_object* v_toWorkspaceConfig_354_; lean_object* v_toLeanConfig_355_; uint8_t v_bootstrap_356_; lean_object* v_extraDepTargets_357_; uint8_t v_precompileModules_358_; lean_object* v_moreGlobalServerArgs_359_; lean_object* v_srcDir_360_; lean_object* v_buildDir_361_; lean_object* v_leanLibDir_362_; lean_object* v_nativeLibDir_363_; lean_object* v_binDir_364_; lean_object* v_irDir_365_; lean_object* v_releaseRepo_366_; lean_object* v_buildArchive_367_; uint8_t v_preferReleaseBuild_368_; lean_object* v_testDriver_369_; lean_object* v_testDriverArgs_370_; lean_object* v_lintDriver_371_; lean_object* v_lintDriverArgs_372_; lean_object* v_version_373_; lean_object* v_versionTags_374_; lean_object* v_description_375_; lean_object* v_keywords_376_; lean_object* v_homepage_377_; lean_object* v_license_378_; lean_object* v_licenseFiles_379_; lean_object* v_readmeFile_380_; uint8_t v_reservoir_381_; lean_object* v_enableArtifactCache_x3f_382_; lean_object* v_restoreAllArtifacts_x3f_383_; uint8_t v_libPrefixOnWindows_384_; uint8_t v_allowImportAll_385_; lean_object* v_builtinLint_x3f_386_; lean_object* v_checks_387_; uint8_t v_fixedToolchain_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_398_; 
v_toWorkspaceConfig_354_ = lean_ctor_get(v_cfg_353_, 0);
v_toLeanConfig_355_ = lean_ctor_get(v_cfg_353_, 1);
v_bootstrap_356_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28);
v_extraDepTargets_357_ = lean_ctor_get(v_cfg_353_, 2);
v_precompileModules_358_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_359_ = lean_ctor_get(v_cfg_353_, 3);
v_srcDir_360_ = lean_ctor_get(v_cfg_353_, 4);
v_buildDir_361_ = lean_ctor_get(v_cfg_353_, 5);
v_leanLibDir_362_ = lean_ctor_get(v_cfg_353_, 6);
v_nativeLibDir_363_ = lean_ctor_get(v_cfg_353_, 7);
v_binDir_364_ = lean_ctor_get(v_cfg_353_, 8);
v_irDir_365_ = lean_ctor_get(v_cfg_353_, 9);
v_releaseRepo_366_ = lean_ctor_get(v_cfg_353_, 10);
v_buildArchive_367_ = lean_ctor_get(v_cfg_353_, 11);
v_preferReleaseBuild_368_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28 + 2);
v_testDriver_369_ = lean_ctor_get(v_cfg_353_, 12);
v_testDriverArgs_370_ = lean_ctor_get(v_cfg_353_, 13);
v_lintDriver_371_ = lean_ctor_get(v_cfg_353_, 14);
v_lintDriverArgs_372_ = lean_ctor_get(v_cfg_353_, 15);
v_version_373_ = lean_ctor_get(v_cfg_353_, 16);
v_versionTags_374_ = lean_ctor_get(v_cfg_353_, 17);
v_description_375_ = lean_ctor_get(v_cfg_353_, 18);
v_keywords_376_ = lean_ctor_get(v_cfg_353_, 19);
v_homepage_377_ = lean_ctor_get(v_cfg_353_, 20);
v_license_378_ = lean_ctor_get(v_cfg_353_, 21);
v_licenseFiles_379_ = lean_ctor_get(v_cfg_353_, 22);
v_readmeFile_380_ = lean_ctor_get(v_cfg_353_, 23);
v_reservoir_381_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_382_ = lean_ctor_get(v_cfg_353_, 24);
v_restoreAllArtifacts_x3f_383_ = lean_ctor_get(v_cfg_353_, 25);
v_libPrefixOnWindows_384_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28 + 4);
v_allowImportAll_385_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_386_ = lean_ctor_get(v_cfg_353_, 26);
v_checks_387_ = lean_ctor_get(v_cfg_353_, 27);
v_fixedToolchain_388_ = lean_ctor_get_uint8(v_cfg_353_, sizeof(void*)*28 + 6);
v_isSharedCheck_398_ = !lean_is_exclusive(v_cfg_353_);
if (v_isSharedCheck_398_ == 0)
{
v___x_390_ = v_cfg_353_;
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_checks_387_);
lean_inc(v_builtinLint_x3f_386_);
lean_inc(v_restoreAllArtifacts_x3f_383_);
lean_inc(v_enableArtifactCache_x3f_382_);
lean_inc(v_readmeFile_380_);
lean_inc(v_licenseFiles_379_);
lean_inc(v_license_378_);
lean_inc(v_homepage_377_);
lean_inc(v_keywords_376_);
lean_inc(v_description_375_);
lean_inc(v_versionTags_374_);
lean_inc(v_version_373_);
lean_inc(v_lintDriverArgs_372_);
lean_inc(v_lintDriver_371_);
lean_inc(v_testDriverArgs_370_);
lean_inc(v_testDriver_369_);
lean_inc(v_buildArchive_367_);
lean_inc(v_releaseRepo_366_);
lean_inc(v_irDir_365_);
lean_inc(v_binDir_364_);
lean_inc(v_nativeLibDir_363_);
lean_inc(v_leanLibDir_362_);
lean_inc(v_buildDir_361_);
lean_inc(v_srcDir_360_);
lean_inc(v_moreGlobalServerArgs_359_);
lean_inc(v_extraDepTargets_357_);
lean_inc(v_toLeanConfig_355_);
lean_inc(v_toWorkspaceConfig_354_);
lean_dec(v_cfg_353_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = lean_box(v_precompileModules_358_);
v___x_393_ = lean_apply_1(v_f_352_, v___x_392_);
if (v_isShared_391_ == 0)
{
v___x_395_ = v___x_390_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_toWorkspaceConfig_354_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_toLeanConfig_355_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_extraDepTargets_357_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_moreGlobalServerArgs_359_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_srcDir_360_);
lean_ctor_set(v_reuseFailAlloc_397_, 5, v_buildDir_361_);
lean_ctor_set(v_reuseFailAlloc_397_, 6, v_leanLibDir_362_);
lean_ctor_set(v_reuseFailAlloc_397_, 7, v_nativeLibDir_363_);
lean_ctor_set(v_reuseFailAlloc_397_, 8, v_binDir_364_);
lean_ctor_set(v_reuseFailAlloc_397_, 9, v_irDir_365_);
lean_ctor_set(v_reuseFailAlloc_397_, 10, v_releaseRepo_366_);
lean_ctor_set(v_reuseFailAlloc_397_, 11, v_buildArchive_367_);
lean_ctor_set(v_reuseFailAlloc_397_, 12, v_testDriver_369_);
lean_ctor_set(v_reuseFailAlloc_397_, 13, v_testDriverArgs_370_);
lean_ctor_set(v_reuseFailAlloc_397_, 14, v_lintDriver_371_);
lean_ctor_set(v_reuseFailAlloc_397_, 15, v_lintDriverArgs_372_);
lean_ctor_set(v_reuseFailAlloc_397_, 16, v_version_373_);
lean_ctor_set(v_reuseFailAlloc_397_, 17, v_versionTags_374_);
lean_ctor_set(v_reuseFailAlloc_397_, 18, v_description_375_);
lean_ctor_set(v_reuseFailAlloc_397_, 19, v_keywords_376_);
lean_ctor_set(v_reuseFailAlloc_397_, 20, v_homepage_377_);
lean_ctor_set(v_reuseFailAlloc_397_, 21, v_license_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 22, v_licenseFiles_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 23, v_readmeFile_380_);
lean_ctor_set(v_reuseFailAlloc_397_, 24, v_enableArtifactCache_x3f_382_);
lean_ctor_set(v_reuseFailAlloc_397_, 25, v_restoreAllArtifacts_x3f_383_);
lean_ctor_set(v_reuseFailAlloc_397_, 26, v_builtinLint_x3f_386_);
lean_ctor_set(v_reuseFailAlloc_397_, 27, v_checks_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_397_, sizeof(void*)*28, v_bootstrap_356_);
v___x_395_ = v_reuseFailAlloc_397_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
uint8_t v___x_396_; 
v___x_396_ = lean_unbox(v___x_393_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*28 + 1, v___x_396_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*28 + 2, v_preferReleaseBuild_368_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*28 + 3, v_reservoir_381_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_384_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*28 + 5, v_allowImportAll_385_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*28 + 6, v_fixedToolchain_388_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_407_, lean_object* v_n_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___closed__3));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_410_, lean_object* v_n_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lake_PackageConfig_precompileModules___proj(v_p_410_, v_n_411_);
lean_dec(v_n_411_);
lean_dec(v_p_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_413_, lean_object* v_n_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lake_PackageConfig_precompileModules___proj(v_p_413_, v_n_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_416_, lean_object* v_n_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_416_, v_n_417_);
lean_dec(v_n_417_);
lean_dec(v_p_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(lean_object* v_cfg_419_){
_start:
{
lean_object* v_moreGlobalServerArgs_420_; 
v_moreGlobalServerArgs_420_ = lean_ctor_get(v_cfg_419_, 3);
lean_inc_ref(v_moreGlobalServerArgs_420_);
return v_moreGlobalServerArgs_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0___boxed(lean_object* v_cfg_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__0(v_cfg_421_);
lean_dec_ref(v_cfg_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__1(lean_object* v_val_423_, lean_object* v_cfg_424_){
_start:
{
lean_object* v_toWorkspaceConfig_425_; lean_object* v_toLeanConfig_426_; uint8_t v_bootstrap_427_; lean_object* v_extraDepTargets_428_; uint8_t v_precompileModules_429_; lean_object* v_srcDir_430_; lean_object* v_buildDir_431_; lean_object* v_leanLibDir_432_; lean_object* v_nativeLibDir_433_; lean_object* v_binDir_434_; lean_object* v_irDir_435_; lean_object* v_releaseRepo_436_; lean_object* v_buildArchive_437_; uint8_t v_preferReleaseBuild_438_; lean_object* v_testDriver_439_; lean_object* v_testDriverArgs_440_; lean_object* v_lintDriver_441_; lean_object* v_lintDriverArgs_442_; lean_object* v_version_443_; lean_object* v_versionTags_444_; lean_object* v_description_445_; lean_object* v_keywords_446_; lean_object* v_homepage_447_; lean_object* v_license_448_; lean_object* v_licenseFiles_449_; lean_object* v_readmeFile_450_; uint8_t v_reservoir_451_; lean_object* v_enableArtifactCache_x3f_452_; lean_object* v_restoreAllArtifacts_x3f_453_; uint8_t v_libPrefixOnWindows_454_; uint8_t v_allowImportAll_455_; lean_object* v_builtinLint_x3f_456_; lean_object* v_checks_457_; uint8_t v_fixedToolchain_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_toWorkspaceConfig_425_ = lean_ctor_get(v_cfg_424_, 0);
v_toLeanConfig_426_ = lean_ctor_get(v_cfg_424_, 1);
v_bootstrap_427_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28);
v_extraDepTargets_428_ = lean_ctor_get(v_cfg_424_, 2);
v_precompileModules_429_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28 + 1);
v_srcDir_430_ = lean_ctor_get(v_cfg_424_, 4);
v_buildDir_431_ = lean_ctor_get(v_cfg_424_, 5);
v_leanLibDir_432_ = lean_ctor_get(v_cfg_424_, 6);
v_nativeLibDir_433_ = lean_ctor_get(v_cfg_424_, 7);
v_binDir_434_ = lean_ctor_get(v_cfg_424_, 8);
v_irDir_435_ = lean_ctor_get(v_cfg_424_, 9);
v_releaseRepo_436_ = lean_ctor_get(v_cfg_424_, 10);
v_buildArchive_437_ = lean_ctor_get(v_cfg_424_, 11);
v_preferReleaseBuild_438_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28 + 2);
v_testDriver_439_ = lean_ctor_get(v_cfg_424_, 12);
v_testDriverArgs_440_ = lean_ctor_get(v_cfg_424_, 13);
v_lintDriver_441_ = lean_ctor_get(v_cfg_424_, 14);
v_lintDriverArgs_442_ = lean_ctor_get(v_cfg_424_, 15);
v_version_443_ = lean_ctor_get(v_cfg_424_, 16);
v_versionTags_444_ = lean_ctor_get(v_cfg_424_, 17);
v_description_445_ = lean_ctor_get(v_cfg_424_, 18);
v_keywords_446_ = lean_ctor_get(v_cfg_424_, 19);
v_homepage_447_ = lean_ctor_get(v_cfg_424_, 20);
v_license_448_ = lean_ctor_get(v_cfg_424_, 21);
v_licenseFiles_449_ = lean_ctor_get(v_cfg_424_, 22);
v_readmeFile_450_ = lean_ctor_get(v_cfg_424_, 23);
v_reservoir_451_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_452_ = lean_ctor_get(v_cfg_424_, 24);
v_restoreAllArtifacts_x3f_453_ = lean_ctor_get(v_cfg_424_, 25);
v_libPrefixOnWindows_454_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28 + 4);
v_allowImportAll_455_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_456_ = lean_ctor_get(v_cfg_424_, 26);
v_checks_457_ = lean_ctor_get(v_cfg_424_, 27);
v_fixedToolchain_458_ = lean_ctor_get_uint8(v_cfg_424_, sizeof(void*)*28 + 6);
v_isSharedCheck_465_ = !lean_is_exclusive(v_cfg_424_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_cfg_424_, 3);
lean_dec(v_unused_466_);
v___x_460_ = v_cfg_424_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_checks_457_);
lean_inc(v_builtinLint_x3f_456_);
lean_inc(v_restoreAllArtifacts_x3f_453_);
lean_inc(v_enableArtifactCache_x3f_452_);
lean_inc(v_readmeFile_450_);
lean_inc(v_licenseFiles_449_);
lean_inc(v_license_448_);
lean_inc(v_homepage_447_);
lean_inc(v_keywords_446_);
lean_inc(v_description_445_);
lean_inc(v_versionTags_444_);
lean_inc(v_version_443_);
lean_inc(v_lintDriverArgs_442_);
lean_inc(v_lintDriver_441_);
lean_inc(v_testDriverArgs_440_);
lean_inc(v_testDriver_439_);
lean_inc(v_buildArchive_437_);
lean_inc(v_releaseRepo_436_);
lean_inc(v_irDir_435_);
lean_inc(v_binDir_434_);
lean_inc(v_nativeLibDir_433_);
lean_inc(v_leanLibDir_432_);
lean_inc(v_buildDir_431_);
lean_inc(v_srcDir_430_);
lean_inc(v_extraDepTargets_428_);
lean_inc(v_toLeanConfig_426_);
lean_inc(v_toWorkspaceConfig_425_);
lean_dec(v_cfg_424_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 3, v_val_423_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_toWorkspaceConfig_425_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_toLeanConfig_426_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_extraDepTargets_428_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_val_423_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_srcDir_430_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_buildDir_431_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_leanLibDir_432_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_nativeLibDir_433_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v_binDir_434_);
lean_ctor_set(v_reuseFailAlloc_464_, 9, v_irDir_435_);
lean_ctor_set(v_reuseFailAlloc_464_, 10, v_releaseRepo_436_);
lean_ctor_set(v_reuseFailAlloc_464_, 11, v_buildArchive_437_);
lean_ctor_set(v_reuseFailAlloc_464_, 12, v_testDriver_439_);
lean_ctor_set(v_reuseFailAlloc_464_, 13, v_testDriverArgs_440_);
lean_ctor_set(v_reuseFailAlloc_464_, 14, v_lintDriver_441_);
lean_ctor_set(v_reuseFailAlloc_464_, 15, v_lintDriverArgs_442_);
lean_ctor_set(v_reuseFailAlloc_464_, 16, v_version_443_);
lean_ctor_set(v_reuseFailAlloc_464_, 17, v_versionTags_444_);
lean_ctor_set(v_reuseFailAlloc_464_, 18, v_description_445_);
lean_ctor_set(v_reuseFailAlloc_464_, 19, v_keywords_446_);
lean_ctor_set(v_reuseFailAlloc_464_, 20, v_homepage_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 21, v_license_448_);
lean_ctor_set(v_reuseFailAlloc_464_, 22, v_licenseFiles_449_);
lean_ctor_set(v_reuseFailAlloc_464_, 23, v_readmeFile_450_);
lean_ctor_set(v_reuseFailAlloc_464_, 24, v_enableArtifactCache_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 25, v_restoreAllArtifacts_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 26, v_builtinLint_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_464_, 27, v_checks_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28, v_bootstrap_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28 + 1, v_precompileModules_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28 + 2, v_preferReleaseBuild_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28 + 3, v_reservoir_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28 + 5, v_allowImportAll_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*28 + 6, v_fixedToolchain_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__2(lean_object* v_f_467_, lean_object* v_cfg_468_){
_start:
{
lean_object* v_toWorkspaceConfig_469_; lean_object* v_toLeanConfig_470_; uint8_t v_bootstrap_471_; lean_object* v_extraDepTargets_472_; uint8_t v_precompileModules_473_; lean_object* v_moreGlobalServerArgs_474_; lean_object* v_srcDir_475_; lean_object* v_buildDir_476_; lean_object* v_leanLibDir_477_; lean_object* v_nativeLibDir_478_; lean_object* v_binDir_479_; lean_object* v_irDir_480_; lean_object* v_releaseRepo_481_; lean_object* v_buildArchive_482_; uint8_t v_preferReleaseBuild_483_; lean_object* v_testDriver_484_; lean_object* v_testDriverArgs_485_; lean_object* v_lintDriver_486_; lean_object* v_lintDriverArgs_487_; lean_object* v_version_488_; lean_object* v_versionTags_489_; lean_object* v_description_490_; lean_object* v_keywords_491_; lean_object* v_homepage_492_; lean_object* v_license_493_; lean_object* v_licenseFiles_494_; lean_object* v_readmeFile_495_; uint8_t v_reservoir_496_; lean_object* v_enableArtifactCache_x3f_497_; lean_object* v_restoreAllArtifacts_x3f_498_; uint8_t v_libPrefixOnWindows_499_; uint8_t v_allowImportAll_500_; lean_object* v_builtinLint_x3f_501_; lean_object* v_checks_502_; uint8_t v_fixedToolchain_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_toWorkspaceConfig_469_ = lean_ctor_get(v_cfg_468_, 0);
v_toLeanConfig_470_ = lean_ctor_get(v_cfg_468_, 1);
v_bootstrap_471_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28);
v_extraDepTargets_472_ = lean_ctor_get(v_cfg_468_, 2);
v_precompileModules_473_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_474_ = lean_ctor_get(v_cfg_468_, 3);
v_srcDir_475_ = lean_ctor_get(v_cfg_468_, 4);
v_buildDir_476_ = lean_ctor_get(v_cfg_468_, 5);
v_leanLibDir_477_ = lean_ctor_get(v_cfg_468_, 6);
v_nativeLibDir_478_ = lean_ctor_get(v_cfg_468_, 7);
v_binDir_479_ = lean_ctor_get(v_cfg_468_, 8);
v_irDir_480_ = lean_ctor_get(v_cfg_468_, 9);
v_releaseRepo_481_ = lean_ctor_get(v_cfg_468_, 10);
v_buildArchive_482_ = lean_ctor_get(v_cfg_468_, 11);
v_preferReleaseBuild_483_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28 + 2);
v_testDriver_484_ = lean_ctor_get(v_cfg_468_, 12);
v_testDriverArgs_485_ = lean_ctor_get(v_cfg_468_, 13);
v_lintDriver_486_ = lean_ctor_get(v_cfg_468_, 14);
v_lintDriverArgs_487_ = lean_ctor_get(v_cfg_468_, 15);
v_version_488_ = lean_ctor_get(v_cfg_468_, 16);
v_versionTags_489_ = lean_ctor_get(v_cfg_468_, 17);
v_description_490_ = lean_ctor_get(v_cfg_468_, 18);
v_keywords_491_ = lean_ctor_get(v_cfg_468_, 19);
v_homepage_492_ = lean_ctor_get(v_cfg_468_, 20);
v_license_493_ = lean_ctor_get(v_cfg_468_, 21);
v_licenseFiles_494_ = lean_ctor_get(v_cfg_468_, 22);
v_readmeFile_495_ = lean_ctor_get(v_cfg_468_, 23);
v_reservoir_496_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_497_ = lean_ctor_get(v_cfg_468_, 24);
v_restoreAllArtifacts_x3f_498_ = lean_ctor_get(v_cfg_468_, 25);
v_libPrefixOnWindows_499_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28 + 4);
v_allowImportAll_500_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_501_ = lean_ctor_get(v_cfg_468_, 26);
v_checks_502_ = lean_ctor_get(v_cfg_468_, 27);
v_fixedToolchain_503_ = lean_ctor_get_uint8(v_cfg_468_, sizeof(void*)*28 + 6);
v_isSharedCheck_511_ = !lean_is_exclusive(v_cfg_468_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_cfg_468_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_checks_502_);
lean_inc(v_builtinLint_x3f_501_);
lean_inc(v_restoreAllArtifacts_x3f_498_);
lean_inc(v_enableArtifactCache_x3f_497_);
lean_inc(v_readmeFile_495_);
lean_inc(v_licenseFiles_494_);
lean_inc(v_license_493_);
lean_inc(v_homepage_492_);
lean_inc(v_keywords_491_);
lean_inc(v_description_490_);
lean_inc(v_versionTags_489_);
lean_inc(v_version_488_);
lean_inc(v_lintDriverArgs_487_);
lean_inc(v_lintDriver_486_);
lean_inc(v_testDriverArgs_485_);
lean_inc(v_testDriver_484_);
lean_inc(v_buildArchive_482_);
lean_inc(v_releaseRepo_481_);
lean_inc(v_irDir_480_);
lean_inc(v_binDir_479_);
lean_inc(v_nativeLibDir_478_);
lean_inc(v_leanLibDir_477_);
lean_inc(v_buildDir_476_);
lean_inc(v_srcDir_475_);
lean_inc(v_moreGlobalServerArgs_474_);
lean_inc(v_extraDepTargets_472_);
lean_inc(v_toLeanConfig_470_);
lean_inc(v_toWorkspaceConfig_469_);
lean_dec(v_cfg_468_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_apply_1(v_f_467_, v_moreGlobalServerArgs_474_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 3, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_toWorkspaceConfig_469_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_toLeanConfig_470_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_extraDepTargets_472_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_srcDir_475_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v_buildDir_476_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_leanLibDir_477_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v_nativeLibDir_478_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_binDir_479_);
lean_ctor_set(v_reuseFailAlloc_510_, 9, v_irDir_480_);
lean_ctor_set(v_reuseFailAlloc_510_, 10, v_releaseRepo_481_);
lean_ctor_set(v_reuseFailAlloc_510_, 11, v_buildArchive_482_);
lean_ctor_set(v_reuseFailAlloc_510_, 12, v_testDriver_484_);
lean_ctor_set(v_reuseFailAlloc_510_, 13, v_testDriverArgs_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 14, v_lintDriver_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 15, v_lintDriverArgs_487_);
lean_ctor_set(v_reuseFailAlloc_510_, 16, v_version_488_);
lean_ctor_set(v_reuseFailAlloc_510_, 17, v_versionTags_489_);
lean_ctor_set(v_reuseFailAlloc_510_, 18, v_description_490_);
lean_ctor_set(v_reuseFailAlloc_510_, 19, v_keywords_491_);
lean_ctor_set(v_reuseFailAlloc_510_, 20, v_homepage_492_);
lean_ctor_set(v_reuseFailAlloc_510_, 21, v_license_493_);
lean_ctor_set(v_reuseFailAlloc_510_, 22, v_licenseFiles_494_);
lean_ctor_set(v_reuseFailAlloc_510_, 23, v_readmeFile_495_);
lean_ctor_set(v_reuseFailAlloc_510_, 24, v_enableArtifactCache_x3f_497_);
lean_ctor_set(v_reuseFailAlloc_510_, 25, v_restoreAllArtifacts_x3f_498_);
lean_ctor_set(v_reuseFailAlloc_510_, 26, v_builtinLint_x3f_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 27, v_checks_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28, v_bootstrap_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28 + 1, v_precompileModules_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28 + 2, v_preferReleaseBuild_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28 + 3, v_reservoir_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28 + 5, v_allowImportAll_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_510_, sizeof(void*)*28 + 6, v_fixedToolchain_503_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___closed__0));
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3___boxed(lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___lam__3(v_x_516_);
lean_dec_ref(v_x_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_527_, lean_object* v_n_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__4));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_530_, lean_object* v_n_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_530_, v_n_531_);
lean_dec(v_n_531_);
lean_dec(v_p_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_533_, lean_object* v_n_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_533_, v_n_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_536_, lean_object* v_n_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_536_, v_n_537_);
lean_dec(v_n_537_);
lean_dec(v_p_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_539_, lean_object* v_n_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_539_, v_n_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_542_, lean_object* v_n_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_542_, v_n_543_);
lean_dec(v_n_543_);
lean_dec(v_p_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0(lean_object* v_cfg_545_){
_start:
{
lean_object* v_srcDir_546_; 
v_srcDir_546_ = lean_ctor_get(v_cfg_545_, 4);
lean_inc_ref(v_srcDir_546_);
return v_srcDir_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__0___boxed(lean_object* v_cfg_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lake_PackageConfig_srcDir___proj___lam__0(v_cfg_547_);
lean_dec_ref(v_cfg_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__1(lean_object* v_val_549_, lean_object* v_cfg_550_){
_start:
{
lean_object* v_toWorkspaceConfig_551_; lean_object* v_toLeanConfig_552_; uint8_t v_bootstrap_553_; lean_object* v_extraDepTargets_554_; uint8_t v_precompileModules_555_; lean_object* v_moreGlobalServerArgs_556_; lean_object* v_buildDir_557_; lean_object* v_leanLibDir_558_; lean_object* v_nativeLibDir_559_; lean_object* v_binDir_560_; lean_object* v_irDir_561_; lean_object* v_releaseRepo_562_; lean_object* v_buildArchive_563_; uint8_t v_preferReleaseBuild_564_; lean_object* v_testDriver_565_; lean_object* v_testDriverArgs_566_; lean_object* v_lintDriver_567_; lean_object* v_lintDriverArgs_568_; lean_object* v_version_569_; lean_object* v_versionTags_570_; lean_object* v_description_571_; lean_object* v_keywords_572_; lean_object* v_homepage_573_; lean_object* v_license_574_; lean_object* v_licenseFiles_575_; lean_object* v_readmeFile_576_; uint8_t v_reservoir_577_; lean_object* v_enableArtifactCache_x3f_578_; lean_object* v_restoreAllArtifacts_x3f_579_; uint8_t v_libPrefixOnWindows_580_; uint8_t v_allowImportAll_581_; lean_object* v_builtinLint_x3f_582_; lean_object* v_checks_583_; uint8_t v_fixedToolchain_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_toWorkspaceConfig_551_ = lean_ctor_get(v_cfg_550_, 0);
v_toLeanConfig_552_ = lean_ctor_get(v_cfg_550_, 1);
v_bootstrap_553_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28);
v_extraDepTargets_554_ = lean_ctor_get(v_cfg_550_, 2);
v_precompileModules_555_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_556_ = lean_ctor_get(v_cfg_550_, 3);
v_buildDir_557_ = lean_ctor_get(v_cfg_550_, 5);
v_leanLibDir_558_ = lean_ctor_get(v_cfg_550_, 6);
v_nativeLibDir_559_ = lean_ctor_get(v_cfg_550_, 7);
v_binDir_560_ = lean_ctor_get(v_cfg_550_, 8);
v_irDir_561_ = lean_ctor_get(v_cfg_550_, 9);
v_releaseRepo_562_ = lean_ctor_get(v_cfg_550_, 10);
v_buildArchive_563_ = lean_ctor_get(v_cfg_550_, 11);
v_preferReleaseBuild_564_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28 + 2);
v_testDriver_565_ = lean_ctor_get(v_cfg_550_, 12);
v_testDriverArgs_566_ = lean_ctor_get(v_cfg_550_, 13);
v_lintDriver_567_ = lean_ctor_get(v_cfg_550_, 14);
v_lintDriverArgs_568_ = lean_ctor_get(v_cfg_550_, 15);
v_version_569_ = lean_ctor_get(v_cfg_550_, 16);
v_versionTags_570_ = lean_ctor_get(v_cfg_550_, 17);
v_description_571_ = lean_ctor_get(v_cfg_550_, 18);
v_keywords_572_ = lean_ctor_get(v_cfg_550_, 19);
v_homepage_573_ = lean_ctor_get(v_cfg_550_, 20);
v_license_574_ = lean_ctor_get(v_cfg_550_, 21);
v_licenseFiles_575_ = lean_ctor_get(v_cfg_550_, 22);
v_readmeFile_576_ = lean_ctor_get(v_cfg_550_, 23);
v_reservoir_577_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_578_ = lean_ctor_get(v_cfg_550_, 24);
v_restoreAllArtifacts_x3f_579_ = lean_ctor_get(v_cfg_550_, 25);
v_libPrefixOnWindows_580_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28 + 4);
v_allowImportAll_581_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_582_ = lean_ctor_get(v_cfg_550_, 26);
v_checks_583_ = lean_ctor_get(v_cfg_550_, 27);
v_fixedToolchain_584_ = lean_ctor_get_uint8(v_cfg_550_, sizeof(void*)*28 + 6);
v_isSharedCheck_591_ = !lean_is_exclusive(v_cfg_550_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_cfg_550_, 4);
lean_dec(v_unused_592_);
v___x_586_ = v_cfg_550_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_checks_583_);
lean_inc(v_builtinLint_x3f_582_);
lean_inc(v_restoreAllArtifacts_x3f_579_);
lean_inc(v_enableArtifactCache_x3f_578_);
lean_inc(v_readmeFile_576_);
lean_inc(v_licenseFiles_575_);
lean_inc(v_license_574_);
lean_inc(v_homepage_573_);
lean_inc(v_keywords_572_);
lean_inc(v_description_571_);
lean_inc(v_versionTags_570_);
lean_inc(v_version_569_);
lean_inc(v_lintDriverArgs_568_);
lean_inc(v_lintDriver_567_);
lean_inc(v_testDriverArgs_566_);
lean_inc(v_testDriver_565_);
lean_inc(v_buildArchive_563_);
lean_inc(v_releaseRepo_562_);
lean_inc(v_irDir_561_);
lean_inc(v_binDir_560_);
lean_inc(v_nativeLibDir_559_);
lean_inc(v_leanLibDir_558_);
lean_inc(v_buildDir_557_);
lean_inc(v_moreGlobalServerArgs_556_);
lean_inc(v_extraDepTargets_554_);
lean_inc(v_toLeanConfig_552_);
lean_inc(v_toWorkspaceConfig_551_);
lean_dec(v_cfg_550_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 4, v_val_549_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_toWorkspaceConfig_551_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_toLeanConfig_552_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_extraDepTargets_554_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_moreGlobalServerArgs_556_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_val_549_);
lean_ctor_set(v_reuseFailAlloc_590_, 5, v_buildDir_557_);
lean_ctor_set(v_reuseFailAlloc_590_, 6, v_leanLibDir_558_);
lean_ctor_set(v_reuseFailAlloc_590_, 7, v_nativeLibDir_559_);
lean_ctor_set(v_reuseFailAlloc_590_, 8, v_binDir_560_);
lean_ctor_set(v_reuseFailAlloc_590_, 9, v_irDir_561_);
lean_ctor_set(v_reuseFailAlloc_590_, 10, v_releaseRepo_562_);
lean_ctor_set(v_reuseFailAlloc_590_, 11, v_buildArchive_563_);
lean_ctor_set(v_reuseFailAlloc_590_, 12, v_testDriver_565_);
lean_ctor_set(v_reuseFailAlloc_590_, 13, v_testDriverArgs_566_);
lean_ctor_set(v_reuseFailAlloc_590_, 14, v_lintDriver_567_);
lean_ctor_set(v_reuseFailAlloc_590_, 15, v_lintDriverArgs_568_);
lean_ctor_set(v_reuseFailAlloc_590_, 16, v_version_569_);
lean_ctor_set(v_reuseFailAlloc_590_, 17, v_versionTags_570_);
lean_ctor_set(v_reuseFailAlloc_590_, 18, v_description_571_);
lean_ctor_set(v_reuseFailAlloc_590_, 19, v_keywords_572_);
lean_ctor_set(v_reuseFailAlloc_590_, 20, v_homepage_573_);
lean_ctor_set(v_reuseFailAlloc_590_, 21, v_license_574_);
lean_ctor_set(v_reuseFailAlloc_590_, 22, v_licenseFiles_575_);
lean_ctor_set(v_reuseFailAlloc_590_, 23, v_readmeFile_576_);
lean_ctor_set(v_reuseFailAlloc_590_, 24, v_enableArtifactCache_x3f_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 25, v_restoreAllArtifacts_x3f_579_);
lean_ctor_set(v_reuseFailAlloc_590_, 26, v_builtinLint_x3f_582_);
lean_ctor_set(v_reuseFailAlloc_590_, 27, v_checks_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28, v_bootstrap_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28 + 1, v_precompileModules_555_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28 + 2, v_preferReleaseBuild_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28 + 3, v_reservoir_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28 + 5, v_allowImportAll_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*28 + 6, v_fixedToolchain_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__2(lean_object* v_f_593_, lean_object* v_cfg_594_){
_start:
{
lean_object* v_toWorkspaceConfig_595_; lean_object* v_toLeanConfig_596_; uint8_t v_bootstrap_597_; lean_object* v_extraDepTargets_598_; uint8_t v_precompileModules_599_; lean_object* v_moreGlobalServerArgs_600_; lean_object* v_srcDir_601_; lean_object* v_buildDir_602_; lean_object* v_leanLibDir_603_; lean_object* v_nativeLibDir_604_; lean_object* v_binDir_605_; lean_object* v_irDir_606_; lean_object* v_releaseRepo_607_; lean_object* v_buildArchive_608_; uint8_t v_preferReleaseBuild_609_; lean_object* v_testDriver_610_; lean_object* v_testDriverArgs_611_; lean_object* v_lintDriver_612_; lean_object* v_lintDriverArgs_613_; lean_object* v_version_614_; lean_object* v_versionTags_615_; lean_object* v_description_616_; lean_object* v_keywords_617_; lean_object* v_homepage_618_; lean_object* v_license_619_; lean_object* v_licenseFiles_620_; lean_object* v_readmeFile_621_; uint8_t v_reservoir_622_; lean_object* v_enableArtifactCache_x3f_623_; lean_object* v_restoreAllArtifacts_x3f_624_; uint8_t v_libPrefixOnWindows_625_; uint8_t v_allowImportAll_626_; lean_object* v_builtinLint_x3f_627_; lean_object* v_checks_628_; uint8_t v_fixedToolchain_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_toWorkspaceConfig_595_ = lean_ctor_get(v_cfg_594_, 0);
v_toLeanConfig_596_ = lean_ctor_get(v_cfg_594_, 1);
v_bootstrap_597_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28);
v_extraDepTargets_598_ = lean_ctor_get(v_cfg_594_, 2);
v_precompileModules_599_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_600_ = lean_ctor_get(v_cfg_594_, 3);
v_srcDir_601_ = lean_ctor_get(v_cfg_594_, 4);
v_buildDir_602_ = lean_ctor_get(v_cfg_594_, 5);
v_leanLibDir_603_ = lean_ctor_get(v_cfg_594_, 6);
v_nativeLibDir_604_ = lean_ctor_get(v_cfg_594_, 7);
v_binDir_605_ = lean_ctor_get(v_cfg_594_, 8);
v_irDir_606_ = lean_ctor_get(v_cfg_594_, 9);
v_releaseRepo_607_ = lean_ctor_get(v_cfg_594_, 10);
v_buildArchive_608_ = lean_ctor_get(v_cfg_594_, 11);
v_preferReleaseBuild_609_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28 + 2);
v_testDriver_610_ = lean_ctor_get(v_cfg_594_, 12);
v_testDriverArgs_611_ = lean_ctor_get(v_cfg_594_, 13);
v_lintDriver_612_ = lean_ctor_get(v_cfg_594_, 14);
v_lintDriverArgs_613_ = lean_ctor_get(v_cfg_594_, 15);
v_version_614_ = lean_ctor_get(v_cfg_594_, 16);
v_versionTags_615_ = lean_ctor_get(v_cfg_594_, 17);
v_description_616_ = lean_ctor_get(v_cfg_594_, 18);
v_keywords_617_ = lean_ctor_get(v_cfg_594_, 19);
v_homepage_618_ = lean_ctor_get(v_cfg_594_, 20);
v_license_619_ = lean_ctor_get(v_cfg_594_, 21);
v_licenseFiles_620_ = lean_ctor_get(v_cfg_594_, 22);
v_readmeFile_621_ = lean_ctor_get(v_cfg_594_, 23);
v_reservoir_622_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_623_ = lean_ctor_get(v_cfg_594_, 24);
v_restoreAllArtifacts_x3f_624_ = lean_ctor_get(v_cfg_594_, 25);
v_libPrefixOnWindows_625_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28 + 4);
v_allowImportAll_626_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_627_ = lean_ctor_get(v_cfg_594_, 26);
v_checks_628_ = lean_ctor_get(v_cfg_594_, 27);
v_fixedToolchain_629_ = lean_ctor_get_uint8(v_cfg_594_, sizeof(void*)*28 + 6);
v_isSharedCheck_637_ = !lean_is_exclusive(v_cfg_594_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v_cfg_594_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_checks_628_);
lean_inc(v_builtinLint_x3f_627_);
lean_inc(v_restoreAllArtifacts_x3f_624_);
lean_inc(v_enableArtifactCache_x3f_623_);
lean_inc(v_readmeFile_621_);
lean_inc(v_licenseFiles_620_);
lean_inc(v_license_619_);
lean_inc(v_homepage_618_);
lean_inc(v_keywords_617_);
lean_inc(v_description_616_);
lean_inc(v_versionTags_615_);
lean_inc(v_version_614_);
lean_inc(v_lintDriverArgs_613_);
lean_inc(v_lintDriver_612_);
lean_inc(v_testDriverArgs_611_);
lean_inc(v_testDriver_610_);
lean_inc(v_buildArchive_608_);
lean_inc(v_releaseRepo_607_);
lean_inc(v_irDir_606_);
lean_inc(v_binDir_605_);
lean_inc(v_nativeLibDir_604_);
lean_inc(v_leanLibDir_603_);
lean_inc(v_buildDir_602_);
lean_inc(v_srcDir_601_);
lean_inc(v_moreGlobalServerArgs_600_);
lean_inc(v_extraDepTargets_598_);
lean_inc(v_toLeanConfig_596_);
lean_inc(v_toWorkspaceConfig_595_);
lean_dec(v_cfg_594_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_apply_1(v_f_593_, v_srcDir_601_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 4, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_toWorkspaceConfig_595_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_toLeanConfig_596_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_extraDepTargets_598_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_moreGlobalServerArgs_600_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_buildDir_602_);
lean_ctor_set(v_reuseFailAlloc_636_, 6, v_leanLibDir_603_);
lean_ctor_set(v_reuseFailAlloc_636_, 7, v_nativeLibDir_604_);
lean_ctor_set(v_reuseFailAlloc_636_, 8, v_binDir_605_);
lean_ctor_set(v_reuseFailAlloc_636_, 9, v_irDir_606_);
lean_ctor_set(v_reuseFailAlloc_636_, 10, v_releaseRepo_607_);
lean_ctor_set(v_reuseFailAlloc_636_, 11, v_buildArchive_608_);
lean_ctor_set(v_reuseFailAlloc_636_, 12, v_testDriver_610_);
lean_ctor_set(v_reuseFailAlloc_636_, 13, v_testDriverArgs_611_);
lean_ctor_set(v_reuseFailAlloc_636_, 14, v_lintDriver_612_);
lean_ctor_set(v_reuseFailAlloc_636_, 15, v_lintDriverArgs_613_);
lean_ctor_set(v_reuseFailAlloc_636_, 16, v_version_614_);
lean_ctor_set(v_reuseFailAlloc_636_, 17, v_versionTags_615_);
lean_ctor_set(v_reuseFailAlloc_636_, 18, v_description_616_);
lean_ctor_set(v_reuseFailAlloc_636_, 19, v_keywords_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 20, v_homepage_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 21, v_license_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 22, v_licenseFiles_620_);
lean_ctor_set(v_reuseFailAlloc_636_, 23, v_readmeFile_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 24, v_enableArtifactCache_x3f_623_);
lean_ctor_set(v_reuseFailAlloc_636_, 25, v_restoreAllArtifacts_x3f_624_);
lean_ctor_set(v_reuseFailAlloc_636_, 26, v_builtinLint_x3f_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 27, v_checks_628_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28, v_bootstrap_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28 + 1, v_precompileModules_599_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28 + 2, v_preferReleaseBuild_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28 + 3, v_reservoir_622_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28 + 5, v_allowImportAll_626_);
lean_ctor_set_uint8(v_reuseFailAlloc_636_, sizeof(void*)*28 + 6, v_fixedToolchain_629_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3(lean_object* v_x_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___lam__3___boxed(lean_object* v_x_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lake_PackageConfig_srcDir___proj___lam__3(v_x_640_);
lean_dec_ref(v_x_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_651_, lean_object* v_n_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___closed__4));
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_654_, lean_object* v_n_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lake_PackageConfig_srcDir___proj(v_p_654_, v_n_655_);
lean_dec(v_n_655_);
lean_dec(v_p_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_657_, lean_object* v_n_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lake_PackageConfig_srcDir___proj(v_p_657_, v_n_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_660_, lean_object* v_n_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_660_, v_n_661_);
lean_dec(v_n_661_);
lean_dec(v_p_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0(lean_object* v_cfg_663_){
_start:
{
lean_object* v_buildDir_664_; 
v_buildDir_664_ = lean_ctor_get(v_cfg_663_, 5);
lean_inc_ref(v_buildDir_664_);
return v_buildDir_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__0___boxed(lean_object* v_cfg_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_PackageConfig_buildDir___proj___lam__0(v_cfg_665_);
lean_dec_ref(v_cfg_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__1(lean_object* v_val_667_, lean_object* v_cfg_668_){
_start:
{
lean_object* v_toWorkspaceConfig_669_; lean_object* v_toLeanConfig_670_; uint8_t v_bootstrap_671_; lean_object* v_extraDepTargets_672_; uint8_t v_precompileModules_673_; lean_object* v_moreGlobalServerArgs_674_; lean_object* v_srcDir_675_; lean_object* v_leanLibDir_676_; lean_object* v_nativeLibDir_677_; lean_object* v_binDir_678_; lean_object* v_irDir_679_; lean_object* v_releaseRepo_680_; lean_object* v_buildArchive_681_; uint8_t v_preferReleaseBuild_682_; lean_object* v_testDriver_683_; lean_object* v_testDriverArgs_684_; lean_object* v_lintDriver_685_; lean_object* v_lintDriverArgs_686_; lean_object* v_version_687_; lean_object* v_versionTags_688_; lean_object* v_description_689_; lean_object* v_keywords_690_; lean_object* v_homepage_691_; lean_object* v_license_692_; lean_object* v_licenseFiles_693_; lean_object* v_readmeFile_694_; uint8_t v_reservoir_695_; lean_object* v_enableArtifactCache_x3f_696_; lean_object* v_restoreAllArtifacts_x3f_697_; uint8_t v_libPrefixOnWindows_698_; uint8_t v_allowImportAll_699_; lean_object* v_builtinLint_x3f_700_; lean_object* v_checks_701_; uint8_t v_fixedToolchain_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_toWorkspaceConfig_669_ = lean_ctor_get(v_cfg_668_, 0);
v_toLeanConfig_670_ = lean_ctor_get(v_cfg_668_, 1);
v_bootstrap_671_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28);
v_extraDepTargets_672_ = lean_ctor_get(v_cfg_668_, 2);
v_precompileModules_673_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_674_ = lean_ctor_get(v_cfg_668_, 3);
v_srcDir_675_ = lean_ctor_get(v_cfg_668_, 4);
v_leanLibDir_676_ = lean_ctor_get(v_cfg_668_, 6);
v_nativeLibDir_677_ = lean_ctor_get(v_cfg_668_, 7);
v_binDir_678_ = lean_ctor_get(v_cfg_668_, 8);
v_irDir_679_ = lean_ctor_get(v_cfg_668_, 9);
v_releaseRepo_680_ = lean_ctor_get(v_cfg_668_, 10);
v_buildArchive_681_ = lean_ctor_get(v_cfg_668_, 11);
v_preferReleaseBuild_682_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28 + 2);
v_testDriver_683_ = lean_ctor_get(v_cfg_668_, 12);
v_testDriverArgs_684_ = lean_ctor_get(v_cfg_668_, 13);
v_lintDriver_685_ = lean_ctor_get(v_cfg_668_, 14);
v_lintDriverArgs_686_ = lean_ctor_get(v_cfg_668_, 15);
v_version_687_ = lean_ctor_get(v_cfg_668_, 16);
v_versionTags_688_ = lean_ctor_get(v_cfg_668_, 17);
v_description_689_ = lean_ctor_get(v_cfg_668_, 18);
v_keywords_690_ = lean_ctor_get(v_cfg_668_, 19);
v_homepage_691_ = lean_ctor_get(v_cfg_668_, 20);
v_license_692_ = lean_ctor_get(v_cfg_668_, 21);
v_licenseFiles_693_ = lean_ctor_get(v_cfg_668_, 22);
v_readmeFile_694_ = lean_ctor_get(v_cfg_668_, 23);
v_reservoir_695_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_696_ = lean_ctor_get(v_cfg_668_, 24);
v_restoreAllArtifacts_x3f_697_ = lean_ctor_get(v_cfg_668_, 25);
v_libPrefixOnWindows_698_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28 + 4);
v_allowImportAll_699_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_700_ = lean_ctor_get(v_cfg_668_, 26);
v_checks_701_ = lean_ctor_get(v_cfg_668_, 27);
v_fixedToolchain_702_ = lean_ctor_get_uint8(v_cfg_668_, sizeof(void*)*28 + 6);
v_isSharedCheck_709_ = !lean_is_exclusive(v_cfg_668_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_cfg_668_, 5);
lean_dec(v_unused_710_);
v___x_704_ = v_cfg_668_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_checks_701_);
lean_inc(v_builtinLint_x3f_700_);
lean_inc(v_restoreAllArtifacts_x3f_697_);
lean_inc(v_enableArtifactCache_x3f_696_);
lean_inc(v_readmeFile_694_);
lean_inc(v_licenseFiles_693_);
lean_inc(v_license_692_);
lean_inc(v_homepage_691_);
lean_inc(v_keywords_690_);
lean_inc(v_description_689_);
lean_inc(v_versionTags_688_);
lean_inc(v_version_687_);
lean_inc(v_lintDriverArgs_686_);
lean_inc(v_lintDriver_685_);
lean_inc(v_testDriverArgs_684_);
lean_inc(v_testDriver_683_);
lean_inc(v_buildArchive_681_);
lean_inc(v_releaseRepo_680_);
lean_inc(v_irDir_679_);
lean_inc(v_binDir_678_);
lean_inc(v_nativeLibDir_677_);
lean_inc(v_leanLibDir_676_);
lean_inc(v_srcDir_675_);
lean_inc(v_moreGlobalServerArgs_674_);
lean_inc(v_extraDepTargets_672_);
lean_inc(v_toLeanConfig_670_);
lean_inc(v_toWorkspaceConfig_669_);
lean_dec(v_cfg_668_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 5, v_val_667_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_toWorkspaceConfig_669_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_toLeanConfig_670_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_extraDepTargets_672_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_moreGlobalServerArgs_674_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_srcDir_675_);
lean_ctor_set(v_reuseFailAlloc_708_, 5, v_val_667_);
lean_ctor_set(v_reuseFailAlloc_708_, 6, v_leanLibDir_676_);
lean_ctor_set(v_reuseFailAlloc_708_, 7, v_nativeLibDir_677_);
lean_ctor_set(v_reuseFailAlloc_708_, 8, v_binDir_678_);
lean_ctor_set(v_reuseFailAlloc_708_, 9, v_irDir_679_);
lean_ctor_set(v_reuseFailAlloc_708_, 10, v_releaseRepo_680_);
lean_ctor_set(v_reuseFailAlloc_708_, 11, v_buildArchive_681_);
lean_ctor_set(v_reuseFailAlloc_708_, 12, v_testDriver_683_);
lean_ctor_set(v_reuseFailAlloc_708_, 13, v_testDriverArgs_684_);
lean_ctor_set(v_reuseFailAlloc_708_, 14, v_lintDriver_685_);
lean_ctor_set(v_reuseFailAlloc_708_, 15, v_lintDriverArgs_686_);
lean_ctor_set(v_reuseFailAlloc_708_, 16, v_version_687_);
lean_ctor_set(v_reuseFailAlloc_708_, 17, v_versionTags_688_);
lean_ctor_set(v_reuseFailAlloc_708_, 18, v_description_689_);
lean_ctor_set(v_reuseFailAlloc_708_, 19, v_keywords_690_);
lean_ctor_set(v_reuseFailAlloc_708_, 20, v_homepage_691_);
lean_ctor_set(v_reuseFailAlloc_708_, 21, v_license_692_);
lean_ctor_set(v_reuseFailAlloc_708_, 22, v_licenseFiles_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 23, v_readmeFile_694_);
lean_ctor_set(v_reuseFailAlloc_708_, 24, v_enableArtifactCache_x3f_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 25, v_restoreAllArtifacts_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 26, v_builtinLint_x3f_700_);
lean_ctor_set(v_reuseFailAlloc_708_, 27, v_checks_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28, v_bootstrap_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28 + 1, v_precompileModules_673_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28 + 2, v_preferReleaseBuild_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28 + 3, v_reservoir_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_698_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28 + 5, v_allowImportAll_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*28 + 6, v_fixedToolchain_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__2(lean_object* v_f_711_, lean_object* v_cfg_712_){
_start:
{
lean_object* v_toWorkspaceConfig_713_; lean_object* v_toLeanConfig_714_; uint8_t v_bootstrap_715_; lean_object* v_extraDepTargets_716_; uint8_t v_precompileModules_717_; lean_object* v_moreGlobalServerArgs_718_; lean_object* v_srcDir_719_; lean_object* v_buildDir_720_; lean_object* v_leanLibDir_721_; lean_object* v_nativeLibDir_722_; lean_object* v_binDir_723_; lean_object* v_irDir_724_; lean_object* v_releaseRepo_725_; lean_object* v_buildArchive_726_; uint8_t v_preferReleaseBuild_727_; lean_object* v_testDriver_728_; lean_object* v_testDriverArgs_729_; lean_object* v_lintDriver_730_; lean_object* v_lintDriverArgs_731_; lean_object* v_version_732_; lean_object* v_versionTags_733_; lean_object* v_description_734_; lean_object* v_keywords_735_; lean_object* v_homepage_736_; lean_object* v_license_737_; lean_object* v_licenseFiles_738_; lean_object* v_readmeFile_739_; uint8_t v_reservoir_740_; lean_object* v_enableArtifactCache_x3f_741_; lean_object* v_restoreAllArtifacts_x3f_742_; uint8_t v_libPrefixOnWindows_743_; uint8_t v_allowImportAll_744_; lean_object* v_builtinLint_x3f_745_; lean_object* v_checks_746_; uint8_t v_fixedToolchain_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_toWorkspaceConfig_713_ = lean_ctor_get(v_cfg_712_, 0);
v_toLeanConfig_714_ = lean_ctor_get(v_cfg_712_, 1);
v_bootstrap_715_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28);
v_extraDepTargets_716_ = lean_ctor_get(v_cfg_712_, 2);
v_precompileModules_717_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_718_ = lean_ctor_get(v_cfg_712_, 3);
v_srcDir_719_ = lean_ctor_get(v_cfg_712_, 4);
v_buildDir_720_ = lean_ctor_get(v_cfg_712_, 5);
v_leanLibDir_721_ = lean_ctor_get(v_cfg_712_, 6);
v_nativeLibDir_722_ = lean_ctor_get(v_cfg_712_, 7);
v_binDir_723_ = lean_ctor_get(v_cfg_712_, 8);
v_irDir_724_ = lean_ctor_get(v_cfg_712_, 9);
v_releaseRepo_725_ = lean_ctor_get(v_cfg_712_, 10);
v_buildArchive_726_ = lean_ctor_get(v_cfg_712_, 11);
v_preferReleaseBuild_727_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28 + 2);
v_testDriver_728_ = lean_ctor_get(v_cfg_712_, 12);
v_testDriverArgs_729_ = lean_ctor_get(v_cfg_712_, 13);
v_lintDriver_730_ = lean_ctor_get(v_cfg_712_, 14);
v_lintDriverArgs_731_ = lean_ctor_get(v_cfg_712_, 15);
v_version_732_ = lean_ctor_get(v_cfg_712_, 16);
v_versionTags_733_ = lean_ctor_get(v_cfg_712_, 17);
v_description_734_ = lean_ctor_get(v_cfg_712_, 18);
v_keywords_735_ = lean_ctor_get(v_cfg_712_, 19);
v_homepage_736_ = lean_ctor_get(v_cfg_712_, 20);
v_license_737_ = lean_ctor_get(v_cfg_712_, 21);
v_licenseFiles_738_ = lean_ctor_get(v_cfg_712_, 22);
v_readmeFile_739_ = lean_ctor_get(v_cfg_712_, 23);
v_reservoir_740_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_741_ = lean_ctor_get(v_cfg_712_, 24);
v_restoreAllArtifacts_x3f_742_ = lean_ctor_get(v_cfg_712_, 25);
v_libPrefixOnWindows_743_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28 + 4);
v_allowImportAll_744_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_745_ = lean_ctor_get(v_cfg_712_, 26);
v_checks_746_ = lean_ctor_get(v_cfg_712_, 27);
v_fixedToolchain_747_ = lean_ctor_get_uint8(v_cfg_712_, sizeof(void*)*28 + 6);
v_isSharedCheck_755_ = !lean_is_exclusive(v_cfg_712_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v_cfg_712_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_checks_746_);
lean_inc(v_builtinLint_x3f_745_);
lean_inc(v_restoreAllArtifacts_x3f_742_);
lean_inc(v_enableArtifactCache_x3f_741_);
lean_inc(v_readmeFile_739_);
lean_inc(v_licenseFiles_738_);
lean_inc(v_license_737_);
lean_inc(v_homepage_736_);
lean_inc(v_keywords_735_);
lean_inc(v_description_734_);
lean_inc(v_versionTags_733_);
lean_inc(v_version_732_);
lean_inc(v_lintDriverArgs_731_);
lean_inc(v_lintDriver_730_);
lean_inc(v_testDriverArgs_729_);
lean_inc(v_testDriver_728_);
lean_inc(v_buildArchive_726_);
lean_inc(v_releaseRepo_725_);
lean_inc(v_irDir_724_);
lean_inc(v_binDir_723_);
lean_inc(v_nativeLibDir_722_);
lean_inc(v_leanLibDir_721_);
lean_inc(v_buildDir_720_);
lean_inc(v_srcDir_719_);
lean_inc(v_moreGlobalServerArgs_718_);
lean_inc(v_extraDepTargets_716_);
lean_inc(v_toLeanConfig_714_);
lean_inc(v_toWorkspaceConfig_713_);
lean_dec(v_cfg_712_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_apply_1(v_f_711_, v_buildDir_720_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 5, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_toWorkspaceConfig_713_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_toLeanConfig_714_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_extraDepTargets_716_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_moreGlobalServerArgs_718_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_srcDir_719_);
lean_ctor_set(v_reuseFailAlloc_754_, 5, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 6, v_leanLibDir_721_);
lean_ctor_set(v_reuseFailAlloc_754_, 7, v_nativeLibDir_722_);
lean_ctor_set(v_reuseFailAlloc_754_, 8, v_binDir_723_);
lean_ctor_set(v_reuseFailAlloc_754_, 9, v_irDir_724_);
lean_ctor_set(v_reuseFailAlloc_754_, 10, v_releaseRepo_725_);
lean_ctor_set(v_reuseFailAlloc_754_, 11, v_buildArchive_726_);
lean_ctor_set(v_reuseFailAlloc_754_, 12, v_testDriver_728_);
lean_ctor_set(v_reuseFailAlloc_754_, 13, v_testDriverArgs_729_);
lean_ctor_set(v_reuseFailAlloc_754_, 14, v_lintDriver_730_);
lean_ctor_set(v_reuseFailAlloc_754_, 15, v_lintDriverArgs_731_);
lean_ctor_set(v_reuseFailAlloc_754_, 16, v_version_732_);
lean_ctor_set(v_reuseFailAlloc_754_, 17, v_versionTags_733_);
lean_ctor_set(v_reuseFailAlloc_754_, 18, v_description_734_);
lean_ctor_set(v_reuseFailAlloc_754_, 19, v_keywords_735_);
lean_ctor_set(v_reuseFailAlloc_754_, 20, v_homepage_736_);
lean_ctor_set(v_reuseFailAlloc_754_, 21, v_license_737_);
lean_ctor_set(v_reuseFailAlloc_754_, 22, v_licenseFiles_738_);
lean_ctor_set(v_reuseFailAlloc_754_, 23, v_readmeFile_739_);
lean_ctor_set(v_reuseFailAlloc_754_, 24, v_enableArtifactCache_x3f_741_);
lean_ctor_set(v_reuseFailAlloc_754_, 25, v_restoreAllArtifacts_x3f_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 26, v_builtinLint_x3f_745_);
lean_ctor_set(v_reuseFailAlloc_754_, 27, v_checks_746_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28, v_bootstrap_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28 + 1, v_precompileModules_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28 + 2, v_preferReleaseBuild_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28 + 3, v_reservoir_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28 + 5, v_allowImportAll_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*28 + 6, v_fixedToolchain_747_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3(lean_object* v_x_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lake_defaultBuildDir;
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___lam__3___boxed(lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lake_PackageConfig_buildDir___proj___lam__3(v_x_758_);
lean_dec_ref(v_x_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_769_, lean_object* v_n_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___closed__4));
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_772_, lean_object* v_n_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lake_PackageConfig_buildDir___proj(v_p_772_, v_n_773_);
lean_dec(v_n_773_);
lean_dec(v_p_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_775_, lean_object* v_n_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lake_PackageConfig_buildDir___proj(v_p_775_, v_n_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_778_, lean_object* v_n_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_778_, v_n_779_);
lean_dec(v_n_779_);
lean_dec(v_p_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0(lean_object* v_cfg_781_){
_start:
{
lean_object* v_leanLibDir_782_; 
v_leanLibDir_782_ = lean_ctor_get(v_cfg_781_, 6);
lean_inc_ref(v_leanLibDir_782_);
return v_leanLibDir_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__0___boxed(lean_object* v_cfg_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lake_PackageConfig_leanLibDir___proj___lam__0(v_cfg_783_);
lean_dec_ref(v_cfg_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__1(lean_object* v_val_785_, lean_object* v_cfg_786_){
_start:
{
lean_object* v_toWorkspaceConfig_787_; lean_object* v_toLeanConfig_788_; uint8_t v_bootstrap_789_; lean_object* v_extraDepTargets_790_; uint8_t v_precompileModules_791_; lean_object* v_moreGlobalServerArgs_792_; lean_object* v_srcDir_793_; lean_object* v_buildDir_794_; lean_object* v_nativeLibDir_795_; lean_object* v_binDir_796_; lean_object* v_irDir_797_; lean_object* v_releaseRepo_798_; lean_object* v_buildArchive_799_; uint8_t v_preferReleaseBuild_800_; lean_object* v_testDriver_801_; lean_object* v_testDriverArgs_802_; lean_object* v_lintDriver_803_; lean_object* v_lintDriverArgs_804_; lean_object* v_version_805_; lean_object* v_versionTags_806_; lean_object* v_description_807_; lean_object* v_keywords_808_; lean_object* v_homepage_809_; lean_object* v_license_810_; lean_object* v_licenseFiles_811_; lean_object* v_readmeFile_812_; uint8_t v_reservoir_813_; lean_object* v_enableArtifactCache_x3f_814_; lean_object* v_restoreAllArtifacts_x3f_815_; uint8_t v_libPrefixOnWindows_816_; uint8_t v_allowImportAll_817_; lean_object* v_builtinLint_x3f_818_; lean_object* v_checks_819_; uint8_t v_fixedToolchain_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_toWorkspaceConfig_787_ = lean_ctor_get(v_cfg_786_, 0);
v_toLeanConfig_788_ = lean_ctor_get(v_cfg_786_, 1);
v_bootstrap_789_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28);
v_extraDepTargets_790_ = lean_ctor_get(v_cfg_786_, 2);
v_precompileModules_791_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_792_ = lean_ctor_get(v_cfg_786_, 3);
v_srcDir_793_ = lean_ctor_get(v_cfg_786_, 4);
v_buildDir_794_ = lean_ctor_get(v_cfg_786_, 5);
v_nativeLibDir_795_ = lean_ctor_get(v_cfg_786_, 7);
v_binDir_796_ = lean_ctor_get(v_cfg_786_, 8);
v_irDir_797_ = lean_ctor_get(v_cfg_786_, 9);
v_releaseRepo_798_ = lean_ctor_get(v_cfg_786_, 10);
v_buildArchive_799_ = lean_ctor_get(v_cfg_786_, 11);
v_preferReleaseBuild_800_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28 + 2);
v_testDriver_801_ = lean_ctor_get(v_cfg_786_, 12);
v_testDriverArgs_802_ = lean_ctor_get(v_cfg_786_, 13);
v_lintDriver_803_ = lean_ctor_get(v_cfg_786_, 14);
v_lintDriverArgs_804_ = lean_ctor_get(v_cfg_786_, 15);
v_version_805_ = lean_ctor_get(v_cfg_786_, 16);
v_versionTags_806_ = lean_ctor_get(v_cfg_786_, 17);
v_description_807_ = lean_ctor_get(v_cfg_786_, 18);
v_keywords_808_ = lean_ctor_get(v_cfg_786_, 19);
v_homepage_809_ = lean_ctor_get(v_cfg_786_, 20);
v_license_810_ = lean_ctor_get(v_cfg_786_, 21);
v_licenseFiles_811_ = lean_ctor_get(v_cfg_786_, 22);
v_readmeFile_812_ = lean_ctor_get(v_cfg_786_, 23);
v_reservoir_813_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_814_ = lean_ctor_get(v_cfg_786_, 24);
v_restoreAllArtifacts_x3f_815_ = lean_ctor_get(v_cfg_786_, 25);
v_libPrefixOnWindows_816_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28 + 4);
v_allowImportAll_817_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_818_ = lean_ctor_get(v_cfg_786_, 26);
v_checks_819_ = lean_ctor_get(v_cfg_786_, 27);
v_fixedToolchain_820_ = lean_ctor_get_uint8(v_cfg_786_, sizeof(void*)*28 + 6);
v_isSharedCheck_827_ = !lean_is_exclusive(v_cfg_786_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_cfg_786_, 6);
lean_dec(v_unused_828_);
v___x_822_ = v_cfg_786_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_checks_819_);
lean_inc(v_builtinLint_x3f_818_);
lean_inc(v_restoreAllArtifacts_x3f_815_);
lean_inc(v_enableArtifactCache_x3f_814_);
lean_inc(v_readmeFile_812_);
lean_inc(v_licenseFiles_811_);
lean_inc(v_license_810_);
lean_inc(v_homepage_809_);
lean_inc(v_keywords_808_);
lean_inc(v_description_807_);
lean_inc(v_versionTags_806_);
lean_inc(v_version_805_);
lean_inc(v_lintDriverArgs_804_);
lean_inc(v_lintDriver_803_);
lean_inc(v_testDriverArgs_802_);
lean_inc(v_testDriver_801_);
lean_inc(v_buildArchive_799_);
lean_inc(v_releaseRepo_798_);
lean_inc(v_irDir_797_);
lean_inc(v_binDir_796_);
lean_inc(v_nativeLibDir_795_);
lean_inc(v_buildDir_794_);
lean_inc(v_srcDir_793_);
lean_inc(v_moreGlobalServerArgs_792_);
lean_inc(v_extraDepTargets_790_);
lean_inc(v_toLeanConfig_788_);
lean_inc(v_toWorkspaceConfig_787_);
lean_dec(v_cfg_786_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 6, v_val_785_);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_toWorkspaceConfig_787_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_toLeanConfig_788_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_extraDepTargets_790_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v_moreGlobalServerArgs_792_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_srcDir_793_);
lean_ctor_set(v_reuseFailAlloc_826_, 5, v_buildDir_794_);
lean_ctor_set(v_reuseFailAlloc_826_, 6, v_val_785_);
lean_ctor_set(v_reuseFailAlloc_826_, 7, v_nativeLibDir_795_);
lean_ctor_set(v_reuseFailAlloc_826_, 8, v_binDir_796_);
lean_ctor_set(v_reuseFailAlloc_826_, 9, v_irDir_797_);
lean_ctor_set(v_reuseFailAlloc_826_, 10, v_releaseRepo_798_);
lean_ctor_set(v_reuseFailAlloc_826_, 11, v_buildArchive_799_);
lean_ctor_set(v_reuseFailAlloc_826_, 12, v_testDriver_801_);
lean_ctor_set(v_reuseFailAlloc_826_, 13, v_testDriverArgs_802_);
lean_ctor_set(v_reuseFailAlloc_826_, 14, v_lintDriver_803_);
lean_ctor_set(v_reuseFailAlloc_826_, 15, v_lintDriverArgs_804_);
lean_ctor_set(v_reuseFailAlloc_826_, 16, v_version_805_);
lean_ctor_set(v_reuseFailAlloc_826_, 17, v_versionTags_806_);
lean_ctor_set(v_reuseFailAlloc_826_, 18, v_description_807_);
lean_ctor_set(v_reuseFailAlloc_826_, 19, v_keywords_808_);
lean_ctor_set(v_reuseFailAlloc_826_, 20, v_homepage_809_);
lean_ctor_set(v_reuseFailAlloc_826_, 21, v_license_810_);
lean_ctor_set(v_reuseFailAlloc_826_, 22, v_licenseFiles_811_);
lean_ctor_set(v_reuseFailAlloc_826_, 23, v_readmeFile_812_);
lean_ctor_set(v_reuseFailAlloc_826_, 24, v_enableArtifactCache_x3f_814_);
lean_ctor_set(v_reuseFailAlloc_826_, 25, v_restoreAllArtifacts_x3f_815_);
lean_ctor_set(v_reuseFailAlloc_826_, 26, v_builtinLint_x3f_818_);
lean_ctor_set(v_reuseFailAlloc_826_, 27, v_checks_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28, v_bootstrap_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28 + 1, v_precompileModules_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28 + 2, v_preferReleaseBuild_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28 + 3, v_reservoir_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28 + 5, v_allowImportAll_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*28 + 6, v_fixedToolchain_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__2(lean_object* v_f_829_, lean_object* v_cfg_830_){
_start:
{
lean_object* v_toWorkspaceConfig_831_; lean_object* v_toLeanConfig_832_; uint8_t v_bootstrap_833_; lean_object* v_extraDepTargets_834_; uint8_t v_precompileModules_835_; lean_object* v_moreGlobalServerArgs_836_; lean_object* v_srcDir_837_; lean_object* v_buildDir_838_; lean_object* v_leanLibDir_839_; lean_object* v_nativeLibDir_840_; lean_object* v_binDir_841_; lean_object* v_irDir_842_; lean_object* v_releaseRepo_843_; lean_object* v_buildArchive_844_; uint8_t v_preferReleaseBuild_845_; lean_object* v_testDriver_846_; lean_object* v_testDriverArgs_847_; lean_object* v_lintDriver_848_; lean_object* v_lintDriverArgs_849_; lean_object* v_version_850_; lean_object* v_versionTags_851_; lean_object* v_description_852_; lean_object* v_keywords_853_; lean_object* v_homepage_854_; lean_object* v_license_855_; lean_object* v_licenseFiles_856_; lean_object* v_readmeFile_857_; uint8_t v_reservoir_858_; lean_object* v_enableArtifactCache_x3f_859_; lean_object* v_restoreAllArtifacts_x3f_860_; uint8_t v_libPrefixOnWindows_861_; uint8_t v_allowImportAll_862_; lean_object* v_builtinLint_x3f_863_; lean_object* v_checks_864_; uint8_t v_fixedToolchain_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
v_toWorkspaceConfig_831_ = lean_ctor_get(v_cfg_830_, 0);
v_toLeanConfig_832_ = lean_ctor_get(v_cfg_830_, 1);
v_bootstrap_833_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28);
v_extraDepTargets_834_ = lean_ctor_get(v_cfg_830_, 2);
v_precompileModules_835_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_836_ = lean_ctor_get(v_cfg_830_, 3);
v_srcDir_837_ = lean_ctor_get(v_cfg_830_, 4);
v_buildDir_838_ = lean_ctor_get(v_cfg_830_, 5);
v_leanLibDir_839_ = lean_ctor_get(v_cfg_830_, 6);
v_nativeLibDir_840_ = lean_ctor_get(v_cfg_830_, 7);
v_binDir_841_ = lean_ctor_get(v_cfg_830_, 8);
v_irDir_842_ = lean_ctor_get(v_cfg_830_, 9);
v_releaseRepo_843_ = lean_ctor_get(v_cfg_830_, 10);
v_buildArchive_844_ = lean_ctor_get(v_cfg_830_, 11);
v_preferReleaseBuild_845_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28 + 2);
v_testDriver_846_ = lean_ctor_get(v_cfg_830_, 12);
v_testDriverArgs_847_ = lean_ctor_get(v_cfg_830_, 13);
v_lintDriver_848_ = lean_ctor_get(v_cfg_830_, 14);
v_lintDriverArgs_849_ = lean_ctor_get(v_cfg_830_, 15);
v_version_850_ = lean_ctor_get(v_cfg_830_, 16);
v_versionTags_851_ = lean_ctor_get(v_cfg_830_, 17);
v_description_852_ = lean_ctor_get(v_cfg_830_, 18);
v_keywords_853_ = lean_ctor_get(v_cfg_830_, 19);
v_homepage_854_ = lean_ctor_get(v_cfg_830_, 20);
v_license_855_ = lean_ctor_get(v_cfg_830_, 21);
v_licenseFiles_856_ = lean_ctor_get(v_cfg_830_, 22);
v_readmeFile_857_ = lean_ctor_get(v_cfg_830_, 23);
v_reservoir_858_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_859_ = lean_ctor_get(v_cfg_830_, 24);
v_restoreAllArtifacts_x3f_860_ = lean_ctor_get(v_cfg_830_, 25);
v_libPrefixOnWindows_861_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28 + 4);
v_allowImportAll_862_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_863_ = lean_ctor_get(v_cfg_830_, 26);
v_checks_864_ = lean_ctor_get(v_cfg_830_, 27);
v_fixedToolchain_865_ = lean_ctor_get_uint8(v_cfg_830_, sizeof(void*)*28 + 6);
v_isSharedCheck_873_ = !lean_is_exclusive(v_cfg_830_);
if (v_isSharedCheck_873_ == 0)
{
v___x_867_ = v_cfg_830_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_checks_864_);
lean_inc(v_builtinLint_x3f_863_);
lean_inc(v_restoreAllArtifacts_x3f_860_);
lean_inc(v_enableArtifactCache_x3f_859_);
lean_inc(v_readmeFile_857_);
lean_inc(v_licenseFiles_856_);
lean_inc(v_license_855_);
lean_inc(v_homepage_854_);
lean_inc(v_keywords_853_);
lean_inc(v_description_852_);
lean_inc(v_versionTags_851_);
lean_inc(v_version_850_);
lean_inc(v_lintDriverArgs_849_);
lean_inc(v_lintDriver_848_);
lean_inc(v_testDriverArgs_847_);
lean_inc(v_testDriver_846_);
lean_inc(v_buildArchive_844_);
lean_inc(v_releaseRepo_843_);
lean_inc(v_irDir_842_);
lean_inc(v_binDir_841_);
lean_inc(v_nativeLibDir_840_);
lean_inc(v_leanLibDir_839_);
lean_inc(v_buildDir_838_);
lean_inc(v_srcDir_837_);
lean_inc(v_moreGlobalServerArgs_836_);
lean_inc(v_extraDepTargets_834_);
lean_inc(v_toLeanConfig_832_);
lean_inc(v_toWorkspaceConfig_831_);
lean_dec(v_cfg_830_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_apply_1(v_f_829_, v_leanLibDir_839_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 6, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_toWorkspaceConfig_831_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_toLeanConfig_832_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_extraDepTargets_834_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_moreGlobalServerArgs_836_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_srcDir_837_);
lean_ctor_set(v_reuseFailAlloc_872_, 5, v_buildDir_838_);
lean_ctor_set(v_reuseFailAlloc_872_, 6, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_872_, 7, v_nativeLibDir_840_);
lean_ctor_set(v_reuseFailAlloc_872_, 8, v_binDir_841_);
lean_ctor_set(v_reuseFailAlloc_872_, 9, v_irDir_842_);
lean_ctor_set(v_reuseFailAlloc_872_, 10, v_releaseRepo_843_);
lean_ctor_set(v_reuseFailAlloc_872_, 11, v_buildArchive_844_);
lean_ctor_set(v_reuseFailAlloc_872_, 12, v_testDriver_846_);
lean_ctor_set(v_reuseFailAlloc_872_, 13, v_testDriverArgs_847_);
lean_ctor_set(v_reuseFailAlloc_872_, 14, v_lintDriver_848_);
lean_ctor_set(v_reuseFailAlloc_872_, 15, v_lintDriverArgs_849_);
lean_ctor_set(v_reuseFailAlloc_872_, 16, v_version_850_);
lean_ctor_set(v_reuseFailAlloc_872_, 17, v_versionTags_851_);
lean_ctor_set(v_reuseFailAlloc_872_, 18, v_description_852_);
lean_ctor_set(v_reuseFailAlloc_872_, 19, v_keywords_853_);
lean_ctor_set(v_reuseFailAlloc_872_, 20, v_homepage_854_);
lean_ctor_set(v_reuseFailAlloc_872_, 21, v_license_855_);
lean_ctor_set(v_reuseFailAlloc_872_, 22, v_licenseFiles_856_);
lean_ctor_set(v_reuseFailAlloc_872_, 23, v_readmeFile_857_);
lean_ctor_set(v_reuseFailAlloc_872_, 24, v_enableArtifactCache_x3f_859_);
lean_ctor_set(v_reuseFailAlloc_872_, 25, v_restoreAllArtifacts_x3f_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 26, v_builtinLint_x3f_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 27, v_checks_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28, v_bootstrap_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28 + 1, v_precompileModules_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28 + 2, v_preferReleaseBuild_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28 + 3, v_reservoir_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28 + 5, v_allowImportAll_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*28 + 6, v_fixedToolchain_865_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3(lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lake_defaultLeanLibDir;
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___lam__3___boxed(lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lake_PackageConfig_leanLibDir___proj___lam__3(v_x_876_);
lean_dec_ref(v_x_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_887_, lean_object* v_n_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___closed__4));
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_890_, lean_object* v_n_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_890_, v_n_891_);
lean_dec(v_n_891_);
lean_dec(v_p_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_893_, lean_object* v_n_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_893_, v_n_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_896_, lean_object* v_n_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_896_, v_n_897_);
lean_dec(v_n_897_);
lean_dec(v_p_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0(lean_object* v_cfg_899_){
_start:
{
lean_object* v_nativeLibDir_900_; 
v_nativeLibDir_900_ = lean_ctor_get(v_cfg_899_, 7);
lean_inc_ref(v_nativeLibDir_900_);
return v_nativeLibDir_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__0___boxed(lean_object* v_cfg_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__0(v_cfg_901_);
lean_dec_ref(v_cfg_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__1(lean_object* v_val_903_, lean_object* v_cfg_904_){
_start:
{
lean_object* v_toWorkspaceConfig_905_; lean_object* v_toLeanConfig_906_; uint8_t v_bootstrap_907_; lean_object* v_extraDepTargets_908_; uint8_t v_precompileModules_909_; lean_object* v_moreGlobalServerArgs_910_; lean_object* v_srcDir_911_; lean_object* v_buildDir_912_; lean_object* v_leanLibDir_913_; lean_object* v_binDir_914_; lean_object* v_irDir_915_; lean_object* v_releaseRepo_916_; lean_object* v_buildArchive_917_; uint8_t v_preferReleaseBuild_918_; lean_object* v_testDriver_919_; lean_object* v_testDriverArgs_920_; lean_object* v_lintDriver_921_; lean_object* v_lintDriverArgs_922_; lean_object* v_version_923_; lean_object* v_versionTags_924_; lean_object* v_description_925_; lean_object* v_keywords_926_; lean_object* v_homepage_927_; lean_object* v_license_928_; lean_object* v_licenseFiles_929_; lean_object* v_readmeFile_930_; uint8_t v_reservoir_931_; lean_object* v_enableArtifactCache_x3f_932_; lean_object* v_restoreAllArtifacts_x3f_933_; uint8_t v_libPrefixOnWindows_934_; uint8_t v_allowImportAll_935_; lean_object* v_builtinLint_x3f_936_; lean_object* v_checks_937_; uint8_t v_fixedToolchain_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_toWorkspaceConfig_905_ = lean_ctor_get(v_cfg_904_, 0);
v_toLeanConfig_906_ = lean_ctor_get(v_cfg_904_, 1);
v_bootstrap_907_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28);
v_extraDepTargets_908_ = lean_ctor_get(v_cfg_904_, 2);
v_precompileModules_909_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_910_ = lean_ctor_get(v_cfg_904_, 3);
v_srcDir_911_ = lean_ctor_get(v_cfg_904_, 4);
v_buildDir_912_ = lean_ctor_get(v_cfg_904_, 5);
v_leanLibDir_913_ = lean_ctor_get(v_cfg_904_, 6);
v_binDir_914_ = lean_ctor_get(v_cfg_904_, 8);
v_irDir_915_ = lean_ctor_get(v_cfg_904_, 9);
v_releaseRepo_916_ = lean_ctor_get(v_cfg_904_, 10);
v_buildArchive_917_ = lean_ctor_get(v_cfg_904_, 11);
v_preferReleaseBuild_918_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28 + 2);
v_testDriver_919_ = lean_ctor_get(v_cfg_904_, 12);
v_testDriverArgs_920_ = lean_ctor_get(v_cfg_904_, 13);
v_lintDriver_921_ = lean_ctor_get(v_cfg_904_, 14);
v_lintDriverArgs_922_ = lean_ctor_get(v_cfg_904_, 15);
v_version_923_ = lean_ctor_get(v_cfg_904_, 16);
v_versionTags_924_ = lean_ctor_get(v_cfg_904_, 17);
v_description_925_ = lean_ctor_get(v_cfg_904_, 18);
v_keywords_926_ = lean_ctor_get(v_cfg_904_, 19);
v_homepage_927_ = lean_ctor_get(v_cfg_904_, 20);
v_license_928_ = lean_ctor_get(v_cfg_904_, 21);
v_licenseFiles_929_ = lean_ctor_get(v_cfg_904_, 22);
v_readmeFile_930_ = lean_ctor_get(v_cfg_904_, 23);
v_reservoir_931_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_932_ = lean_ctor_get(v_cfg_904_, 24);
v_restoreAllArtifacts_x3f_933_ = lean_ctor_get(v_cfg_904_, 25);
v_libPrefixOnWindows_934_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28 + 4);
v_allowImportAll_935_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_936_ = lean_ctor_get(v_cfg_904_, 26);
v_checks_937_ = lean_ctor_get(v_cfg_904_, 27);
v_fixedToolchain_938_ = lean_ctor_get_uint8(v_cfg_904_, sizeof(void*)*28 + 6);
v_isSharedCheck_945_ = !lean_is_exclusive(v_cfg_904_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_cfg_904_, 7);
lean_dec(v_unused_946_);
v___x_940_ = v_cfg_904_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_checks_937_);
lean_inc(v_builtinLint_x3f_936_);
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
lean_inc(v_leanLibDir_913_);
lean_inc(v_buildDir_912_);
lean_inc(v_srcDir_911_);
lean_inc(v_moreGlobalServerArgs_910_);
lean_inc(v_extraDepTargets_908_);
lean_inc(v_toLeanConfig_906_);
lean_inc(v_toWorkspaceConfig_905_);
lean_dec(v_cfg_904_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 7, v_val_903_);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_toWorkspaceConfig_905_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_toLeanConfig_906_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_extraDepTargets_908_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_moreGlobalServerArgs_910_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_srcDir_911_);
lean_ctor_set(v_reuseFailAlloc_944_, 5, v_buildDir_912_);
lean_ctor_set(v_reuseFailAlloc_944_, 6, v_leanLibDir_913_);
lean_ctor_set(v_reuseFailAlloc_944_, 7, v_val_903_);
lean_ctor_set(v_reuseFailAlloc_944_, 8, v_binDir_914_);
lean_ctor_set(v_reuseFailAlloc_944_, 9, v_irDir_915_);
lean_ctor_set(v_reuseFailAlloc_944_, 10, v_releaseRepo_916_);
lean_ctor_set(v_reuseFailAlloc_944_, 11, v_buildArchive_917_);
lean_ctor_set(v_reuseFailAlloc_944_, 12, v_testDriver_919_);
lean_ctor_set(v_reuseFailAlloc_944_, 13, v_testDriverArgs_920_);
lean_ctor_set(v_reuseFailAlloc_944_, 14, v_lintDriver_921_);
lean_ctor_set(v_reuseFailAlloc_944_, 15, v_lintDriverArgs_922_);
lean_ctor_set(v_reuseFailAlloc_944_, 16, v_version_923_);
lean_ctor_set(v_reuseFailAlloc_944_, 17, v_versionTags_924_);
lean_ctor_set(v_reuseFailAlloc_944_, 18, v_description_925_);
lean_ctor_set(v_reuseFailAlloc_944_, 19, v_keywords_926_);
lean_ctor_set(v_reuseFailAlloc_944_, 20, v_homepage_927_);
lean_ctor_set(v_reuseFailAlloc_944_, 21, v_license_928_);
lean_ctor_set(v_reuseFailAlloc_944_, 22, v_licenseFiles_929_);
lean_ctor_set(v_reuseFailAlloc_944_, 23, v_readmeFile_930_);
lean_ctor_set(v_reuseFailAlloc_944_, 24, v_enableArtifactCache_x3f_932_);
lean_ctor_set(v_reuseFailAlloc_944_, 25, v_restoreAllArtifacts_x3f_933_);
lean_ctor_set(v_reuseFailAlloc_944_, 26, v_builtinLint_x3f_936_);
lean_ctor_set(v_reuseFailAlloc_944_, 27, v_checks_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28, v_bootstrap_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28 + 1, v_precompileModules_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28 + 2, v_preferReleaseBuild_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28 + 3, v_reservoir_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28 + 5, v_allowImportAll_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*28 + 6, v_fixedToolchain_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__2(lean_object* v_f_947_, lean_object* v_cfg_948_){
_start:
{
lean_object* v_toWorkspaceConfig_949_; lean_object* v_toLeanConfig_950_; uint8_t v_bootstrap_951_; lean_object* v_extraDepTargets_952_; uint8_t v_precompileModules_953_; lean_object* v_moreGlobalServerArgs_954_; lean_object* v_srcDir_955_; lean_object* v_buildDir_956_; lean_object* v_leanLibDir_957_; lean_object* v_nativeLibDir_958_; lean_object* v_binDir_959_; lean_object* v_irDir_960_; lean_object* v_releaseRepo_961_; lean_object* v_buildArchive_962_; uint8_t v_preferReleaseBuild_963_; lean_object* v_testDriver_964_; lean_object* v_testDriverArgs_965_; lean_object* v_lintDriver_966_; lean_object* v_lintDriverArgs_967_; lean_object* v_version_968_; lean_object* v_versionTags_969_; lean_object* v_description_970_; lean_object* v_keywords_971_; lean_object* v_homepage_972_; lean_object* v_license_973_; lean_object* v_licenseFiles_974_; lean_object* v_readmeFile_975_; uint8_t v_reservoir_976_; lean_object* v_enableArtifactCache_x3f_977_; lean_object* v_restoreAllArtifacts_x3f_978_; uint8_t v_libPrefixOnWindows_979_; uint8_t v_allowImportAll_980_; lean_object* v_builtinLint_x3f_981_; lean_object* v_checks_982_; uint8_t v_fixedToolchain_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
v_toWorkspaceConfig_949_ = lean_ctor_get(v_cfg_948_, 0);
v_toLeanConfig_950_ = lean_ctor_get(v_cfg_948_, 1);
v_bootstrap_951_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28);
v_extraDepTargets_952_ = lean_ctor_get(v_cfg_948_, 2);
v_precompileModules_953_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_954_ = lean_ctor_get(v_cfg_948_, 3);
v_srcDir_955_ = lean_ctor_get(v_cfg_948_, 4);
v_buildDir_956_ = lean_ctor_get(v_cfg_948_, 5);
v_leanLibDir_957_ = lean_ctor_get(v_cfg_948_, 6);
v_nativeLibDir_958_ = lean_ctor_get(v_cfg_948_, 7);
v_binDir_959_ = lean_ctor_get(v_cfg_948_, 8);
v_irDir_960_ = lean_ctor_get(v_cfg_948_, 9);
v_releaseRepo_961_ = lean_ctor_get(v_cfg_948_, 10);
v_buildArchive_962_ = lean_ctor_get(v_cfg_948_, 11);
v_preferReleaseBuild_963_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28 + 2);
v_testDriver_964_ = lean_ctor_get(v_cfg_948_, 12);
v_testDriverArgs_965_ = lean_ctor_get(v_cfg_948_, 13);
v_lintDriver_966_ = lean_ctor_get(v_cfg_948_, 14);
v_lintDriverArgs_967_ = lean_ctor_get(v_cfg_948_, 15);
v_version_968_ = lean_ctor_get(v_cfg_948_, 16);
v_versionTags_969_ = lean_ctor_get(v_cfg_948_, 17);
v_description_970_ = lean_ctor_get(v_cfg_948_, 18);
v_keywords_971_ = lean_ctor_get(v_cfg_948_, 19);
v_homepage_972_ = lean_ctor_get(v_cfg_948_, 20);
v_license_973_ = lean_ctor_get(v_cfg_948_, 21);
v_licenseFiles_974_ = lean_ctor_get(v_cfg_948_, 22);
v_readmeFile_975_ = lean_ctor_get(v_cfg_948_, 23);
v_reservoir_976_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_977_ = lean_ctor_get(v_cfg_948_, 24);
v_restoreAllArtifacts_x3f_978_ = lean_ctor_get(v_cfg_948_, 25);
v_libPrefixOnWindows_979_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28 + 4);
v_allowImportAll_980_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_981_ = lean_ctor_get(v_cfg_948_, 26);
v_checks_982_ = lean_ctor_get(v_cfg_948_, 27);
v_fixedToolchain_983_ = lean_ctor_get_uint8(v_cfg_948_, sizeof(void*)*28 + 6);
v_isSharedCheck_991_ = !lean_is_exclusive(v_cfg_948_);
if (v_isSharedCheck_991_ == 0)
{
v___x_985_ = v_cfg_948_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_checks_982_);
lean_inc(v_builtinLint_x3f_981_);
lean_inc(v_restoreAllArtifacts_x3f_978_);
lean_inc(v_enableArtifactCache_x3f_977_);
lean_inc(v_readmeFile_975_);
lean_inc(v_licenseFiles_974_);
lean_inc(v_license_973_);
lean_inc(v_homepage_972_);
lean_inc(v_keywords_971_);
lean_inc(v_description_970_);
lean_inc(v_versionTags_969_);
lean_inc(v_version_968_);
lean_inc(v_lintDriverArgs_967_);
lean_inc(v_lintDriver_966_);
lean_inc(v_testDriverArgs_965_);
lean_inc(v_testDriver_964_);
lean_inc(v_buildArchive_962_);
lean_inc(v_releaseRepo_961_);
lean_inc(v_irDir_960_);
lean_inc(v_binDir_959_);
lean_inc(v_nativeLibDir_958_);
lean_inc(v_leanLibDir_957_);
lean_inc(v_buildDir_956_);
lean_inc(v_srcDir_955_);
lean_inc(v_moreGlobalServerArgs_954_);
lean_inc(v_extraDepTargets_952_);
lean_inc(v_toLeanConfig_950_);
lean_inc(v_toWorkspaceConfig_949_);
lean_dec(v_cfg_948_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_apply_1(v_f_947_, v_nativeLibDir_958_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 7, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_toWorkspaceConfig_949_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_toLeanConfig_950_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_extraDepTargets_952_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_moreGlobalServerArgs_954_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_srcDir_955_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v_buildDir_956_);
lean_ctor_set(v_reuseFailAlloc_990_, 6, v_leanLibDir_957_);
lean_ctor_set(v_reuseFailAlloc_990_, 7, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_990_, 8, v_binDir_959_);
lean_ctor_set(v_reuseFailAlloc_990_, 9, v_irDir_960_);
lean_ctor_set(v_reuseFailAlloc_990_, 10, v_releaseRepo_961_);
lean_ctor_set(v_reuseFailAlloc_990_, 11, v_buildArchive_962_);
lean_ctor_set(v_reuseFailAlloc_990_, 12, v_testDriver_964_);
lean_ctor_set(v_reuseFailAlloc_990_, 13, v_testDriverArgs_965_);
lean_ctor_set(v_reuseFailAlloc_990_, 14, v_lintDriver_966_);
lean_ctor_set(v_reuseFailAlloc_990_, 15, v_lintDriverArgs_967_);
lean_ctor_set(v_reuseFailAlloc_990_, 16, v_version_968_);
lean_ctor_set(v_reuseFailAlloc_990_, 17, v_versionTags_969_);
lean_ctor_set(v_reuseFailAlloc_990_, 18, v_description_970_);
lean_ctor_set(v_reuseFailAlloc_990_, 19, v_keywords_971_);
lean_ctor_set(v_reuseFailAlloc_990_, 20, v_homepage_972_);
lean_ctor_set(v_reuseFailAlloc_990_, 21, v_license_973_);
lean_ctor_set(v_reuseFailAlloc_990_, 22, v_licenseFiles_974_);
lean_ctor_set(v_reuseFailAlloc_990_, 23, v_readmeFile_975_);
lean_ctor_set(v_reuseFailAlloc_990_, 24, v_enableArtifactCache_x3f_977_);
lean_ctor_set(v_reuseFailAlloc_990_, 25, v_restoreAllArtifacts_x3f_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 26, v_builtinLint_x3f_981_);
lean_ctor_set(v_reuseFailAlloc_990_, 27, v_checks_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28, v_bootstrap_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28 + 1, v_precompileModules_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28 + 2, v_preferReleaseBuild_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28 + 3, v_reservoir_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28 + 5, v_allowImportAll_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*28 + 6, v_fixedToolchain_983_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3(lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lake_defaultNativeLibDir;
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___lam__3___boxed(lean_object* v_x_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lake_PackageConfig_nativeLibDir___proj___lam__3(v_x_994_);
lean_dec_ref(v_x_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_1005_, lean_object* v_n_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___closed__4));
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_1008_, lean_object* v_n_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1008_, v_n_1009_);
lean_dec(v_n_1009_);
lean_dec(v_p_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_1011_, lean_object* v_n_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1011_, v_n_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_1014_, lean_object* v_n_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_1014_, v_n_1015_);
lean_dec(v_n_1015_);
lean_dec(v_p_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0(lean_object* v_cfg_1017_){
_start:
{
lean_object* v_binDir_1018_; 
v_binDir_1018_ = lean_ctor_get(v_cfg_1017_, 8);
lean_inc_ref(v_binDir_1018_);
return v_binDir_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__0___boxed(lean_object* v_cfg_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lake_PackageConfig_binDir___proj___lam__0(v_cfg_1019_);
lean_dec_ref(v_cfg_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__1(lean_object* v_val_1021_, lean_object* v_cfg_1022_){
_start:
{
lean_object* v_toWorkspaceConfig_1023_; lean_object* v_toLeanConfig_1024_; uint8_t v_bootstrap_1025_; lean_object* v_extraDepTargets_1026_; uint8_t v_precompileModules_1027_; lean_object* v_moreGlobalServerArgs_1028_; lean_object* v_srcDir_1029_; lean_object* v_buildDir_1030_; lean_object* v_leanLibDir_1031_; lean_object* v_nativeLibDir_1032_; lean_object* v_irDir_1033_; lean_object* v_releaseRepo_1034_; lean_object* v_buildArchive_1035_; uint8_t v_preferReleaseBuild_1036_; lean_object* v_testDriver_1037_; lean_object* v_testDriverArgs_1038_; lean_object* v_lintDriver_1039_; lean_object* v_lintDriverArgs_1040_; lean_object* v_version_1041_; lean_object* v_versionTags_1042_; lean_object* v_description_1043_; lean_object* v_keywords_1044_; lean_object* v_homepage_1045_; lean_object* v_license_1046_; lean_object* v_licenseFiles_1047_; lean_object* v_readmeFile_1048_; uint8_t v_reservoir_1049_; lean_object* v_enableArtifactCache_x3f_1050_; lean_object* v_restoreAllArtifacts_x3f_1051_; uint8_t v_libPrefixOnWindows_1052_; uint8_t v_allowImportAll_1053_; lean_object* v_builtinLint_x3f_1054_; lean_object* v_checks_1055_; uint8_t v_fixedToolchain_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_toWorkspaceConfig_1023_ = lean_ctor_get(v_cfg_1022_, 0);
v_toLeanConfig_1024_ = lean_ctor_get(v_cfg_1022_, 1);
v_bootstrap_1025_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28);
v_extraDepTargets_1026_ = lean_ctor_get(v_cfg_1022_, 2);
v_precompileModules_1027_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1028_ = lean_ctor_get(v_cfg_1022_, 3);
v_srcDir_1029_ = lean_ctor_get(v_cfg_1022_, 4);
v_buildDir_1030_ = lean_ctor_get(v_cfg_1022_, 5);
v_leanLibDir_1031_ = lean_ctor_get(v_cfg_1022_, 6);
v_nativeLibDir_1032_ = lean_ctor_get(v_cfg_1022_, 7);
v_irDir_1033_ = lean_ctor_get(v_cfg_1022_, 9);
v_releaseRepo_1034_ = lean_ctor_get(v_cfg_1022_, 10);
v_buildArchive_1035_ = lean_ctor_get(v_cfg_1022_, 11);
v_preferReleaseBuild_1036_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28 + 2);
v_testDriver_1037_ = lean_ctor_get(v_cfg_1022_, 12);
v_testDriverArgs_1038_ = lean_ctor_get(v_cfg_1022_, 13);
v_lintDriver_1039_ = lean_ctor_get(v_cfg_1022_, 14);
v_lintDriverArgs_1040_ = lean_ctor_get(v_cfg_1022_, 15);
v_version_1041_ = lean_ctor_get(v_cfg_1022_, 16);
v_versionTags_1042_ = lean_ctor_get(v_cfg_1022_, 17);
v_description_1043_ = lean_ctor_get(v_cfg_1022_, 18);
v_keywords_1044_ = lean_ctor_get(v_cfg_1022_, 19);
v_homepage_1045_ = lean_ctor_get(v_cfg_1022_, 20);
v_license_1046_ = lean_ctor_get(v_cfg_1022_, 21);
v_licenseFiles_1047_ = lean_ctor_get(v_cfg_1022_, 22);
v_readmeFile_1048_ = lean_ctor_get(v_cfg_1022_, 23);
v_reservoir_1049_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1050_ = lean_ctor_get(v_cfg_1022_, 24);
v_restoreAllArtifacts_x3f_1051_ = lean_ctor_get(v_cfg_1022_, 25);
v_libPrefixOnWindows_1052_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28 + 4);
v_allowImportAll_1053_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1054_ = lean_ctor_get(v_cfg_1022_, 26);
v_checks_1055_ = lean_ctor_get(v_cfg_1022_, 27);
v_fixedToolchain_1056_ = lean_ctor_get_uint8(v_cfg_1022_, sizeof(void*)*28 + 6);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_cfg_1022_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_cfg_1022_, 8);
lean_dec(v_unused_1064_);
v___x_1058_ = v_cfg_1022_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_checks_1055_);
lean_inc(v_builtinLint_x3f_1054_);
lean_inc(v_restoreAllArtifacts_x3f_1051_);
lean_inc(v_enableArtifactCache_x3f_1050_);
lean_inc(v_readmeFile_1048_);
lean_inc(v_licenseFiles_1047_);
lean_inc(v_license_1046_);
lean_inc(v_homepage_1045_);
lean_inc(v_keywords_1044_);
lean_inc(v_description_1043_);
lean_inc(v_versionTags_1042_);
lean_inc(v_version_1041_);
lean_inc(v_lintDriverArgs_1040_);
lean_inc(v_lintDriver_1039_);
lean_inc(v_testDriverArgs_1038_);
lean_inc(v_testDriver_1037_);
lean_inc(v_buildArchive_1035_);
lean_inc(v_releaseRepo_1034_);
lean_inc(v_irDir_1033_);
lean_inc(v_nativeLibDir_1032_);
lean_inc(v_leanLibDir_1031_);
lean_inc(v_buildDir_1030_);
lean_inc(v_srcDir_1029_);
lean_inc(v_moreGlobalServerArgs_1028_);
lean_inc(v_extraDepTargets_1026_);
lean_inc(v_toLeanConfig_1024_);
lean_inc(v_toWorkspaceConfig_1023_);
lean_dec(v_cfg_1022_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 8, v_val_1021_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_toWorkspaceConfig_1023_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_toLeanConfig_1024_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_extraDepTargets_1026_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_moreGlobalServerArgs_1028_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_srcDir_1029_);
lean_ctor_set(v_reuseFailAlloc_1062_, 5, v_buildDir_1030_);
lean_ctor_set(v_reuseFailAlloc_1062_, 6, v_leanLibDir_1031_);
lean_ctor_set(v_reuseFailAlloc_1062_, 7, v_nativeLibDir_1032_);
lean_ctor_set(v_reuseFailAlloc_1062_, 8, v_val_1021_);
lean_ctor_set(v_reuseFailAlloc_1062_, 9, v_irDir_1033_);
lean_ctor_set(v_reuseFailAlloc_1062_, 10, v_releaseRepo_1034_);
lean_ctor_set(v_reuseFailAlloc_1062_, 11, v_buildArchive_1035_);
lean_ctor_set(v_reuseFailAlloc_1062_, 12, v_testDriver_1037_);
lean_ctor_set(v_reuseFailAlloc_1062_, 13, v_testDriverArgs_1038_);
lean_ctor_set(v_reuseFailAlloc_1062_, 14, v_lintDriver_1039_);
lean_ctor_set(v_reuseFailAlloc_1062_, 15, v_lintDriverArgs_1040_);
lean_ctor_set(v_reuseFailAlloc_1062_, 16, v_version_1041_);
lean_ctor_set(v_reuseFailAlloc_1062_, 17, v_versionTags_1042_);
lean_ctor_set(v_reuseFailAlloc_1062_, 18, v_description_1043_);
lean_ctor_set(v_reuseFailAlloc_1062_, 19, v_keywords_1044_);
lean_ctor_set(v_reuseFailAlloc_1062_, 20, v_homepage_1045_);
lean_ctor_set(v_reuseFailAlloc_1062_, 21, v_license_1046_);
lean_ctor_set(v_reuseFailAlloc_1062_, 22, v_licenseFiles_1047_);
lean_ctor_set(v_reuseFailAlloc_1062_, 23, v_readmeFile_1048_);
lean_ctor_set(v_reuseFailAlloc_1062_, 24, v_enableArtifactCache_x3f_1050_);
lean_ctor_set(v_reuseFailAlloc_1062_, 25, v_restoreAllArtifacts_x3f_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 26, v_builtinLint_x3f_1054_);
lean_ctor_set(v_reuseFailAlloc_1062_, 27, v_checks_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28, v_bootstrap_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28 + 1, v_precompileModules_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1036_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28 + 3, v_reservoir_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28 + 5, v_allowImportAll_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*28 + 6, v_fixedToolchain_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__2(lean_object* v_f_1065_, lean_object* v_cfg_1066_){
_start:
{
lean_object* v_toWorkspaceConfig_1067_; lean_object* v_toLeanConfig_1068_; uint8_t v_bootstrap_1069_; lean_object* v_extraDepTargets_1070_; uint8_t v_precompileModules_1071_; lean_object* v_moreGlobalServerArgs_1072_; lean_object* v_srcDir_1073_; lean_object* v_buildDir_1074_; lean_object* v_leanLibDir_1075_; lean_object* v_nativeLibDir_1076_; lean_object* v_binDir_1077_; lean_object* v_irDir_1078_; lean_object* v_releaseRepo_1079_; lean_object* v_buildArchive_1080_; uint8_t v_preferReleaseBuild_1081_; lean_object* v_testDriver_1082_; lean_object* v_testDriverArgs_1083_; lean_object* v_lintDriver_1084_; lean_object* v_lintDriverArgs_1085_; lean_object* v_version_1086_; lean_object* v_versionTags_1087_; lean_object* v_description_1088_; lean_object* v_keywords_1089_; lean_object* v_homepage_1090_; lean_object* v_license_1091_; lean_object* v_licenseFiles_1092_; lean_object* v_readmeFile_1093_; uint8_t v_reservoir_1094_; lean_object* v_enableArtifactCache_x3f_1095_; lean_object* v_restoreAllArtifacts_x3f_1096_; uint8_t v_libPrefixOnWindows_1097_; uint8_t v_allowImportAll_1098_; lean_object* v_builtinLint_x3f_1099_; lean_object* v_checks_1100_; uint8_t v_fixedToolchain_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1109_; 
v_toWorkspaceConfig_1067_ = lean_ctor_get(v_cfg_1066_, 0);
v_toLeanConfig_1068_ = lean_ctor_get(v_cfg_1066_, 1);
v_bootstrap_1069_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28);
v_extraDepTargets_1070_ = lean_ctor_get(v_cfg_1066_, 2);
v_precompileModules_1071_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1072_ = lean_ctor_get(v_cfg_1066_, 3);
v_srcDir_1073_ = lean_ctor_get(v_cfg_1066_, 4);
v_buildDir_1074_ = lean_ctor_get(v_cfg_1066_, 5);
v_leanLibDir_1075_ = lean_ctor_get(v_cfg_1066_, 6);
v_nativeLibDir_1076_ = lean_ctor_get(v_cfg_1066_, 7);
v_binDir_1077_ = lean_ctor_get(v_cfg_1066_, 8);
v_irDir_1078_ = lean_ctor_get(v_cfg_1066_, 9);
v_releaseRepo_1079_ = lean_ctor_get(v_cfg_1066_, 10);
v_buildArchive_1080_ = lean_ctor_get(v_cfg_1066_, 11);
v_preferReleaseBuild_1081_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28 + 2);
v_testDriver_1082_ = lean_ctor_get(v_cfg_1066_, 12);
v_testDriverArgs_1083_ = lean_ctor_get(v_cfg_1066_, 13);
v_lintDriver_1084_ = lean_ctor_get(v_cfg_1066_, 14);
v_lintDriverArgs_1085_ = lean_ctor_get(v_cfg_1066_, 15);
v_version_1086_ = lean_ctor_get(v_cfg_1066_, 16);
v_versionTags_1087_ = lean_ctor_get(v_cfg_1066_, 17);
v_description_1088_ = lean_ctor_get(v_cfg_1066_, 18);
v_keywords_1089_ = lean_ctor_get(v_cfg_1066_, 19);
v_homepage_1090_ = lean_ctor_get(v_cfg_1066_, 20);
v_license_1091_ = lean_ctor_get(v_cfg_1066_, 21);
v_licenseFiles_1092_ = lean_ctor_get(v_cfg_1066_, 22);
v_readmeFile_1093_ = lean_ctor_get(v_cfg_1066_, 23);
v_reservoir_1094_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1095_ = lean_ctor_get(v_cfg_1066_, 24);
v_restoreAllArtifacts_x3f_1096_ = lean_ctor_get(v_cfg_1066_, 25);
v_libPrefixOnWindows_1097_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28 + 4);
v_allowImportAll_1098_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1099_ = lean_ctor_get(v_cfg_1066_, 26);
v_checks_1100_ = lean_ctor_get(v_cfg_1066_, 27);
v_fixedToolchain_1101_ = lean_ctor_get_uint8(v_cfg_1066_, sizeof(void*)*28 + 6);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_cfg_1066_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1103_ = v_cfg_1066_;
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_checks_1100_);
lean_inc(v_builtinLint_x3f_1099_);
lean_inc(v_restoreAllArtifacts_x3f_1096_);
lean_inc(v_enableArtifactCache_x3f_1095_);
lean_inc(v_readmeFile_1093_);
lean_inc(v_licenseFiles_1092_);
lean_inc(v_license_1091_);
lean_inc(v_homepage_1090_);
lean_inc(v_keywords_1089_);
lean_inc(v_description_1088_);
lean_inc(v_versionTags_1087_);
lean_inc(v_version_1086_);
lean_inc(v_lintDriverArgs_1085_);
lean_inc(v_lintDriver_1084_);
lean_inc(v_testDriverArgs_1083_);
lean_inc(v_testDriver_1082_);
lean_inc(v_buildArchive_1080_);
lean_inc(v_releaseRepo_1079_);
lean_inc(v_irDir_1078_);
lean_inc(v_binDir_1077_);
lean_inc(v_nativeLibDir_1076_);
lean_inc(v_leanLibDir_1075_);
lean_inc(v_buildDir_1074_);
lean_inc(v_srcDir_1073_);
lean_inc(v_moreGlobalServerArgs_1072_);
lean_inc(v_extraDepTargets_1070_);
lean_inc(v_toLeanConfig_1068_);
lean_inc(v_toWorkspaceConfig_1067_);
lean_dec(v_cfg_1066_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_apply_1(v_f_1065_, v_binDir_1077_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 8, v___x_1105_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_toWorkspaceConfig_1067_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_toLeanConfig_1068_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_extraDepTargets_1070_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_moreGlobalServerArgs_1072_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_srcDir_1073_);
lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_buildDir_1074_);
lean_ctor_set(v_reuseFailAlloc_1108_, 6, v_leanLibDir_1075_);
lean_ctor_set(v_reuseFailAlloc_1108_, 7, v_nativeLibDir_1076_);
lean_ctor_set(v_reuseFailAlloc_1108_, 8, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1108_, 9, v_irDir_1078_);
lean_ctor_set(v_reuseFailAlloc_1108_, 10, v_releaseRepo_1079_);
lean_ctor_set(v_reuseFailAlloc_1108_, 11, v_buildArchive_1080_);
lean_ctor_set(v_reuseFailAlloc_1108_, 12, v_testDriver_1082_);
lean_ctor_set(v_reuseFailAlloc_1108_, 13, v_testDriverArgs_1083_);
lean_ctor_set(v_reuseFailAlloc_1108_, 14, v_lintDriver_1084_);
lean_ctor_set(v_reuseFailAlloc_1108_, 15, v_lintDriverArgs_1085_);
lean_ctor_set(v_reuseFailAlloc_1108_, 16, v_version_1086_);
lean_ctor_set(v_reuseFailAlloc_1108_, 17, v_versionTags_1087_);
lean_ctor_set(v_reuseFailAlloc_1108_, 18, v_description_1088_);
lean_ctor_set(v_reuseFailAlloc_1108_, 19, v_keywords_1089_);
lean_ctor_set(v_reuseFailAlloc_1108_, 20, v_homepage_1090_);
lean_ctor_set(v_reuseFailAlloc_1108_, 21, v_license_1091_);
lean_ctor_set(v_reuseFailAlloc_1108_, 22, v_licenseFiles_1092_);
lean_ctor_set(v_reuseFailAlloc_1108_, 23, v_readmeFile_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 24, v_enableArtifactCache_x3f_1095_);
lean_ctor_set(v_reuseFailAlloc_1108_, 25, v_restoreAllArtifacts_x3f_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 26, v_builtinLint_x3f_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 27, v_checks_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28, v_bootstrap_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28 + 1, v_precompileModules_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28 + 3, v_reservoir_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28 + 5, v_allowImportAll_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*28 + 6, v_fixedToolchain_1101_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3(lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lake_defaultBinDir;
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___lam__3___boxed(lean_object* v_x_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lake_PackageConfig_binDir___proj___lam__3(v_x_1112_);
lean_dec_ref(v_x_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1123_, lean_object* v_n_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___closed__4));
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1126_, lean_object* v_n_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lake_PackageConfig_binDir___proj(v_p_1126_, v_n_1127_);
lean_dec(v_n_1127_);
lean_dec(v_p_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1129_, lean_object* v_n_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lake_PackageConfig_binDir___proj(v_p_1129_, v_n_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1132_, lean_object* v_n_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1132_, v_n_1133_);
lean_dec(v_n_1133_);
lean_dec(v_p_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0(lean_object* v_cfg_1135_){
_start:
{
lean_object* v_irDir_1136_; 
v_irDir_1136_ = lean_ctor_get(v_cfg_1135_, 9);
lean_inc_ref(v_irDir_1136_);
return v_irDir_1136_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__0___boxed(lean_object* v_cfg_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lake_PackageConfig_irDir___proj___lam__0(v_cfg_1137_);
lean_dec_ref(v_cfg_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__1(lean_object* v_val_1139_, lean_object* v_cfg_1140_){
_start:
{
lean_object* v_toWorkspaceConfig_1141_; lean_object* v_toLeanConfig_1142_; uint8_t v_bootstrap_1143_; lean_object* v_extraDepTargets_1144_; uint8_t v_precompileModules_1145_; lean_object* v_moreGlobalServerArgs_1146_; lean_object* v_srcDir_1147_; lean_object* v_buildDir_1148_; lean_object* v_leanLibDir_1149_; lean_object* v_nativeLibDir_1150_; lean_object* v_binDir_1151_; lean_object* v_releaseRepo_1152_; lean_object* v_buildArchive_1153_; uint8_t v_preferReleaseBuild_1154_; lean_object* v_testDriver_1155_; lean_object* v_testDriverArgs_1156_; lean_object* v_lintDriver_1157_; lean_object* v_lintDriverArgs_1158_; lean_object* v_version_1159_; lean_object* v_versionTags_1160_; lean_object* v_description_1161_; lean_object* v_keywords_1162_; lean_object* v_homepage_1163_; lean_object* v_license_1164_; lean_object* v_licenseFiles_1165_; lean_object* v_readmeFile_1166_; uint8_t v_reservoir_1167_; lean_object* v_enableArtifactCache_x3f_1168_; lean_object* v_restoreAllArtifacts_x3f_1169_; uint8_t v_libPrefixOnWindows_1170_; uint8_t v_allowImportAll_1171_; lean_object* v_builtinLint_x3f_1172_; lean_object* v_checks_1173_; uint8_t v_fixedToolchain_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v_toWorkspaceConfig_1141_ = lean_ctor_get(v_cfg_1140_, 0);
v_toLeanConfig_1142_ = lean_ctor_get(v_cfg_1140_, 1);
v_bootstrap_1143_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28);
v_extraDepTargets_1144_ = lean_ctor_get(v_cfg_1140_, 2);
v_precompileModules_1145_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1146_ = lean_ctor_get(v_cfg_1140_, 3);
v_srcDir_1147_ = lean_ctor_get(v_cfg_1140_, 4);
v_buildDir_1148_ = lean_ctor_get(v_cfg_1140_, 5);
v_leanLibDir_1149_ = lean_ctor_get(v_cfg_1140_, 6);
v_nativeLibDir_1150_ = lean_ctor_get(v_cfg_1140_, 7);
v_binDir_1151_ = lean_ctor_get(v_cfg_1140_, 8);
v_releaseRepo_1152_ = lean_ctor_get(v_cfg_1140_, 10);
v_buildArchive_1153_ = lean_ctor_get(v_cfg_1140_, 11);
v_preferReleaseBuild_1154_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28 + 2);
v_testDriver_1155_ = lean_ctor_get(v_cfg_1140_, 12);
v_testDriverArgs_1156_ = lean_ctor_get(v_cfg_1140_, 13);
v_lintDriver_1157_ = lean_ctor_get(v_cfg_1140_, 14);
v_lintDriverArgs_1158_ = lean_ctor_get(v_cfg_1140_, 15);
v_version_1159_ = lean_ctor_get(v_cfg_1140_, 16);
v_versionTags_1160_ = lean_ctor_get(v_cfg_1140_, 17);
v_description_1161_ = lean_ctor_get(v_cfg_1140_, 18);
v_keywords_1162_ = lean_ctor_get(v_cfg_1140_, 19);
v_homepage_1163_ = lean_ctor_get(v_cfg_1140_, 20);
v_license_1164_ = lean_ctor_get(v_cfg_1140_, 21);
v_licenseFiles_1165_ = lean_ctor_get(v_cfg_1140_, 22);
v_readmeFile_1166_ = lean_ctor_get(v_cfg_1140_, 23);
v_reservoir_1167_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1168_ = lean_ctor_get(v_cfg_1140_, 24);
v_restoreAllArtifacts_x3f_1169_ = lean_ctor_get(v_cfg_1140_, 25);
v_libPrefixOnWindows_1170_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28 + 4);
v_allowImportAll_1171_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1172_ = lean_ctor_get(v_cfg_1140_, 26);
v_checks_1173_ = lean_ctor_get(v_cfg_1140_, 27);
v_fixedToolchain_1174_ = lean_ctor_get_uint8(v_cfg_1140_, sizeof(void*)*28 + 6);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_cfg_1140_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_cfg_1140_, 9);
lean_dec(v_unused_1182_);
v___x_1176_ = v_cfg_1140_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_checks_1173_);
lean_inc(v_builtinLint_x3f_1172_);
lean_inc(v_restoreAllArtifacts_x3f_1169_);
lean_inc(v_enableArtifactCache_x3f_1168_);
lean_inc(v_readmeFile_1166_);
lean_inc(v_licenseFiles_1165_);
lean_inc(v_license_1164_);
lean_inc(v_homepage_1163_);
lean_inc(v_keywords_1162_);
lean_inc(v_description_1161_);
lean_inc(v_versionTags_1160_);
lean_inc(v_version_1159_);
lean_inc(v_lintDriverArgs_1158_);
lean_inc(v_lintDriver_1157_);
lean_inc(v_testDriverArgs_1156_);
lean_inc(v_testDriver_1155_);
lean_inc(v_buildArchive_1153_);
lean_inc(v_releaseRepo_1152_);
lean_inc(v_binDir_1151_);
lean_inc(v_nativeLibDir_1150_);
lean_inc(v_leanLibDir_1149_);
lean_inc(v_buildDir_1148_);
lean_inc(v_srcDir_1147_);
lean_inc(v_moreGlobalServerArgs_1146_);
lean_inc(v_extraDepTargets_1144_);
lean_inc(v_toLeanConfig_1142_);
lean_inc(v_toWorkspaceConfig_1141_);
lean_dec(v_cfg_1140_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 9, v_val_1139_);
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_toWorkspaceConfig_1141_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_toLeanConfig_1142_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_extraDepTargets_1144_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_moreGlobalServerArgs_1146_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_srcDir_1147_);
lean_ctor_set(v_reuseFailAlloc_1180_, 5, v_buildDir_1148_);
lean_ctor_set(v_reuseFailAlloc_1180_, 6, v_leanLibDir_1149_);
lean_ctor_set(v_reuseFailAlloc_1180_, 7, v_nativeLibDir_1150_);
lean_ctor_set(v_reuseFailAlloc_1180_, 8, v_binDir_1151_);
lean_ctor_set(v_reuseFailAlloc_1180_, 9, v_val_1139_);
lean_ctor_set(v_reuseFailAlloc_1180_, 10, v_releaseRepo_1152_);
lean_ctor_set(v_reuseFailAlloc_1180_, 11, v_buildArchive_1153_);
lean_ctor_set(v_reuseFailAlloc_1180_, 12, v_testDriver_1155_);
lean_ctor_set(v_reuseFailAlloc_1180_, 13, v_testDriverArgs_1156_);
lean_ctor_set(v_reuseFailAlloc_1180_, 14, v_lintDriver_1157_);
lean_ctor_set(v_reuseFailAlloc_1180_, 15, v_lintDriverArgs_1158_);
lean_ctor_set(v_reuseFailAlloc_1180_, 16, v_version_1159_);
lean_ctor_set(v_reuseFailAlloc_1180_, 17, v_versionTags_1160_);
lean_ctor_set(v_reuseFailAlloc_1180_, 18, v_description_1161_);
lean_ctor_set(v_reuseFailAlloc_1180_, 19, v_keywords_1162_);
lean_ctor_set(v_reuseFailAlloc_1180_, 20, v_homepage_1163_);
lean_ctor_set(v_reuseFailAlloc_1180_, 21, v_license_1164_);
lean_ctor_set(v_reuseFailAlloc_1180_, 22, v_licenseFiles_1165_);
lean_ctor_set(v_reuseFailAlloc_1180_, 23, v_readmeFile_1166_);
lean_ctor_set(v_reuseFailAlloc_1180_, 24, v_enableArtifactCache_x3f_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 25, v_restoreAllArtifacts_x3f_1169_);
lean_ctor_set(v_reuseFailAlloc_1180_, 26, v_builtinLint_x3f_1172_);
lean_ctor_set(v_reuseFailAlloc_1180_, 27, v_checks_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28, v_bootstrap_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28 + 1, v_precompileModules_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28 + 3, v_reservoir_1167_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28 + 5, v_allowImportAll_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*28 + 6, v_fixedToolchain_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__2(lean_object* v_f_1183_, lean_object* v_cfg_1184_){
_start:
{
lean_object* v_toWorkspaceConfig_1185_; lean_object* v_toLeanConfig_1186_; uint8_t v_bootstrap_1187_; lean_object* v_extraDepTargets_1188_; uint8_t v_precompileModules_1189_; lean_object* v_moreGlobalServerArgs_1190_; lean_object* v_srcDir_1191_; lean_object* v_buildDir_1192_; lean_object* v_leanLibDir_1193_; lean_object* v_nativeLibDir_1194_; lean_object* v_binDir_1195_; lean_object* v_irDir_1196_; lean_object* v_releaseRepo_1197_; lean_object* v_buildArchive_1198_; uint8_t v_preferReleaseBuild_1199_; lean_object* v_testDriver_1200_; lean_object* v_testDriverArgs_1201_; lean_object* v_lintDriver_1202_; lean_object* v_lintDriverArgs_1203_; lean_object* v_version_1204_; lean_object* v_versionTags_1205_; lean_object* v_description_1206_; lean_object* v_keywords_1207_; lean_object* v_homepage_1208_; lean_object* v_license_1209_; lean_object* v_licenseFiles_1210_; lean_object* v_readmeFile_1211_; uint8_t v_reservoir_1212_; lean_object* v_enableArtifactCache_x3f_1213_; lean_object* v_restoreAllArtifacts_x3f_1214_; uint8_t v_libPrefixOnWindows_1215_; uint8_t v_allowImportAll_1216_; lean_object* v_builtinLint_x3f_1217_; lean_object* v_checks_1218_; uint8_t v_fixedToolchain_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_toWorkspaceConfig_1185_ = lean_ctor_get(v_cfg_1184_, 0);
v_toLeanConfig_1186_ = lean_ctor_get(v_cfg_1184_, 1);
v_bootstrap_1187_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28);
v_extraDepTargets_1188_ = lean_ctor_get(v_cfg_1184_, 2);
v_precompileModules_1189_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1190_ = lean_ctor_get(v_cfg_1184_, 3);
v_srcDir_1191_ = lean_ctor_get(v_cfg_1184_, 4);
v_buildDir_1192_ = lean_ctor_get(v_cfg_1184_, 5);
v_leanLibDir_1193_ = lean_ctor_get(v_cfg_1184_, 6);
v_nativeLibDir_1194_ = lean_ctor_get(v_cfg_1184_, 7);
v_binDir_1195_ = lean_ctor_get(v_cfg_1184_, 8);
v_irDir_1196_ = lean_ctor_get(v_cfg_1184_, 9);
v_releaseRepo_1197_ = lean_ctor_get(v_cfg_1184_, 10);
v_buildArchive_1198_ = lean_ctor_get(v_cfg_1184_, 11);
v_preferReleaseBuild_1199_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28 + 2);
v_testDriver_1200_ = lean_ctor_get(v_cfg_1184_, 12);
v_testDriverArgs_1201_ = lean_ctor_get(v_cfg_1184_, 13);
v_lintDriver_1202_ = lean_ctor_get(v_cfg_1184_, 14);
v_lintDriverArgs_1203_ = lean_ctor_get(v_cfg_1184_, 15);
v_version_1204_ = lean_ctor_get(v_cfg_1184_, 16);
v_versionTags_1205_ = lean_ctor_get(v_cfg_1184_, 17);
v_description_1206_ = lean_ctor_get(v_cfg_1184_, 18);
v_keywords_1207_ = lean_ctor_get(v_cfg_1184_, 19);
v_homepage_1208_ = lean_ctor_get(v_cfg_1184_, 20);
v_license_1209_ = lean_ctor_get(v_cfg_1184_, 21);
v_licenseFiles_1210_ = lean_ctor_get(v_cfg_1184_, 22);
v_readmeFile_1211_ = lean_ctor_get(v_cfg_1184_, 23);
v_reservoir_1212_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1213_ = lean_ctor_get(v_cfg_1184_, 24);
v_restoreAllArtifacts_x3f_1214_ = lean_ctor_get(v_cfg_1184_, 25);
v_libPrefixOnWindows_1215_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28 + 4);
v_allowImportAll_1216_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1217_ = lean_ctor_get(v_cfg_1184_, 26);
v_checks_1218_ = lean_ctor_get(v_cfg_1184_, 27);
v_fixedToolchain_1219_ = lean_ctor_get_uint8(v_cfg_1184_, sizeof(void*)*28 + 6);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_cfg_1184_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v_cfg_1184_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_checks_1218_);
lean_inc(v_builtinLint_x3f_1217_);
lean_inc(v_restoreAllArtifacts_x3f_1214_);
lean_inc(v_enableArtifactCache_x3f_1213_);
lean_inc(v_readmeFile_1211_);
lean_inc(v_licenseFiles_1210_);
lean_inc(v_license_1209_);
lean_inc(v_homepage_1208_);
lean_inc(v_keywords_1207_);
lean_inc(v_description_1206_);
lean_inc(v_versionTags_1205_);
lean_inc(v_version_1204_);
lean_inc(v_lintDriverArgs_1203_);
lean_inc(v_lintDriver_1202_);
lean_inc(v_testDriverArgs_1201_);
lean_inc(v_testDriver_1200_);
lean_inc(v_buildArchive_1198_);
lean_inc(v_releaseRepo_1197_);
lean_inc(v_irDir_1196_);
lean_inc(v_binDir_1195_);
lean_inc(v_nativeLibDir_1194_);
lean_inc(v_leanLibDir_1193_);
lean_inc(v_buildDir_1192_);
lean_inc(v_srcDir_1191_);
lean_inc(v_moreGlobalServerArgs_1190_);
lean_inc(v_extraDepTargets_1188_);
lean_inc(v_toLeanConfig_1186_);
lean_inc(v_toWorkspaceConfig_1185_);
lean_dec(v_cfg_1184_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_apply_1(v_f_1183_, v_irDir_1196_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 9, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_toWorkspaceConfig_1185_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_toLeanConfig_1186_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_extraDepTargets_1188_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_moreGlobalServerArgs_1190_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_srcDir_1191_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v_buildDir_1192_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_leanLibDir_1193_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v_nativeLibDir_1194_);
lean_ctor_set(v_reuseFailAlloc_1226_, 8, v_binDir_1195_);
lean_ctor_set(v_reuseFailAlloc_1226_, 9, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 10, v_releaseRepo_1197_);
lean_ctor_set(v_reuseFailAlloc_1226_, 11, v_buildArchive_1198_);
lean_ctor_set(v_reuseFailAlloc_1226_, 12, v_testDriver_1200_);
lean_ctor_set(v_reuseFailAlloc_1226_, 13, v_testDriverArgs_1201_);
lean_ctor_set(v_reuseFailAlloc_1226_, 14, v_lintDriver_1202_);
lean_ctor_set(v_reuseFailAlloc_1226_, 15, v_lintDriverArgs_1203_);
lean_ctor_set(v_reuseFailAlloc_1226_, 16, v_version_1204_);
lean_ctor_set(v_reuseFailAlloc_1226_, 17, v_versionTags_1205_);
lean_ctor_set(v_reuseFailAlloc_1226_, 18, v_description_1206_);
lean_ctor_set(v_reuseFailAlloc_1226_, 19, v_keywords_1207_);
lean_ctor_set(v_reuseFailAlloc_1226_, 20, v_homepage_1208_);
lean_ctor_set(v_reuseFailAlloc_1226_, 21, v_license_1209_);
lean_ctor_set(v_reuseFailAlloc_1226_, 22, v_licenseFiles_1210_);
lean_ctor_set(v_reuseFailAlloc_1226_, 23, v_readmeFile_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 24, v_enableArtifactCache_x3f_1213_);
lean_ctor_set(v_reuseFailAlloc_1226_, 25, v_restoreAllArtifacts_x3f_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 26, v_builtinLint_x3f_1217_);
lean_ctor_set(v_reuseFailAlloc_1226_, 27, v_checks_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28, v_bootstrap_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28 + 1, v_precompileModules_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28 + 3, v_reservoir_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28 + 5, v_allowImportAll_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*28 + 6, v_fixedToolchain_1219_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3(lean_object* v_x_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lake_defaultIrDir;
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___lam__3___boxed(lean_object* v_x_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lake_PackageConfig_irDir___proj___lam__3(v_x_1230_);
lean_dec_ref(v_x_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1241_, lean_object* v_n_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___closed__4));
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1244_, lean_object* v_n_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lake_PackageConfig_irDir___proj(v_p_1244_, v_n_1245_);
lean_dec(v_n_1245_);
lean_dec(v_p_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1247_, lean_object* v_n_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lake_PackageConfig_irDir___proj(v_p_1247_, v_n_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1250_, lean_object* v_n_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1250_, v_n_1251_);
lean_dec(v_n_1251_);
lean_dec(v_p_1250_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0(lean_object* v_cfg_1253_){
_start:
{
lean_object* v_releaseRepo_1254_; 
v_releaseRepo_1254_ = lean_ctor_get(v_cfg_1253_, 10);
lean_inc(v_releaseRepo_1254_);
return v_releaseRepo_1254_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__0___boxed(lean_object* v_cfg_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lake_PackageConfig_releaseRepo___proj___lam__0(v_cfg_1255_);
lean_dec_ref(v_cfg_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__1(lean_object* v_val_1257_, lean_object* v_cfg_1258_){
_start:
{
lean_object* v_toWorkspaceConfig_1259_; lean_object* v_toLeanConfig_1260_; uint8_t v_bootstrap_1261_; lean_object* v_extraDepTargets_1262_; uint8_t v_precompileModules_1263_; lean_object* v_moreGlobalServerArgs_1264_; lean_object* v_srcDir_1265_; lean_object* v_buildDir_1266_; lean_object* v_leanLibDir_1267_; lean_object* v_nativeLibDir_1268_; lean_object* v_binDir_1269_; lean_object* v_irDir_1270_; lean_object* v_buildArchive_1271_; uint8_t v_preferReleaseBuild_1272_; lean_object* v_testDriver_1273_; lean_object* v_testDriverArgs_1274_; lean_object* v_lintDriver_1275_; lean_object* v_lintDriverArgs_1276_; lean_object* v_version_1277_; lean_object* v_versionTags_1278_; lean_object* v_description_1279_; lean_object* v_keywords_1280_; lean_object* v_homepage_1281_; lean_object* v_license_1282_; lean_object* v_licenseFiles_1283_; lean_object* v_readmeFile_1284_; uint8_t v_reservoir_1285_; lean_object* v_enableArtifactCache_x3f_1286_; lean_object* v_restoreAllArtifacts_x3f_1287_; uint8_t v_libPrefixOnWindows_1288_; uint8_t v_allowImportAll_1289_; lean_object* v_builtinLint_x3f_1290_; lean_object* v_checks_1291_; uint8_t v_fixedToolchain_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_toWorkspaceConfig_1259_ = lean_ctor_get(v_cfg_1258_, 0);
v_toLeanConfig_1260_ = lean_ctor_get(v_cfg_1258_, 1);
v_bootstrap_1261_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28);
v_extraDepTargets_1262_ = lean_ctor_get(v_cfg_1258_, 2);
v_precompileModules_1263_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1264_ = lean_ctor_get(v_cfg_1258_, 3);
v_srcDir_1265_ = lean_ctor_get(v_cfg_1258_, 4);
v_buildDir_1266_ = lean_ctor_get(v_cfg_1258_, 5);
v_leanLibDir_1267_ = lean_ctor_get(v_cfg_1258_, 6);
v_nativeLibDir_1268_ = lean_ctor_get(v_cfg_1258_, 7);
v_binDir_1269_ = lean_ctor_get(v_cfg_1258_, 8);
v_irDir_1270_ = lean_ctor_get(v_cfg_1258_, 9);
v_buildArchive_1271_ = lean_ctor_get(v_cfg_1258_, 11);
v_preferReleaseBuild_1272_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28 + 2);
v_testDriver_1273_ = lean_ctor_get(v_cfg_1258_, 12);
v_testDriverArgs_1274_ = lean_ctor_get(v_cfg_1258_, 13);
v_lintDriver_1275_ = lean_ctor_get(v_cfg_1258_, 14);
v_lintDriverArgs_1276_ = lean_ctor_get(v_cfg_1258_, 15);
v_version_1277_ = lean_ctor_get(v_cfg_1258_, 16);
v_versionTags_1278_ = lean_ctor_get(v_cfg_1258_, 17);
v_description_1279_ = lean_ctor_get(v_cfg_1258_, 18);
v_keywords_1280_ = lean_ctor_get(v_cfg_1258_, 19);
v_homepage_1281_ = lean_ctor_get(v_cfg_1258_, 20);
v_license_1282_ = lean_ctor_get(v_cfg_1258_, 21);
v_licenseFiles_1283_ = lean_ctor_get(v_cfg_1258_, 22);
v_readmeFile_1284_ = lean_ctor_get(v_cfg_1258_, 23);
v_reservoir_1285_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1286_ = lean_ctor_get(v_cfg_1258_, 24);
v_restoreAllArtifacts_x3f_1287_ = lean_ctor_get(v_cfg_1258_, 25);
v_libPrefixOnWindows_1288_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28 + 4);
v_allowImportAll_1289_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1290_ = lean_ctor_get(v_cfg_1258_, 26);
v_checks_1291_ = lean_ctor_get(v_cfg_1258_, 27);
v_fixedToolchain_1292_ = lean_ctor_get_uint8(v_cfg_1258_, sizeof(void*)*28 + 6);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_cfg_1258_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_cfg_1258_, 10);
lean_dec(v_unused_1300_);
v___x_1294_ = v_cfg_1258_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_checks_1291_);
lean_inc(v_builtinLint_x3f_1290_);
lean_inc(v_restoreAllArtifacts_x3f_1287_);
lean_inc(v_enableArtifactCache_x3f_1286_);
lean_inc(v_readmeFile_1284_);
lean_inc(v_licenseFiles_1283_);
lean_inc(v_license_1282_);
lean_inc(v_homepage_1281_);
lean_inc(v_keywords_1280_);
lean_inc(v_description_1279_);
lean_inc(v_versionTags_1278_);
lean_inc(v_version_1277_);
lean_inc(v_lintDriverArgs_1276_);
lean_inc(v_lintDriver_1275_);
lean_inc(v_testDriverArgs_1274_);
lean_inc(v_testDriver_1273_);
lean_inc(v_buildArchive_1271_);
lean_inc(v_irDir_1270_);
lean_inc(v_binDir_1269_);
lean_inc(v_nativeLibDir_1268_);
lean_inc(v_leanLibDir_1267_);
lean_inc(v_buildDir_1266_);
lean_inc(v_srcDir_1265_);
lean_inc(v_moreGlobalServerArgs_1264_);
lean_inc(v_extraDepTargets_1262_);
lean_inc(v_toLeanConfig_1260_);
lean_inc(v_toWorkspaceConfig_1259_);
lean_dec(v_cfg_1258_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 10, v_val_1257_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_toWorkspaceConfig_1259_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_toLeanConfig_1260_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_extraDepTargets_1262_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_moreGlobalServerArgs_1264_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v_srcDir_1265_);
lean_ctor_set(v_reuseFailAlloc_1298_, 5, v_buildDir_1266_);
lean_ctor_set(v_reuseFailAlloc_1298_, 6, v_leanLibDir_1267_);
lean_ctor_set(v_reuseFailAlloc_1298_, 7, v_nativeLibDir_1268_);
lean_ctor_set(v_reuseFailAlloc_1298_, 8, v_binDir_1269_);
lean_ctor_set(v_reuseFailAlloc_1298_, 9, v_irDir_1270_);
lean_ctor_set(v_reuseFailAlloc_1298_, 10, v_val_1257_);
lean_ctor_set(v_reuseFailAlloc_1298_, 11, v_buildArchive_1271_);
lean_ctor_set(v_reuseFailAlloc_1298_, 12, v_testDriver_1273_);
lean_ctor_set(v_reuseFailAlloc_1298_, 13, v_testDriverArgs_1274_);
lean_ctor_set(v_reuseFailAlloc_1298_, 14, v_lintDriver_1275_);
lean_ctor_set(v_reuseFailAlloc_1298_, 15, v_lintDriverArgs_1276_);
lean_ctor_set(v_reuseFailAlloc_1298_, 16, v_version_1277_);
lean_ctor_set(v_reuseFailAlloc_1298_, 17, v_versionTags_1278_);
lean_ctor_set(v_reuseFailAlloc_1298_, 18, v_description_1279_);
lean_ctor_set(v_reuseFailAlloc_1298_, 19, v_keywords_1280_);
lean_ctor_set(v_reuseFailAlloc_1298_, 20, v_homepage_1281_);
lean_ctor_set(v_reuseFailAlloc_1298_, 21, v_license_1282_);
lean_ctor_set(v_reuseFailAlloc_1298_, 22, v_licenseFiles_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 23, v_readmeFile_1284_);
lean_ctor_set(v_reuseFailAlloc_1298_, 24, v_enableArtifactCache_x3f_1286_);
lean_ctor_set(v_reuseFailAlloc_1298_, 25, v_restoreAllArtifacts_x3f_1287_);
lean_ctor_set(v_reuseFailAlloc_1298_, 26, v_builtinLint_x3f_1290_);
lean_ctor_set(v_reuseFailAlloc_1298_, 27, v_checks_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28, v_bootstrap_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28 + 1, v_precompileModules_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28 + 3, v_reservoir_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28 + 5, v_allowImportAll_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*28 + 6, v_fixedToolchain_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__2(lean_object* v_f_1301_, lean_object* v_cfg_1302_){
_start:
{
lean_object* v_toWorkspaceConfig_1303_; lean_object* v_toLeanConfig_1304_; uint8_t v_bootstrap_1305_; lean_object* v_extraDepTargets_1306_; uint8_t v_precompileModules_1307_; lean_object* v_moreGlobalServerArgs_1308_; lean_object* v_srcDir_1309_; lean_object* v_buildDir_1310_; lean_object* v_leanLibDir_1311_; lean_object* v_nativeLibDir_1312_; lean_object* v_binDir_1313_; lean_object* v_irDir_1314_; lean_object* v_releaseRepo_1315_; lean_object* v_buildArchive_1316_; uint8_t v_preferReleaseBuild_1317_; lean_object* v_testDriver_1318_; lean_object* v_testDriverArgs_1319_; lean_object* v_lintDriver_1320_; lean_object* v_lintDriverArgs_1321_; lean_object* v_version_1322_; lean_object* v_versionTags_1323_; lean_object* v_description_1324_; lean_object* v_keywords_1325_; lean_object* v_homepage_1326_; lean_object* v_license_1327_; lean_object* v_licenseFiles_1328_; lean_object* v_readmeFile_1329_; uint8_t v_reservoir_1330_; lean_object* v_enableArtifactCache_x3f_1331_; lean_object* v_restoreAllArtifacts_x3f_1332_; uint8_t v_libPrefixOnWindows_1333_; uint8_t v_allowImportAll_1334_; lean_object* v_builtinLint_x3f_1335_; lean_object* v_checks_1336_; uint8_t v_fixedToolchain_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1345_; 
v_toWorkspaceConfig_1303_ = lean_ctor_get(v_cfg_1302_, 0);
v_toLeanConfig_1304_ = lean_ctor_get(v_cfg_1302_, 1);
v_bootstrap_1305_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28);
v_extraDepTargets_1306_ = lean_ctor_get(v_cfg_1302_, 2);
v_precompileModules_1307_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1308_ = lean_ctor_get(v_cfg_1302_, 3);
v_srcDir_1309_ = lean_ctor_get(v_cfg_1302_, 4);
v_buildDir_1310_ = lean_ctor_get(v_cfg_1302_, 5);
v_leanLibDir_1311_ = lean_ctor_get(v_cfg_1302_, 6);
v_nativeLibDir_1312_ = lean_ctor_get(v_cfg_1302_, 7);
v_binDir_1313_ = lean_ctor_get(v_cfg_1302_, 8);
v_irDir_1314_ = lean_ctor_get(v_cfg_1302_, 9);
v_releaseRepo_1315_ = lean_ctor_get(v_cfg_1302_, 10);
v_buildArchive_1316_ = lean_ctor_get(v_cfg_1302_, 11);
v_preferReleaseBuild_1317_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28 + 2);
v_testDriver_1318_ = lean_ctor_get(v_cfg_1302_, 12);
v_testDriverArgs_1319_ = lean_ctor_get(v_cfg_1302_, 13);
v_lintDriver_1320_ = lean_ctor_get(v_cfg_1302_, 14);
v_lintDriverArgs_1321_ = lean_ctor_get(v_cfg_1302_, 15);
v_version_1322_ = lean_ctor_get(v_cfg_1302_, 16);
v_versionTags_1323_ = lean_ctor_get(v_cfg_1302_, 17);
v_description_1324_ = lean_ctor_get(v_cfg_1302_, 18);
v_keywords_1325_ = lean_ctor_get(v_cfg_1302_, 19);
v_homepage_1326_ = lean_ctor_get(v_cfg_1302_, 20);
v_license_1327_ = lean_ctor_get(v_cfg_1302_, 21);
v_licenseFiles_1328_ = lean_ctor_get(v_cfg_1302_, 22);
v_readmeFile_1329_ = lean_ctor_get(v_cfg_1302_, 23);
v_reservoir_1330_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1331_ = lean_ctor_get(v_cfg_1302_, 24);
v_restoreAllArtifacts_x3f_1332_ = lean_ctor_get(v_cfg_1302_, 25);
v_libPrefixOnWindows_1333_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28 + 4);
v_allowImportAll_1334_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1335_ = lean_ctor_get(v_cfg_1302_, 26);
v_checks_1336_ = lean_ctor_get(v_cfg_1302_, 27);
v_fixedToolchain_1337_ = lean_ctor_get_uint8(v_cfg_1302_, sizeof(void*)*28 + 6);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_cfg_1302_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1339_ = v_cfg_1302_;
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_checks_1336_);
lean_inc(v_builtinLint_x3f_1335_);
lean_inc(v_restoreAllArtifacts_x3f_1332_);
lean_inc(v_enableArtifactCache_x3f_1331_);
lean_inc(v_readmeFile_1329_);
lean_inc(v_licenseFiles_1328_);
lean_inc(v_license_1327_);
lean_inc(v_homepage_1326_);
lean_inc(v_keywords_1325_);
lean_inc(v_description_1324_);
lean_inc(v_versionTags_1323_);
lean_inc(v_version_1322_);
lean_inc(v_lintDriverArgs_1321_);
lean_inc(v_lintDriver_1320_);
lean_inc(v_testDriverArgs_1319_);
lean_inc(v_testDriver_1318_);
lean_inc(v_buildArchive_1316_);
lean_inc(v_releaseRepo_1315_);
lean_inc(v_irDir_1314_);
lean_inc(v_binDir_1313_);
lean_inc(v_nativeLibDir_1312_);
lean_inc(v_leanLibDir_1311_);
lean_inc(v_buildDir_1310_);
lean_inc(v_srcDir_1309_);
lean_inc(v_moreGlobalServerArgs_1308_);
lean_inc(v_extraDepTargets_1306_);
lean_inc(v_toLeanConfig_1304_);
lean_inc(v_toWorkspaceConfig_1303_);
lean_dec(v_cfg_1302_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_apply_1(v_f_1301_, v_releaseRepo_1315_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 10, v___x_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_toWorkspaceConfig_1303_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_toLeanConfig_1304_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_extraDepTargets_1306_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_moreGlobalServerArgs_1308_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_srcDir_1309_);
lean_ctor_set(v_reuseFailAlloc_1344_, 5, v_buildDir_1310_);
lean_ctor_set(v_reuseFailAlloc_1344_, 6, v_leanLibDir_1311_);
lean_ctor_set(v_reuseFailAlloc_1344_, 7, v_nativeLibDir_1312_);
lean_ctor_set(v_reuseFailAlloc_1344_, 8, v_binDir_1313_);
lean_ctor_set(v_reuseFailAlloc_1344_, 9, v_irDir_1314_);
lean_ctor_set(v_reuseFailAlloc_1344_, 10, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1344_, 11, v_buildArchive_1316_);
lean_ctor_set(v_reuseFailAlloc_1344_, 12, v_testDriver_1318_);
lean_ctor_set(v_reuseFailAlloc_1344_, 13, v_testDriverArgs_1319_);
lean_ctor_set(v_reuseFailAlloc_1344_, 14, v_lintDriver_1320_);
lean_ctor_set(v_reuseFailAlloc_1344_, 15, v_lintDriverArgs_1321_);
lean_ctor_set(v_reuseFailAlloc_1344_, 16, v_version_1322_);
lean_ctor_set(v_reuseFailAlloc_1344_, 17, v_versionTags_1323_);
lean_ctor_set(v_reuseFailAlloc_1344_, 18, v_description_1324_);
lean_ctor_set(v_reuseFailAlloc_1344_, 19, v_keywords_1325_);
lean_ctor_set(v_reuseFailAlloc_1344_, 20, v_homepage_1326_);
lean_ctor_set(v_reuseFailAlloc_1344_, 21, v_license_1327_);
lean_ctor_set(v_reuseFailAlloc_1344_, 22, v_licenseFiles_1328_);
lean_ctor_set(v_reuseFailAlloc_1344_, 23, v_readmeFile_1329_);
lean_ctor_set(v_reuseFailAlloc_1344_, 24, v_enableArtifactCache_x3f_1331_);
lean_ctor_set(v_reuseFailAlloc_1344_, 25, v_restoreAllArtifacts_x3f_1332_);
lean_ctor_set(v_reuseFailAlloc_1344_, 26, v_builtinLint_x3f_1335_);
lean_ctor_set(v_reuseFailAlloc_1344_, 27, v_checks_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28, v_bootstrap_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28 + 1, v_precompileModules_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28 + 3, v_reservoir_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28 + 5, v_allowImportAll_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*28 + 6, v_fixedToolchain_1337_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3(lean_object* v_x_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___lam__3___boxed(lean_object* v_x_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lake_PackageConfig_releaseRepo___proj___lam__3(v_x_1348_);
lean_dec_ref(v_x_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1359_, lean_object* v_n_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___closed__4));
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1362_, lean_object* v_n_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1362_, v_n_1363_);
lean_dec(v_n_1363_);
lean_dec(v_p_1362_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1365_, lean_object* v_n_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1365_, v_n_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1368_, lean_object* v_n_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1368_, v_n_1369_);
lean_dec(v_n_1369_);
lean_dec(v_p_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1371_, lean_object* v_n_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1371_, v_n_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1374_, lean_object* v_n_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1374_, v_n_1375_);
lean_dec(v_n_1375_);
lean_dec(v_p_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0(lean_object* v_cfg_1377_){
_start:
{
lean_object* v_buildArchive_1378_; 
v_buildArchive_1378_ = lean_ctor_get(v_cfg_1377_, 11);
lean_inc(v_buildArchive_1378_);
return v_buildArchive_1378_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__0___boxed(lean_object* v_cfg_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lake_PackageConfig_buildArchive___proj___lam__0(v_cfg_1379_);
lean_dec_ref(v_cfg_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__1(lean_object* v_val_1381_, lean_object* v_cfg_1382_){
_start:
{
lean_object* v_toWorkspaceConfig_1383_; lean_object* v_toLeanConfig_1384_; uint8_t v_bootstrap_1385_; lean_object* v_extraDepTargets_1386_; uint8_t v_precompileModules_1387_; lean_object* v_moreGlobalServerArgs_1388_; lean_object* v_srcDir_1389_; lean_object* v_buildDir_1390_; lean_object* v_leanLibDir_1391_; lean_object* v_nativeLibDir_1392_; lean_object* v_binDir_1393_; lean_object* v_irDir_1394_; lean_object* v_releaseRepo_1395_; uint8_t v_preferReleaseBuild_1396_; lean_object* v_testDriver_1397_; lean_object* v_testDriverArgs_1398_; lean_object* v_lintDriver_1399_; lean_object* v_lintDriverArgs_1400_; lean_object* v_version_1401_; lean_object* v_versionTags_1402_; lean_object* v_description_1403_; lean_object* v_keywords_1404_; lean_object* v_homepage_1405_; lean_object* v_license_1406_; lean_object* v_licenseFiles_1407_; lean_object* v_readmeFile_1408_; uint8_t v_reservoir_1409_; lean_object* v_enableArtifactCache_x3f_1410_; lean_object* v_restoreAllArtifacts_x3f_1411_; uint8_t v_libPrefixOnWindows_1412_; uint8_t v_allowImportAll_1413_; lean_object* v_builtinLint_x3f_1414_; lean_object* v_checks_1415_; uint8_t v_fixedToolchain_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_toWorkspaceConfig_1383_ = lean_ctor_get(v_cfg_1382_, 0);
v_toLeanConfig_1384_ = lean_ctor_get(v_cfg_1382_, 1);
v_bootstrap_1385_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28);
v_extraDepTargets_1386_ = lean_ctor_get(v_cfg_1382_, 2);
v_precompileModules_1387_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1388_ = lean_ctor_get(v_cfg_1382_, 3);
v_srcDir_1389_ = lean_ctor_get(v_cfg_1382_, 4);
v_buildDir_1390_ = lean_ctor_get(v_cfg_1382_, 5);
v_leanLibDir_1391_ = lean_ctor_get(v_cfg_1382_, 6);
v_nativeLibDir_1392_ = lean_ctor_get(v_cfg_1382_, 7);
v_binDir_1393_ = lean_ctor_get(v_cfg_1382_, 8);
v_irDir_1394_ = lean_ctor_get(v_cfg_1382_, 9);
v_releaseRepo_1395_ = lean_ctor_get(v_cfg_1382_, 10);
v_preferReleaseBuild_1396_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28 + 2);
v_testDriver_1397_ = lean_ctor_get(v_cfg_1382_, 12);
v_testDriverArgs_1398_ = lean_ctor_get(v_cfg_1382_, 13);
v_lintDriver_1399_ = lean_ctor_get(v_cfg_1382_, 14);
v_lintDriverArgs_1400_ = lean_ctor_get(v_cfg_1382_, 15);
v_version_1401_ = lean_ctor_get(v_cfg_1382_, 16);
v_versionTags_1402_ = lean_ctor_get(v_cfg_1382_, 17);
v_description_1403_ = lean_ctor_get(v_cfg_1382_, 18);
v_keywords_1404_ = lean_ctor_get(v_cfg_1382_, 19);
v_homepage_1405_ = lean_ctor_get(v_cfg_1382_, 20);
v_license_1406_ = lean_ctor_get(v_cfg_1382_, 21);
v_licenseFiles_1407_ = lean_ctor_get(v_cfg_1382_, 22);
v_readmeFile_1408_ = lean_ctor_get(v_cfg_1382_, 23);
v_reservoir_1409_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1410_ = lean_ctor_get(v_cfg_1382_, 24);
v_restoreAllArtifacts_x3f_1411_ = lean_ctor_get(v_cfg_1382_, 25);
v_libPrefixOnWindows_1412_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28 + 4);
v_allowImportAll_1413_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1414_ = lean_ctor_get(v_cfg_1382_, 26);
v_checks_1415_ = lean_ctor_get(v_cfg_1382_, 27);
v_fixedToolchain_1416_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*28 + 6);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_cfg_1382_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_cfg_1382_, 11);
lean_dec(v_unused_1424_);
v___x_1418_ = v_cfg_1382_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_checks_1415_);
lean_inc(v_builtinLint_x3f_1414_);
lean_inc(v_restoreAllArtifacts_x3f_1411_);
lean_inc(v_enableArtifactCache_x3f_1410_);
lean_inc(v_readmeFile_1408_);
lean_inc(v_licenseFiles_1407_);
lean_inc(v_license_1406_);
lean_inc(v_homepage_1405_);
lean_inc(v_keywords_1404_);
lean_inc(v_description_1403_);
lean_inc(v_versionTags_1402_);
lean_inc(v_version_1401_);
lean_inc(v_lintDriverArgs_1400_);
lean_inc(v_lintDriver_1399_);
lean_inc(v_testDriverArgs_1398_);
lean_inc(v_testDriver_1397_);
lean_inc(v_releaseRepo_1395_);
lean_inc(v_irDir_1394_);
lean_inc(v_binDir_1393_);
lean_inc(v_nativeLibDir_1392_);
lean_inc(v_leanLibDir_1391_);
lean_inc(v_buildDir_1390_);
lean_inc(v_srcDir_1389_);
lean_inc(v_moreGlobalServerArgs_1388_);
lean_inc(v_extraDepTargets_1386_);
lean_inc(v_toLeanConfig_1384_);
lean_inc(v_toWorkspaceConfig_1383_);
lean_dec(v_cfg_1382_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 11, v_val_1381_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_toWorkspaceConfig_1383_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_toLeanConfig_1384_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_extraDepTargets_1386_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_moreGlobalServerArgs_1388_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_srcDir_1389_);
lean_ctor_set(v_reuseFailAlloc_1422_, 5, v_buildDir_1390_);
lean_ctor_set(v_reuseFailAlloc_1422_, 6, v_leanLibDir_1391_);
lean_ctor_set(v_reuseFailAlloc_1422_, 7, v_nativeLibDir_1392_);
lean_ctor_set(v_reuseFailAlloc_1422_, 8, v_binDir_1393_);
lean_ctor_set(v_reuseFailAlloc_1422_, 9, v_irDir_1394_);
lean_ctor_set(v_reuseFailAlloc_1422_, 10, v_releaseRepo_1395_);
lean_ctor_set(v_reuseFailAlloc_1422_, 11, v_val_1381_);
lean_ctor_set(v_reuseFailAlloc_1422_, 12, v_testDriver_1397_);
lean_ctor_set(v_reuseFailAlloc_1422_, 13, v_testDriverArgs_1398_);
lean_ctor_set(v_reuseFailAlloc_1422_, 14, v_lintDriver_1399_);
lean_ctor_set(v_reuseFailAlloc_1422_, 15, v_lintDriverArgs_1400_);
lean_ctor_set(v_reuseFailAlloc_1422_, 16, v_version_1401_);
lean_ctor_set(v_reuseFailAlloc_1422_, 17, v_versionTags_1402_);
lean_ctor_set(v_reuseFailAlloc_1422_, 18, v_description_1403_);
lean_ctor_set(v_reuseFailAlloc_1422_, 19, v_keywords_1404_);
lean_ctor_set(v_reuseFailAlloc_1422_, 20, v_homepage_1405_);
lean_ctor_set(v_reuseFailAlloc_1422_, 21, v_license_1406_);
lean_ctor_set(v_reuseFailAlloc_1422_, 22, v_licenseFiles_1407_);
lean_ctor_set(v_reuseFailAlloc_1422_, 23, v_readmeFile_1408_);
lean_ctor_set(v_reuseFailAlloc_1422_, 24, v_enableArtifactCache_x3f_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 25, v_restoreAllArtifacts_x3f_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 26, v_builtinLint_x3f_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 27, v_checks_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28, v_bootstrap_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28 + 1, v_precompileModules_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28 + 3, v_reservoir_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28 + 5, v_allowImportAll_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*28 + 6, v_fixedToolchain_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___lam__2(lean_object* v_f_1425_, lean_object* v_cfg_1426_){
_start:
{
lean_object* v_toWorkspaceConfig_1427_; lean_object* v_toLeanConfig_1428_; uint8_t v_bootstrap_1429_; lean_object* v_extraDepTargets_1430_; uint8_t v_precompileModules_1431_; lean_object* v_moreGlobalServerArgs_1432_; lean_object* v_srcDir_1433_; lean_object* v_buildDir_1434_; lean_object* v_leanLibDir_1435_; lean_object* v_nativeLibDir_1436_; lean_object* v_binDir_1437_; lean_object* v_irDir_1438_; lean_object* v_releaseRepo_1439_; lean_object* v_buildArchive_1440_; uint8_t v_preferReleaseBuild_1441_; lean_object* v_testDriver_1442_; lean_object* v_testDriverArgs_1443_; lean_object* v_lintDriver_1444_; lean_object* v_lintDriverArgs_1445_; lean_object* v_version_1446_; lean_object* v_versionTags_1447_; lean_object* v_description_1448_; lean_object* v_keywords_1449_; lean_object* v_homepage_1450_; lean_object* v_license_1451_; lean_object* v_licenseFiles_1452_; lean_object* v_readmeFile_1453_; uint8_t v_reservoir_1454_; lean_object* v_enableArtifactCache_x3f_1455_; lean_object* v_restoreAllArtifacts_x3f_1456_; uint8_t v_libPrefixOnWindows_1457_; uint8_t v_allowImportAll_1458_; lean_object* v_builtinLint_x3f_1459_; lean_object* v_checks_1460_; uint8_t v_fixedToolchain_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_toWorkspaceConfig_1427_ = lean_ctor_get(v_cfg_1426_, 0);
v_toLeanConfig_1428_ = lean_ctor_get(v_cfg_1426_, 1);
v_bootstrap_1429_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28);
v_extraDepTargets_1430_ = lean_ctor_get(v_cfg_1426_, 2);
v_precompileModules_1431_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1432_ = lean_ctor_get(v_cfg_1426_, 3);
v_srcDir_1433_ = lean_ctor_get(v_cfg_1426_, 4);
v_buildDir_1434_ = lean_ctor_get(v_cfg_1426_, 5);
v_leanLibDir_1435_ = lean_ctor_get(v_cfg_1426_, 6);
v_nativeLibDir_1436_ = lean_ctor_get(v_cfg_1426_, 7);
v_binDir_1437_ = lean_ctor_get(v_cfg_1426_, 8);
v_irDir_1438_ = lean_ctor_get(v_cfg_1426_, 9);
v_releaseRepo_1439_ = lean_ctor_get(v_cfg_1426_, 10);
v_buildArchive_1440_ = lean_ctor_get(v_cfg_1426_, 11);
v_preferReleaseBuild_1441_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28 + 2);
v_testDriver_1442_ = lean_ctor_get(v_cfg_1426_, 12);
v_testDriverArgs_1443_ = lean_ctor_get(v_cfg_1426_, 13);
v_lintDriver_1444_ = lean_ctor_get(v_cfg_1426_, 14);
v_lintDriverArgs_1445_ = lean_ctor_get(v_cfg_1426_, 15);
v_version_1446_ = lean_ctor_get(v_cfg_1426_, 16);
v_versionTags_1447_ = lean_ctor_get(v_cfg_1426_, 17);
v_description_1448_ = lean_ctor_get(v_cfg_1426_, 18);
v_keywords_1449_ = lean_ctor_get(v_cfg_1426_, 19);
v_homepage_1450_ = lean_ctor_get(v_cfg_1426_, 20);
v_license_1451_ = lean_ctor_get(v_cfg_1426_, 21);
v_licenseFiles_1452_ = lean_ctor_get(v_cfg_1426_, 22);
v_readmeFile_1453_ = lean_ctor_get(v_cfg_1426_, 23);
v_reservoir_1454_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1455_ = lean_ctor_get(v_cfg_1426_, 24);
v_restoreAllArtifacts_x3f_1456_ = lean_ctor_get(v_cfg_1426_, 25);
v_libPrefixOnWindows_1457_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28 + 4);
v_allowImportAll_1458_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1459_ = lean_ctor_get(v_cfg_1426_, 26);
v_checks_1460_ = lean_ctor_get(v_cfg_1426_, 27);
v_fixedToolchain_1461_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*28 + 6);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_cfg_1426_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v_cfg_1426_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_checks_1460_);
lean_inc(v_builtinLint_x3f_1459_);
lean_inc(v_restoreAllArtifacts_x3f_1456_);
lean_inc(v_enableArtifactCache_x3f_1455_);
lean_inc(v_readmeFile_1453_);
lean_inc(v_licenseFiles_1452_);
lean_inc(v_license_1451_);
lean_inc(v_homepage_1450_);
lean_inc(v_keywords_1449_);
lean_inc(v_description_1448_);
lean_inc(v_versionTags_1447_);
lean_inc(v_version_1446_);
lean_inc(v_lintDriverArgs_1445_);
lean_inc(v_lintDriver_1444_);
lean_inc(v_testDriverArgs_1443_);
lean_inc(v_testDriver_1442_);
lean_inc(v_buildArchive_1440_);
lean_inc(v_releaseRepo_1439_);
lean_inc(v_irDir_1438_);
lean_inc(v_binDir_1437_);
lean_inc(v_nativeLibDir_1436_);
lean_inc(v_leanLibDir_1435_);
lean_inc(v_buildDir_1434_);
lean_inc(v_srcDir_1433_);
lean_inc(v_moreGlobalServerArgs_1432_);
lean_inc(v_extraDepTargets_1430_);
lean_inc(v_toLeanConfig_1428_);
lean_inc(v_toWorkspaceConfig_1427_);
lean_dec(v_cfg_1426_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_apply_1(v_f_1425_, v_buildArchive_1440_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 11, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_toWorkspaceConfig_1427_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_toLeanConfig_1428_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_extraDepTargets_1430_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_moreGlobalServerArgs_1432_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_srcDir_1433_);
lean_ctor_set(v_reuseFailAlloc_1468_, 5, v_buildDir_1434_);
lean_ctor_set(v_reuseFailAlloc_1468_, 6, v_leanLibDir_1435_);
lean_ctor_set(v_reuseFailAlloc_1468_, 7, v_nativeLibDir_1436_);
lean_ctor_set(v_reuseFailAlloc_1468_, 8, v_binDir_1437_);
lean_ctor_set(v_reuseFailAlloc_1468_, 9, v_irDir_1438_);
lean_ctor_set(v_reuseFailAlloc_1468_, 10, v_releaseRepo_1439_);
lean_ctor_set(v_reuseFailAlloc_1468_, 11, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1468_, 12, v_testDriver_1442_);
lean_ctor_set(v_reuseFailAlloc_1468_, 13, v_testDriverArgs_1443_);
lean_ctor_set(v_reuseFailAlloc_1468_, 14, v_lintDriver_1444_);
lean_ctor_set(v_reuseFailAlloc_1468_, 15, v_lintDriverArgs_1445_);
lean_ctor_set(v_reuseFailAlloc_1468_, 16, v_version_1446_);
lean_ctor_set(v_reuseFailAlloc_1468_, 17, v_versionTags_1447_);
lean_ctor_set(v_reuseFailAlloc_1468_, 18, v_description_1448_);
lean_ctor_set(v_reuseFailAlloc_1468_, 19, v_keywords_1449_);
lean_ctor_set(v_reuseFailAlloc_1468_, 20, v_homepage_1450_);
lean_ctor_set(v_reuseFailAlloc_1468_, 21, v_license_1451_);
lean_ctor_set(v_reuseFailAlloc_1468_, 22, v_licenseFiles_1452_);
lean_ctor_set(v_reuseFailAlloc_1468_, 23, v_readmeFile_1453_);
lean_ctor_set(v_reuseFailAlloc_1468_, 24, v_enableArtifactCache_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1468_, 25, v_restoreAllArtifacts_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1468_, 26, v_builtinLint_x3f_1459_);
lean_ctor_set(v_reuseFailAlloc_1468_, 27, v_checks_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28, v_bootstrap_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28 + 1, v_precompileModules_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28 + 3, v_reservoir_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28 + 5, v_allowImportAll_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*28 + 6, v_fixedToolchain_1461_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1478_, lean_object* v_n_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___closed__3));
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1481_, lean_object* v_n_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1481_, v_n_1482_);
lean_dec(v_n_1482_);
lean_dec(v_p_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1484_, lean_object* v_n_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1484_, v_n_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1487_, lean_object* v_n_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1487_, v_n_1488_);
lean_dec(v_n_1488_);
lean_dec(v_p_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1490_, lean_object* v_n_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1490_, v_n_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1493_, lean_object* v_n_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1493_, v_n_1494_);
lean_dec(v_n_1494_);
lean_dec(v_p_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(lean_object* v_cfg_1496_){
_start:
{
uint8_t v_preferReleaseBuild_1497_; 
v_preferReleaseBuild_1497_ = lean_ctor_get_uint8(v_cfg_1496_, sizeof(void*)*28 + 2);
return v_preferReleaseBuild_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0___boxed(lean_object* v_cfg_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__0(v_cfg_1498_);
lean_dec_ref(v_cfg_1498_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(uint8_t v_val_1501_, lean_object* v_cfg_1502_){
_start:
{
lean_object* v_toWorkspaceConfig_1503_; lean_object* v_toLeanConfig_1504_; uint8_t v_bootstrap_1505_; lean_object* v_extraDepTargets_1506_; uint8_t v_precompileModules_1507_; lean_object* v_moreGlobalServerArgs_1508_; lean_object* v_srcDir_1509_; lean_object* v_buildDir_1510_; lean_object* v_leanLibDir_1511_; lean_object* v_nativeLibDir_1512_; lean_object* v_binDir_1513_; lean_object* v_irDir_1514_; lean_object* v_releaseRepo_1515_; lean_object* v_buildArchive_1516_; lean_object* v_testDriver_1517_; lean_object* v_testDriverArgs_1518_; lean_object* v_lintDriver_1519_; lean_object* v_lintDriverArgs_1520_; lean_object* v_version_1521_; lean_object* v_versionTags_1522_; lean_object* v_description_1523_; lean_object* v_keywords_1524_; lean_object* v_homepage_1525_; lean_object* v_license_1526_; lean_object* v_licenseFiles_1527_; lean_object* v_readmeFile_1528_; uint8_t v_reservoir_1529_; lean_object* v_enableArtifactCache_x3f_1530_; lean_object* v_restoreAllArtifacts_x3f_1531_; uint8_t v_libPrefixOnWindows_1532_; uint8_t v_allowImportAll_1533_; lean_object* v_builtinLint_x3f_1534_; lean_object* v_checks_1535_; uint8_t v_fixedToolchain_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_toWorkspaceConfig_1503_ = lean_ctor_get(v_cfg_1502_, 0);
v_toLeanConfig_1504_ = lean_ctor_get(v_cfg_1502_, 1);
v_bootstrap_1505_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*28);
v_extraDepTargets_1506_ = lean_ctor_get(v_cfg_1502_, 2);
v_precompileModules_1507_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1508_ = lean_ctor_get(v_cfg_1502_, 3);
v_srcDir_1509_ = lean_ctor_get(v_cfg_1502_, 4);
v_buildDir_1510_ = lean_ctor_get(v_cfg_1502_, 5);
v_leanLibDir_1511_ = lean_ctor_get(v_cfg_1502_, 6);
v_nativeLibDir_1512_ = lean_ctor_get(v_cfg_1502_, 7);
v_binDir_1513_ = lean_ctor_get(v_cfg_1502_, 8);
v_irDir_1514_ = lean_ctor_get(v_cfg_1502_, 9);
v_releaseRepo_1515_ = lean_ctor_get(v_cfg_1502_, 10);
v_buildArchive_1516_ = lean_ctor_get(v_cfg_1502_, 11);
v_testDriver_1517_ = lean_ctor_get(v_cfg_1502_, 12);
v_testDriverArgs_1518_ = lean_ctor_get(v_cfg_1502_, 13);
v_lintDriver_1519_ = lean_ctor_get(v_cfg_1502_, 14);
v_lintDriverArgs_1520_ = lean_ctor_get(v_cfg_1502_, 15);
v_version_1521_ = lean_ctor_get(v_cfg_1502_, 16);
v_versionTags_1522_ = lean_ctor_get(v_cfg_1502_, 17);
v_description_1523_ = lean_ctor_get(v_cfg_1502_, 18);
v_keywords_1524_ = lean_ctor_get(v_cfg_1502_, 19);
v_homepage_1525_ = lean_ctor_get(v_cfg_1502_, 20);
v_license_1526_ = lean_ctor_get(v_cfg_1502_, 21);
v_licenseFiles_1527_ = lean_ctor_get(v_cfg_1502_, 22);
v_readmeFile_1528_ = lean_ctor_get(v_cfg_1502_, 23);
v_reservoir_1529_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1530_ = lean_ctor_get(v_cfg_1502_, 24);
v_restoreAllArtifacts_x3f_1531_ = lean_ctor_get(v_cfg_1502_, 25);
v_libPrefixOnWindows_1532_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*28 + 4);
v_allowImportAll_1533_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1534_ = lean_ctor_get(v_cfg_1502_, 26);
v_checks_1535_ = lean_ctor_get(v_cfg_1502_, 27);
v_fixedToolchain_1536_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*28 + 6);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_cfg_1502_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v_cfg_1502_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_checks_1535_);
lean_inc(v_builtinLint_x3f_1534_);
lean_inc(v_restoreAllArtifacts_x3f_1531_);
lean_inc(v_enableArtifactCache_x3f_1530_);
lean_inc(v_readmeFile_1528_);
lean_inc(v_licenseFiles_1527_);
lean_inc(v_license_1526_);
lean_inc(v_homepage_1525_);
lean_inc(v_keywords_1524_);
lean_inc(v_description_1523_);
lean_inc(v_versionTags_1522_);
lean_inc(v_version_1521_);
lean_inc(v_lintDriverArgs_1520_);
lean_inc(v_lintDriver_1519_);
lean_inc(v_testDriverArgs_1518_);
lean_inc(v_testDriver_1517_);
lean_inc(v_buildArchive_1516_);
lean_inc(v_releaseRepo_1515_);
lean_inc(v_irDir_1514_);
lean_inc(v_binDir_1513_);
lean_inc(v_nativeLibDir_1512_);
lean_inc(v_leanLibDir_1511_);
lean_inc(v_buildDir_1510_);
lean_inc(v_srcDir_1509_);
lean_inc(v_moreGlobalServerArgs_1508_);
lean_inc(v_extraDepTargets_1506_);
lean_inc(v_toLeanConfig_1504_);
lean_inc(v_toWorkspaceConfig_1503_);
lean_dec(v_cfg_1502_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_toWorkspaceConfig_1503_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_toLeanConfig_1504_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_extraDepTargets_1506_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_moreGlobalServerArgs_1508_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_srcDir_1509_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v_buildDir_1510_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_leanLibDir_1511_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_nativeLibDir_1512_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_binDir_1513_);
lean_ctor_set(v_reuseFailAlloc_1542_, 9, v_irDir_1514_);
lean_ctor_set(v_reuseFailAlloc_1542_, 10, v_releaseRepo_1515_);
lean_ctor_set(v_reuseFailAlloc_1542_, 11, v_buildArchive_1516_);
lean_ctor_set(v_reuseFailAlloc_1542_, 12, v_testDriver_1517_);
lean_ctor_set(v_reuseFailAlloc_1542_, 13, v_testDriverArgs_1518_);
lean_ctor_set(v_reuseFailAlloc_1542_, 14, v_lintDriver_1519_);
lean_ctor_set(v_reuseFailAlloc_1542_, 15, v_lintDriverArgs_1520_);
lean_ctor_set(v_reuseFailAlloc_1542_, 16, v_version_1521_);
lean_ctor_set(v_reuseFailAlloc_1542_, 17, v_versionTags_1522_);
lean_ctor_set(v_reuseFailAlloc_1542_, 18, v_description_1523_);
lean_ctor_set(v_reuseFailAlloc_1542_, 19, v_keywords_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 20, v_homepage_1525_);
lean_ctor_set(v_reuseFailAlloc_1542_, 21, v_license_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 22, v_licenseFiles_1527_);
lean_ctor_set(v_reuseFailAlloc_1542_, 23, v_readmeFile_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 24, v_enableArtifactCache_x3f_1530_);
lean_ctor_set(v_reuseFailAlloc_1542_, 25, v_restoreAllArtifacts_x3f_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 26, v_builtinLint_x3f_1534_);
lean_ctor_set(v_reuseFailAlloc_1542_, 27, v_checks_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*28, v_bootstrap_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*28 + 1, v_precompileModules_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*28 + 3, v_reservoir_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*28 + 5, v_allowImportAll_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*28 + 6, v_fixedToolchain_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*28 + 2, v_val_1501_);
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1___boxed(lean_object* v_val_1544_, lean_object* v_cfg_1545_){
_start:
{
uint8_t v_val_140__boxed_1546_; lean_object* v_res_1547_; 
v_val_140__boxed_1546_ = lean_unbox(v_val_1544_);
v_res_1547_ = l_Lake_PackageConfig_preferReleaseBuild___proj___lam__1(v_val_140__boxed_1546_, v_cfg_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___lam__2(lean_object* v_f_1548_, lean_object* v_cfg_1549_){
_start:
{
lean_object* v_toWorkspaceConfig_1550_; lean_object* v_toLeanConfig_1551_; uint8_t v_bootstrap_1552_; lean_object* v_extraDepTargets_1553_; uint8_t v_precompileModules_1554_; lean_object* v_moreGlobalServerArgs_1555_; lean_object* v_srcDir_1556_; lean_object* v_buildDir_1557_; lean_object* v_leanLibDir_1558_; lean_object* v_nativeLibDir_1559_; lean_object* v_binDir_1560_; lean_object* v_irDir_1561_; lean_object* v_releaseRepo_1562_; lean_object* v_buildArchive_1563_; uint8_t v_preferReleaseBuild_1564_; lean_object* v_testDriver_1565_; lean_object* v_testDriverArgs_1566_; lean_object* v_lintDriver_1567_; lean_object* v_lintDriverArgs_1568_; lean_object* v_version_1569_; lean_object* v_versionTags_1570_; lean_object* v_description_1571_; lean_object* v_keywords_1572_; lean_object* v_homepage_1573_; lean_object* v_license_1574_; lean_object* v_licenseFiles_1575_; lean_object* v_readmeFile_1576_; uint8_t v_reservoir_1577_; lean_object* v_enableArtifactCache_x3f_1578_; lean_object* v_restoreAllArtifacts_x3f_1579_; uint8_t v_libPrefixOnWindows_1580_; uint8_t v_allowImportAll_1581_; lean_object* v_builtinLint_x3f_1582_; lean_object* v_checks_1583_; uint8_t v_fixedToolchain_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1594_; 
v_toWorkspaceConfig_1550_ = lean_ctor_get(v_cfg_1549_, 0);
v_toLeanConfig_1551_ = lean_ctor_get(v_cfg_1549_, 1);
v_bootstrap_1552_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28);
v_extraDepTargets_1553_ = lean_ctor_get(v_cfg_1549_, 2);
v_precompileModules_1554_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1555_ = lean_ctor_get(v_cfg_1549_, 3);
v_srcDir_1556_ = lean_ctor_get(v_cfg_1549_, 4);
v_buildDir_1557_ = lean_ctor_get(v_cfg_1549_, 5);
v_leanLibDir_1558_ = lean_ctor_get(v_cfg_1549_, 6);
v_nativeLibDir_1559_ = lean_ctor_get(v_cfg_1549_, 7);
v_binDir_1560_ = lean_ctor_get(v_cfg_1549_, 8);
v_irDir_1561_ = lean_ctor_get(v_cfg_1549_, 9);
v_releaseRepo_1562_ = lean_ctor_get(v_cfg_1549_, 10);
v_buildArchive_1563_ = lean_ctor_get(v_cfg_1549_, 11);
v_preferReleaseBuild_1564_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28 + 2);
v_testDriver_1565_ = lean_ctor_get(v_cfg_1549_, 12);
v_testDriverArgs_1566_ = lean_ctor_get(v_cfg_1549_, 13);
v_lintDriver_1567_ = lean_ctor_get(v_cfg_1549_, 14);
v_lintDriverArgs_1568_ = lean_ctor_get(v_cfg_1549_, 15);
v_version_1569_ = lean_ctor_get(v_cfg_1549_, 16);
v_versionTags_1570_ = lean_ctor_get(v_cfg_1549_, 17);
v_description_1571_ = lean_ctor_get(v_cfg_1549_, 18);
v_keywords_1572_ = lean_ctor_get(v_cfg_1549_, 19);
v_homepage_1573_ = lean_ctor_get(v_cfg_1549_, 20);
v_license_1574_ = lean_ctor_get(v_cfg_1549_, 21);
v_licenseFiles_1575_ = lean_ctor_get(v_cfg_1549_, 22);
v_readmeFile_1576_ = lean_ctor_get(v_cfg_1549_, 23);
v_reservoir_1577_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1578_ = lean_ctor_get(v_cfg_1549_, 24);
v_restoreAllArtifacts_x3f_1579_ = lean_ctor_get(v_cfg_1549_, 25);
v_libPrefixOnWindows_1580_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28 + 4);
v_allowImportAll_1581_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1582_ = lean_ctor_get(v_cfg_1549_, 26);
v_checks_1583_ = lean_ctor_get(v_cfg_1549_, 27);
v_fixedToolchain_1584_ = lean_ctor_get_uint8(v_cfg_1549_, sizeof(void*)*28 + 6);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_cfg_1549_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1586_ = v_cfg_1549_;
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_checks_1583_);
lean_inc(v_builtinLint_x3f_1582_);
lean_inc(v_restoreAllArtifacts_x3f_1579_);
lean_inc(v_enableArtifactCache_x3f_1578_);
lean_inc(v_readmeFile_1576_);
lean_inc(v_licenseFiles_1575_);
lean_inc(v_license_1574_);
lean_inc(v_homepage_1573_);
lean_inc(v_keywords_1572_);
lean_inc(v_description_1571_);
lean_inc(v_versionTags_1570_);
lean_inc(v_version_1569_);
lean_inc(v_lintDriverArgs_1568_);
lean_inc(v_lintDriver_1567_);
lean_inc(v_testDriverArgs_1566_);
lean_inc(v_testDriver_1565_);
lean_inc(v_buildArchive_1563_);
lean_inc(v_releaseRepo_1562_);
lean_inc(v_irDir_1561_);
lean_inc(v_binDir_1560_);
lean_inc(v_nativeLibDir_1559_);
lean_inc(v_leanLibDir_1558_);
lean_inc(v_buildDir_1557_);
lean_inc(v_srcDir_1556_);
lean_inc(v_moreGlobalServerArgs_1555_);
lean_inc(v_extraDepTargets_1553_);
lean_inc(v_toLeanConfig_1551_);
lean_inc(v_toWorkspaceConfig_1550_);
lean_dec(v_cfg_1549_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = lean_box(v_preferReleaseBuild_1564_);
v___x_1589_ = lean_apply_1(v_f_1548_, v___x_1588_);
if (v_isShared_1587_ == 0)
{
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_toWorkspaceConfig_1550_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_toLeanConfig_1551_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_extraDepTargets_1553_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_moreGlobalServerArgs_1555_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_srcDir_1556_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_buildDir_1557_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_leanLibDir_1558_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_nativeLibDir_1559_);
lean_ctor_set(v_reuseFailAlloc_1593_, 8, v_binDir_1560_);
lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_irDir_1561_);
lean_ctor_set(v_reuseFailAlloc_1593_, 10, v_releaseRepo_1562_);
lean_ctor_set(v_reuseFailAlloc_1593_, 11, v_buildArchive_1563_);
lean_ctor_set(v_reuseFailAlloc_1593_, 12, v_testDriver_1565_);
lean_ctor_set(v_reuseFailAlloc_1593_, 13, v_testDriverArgs_1566_);
lean_ctor_set(v_reuseFailAlloc_1593_, 14, v_lintDriver_1567_);
lean_ctor_set(v_reuseFailAlloc_1593_, 15, v_lintDriverArgs_1568_);
lean_ctor_set(v_reuseFailAlloc_1593_, 16, v_version_1569_);
lean_ctor_set(v_reuseFailAlloc_1593_, 17, v_versionTags_1570_);
lean_ctor_set(v_reuseFailAlloc_1593_, 18, v_description_1571_);
lean_ctor_set(v_reuseFailAlloc_1593_, 19, v_keywords_1572_);
lean_ctor_set(v_reuseFailAlloc_1593_, 20, v_homepage_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 21, v_license_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 22, v_licenseFiles_1575_);
lean_ctor_set(v_reuseFailAlloc_1593_, 23, v_readmeFile_1576_);
lean_ctor_set(v_reuseFailAlloc_1593_, 24, v_enableArtifactCache_x3f_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 25, v_restoreAllArtifacts_x3f_1579_);
lean_ctor_set(v_reuseFailAlloc_1593_, 26, v_builtinLint_x3f_1582_);
lean_ctor_set(v_reuseFailAlloc_1593_, 27, v_checks_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*28, v_bootstrap_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*28 + 1, v_precompileModules_1554_);
v___x_1591_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_unbox(v___x_1589_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*28 + 2, v___x_1592_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*28 + 3, v_reservoir_1577_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1580_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*28 + 5, v_allowImportAll_1581_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*28 + 6, v_fixedToolchain_1584_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1603_, lean_object* v_n_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___closed__3));
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1606_, lean_object* v_n_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1606_, v_n_1607_);
lean_dec(v_n_1607_);
lean_dec(v_p_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1609_, lean_object* v_n_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1609_, v_n_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1612_, lean_object* v_n_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1612_, v_n_1613_);
lean_dec(v_n_1613_);
lean_dec(v_p_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0(lean_object* v_cfg_1615_){
_start:
{
lean_object* v_testDriver_1616_; 
v_testDriver_1616_ = lean_ctor_get(v_cfg_1615_, 12);
lean_inc_ref(v_testDriver_1616_);
return v_testDriver_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__0___boxed(lean_object* v_cfg_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lake_PackageConfig_testDriver___proj___lam__0(v_cfg_1617_);
lean_dec_ref(v_cfg_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__1(lean_object* v_val_1619_, lean_object* v_cfg_1620_){
_start:
{
lean_object* v_toWorkspaceConfig_1621_; lean_object* v_toLeanConfig_1622_; uint8_t v_bootstrap_1623_; lean_object* v_extraDepTargets_1624_; uint8_t v_precompileModules_1625_; lean_object* v_moreGlobalServerArgs_1626_; lean_object* v_srcDir_1627_; lean_object* v_buildDir_1628_; lean_object* v_leanLibDir_1629_; lean_object* v_nativeLibDir_1630_; lean_object* v_binDir_1631_; lean_object* v_irDir_1632_; lean_object* v_releaseRepo_1633_; lean_object* v_buildArchive_1634_; uint8_t v_preferReleaseBuild_1635_; lean_object* v_testDriverArgs_1636_; lean_object* v_lintDriver_1637_; lean_object* v_lintDriverArgs_1638_; lean_object* v_version_1639_; lean_object* v_versionTags_1640_; lean_object* v_description_1641_; lean_object* v_keywords_1642_; lean_object* v_homepage_1643_; lean_object* v_license_1644_; lean_object* v_licenseFiles_1645_; lean_object* v_readmeFile_1646_; uint8_t v_reservoir_1647_; lean_object* v_enableArtifactCache_x3f_1648_; lean_object* v_restoreAllArtifacts_x3f_1649_; uint8_t v_libPrefixOnWindows_1650_; uint8_t v_allowImportAll_1651_; lean_object* v_builtinLint_x3f_1652_; lean_object* v_checks_1653_; uint8_t v_fixedToolchain_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_toWorkspaceConfig_1621_ = lean_ctor_get(v_cfg_1620_, 0);
v_toLeanConfig_1622_ = lean_ctor_get(v_cfg_1620_, 1);
v_bootstrap_1623_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28);
v_extraDepTargets_1624_ = lean_ctor_get(v_cfg_1620_, 2);
v_precompileModules_1625_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1626_ = lean_ctor_get(v_cfg_1620_, 3);
v_srcDir_1627_ = lean_ctor_get(v_cfg_1620_, 4);
v_buildDir_1628_ = lean_ctor_get(v_cfg_1620_, 5);
v_leanLibDir_1629_ = lean_ctor_get(v_cfg_1620_, 6);
v_nativeLibDir_1630_ = lean_ctor_get(v_cfg_1620_, 7);
v_binDir_1631_ = lean_ctor_get(v_cfg_1620_, 8);
v_irDir_1632_ = lean_ctor_get(v_cfg_1620_, 9);
v_releaseRepo_1633_ = lean_ctor_get(v_cfg_1620_, 10);
v_buildArchive_1634_ = lean_ctor_get(v_cfg_1620_, 11);
v_preferReleaseBuild_1635_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28 + 2);
v_testDriverArgs_1636_ = lean_ctor_get(v_cfg_1620_, 13);
v_lintDriver_1637_ = lean_ctor_get(v_cfg_1620_, 14);
v_lintDriverArgs_1638_ = lean_ctor_get(v_cfg_1620_, 15);
v_version_1639_ = lean_ctor_get(v_cfg_1620_, 16);
v_versionTags_1640_ = lean_ctor_get(v_cfg_1620_, 17);
v_description_1641_ = lean_ctor_get(v_cfg_1620_, 18);
v_keywords_1642_ = lean_ctor_get(v_cfg_1620_, 19);
v_homepage_1643_ = lean_ctor_get(v_cfg_1620_, 20);
v_license_1644_ = lean_ctor_get(v_cfg_1620_, 21);
v_licenseFiles_1645_ = lean_ctor_get(v_cfg_1620_, 22);
v_readmeFile_1646_ = lean_ctor_get(v_cfg_1620_, 23);
v_reservoir_1647_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1648_ = lean_ctor_get(v_cfg_1620_, 24);
v_restoreAllArtifacts_x3f_1649_ = lean_ctor_get(v_cfg_1620_, 25);
v_libPrefixOnWindows_1650_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28 + 4);
v_allowImportAll_1651_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1652_ = lean_ctor_get(v_cfg_1620_, 26);
v_checks_1653_ = lean_ctor_get(v_cfg_1620_, 27);
v_fixedToolchain_1654_ = lean_ctor_get_uint8(v_cfg_1620_, sizeof(void*)*28 + 6);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_cfg_1620_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v_cfg_1620_, 12);
lean_dec(v_unused_1662_);
v___x_1656_ = v_cfg_1620_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_checks_1653_);
lean_inc(v_builtinLint_x3f_1652_);
lean_inc(v_restoreAllArtifacts_x3f_1649_);
lean_inc(v_enableArtifactCache_x3f_1648_);
lean_inc(v_readmeFile_1646_);
lean_inc(v_licenseFiles_1645_);
lean_inc(v_license_1644_);
lean_inc(v_homepage_1643_);
lean_inc(v_keywords_1642_);
lean_inc(v_description_1641_);
lean_inc(v_versionTags_1640_);
lean_inc(v_version_1639_);
lean_inc(v_lintDriverArgs_1638_);
lean_inc(v_lintDriver_1637_);
lean_inc(v_testDriverArgs_1636_);
lean_inc(v_buildArchive_1634_);
lean_inc(v_releaseRepo_1633_);
lean_inc(v_irDir_1632_);
lean_inc(v_binDir_1631_);
lean_inc(v_nativeLibDir_1630_);
lean_inc(v_leanLibDir_1629_);
lean_inc(v_buildDir_1628_);
lean_inc(v_srcDir_1627_);
lean_inc(v_moreGlobalServerArgs_1626_);
lean_inc(v_extraDepTargets_1624_);
lean_inc(v_toLeanConfig_1622_);
lean_inc(v_toWorkspaceConfig_1621_);
lean_dec(v_cfg_1620_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 12, v_val_1619_);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_toWorkspaceConfig_1621_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_toLeanConfig_1622_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_extraDepTargets_1624_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_moreGlobalServerArgs_1626_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_srcDir_1627_);
lean_ctor_set(v_reuseFailAlloc_1660_, 5, v_buildDir_1628_);
lean_ctor_set(v_reuseFailAlloc_1660_, 6, v_leanLibDir_1629_);
lean_ctor_set(v_reuseFailAlloc_1660_, 7, v_nativeLibDir_1630_);
lean_ctor_set(v_reuseFailAlloc_1660_, 8, v_binDir_1631_);
lean_ctor_set(v_reuseFailAlloc_1660_, 9, v_irDir_1632_);
lean_ctor_set(v_reuseFailAlloc_1660_, 10, v_releaseRepo_1633_);
lean_ctor_set(v_reuseFailAlloc_1660_, 11, v_buildArchive_1634_);
lean_ctor_set(v_reuseFailAlloc_1660_, 12, v_val_1619_);
lean_ctor_set(v_reuseFailAlloc_1660_, 13, v_testDriverArgs_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 14, v_lintDriver_1637_);
lean_ctor_set(v_reuseFailAlloc_1660_, 15, v_lintDriverArgs_1638_);
lean_ctor_set(v_reuseFailAlloc_1660_, 16, v_version_1639_);
lean_ctor_set(v_reuseFailAlloc_1660_, 17, v_versionTags_1640_);
lean_ctor_set(v_reuseFailAlloc_1660_, 18, v_description_1641_);
lean_ctor_set(v_reuseFailAlloc_1660_, 19, v_keywords_1642_);
lean_ctor_set(v_reuseFailAlloc_1660_, 20, v_homepage_1643_);
lean_ctor_set(v_reuseFailAlloc_1660_, 21, v_license_1644_);
lean_ctor_set(v_reuseFailAlloc_1660_, 22, v_licenseFiles_1645_);
lean_ctor_set(v_reuseFailAlloc_1660_, 23, v_readmeFile_1646_);
lean_ctor_set(v_reuseFailAlloc_1660_, 24, v_enableArtifactCache_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1660_, 25, v_restoreAllArtifacts_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1660_, 26, v_builtinLint_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1660_, 27, v_checks_1653_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28, v_bootstrap_1623_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28 + 1, v_precompileModules_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28 + 3, v_reservoir_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28 + 5, v_allowImportAll_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*28 + 6, v_fixedToolchain_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__2(lean_object* v_f_1663_, lean_object* v_cfg_1664_){
_start:
{
lean_object* v_toWorkspaceConfig_1665_; lean_object* v_toLeanConfig_1666_; uint8_t v_bootstrap_1667_; lean_object* v_extraDepTargets_1668_; uint8_t v_precompileModules_1669_; lean_object* v_moreGlobalServerArgs_1670_; lean_object* v_srcDir_1671_; lean_object* v_buildDir_1672_; lean_object* v_leanLibDir_1673_; lean_object* v_nativeLibDir_1674_; lean_object* v_binDir_1675_; lean_object* v_irDir_1676_; lean_object* v_releaseRepo_1677_; lean_object* v_buildArchive_1678_; uint8_t v_preferReleaseBuild_1679_; lean_object* v_testDriver_1680_; lean_object* v_testDriverArgs_1681_; lean_object* v_lintDriver_1682_; lean_object* v_lintDriverArgs_1683_; lean_object* v_version_1684_; lean_object* v_versionTags_1685_; lean_object* v_description_1686_; lean_object* v_keywords_1687_; lean_object* v_homepage_1688_; lean_object* v_license_1689_; lean_object* v_licenseFiles_1690_; lean_object* v_readmeFile_1691_; uint8_t v_reservoir_1692_; lean_object* v_enableArtifactCache_x3f_1693_; lean_object* v_restoreAllArtifacts_x3f_1694_; uint8_t v_libPrefixOnWindows_1695_; uint8_t v_allowImportAll_1696_; lean_object* v_builtinLint_x3f_1697_; lean_object* v_checks_1698_; uint8_t v_fixedToolchain_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_toWorkspaceConfig_1665_ = lean_ctor_get(v_cfg_1664_, 0);
v_toLeanConfig_1666_ = lean_ctor_get(v_cfg_1664_, 1);
v_bootstrap_1667_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28);
v_extraDepTargets_1668_ = lean_ctor_get(v_cfg_1664_, 2);
v_precompileModules_1669_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1670_ = lean_ctor_get(v_cfg_1664_, 3);
v_srcDir_1671_ = lean_ctor_get(v_cfg_1664_, 4);
v_buildDir_1672_ = lean_ctor_get(v_cfg_1664_, 5);
v_leanLibDir_1673_ = lean_ctor_get(v_cfg_1664_, 6);
v_nativeLibDir_1674_ = lean_ctor_get(v_cfg_1664_, 7);
v_binDir_1675_ = lean_ctor_get(v_cfg_1664_, 8);
v_irDir_1676_ = lean_ctor_get(v_cfg_1664_, 9);
v_releaseRepo_1677_ = lean_ctor_get(v_cfg_1664_, 10);
v_buildArchive_1678_ = lean_ctor_get(v_cfg_1664_, 11);
v_preferReleaseBuild_1679_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28 + 2);
v_testDriver_1680_ = lean_ctor_get(v_cfg_1664_, 12);
v_testDriverArgs_1681_ = lean_ctor_get(v_cfg_1664_, 13);
v_lintDriver_1682_ = lean_ctor_get(v_cfg_1664_, 14);
v_lintDriverArgs_1683_ = lean_ctor_get(v_cfg_1664_, 15);
v_version_1684_ = lean_ctor_get(v_cfg_1664_, 16);
v_versionTags_1685_ = lean_ctor_get(v_cfg_1664_, 17);
v_description_1686_ = lean_ctor_get(v_cfg_1664_, 18);
v_keywords_1687_ = lean_ctor_get(v_cfg_1664_, 19);
v_homepage_1688_ = lean_ctor_get(v_cfg_1664_, 20);
v_license_1689_ = lean_ctor_get(v_cfg_1664_, 21);
v_licenseFiles_1690_ = lean_ctor_get(v_cfg_1664_, 22);
v_readmeFile_1691_ = lean_ctor_get(v_cfg_1664_, 23);
v_reservoir_1692_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1693_ = lean_ctor_get(v_cfg_1664_, 24);
v_restoreAllArtifacts_x3f_1694_ = lean_ctor_get(v_cfg_1664_, 25);
v_libPrefixOnWindows_1695_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28 + 4);
v_allowImportAll_1696_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1697_ = lean_ctor_get(v_cfg_1664_, 26);
v_checks_1698_ = lean_ctor_get(v_cfg_1664_, 27);
v_fixedToolchain_1699_ = lean_ctor_get_uint8(v_cfg_1664_, sizeof(void*)*28 + 6);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_cfg_1664_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v_cfg_1664_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_checks_1698_);
lean_inc(v_builtinLint_x3f_1697_);
lean_inc(v_restoreAllArtifacts_x3f_1694_);
lean_inc(v_enableArtifactCache_x3f_1693_);
lean_inc(v_readmeFile_1691_);
lean_inc(v_licenseFiles_1690_);
lean_inc(v_license_1689_);
lean_inc(v_homepage_1688_);
lean_inc(v_keywords_1687_);
lean_inc(v_description_1686_);
lean_inc(v_versionTags_1685_);
lean_inc(v_version_1684_);
lean_inc(v_lintDriverArgs_1683_);
lean_inc(v_lintDriver_1682_);
lean_inc(v_testDriverArgs_1681_);
lean_inc(v_testDriver_1680_);
lean_inc(v_buildArchive_1678_);
lean_inc(v_releaseRepo_1677_);
lean_inc(v_irDir_1676_);
lean_inc(v_binDir_1675_);
lean_inc(v_nativeLibDir_1674_);
lean_inc(v_leanLibDir_1673_);
lean_inc(v_buildDir_1672_);
lean_inc(v_srcDir_1671_);
lean_inc(v_moreGlobalServerArgs_1670_);
lean_inc(v_extraDepTargets_1668_);
lean_inc(v_toLeanConfig_1666_);
lean_inc(v_toWorkspaceConfig_1665_);
lean_dec(v_cfg_1664_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_apply_1(v_f_1663_, v_testDriver_1680_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 12, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_toWorkspaceConfig_1665_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_toLeanConfig_1666_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_extraDepTargets_1668_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_moreGlobalServerArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_srcDir_1671_);
lean_ctor_set(v_reuseFailAlloc_1706_, 5, v_buildDir_1672_);
lean_ctor_set(v_reuseFailAlloc_1706_, 6, v_leanLibDir_1673_);
lean_ctor_set(v_reuseFailAlloc_1706_, 7, v_nativeLibDir_1674_);
lean_ctor_set(v_reuseFailAlloc_1706_, 8, v_binDir_1675_);
lean_ctor_set(v_reuseFailAlloc_1706_, 9, v_irDir_1676_);
lean_ctor_set(v_reuseFailAlloc_1706_, 10, v_releaseRepo_1677_);
lean_ctor_set(v_reuseFailAlloc_1706_, 11, v_buildArchive_1678_);
lean_ctor_set(v_reuseFailAlloc_1706_, 12, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1706_, 13, v_testDriverArgs_1681_);
lean_ctor_set(v_reuseFailAlloc_1706_, 14, v_lintDriver_1682_);
lean_ctor_set(v_reuseFailAlloc_1706_, 15, v_lintDriverArgs_1683_);
lean_ctor_set(v_reuseFailAlloc_1706_, 16, v_version_1684_);
lean_ctor_set(v_reuseFailAlloc_1706_, 17, v_versionTags_1685_);
lean_ctor_set(v_reuseFailAlloc_1706_, 18, v_description_1686_);
lean_ctor_set(v_reuseFailAlloc_1706_, 19, v_keywords_1687_);
lean_ctor_set(v_reuseFailAlloc_1706_, 20, v_homepage_1688_);
lean_ctor_set(v_reuseFailAlloc_1706_, 21, v_license_1689_);
lean_ctor_set(v_reuseFailAlloc_1706_, 22, v_licenseFiles_1690_);
lean_ctor_set(v_reuseFailAlloc_1706_, 23, v_readmeFile_1691_);
lean_ctor_set(v_reuseFailAlloc_1706_, 24, v_enableArtifactCache_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1706_, 25, v_restoreAllArtifacts_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 26, v_builtinLint_x3f_1697_);
lean_ctor_set(v_reuseFailAlloc_1706_, 27, v_checks_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28, v_bootstrap_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 1, v_precompileModules_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 3, v_reservoir_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 5, v_allowImportAll_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*28 + 6, v_fixedToolchain_1699_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3(lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___lam__3___boxed(lean_object* v_x_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lake_PackageConfig_testDriver___proj___lam__3(v_x_1710_);
lean_dec_ref(v_x_1710_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_1721_, lean_object* v_n_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___closed__4));
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_1724_, lean_object* v_n_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lake_PackageConfig_testDriver___proj(v_p_1724_, v_n_1725_);
lean_dec(v_n_1725_);
lean_dec(v_p_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_1727_, lean_object* v_n_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lake_PackageConfig_testDriver___proj(v_p_1727_, v_n_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_1730_, lean_object* v_n_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_1730_, v_n_1731_);
lean_dec(v_n_1731_);
lean_dec(v_p_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_1733_, lean_object* v_n_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lake_PackageConfig_testDriver___proj(v_p_1733_, v_n_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_1736_, lean_object* v_n_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_1736_, v_n_1737_);
lean_dec(v_n_1737_);
lean_dec(v_p_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0(lean_object* v_cfg_1739_){
_start:
{
lean_object* v_testDriverArgs_1740_; 
v_testDriverArgs_1740_ = lean_ctor_get(v_cfg_1739_, 13);
lean_inc_ref(v_testDriverArgs_1740_);
return v_testDriverArgs_1740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lake_PackageConfig_testDriverArgs___proj___lam__0(v_cfg_1741_);
lean_dec_ref(v_cfg_1741_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__1(lean_object* v_val_1743_, lean_object* v_cfg_1744_){
_start:
{
lean_object* v_toWorkspaceConfig_1745_; lean_object* v_toLeanConfig_1746_; uint8_t v_bootstrap_1747_; lean_object* v_extraDepTargets_1748_; uint8_t v_precompileModules_1749_; lean_object* v_moreGlobalServerArgs_1750_; lean_object* v_srcDir_1751_; lean_object* v_buildDir_1752_; lean_object* v_leanLibDir_1753_; lean_object* v_nativeLibDir_1754_; lean_object* v_binDir_1755_; lean_object* v_irDir_1756_; lean_object* v_releaseRepo_1757_; lean_object* v_buildArchive_1758_; uint8_t v_preferReleaseBuild_1759_; lean_object* v_testDriver_1760_; lean_object* v_lintDriver_1761_; lean_object* v_lintDriverArgs_1762_; lean_object* v_version_1763_; lean_object* v_versionTags_1764_; lean_object* v_description_1765_; lean_object* v_keywords_1766_; lean_object* v_homepage_1767_; lean_object* v_license_1768_; lean_object* v_licenseFiles_1769_; lean_object* v_readmeFile_1770_; uint8_t v_reservoir_1771_; lean_object* v_enableArtifactCache_x3f_1772_; lean_object* v_restoreAllArtifacts_x3f_1773_; uint8_t v_libPrefixOnWindows_1774_; uint8_t v_allowImportAll_1775_; lean_object* v_builtinLint_x3f_1776_; lean_object* v_checks_1777_; uint8_t v_fixedToolchain_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_toWorkspaceConfig_1745_ = lean_ctor_get(v_cfg_1744_, 0);
v_toLeanConfig_1746_ = lean_ctor_get(v_cfg_1744_, 1);
v_bootstrap_1747_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28);
v_extraDepTargets_1748_ = lean_ctor_get(v_cfg_1744_, 2);
v_precompileModules_1749_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1750_ = lean_ctor_get(v_cfg_1744_, 3);
v_srcDir_1751_ = lean_ctor_get(v_cfg_1744_, 4);
v_buildDir_1752_ = lean_ctor_get(v_cfg_1744_, 5);
v_leanLibDir_1753_ = lean_ctor_get(v_cfg_1744_, 6);
v_nativeLibDir_1754_ = lean_ctor_get(v_cfg_1744_, 7);
v_binDir_1755_ = lean_ctor_get(v_cfg_1744_, 8);
v_irDir_1756_ = lean_ctor_get(v_cfg_1744_, 9);
v_releaseRepo_1757_ = lean_ctor_get(v_cfg_1744_, 10);
v_buildArchive_1758_ = lean_ctor_get(v_cfg_1744_, 11);
v_preferReleaseBuild_1759_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28 + 2);
v_testDriver_1760_ = lean_ctor_get(v_cfg_1744_, 12);
v_lintDriver_1761_ = lean_ctor_get(v_cfg_1744_, 14);
v_lintDriverArgs_1762_ = lean_ctor_get(v_cfg_1744_, 15);
v_version_1763_ = lean_ctor_get(v_cfg_1744_, 16);
v_versionTags_1764_ = lean_ctor_get(v_cfg_1744_, 17);
v_description_1765_ = lean_ctor_get(v_cfg_1744_, 18);
v_keywords_1766_ = lean_ctor_get(v_cfg_1744_, 19);
v_homepage_1767_ = lean_ctor_get(v_cfg_1744_, 20);
v_license_1768_ = lean_ctor_get(v_cfg_1744_, 21);
v_licenseFiles_1769_ = lean_ctor_get(v_cfg_1744_, 22);
v_readmeFile_1770_ = lean_ctor_get(v_cfg_1744_, 23);
v_reservoir_1771_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1772_ = lean_ctor_get(v_cfg_1744_, 24);
v_restoreAllArtifacts_x3f_1773_ = lean_ctor_get(v_cfg_1744_, 25);
v_libPrefixOnWindows_1774_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28 + 4);
v_allowImportAll_1775_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1776_ = lean_ctor_get(v_cfg_1744_, 26);
v_checks_1777_ = lean_ctor_get(v_cfg_1744_, 27);
v_fixedToolchain_1778_ = lean_ctor_get_uint8(v_cfg_1744_, sizeof(void*)*28 + 6);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_cfg_1744_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_cfg_1744_, 13);
lean_dec(v_unused_1786_);
v___x_1780_ = v_cfg_1744_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_checks_1777_);
lean_inc(v_builtinLint_x3f_1776_);
lean_inc(v_restoreAllArtifacts_x3f_1773_);
lean_inc(v_enableArtifactCache_x3f_1772_);
lean_inc(v_readmeFile_1770_);
lean_inc(v_licenseFiles_1769_);
lean_inc(v_license_1768_);
lean_inc(v_homepage_1767_);
lean_inc(v_keywords_1766_);
lean_inc(v_description_1765_);
lean_inc(v_versionTags_1764_);
lean_inc(v_version_1763_);
lean_inc(v_lintDriverArgs_1762_);
lean_inc(v_lintDriver_1761_);
lean_inc(v_testDriver_1760_);
lean_inc(v_buildArchive_1758_);
lean_inc(v_releaseRepo_1757_);
lean_inc(v_irDir_1756_);
lean_inc(v_binDir_1755_);
lean_inc(v_nativeLibDir_1754_);
lean_inc(v_leanLibDir_1753_);
lean_inc(v_buildDir_1752_);
lean_inc(v_srcDir_1751_);
lean_inc(v_moreGlobalServerArgs_1750_);
lean_inc(v_extraDepTargets_1748_);
lean_inc(v_toLeanConfig_1746_);
lean_inc(v_toWorkspaceConfig_1745_);
lean_dec(v_cfg_1744_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 13, v_val_1743_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_toWorkspaceConfig_1745_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_toLeanConfig_1746_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_extraDepTargets_1748_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_moreGlobalServerArgs_1750_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_srcDir_1751_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v_buildDir_1752_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_leanLibDir_1753_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_nativeLibDir_1754_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_binDir_1755_);
lean_ctor_set(v_reuseFailAlloc_1784_, 9, v_irDir_1756_);
lean_ctor_set(v_reuseFailAlloc_1784_, 10, v_releaseRepo_1757_);
lean_ctor_set(v_reuseFailAlloc_1784_, 11, v_buildArchive_1758_);
lean_ctor_set(v_reuseFailAlloc_1784_, 12, v_testDriver_1760_);
lean_ctor_set(v_reuseFailAlloc_1784_, 13, v_val_1743_);
lean_ctor_set(v_reuseFailAlloc_1784_, 14, v_lintDriver_1761_);
lean_ctor_set(v_reuseFailAlloc_1784_, 15, v_lintDriverArgs_1762_);
lean_ctor_set(v_reuseFailAlloc_1784_, 16, v_version_1763_);
lean_ctor_set(v_reuseFailAlloc_1784_, 17, v_versionTags_1764_);
lean_ctor_set(v_reuseFailAlloc_1784_, 18, v_description_1765_);
lean_ctor_set(v_reuseFailAlloc_1784_, 19, v_keywords_1766_);
lean_ctor_set(v_reuseFailAlloc_1784_, 20, v_homepage_1767_);
lean_ctor_set(v_reuseFailAlloc_1784_, 21, v_license_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 22, v_licenseFiles_1769_);
lean_ctor_set(v_reuseFailAlloc_1784_, 23, v_readmeFile_1770_);
lean_ctor_set(v_reuseFailAlloc_1784_, 24, v_enableArtifactCache_x3f_1772_);
lean_ctor_set(v_reuseFailAlloc_1784_, 25, v_restoreAllArtifacts_x3f_1773_);
lean_ctor_set(v_reuseFailAlloc_1784_, 26, v_builtinLint_x3f_1776_);
lean_ctor_set(v_reuseFailAlloc_1784_, 27, v_checks_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28, v_bootstrap_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28 + 1, v_precompileModules_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28 + 3, v_reservoir_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28 + 5, v_allowImportAll_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*28 + 6, v_fixedToolchain_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___lam__2(lean_object* v_f_1787_, lean_object* v_cfg_1788_){
_start:
{
lean_object* v_toWorkspaceConfig_1789_; lean_object* v_toLeanConfig_1790_; uint8_t v_bootstrap_1791_; lean_object* v_extraDepTargets_1792_; uint8_t v_precompileModules_1793_; lean_object* v_moreGlobalServerArgs_1794_; lean_object* v_srcDir_1795_; lean_object* v_buildDir_1796_; lean_object* v_leanLibDir_1797_; lean_object* v_nativeLibDir_1798_; lean_object* v_binDir_1799_; lean_object* v_irDir_1800_; lean_object* v_releaseRepo_1801_; lean_object* v_buildArchive_1802_; uint8_t v_preferReleaseBuild_1803_; lean_object* v_testDriver_1804_; lean_object* v_testDriverArgs_1805_; lean_object* v_lintDriver_1806_; lean_object* v_lintDriverArgs_1807_; lean_object* v_version_1808_; lean_object* v_versionTags_1809_; lean_object* v_description_1810_; lean_object* v_keywords_1811_; lean_object* v_homepage_1812_; lean_object* v_license_1813_; lean_object* v_licenseFiles_1814_; lean_object* v_readmeFile_1815_; uint8_t v_reservoir_1816_; lean_object* v_enableArtifactCache_x3f_1817_; lean_object* v_restoreAllArtifacts_x3f_1818_; uint8_t v_libPrefixOnWindows_1819_; uint8_t v_allowImportAll_1820_; lean_object* v_builtinLint_x3f_1821_; lean_object* v_checks_1822_; uint8_t v_fixedToolchain_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1831_; 
v_toWorkspaceConfig_1789_ = lean_ctor_get(v_cfg_1788_, 0);
v_toLeanConfig_1790_ = lean_ctor_get(v_cfg_1788_, 1);
v_bootstrap_1791_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28);
v_extraDepTargets_1792_ = lean_ctor_get(v_cfg_1788_, 2);
v_precompileModules_1793_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1794_ = lean_ctor_get(v_cfg_1788_, 3);
v_srcDir_1795_ = lean_ctor_get(v_cfg_1788_, 4);
v_buildDir_1796_ = lean_ctor_get(v_cfg_1788_, 5);
v_leanLibDir_1797_ = lean_ctor_get(v_cfg_1788_, 6);
v_nativeLibDir_1798_ = lean_ctor_get(v_cfg_1788_, 7);
v_binDir_1799_ = lean_ctor_get(v_cfg_1788_, 8);
v_irDir_1800_ = lean_ctor_get(v_cfg_1788_, 9);
v_releaseRepo_1801_ = lean_ctor_get(v_cfg_1788_, 10);
v_buildArchive_1802_ = lean_ctor_get(v_cfg_1788_, 11);
v_preferReleaseBuild_1803_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28 + 2);
v_testDriver_1804_ = lean_ctor_get(v_cfg_1788_, 12);
v_testDriverArgs_1805_ = lean_ctor_get(v_cfg_1788_, 13);
v_lintDriver_1806_ = lean_ctor_get(v_cfg_1788_, 14);
v_lintDriverArgs_1807_ = lean_ctor_get(v_cfg_1788_, 15);
v_version_1808_ = lean_ctor_get(v_cfg_1788_, 16);
v_versionTags_1809_ = lean_ctor_get(v_cfg_1788_, 17);
v_description_1810_ = lean_ctor_get(v_cfg_1788_, 18);
v_keywords_1811_ = lean_ctor_get(v_cfg_1788_, 19);
v_homepage_1812_ = lean_ctor_get(v_cfg_1788_, 20);
v_license_1813_ = lean_ctor_get(v_cfg_1788_, 21);
v_licenseFiles_1814_ = lean_ctor_get(v_cfg_1788_, 22);
v_readmeFile_1815_ = lean_ctor_get(v_cfg_1788_, 23);
v_reservoir_1816_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1817_ = lean_ctor_get(v_cfg_1788_, 24);
v_restoreAllArtifacts_x3f_1818_ = lean_ctor_get(v_cfg_1788_, 25);
v_libPrefixOnWindows_1819_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28 + 4);
v_allowImportAll_1820_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1821_ = lean_ctor_get(v_cfg_1788_, 26);
v_checks_1822_ = lean_ctor_get(v_cfg_1788_, 27);
v_fixedToolchain_1823_ = lean_ctor_get_uint8(v_cfg_1788_, sizeof(void*)*28 + 6);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_cfg_1788_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1825_ = v_cfg_1788_;
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_checks_1822_);
lean_inc(v_builtinLint_x3f_1821_);
lean_inc(v_restoreAllArtifacts_x3f_1818_);
lean_inc(v_enableArtifactCache_x3f_1817_);
lean_inc(v_readmeFile_1815_);
lean_inc(v_licenseFiles_1814_);
lean_inc(v_license_1813_);
lean_inc(v_homepage_1812_);
lean_inc(v_keywords_1811_);
lean_inc(v_description_1810_);
lean_inc(v_versionTags_1809_);
lean_inc(v_version_1808_);
lean_inc(v_lintDriverArgs_1807_);
lean_inc(v_lintDriver_1806_);
lean_inc(v_testDriverArgs_1805_);
lean_inc(v_testDriver_1804_);
lean_inc(v_buildArchive_1802_);
lean_inc(v_releaseRepo_1801_);
lean_inc(v_irDir_1800_);
lean_inc(v_binDir_1799_);
lean_inc(v_nativeLibDir_1798_);
lean_inc(v_leanLibDir_1797_);
lean_inc(v_buildDir_1796_);
lean_inc(v_srcDir_1795_);
lean_inc(v_moreGlobalServerArgs_1794_);
lean_inc(v_extraDepTargets_1792_);
lean_inc(v_toLeanConfig_1790_);
lean_inc(v_toWorkspaceConfig_1789_);
lean_dec(v_cfg_1788_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_apply_1(v_f_1787_, v_testDriverArgs_1805_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 13, v___x_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_toWorkspaceConfig_1789_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_toLeanConfig_1790_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_extraDepTargets_1792_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v_moreGlobalServerArgs_1794_);
lean_ctor_set(v_reuseFailAlloc_1830_, 4, v_srcDir_1795_);
lean_ctor_set(v_reuseFailAlloc_1830_, 5, v_buildDir_1796_);
lean_ctor_set(v_reuseFailAlloc_1830_, 6, v_leanLibDir_1797_);
lean_ctor_set(v_reuseFailAlloc_1830_, 7, v_nativeLibDir_1798_);
lean_ctor_set(v_reuseFailAlloc_1830_, 8, v_binDir_1799_);
lean_ctor_set(v_reuseFailAlloc_1830_, 9, v_irDir_1800_);
lean_ctor_set(v_reuseFailAlloc_1830_, 10, v_releaseRepo_1801_);
lean_ctor_set(v_reuseFailAlloc_1830_, 11, v_buildArchive_1802_);
lean_ctor_set(v_reuseFailAlloc_1830_, 12, v_testDriver_1804_);
lean_ctor_set(v_reuseFailAlloc_1830_, 13, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1830_, 14, v_lintDriver_1806_);
lean_ctor_set(v_reuseFailAlloc_1830_, 15, v_lintDriverArgs_1807_);
lean_ctor_set(v_reuseFailAlloc_1830_, 16, v_version_1808_);
lean_ctor_set(v_reuseFailAlloc_1830_, 17, v_versionTags_1809_);
lean_ctor_set(v_reuseFailAlloc_1830_, 18, v_description_1810_);
lean_ctor_set(v_reuseFailAlloc_1830_, 19, v_keywords_1811_);
lean_ctor_set(v_reuseFailAlloc_1830_, 20, v_homepage_1812_);
lean_ctor_set(v_reuseFailAlloc_1830_, 21, v_license_1813_);
lean_ctor_set(v_reuseFailAlloc_1830_, 22, v_licenseFiles_1814_);
lean_ctor_set(v_reuseFailAlloc_1830_, 23, v_readmeFile_1815_);
lean_ctor_set(v_reuseFailAlloc_1830_, 24, v_enableArtifactCache_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1830_, 25, v_restoreAllArtifacts_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1830_, 26, v_builtinLint_x3f_1821_);
lean_ctor_set(v_reuseFailAlloc_1830_, 27, v_checks_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28, v_bootstrap_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28 + 1, v_precompileModules_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28 + 3, v_reservoir_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28 + 5, v_allowImportAll_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*28 + 6, v_fixedToolchain_1823_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_1840_, lean_object* v_n_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___closed__3));
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_1843_, lean_object* v_n_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1843_, v_n_1844_);
lean_dec(v_n_1844_);
lean_dec(v_p_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_1846_, lean_object* v_n_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_1846_, v_n_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_1849_, lean_object* v_n_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_1849_, v_n_1850_);
lean_dec(v_n_1850_);
lean_dec(v_p_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0(lean_object* v_cfg_1852_){
_start:
{
lean_object* v_lintDriver_1853_; 
v_lintDriver_1853_ = lean_ctor_get(v_cfg_1852_, 14);
lean_inc_ref(v_lintDriver_1853_);
return v_lintDriver_1853_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__0___boxed(lean_object* v_cfg_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lake_PackageConfig_lintDriver___proj___lam__0(v_cfg_1854_);
lean_dec_ref(v_cfg_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__1(lean_object* v_val_1856_, lean_object* v_cfg_1857_){
_start:
{
lean_object* v_toWorkspaceConfig_1858_; lean_object* v_toLeanConfig_1859_; uint8_t v_bootstrap_1860_; lean_object* v_extraDepTargets_1861_; uint8_t v_precompileModules_1862_; lean_object* v_moreGlobalServerArgs_1863_; lean_object* v_srcDir_1864_; lean_object* v_buildDir_1865_; lean_object* v_leanLibDir_1866_; lean_object* v_nativeLibDir_1867_; lean_object* v_binDir_1868_; lean_object* v_irDir_1869_; lean_object* v_releaseRepo_1870_; lean_object* v_buildArchive_1871_; uint8_t v_preferReleaseBuild_1872_; lean_object* v_testDriver_1873_; lean_object* v_testDriverArgs_1874_; lean_object* v_lintDriverArgs_1875_; lean_object* v_version_1876_; lean_object* v_versionTags_1877_; lean_object* v_description_1878_; lean_object* v_keywords_1879_; lean_object* v_homepage_1880_; lean_object* v_license_1881_; lean_object* v_licenseFiles_1882_; lean_object* v_readmeFile_1883_; uint8_t v_reservoir_1884_; lean_object* v_enableArtifactCache_x3f_1885_; lean_object* v_restoreAllArtifacts_x3f_1886_; uint8_t v_libPrefixOnWindows_1887_; uint8_t v_allowImportAll_1888_; lean_object* v_builtinLint_x3f_1889_; lean_object* v_checks_1890_; uint8_t v_fixedToolchain_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_toWorkspaceConfig_1858_ = lean_ctor_get(v_cfg_1857_, 0);
v_toLeanConfig_1859_ = lean_ctor_get(v_cfg_1857_, 1);
v_bootstrap_1860_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28);
v_extraDepTargets_1861_ = lean_ctor_get(v_cfg_1857_, 2);
v_precompileModules_1862_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1863_ = lean_ctor_get(v_cfg_1857_, 3);
v_srcDir_1864_ = lean_ctor_get(v_cfg_1857_, 4);
v_buildDir_1865_ = lean_ctor_get(v_cfg_1857_, 5);
v_leanLibDir_1866_ = lean_ctor_get(v_cfg_1857_, 6);
v_nativeLibDir_1867_ = lean_ctor_get(v_cfg_1857_, 7);
v_binDir_1868_ = lean_ctor_get(v_cfg_1857_, 8);
v_irDir_1869_ = lean_ctor_get(v_cfg_1857_, 9);
v_releaseRepo_1870_ = lean_ctor_get(v_cfg_1857_, 10);
v_buildArchive_1871_ = lean_ctor_get(v_cfg_1857_, 11);
v_preferReleaseBuild_1872_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28 + 2);
v_testDriver_1873_ = lean_ctor_get(v_cfg_1857_, 12);
v_testDriverArgs_1874_ = lean_ctor_get(v_cfg_1857_, 13);
v_lintDriverArgs_1875_ = lean_ctor_get(v_cfg_1857_, 15);
v_version_1876_ = lean_ctor_get(v_cfg_1857_, 16);
v_versionTags_1877_ = lean_ctor_get(v_cfg_1857_, 17);
v_description_1878_ = lean_ctor_get(v_cfg_1857_, 18);
v_keywords_1879_ = lean_ctor_get(v_cfg_1857_, 19);
v_homepage_1880_ = lean_ctor_get(v_cfg_1857_, 20);
v_license_1881_ = lean_ctor_get(v_cfg_1857_, 21);
v_licenseFiles_1882_ = lean_ctor_get(v_cfg_1857_, 22);
v_readmeFile_1883_ = lean_ctor_get(v_cfg_1857_, 23);
v_reservoir_1884_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1885_ = lean_ctor_get(v_cfg_1857_, 24);
v_restoreAllArtifacts_x3f_1886_ = lean_ctor_get(v_cfg_1857_, 25);
v_libPrefixOnWindows_1887_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28 + 4);
v_allowImportAll_1888_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1889_ = lean_ctor_get(v_cfg_1857_, 26);
v_checks_1890_ = lean_ctor_get(v_cfg_1857_, 27);
v_fixedToolchain_1891_ = lean_ctor_get_uint8(v_cfg_1857_, sizeof(void*)*28 + 6);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_cfg_1857_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_cfg_1857_, 14);
lean_dec(v_unused_1899_);
v___x_1893_ = v_cfg_1857_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_checks_1890_);
lean_inc(v_builtinLint_x3f_1889_);
lean_inc(v_restoreAllArtifacts_x3f_1886_);
lean_inc(v_enableArtifactCache_x3f_1885_);
lean_inc(v_readmeFile_1883_);
lean_inc(v_licenseFiles_1882_);
lean_inc(v_license_1881_);
lean_inc(v_homepage_1880_);
lean_inc(v_keywords_1879_);
lean_inc(v_description_1878_);
lean_inc(v_versionTags_1877_);
lean_inc(v_version_1876_);
lean_inc(v_lintDriverArgs_1875_);
lean_inc(v_testDriverArgs_1874_);
lean_inc(v_testDriver_1873_);
lean_inc(v_buildArchive_1871_);
lean_inc(v_releaseRepo_1870_);
lean_inc(v_irDir_1869_);
lean_inc(v_binDir_1868_);
lean_inc(v_nativeLibDir_1867_);
lean_inc(v_leanLibDir_1866_);
lean_inc(v_buildDir_1865_);
lean_inc(v_srcDir_1864_);
lean_inc(v_moreGlobalServerArgs_1863_);
lean_inc(v_extraDepTargets_1861_);
lean_inc(v_toLeanConfig_1859_);
lean_inc(v_toWorkspaceConfig_1858_);
lean_dec(v_cfg_1857_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 14, v_val_1856_);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_toWorkspaceConfig_1858_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_toLeanConfig_1859_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_extraDepTargets_1861_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_moreGlobalServerArgs_1863_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v_srcDir_1864_);
lean_ctor_set(v_reuseFailAlloc_1897_, 5, v_buildDir_1865_);
lean_ctor_set(v_reuseFailAlloc_1897_, 6, v_leanLibDir_1866_);
lean_ctor_set(v_reuseFailAlloc_1897_, 7, v_nativeLibDir_1867_);
lean_ctor_set(v_reuseFailAlloc_1897_, 8, v_binDir_1868_);
lean_ctor_set(v_reuseFailAlloc_1897_, 9, v_irDir_1869_);
lean_ctor_set(v_reuseFailAlloc_1897_, 10, v_releaseRepo_1870_);
lean_ctor_set(v_reuseFailAlloc_1897_, 11, v_buildArchive_1871_);
lean_ctor_set(v_reuseFailAlloc_1897_, 12, v_testDriver_1873_);
lean_ctor_set(v_reuseFailAlloc_1897_, 13, v_testDriverArgs_1874_);
lean_ctor_set(v_reuseFailAlloc_1897_, 14, v_val_1856_);
lean_ctor_set(v_reuseFailAlloc_1897_, 15, v_lintDriverArgs_1875_);
lean_ctor_set(v_reuseFailAlloc_1897_, 16, v_version_1876_);
lean_ctor_set(v_reuseFailAlloc_1897_, 17, v_versionTags_1877_);
lean_ctor_set(v_reuseFailAlloc_1897_, 18, v_description_1878_);
lean_ctor_set(v_reuseFailAlloc_1897_, 19, v_keywords_1879_);
lean_ctor_set(v_reuseFailAlloc_1897_, 20, v_homepage_1880_);
lean_ctor_set(v_reuseFailAlloc_1897_, 21, v_license_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 22, v_licenseFiles_1882_);
lean_ctor_set(v_reuseFailAlloc_1897_, 23, v_readmeFile_1883_);
lean_ctor_set(v_reuseFailAlloc_1897_, 24, v_enableArtifactCache_x3f_1885_);
lean_ctor_set(v_reuseFailAlloc_1897_, 25, v_restoreAllArtifacts_x3f_1886_);
lean_ctor_set(v_reuseFailAlloc_1897_, 26, v_builtinLint_x3f_1889_);
lean_ctor_set(v_reuseFailAlloc_1897_, 27, v_checks_1890_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28, v_bootstrap_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28 + 1, v_precompileModules_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28 + 3, v_reservoir_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28 + 5, v_allowImportAll_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*28 + 6, v_fixedToolchain_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___lam__2(lean_object* v_f_1900_, lean_object* v_cfg_1901_){
_start:
{
lean_object* v_toWorkspaceConfig_1902_; lean_object* v_toLeanConfig_1903_; uint8_t v_bootstrap_1904_; lean_object* v_extraDepTargets_1905_; uint8_t v_precompileModules_1906_; lean_object* v_moreGlobalServerArgs_1907_; lean_object* v_srcDir_1908_; lean_object* v_buildDir_1909_; lean_object* v_leanLibDir_1910_; lean_object* v_nativeLibDir_1911_; lean_object* v_binDir_1912_; lean_object* v_irDir_1913_; lean_object* v_releaseRepo_1914_; lean_object* v_buildArchive_1915_; uint8_t v_preferReleaseBuild_1916_; lean_object* v_testDriver_1917_; lean_object* v_testDriverArgs_1918_; lean_object* v_lintDriver_1919_; lean_object* v_lintDriverArgs_1920_; lean_object* v_version_1921_; lean_object* v_versionTags_1922_; lean_object* v_description_1923_; lean_object* v_keywords_1924_; lean_object* v_homepage_1925_; lean_object* v_license_1926_; lean_object* v_licenseFiles_1927_; lean_object* v_readmeFile_1928_; uint8_t v_reservoir_1929_; lean_object* v_enableArtifactCache_x3f_1930_; lean_object* v_restoreAllArtifacts_x3f_1931_; uint8_t v_libPrefixOnWindows_1932_; uint8_t v_allowImportAll_1933_; lean_object* v_builtinLint_x3f_1934_; lean_object* v_checks_1935_; uint8_t v_fixedToolchain_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_toWorkspaceConfig_1902_ = lean_ctor_get(v_cfg_1901_, 0);
v_toLeanConfig_1903_ = lean_ctor_get(v_cfg_1901_, 1);
v_bootstrap_1904_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28);
v_extraDepTargets_1905_ = lean_ctor_get(v_cfg_1901_, 2);
v_precompileModules_1906_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1907_ = lean_ctor_get(v_cfg_1901_, 3);
v_srcDir_1908_ = lean_ctor_get(v_cfg_1901_, 4);
v_buildDir_1909_ = lean_ctor_get(v_cfg_1901_, 5);
v_leanLibDir_1910_ = lean_ctor_get(v_cfg_1901_, 6);
v_nativeLibDir_1911_ = lean_ctor_get(v_cfg_1901_, 7);
v_binDir_1912_ = lean_ctor_get(v_cfg_1901_, 8);
v_irDir_1913_ = lean_ctor_get(v_cfg_1901_, 9);
v_releaseRepo_1914_ = lean_ctor_get(v_cfg_1901_, 10);
v_buildArchive_1915_ = lean_ctor_get(v_cfg_1901_, 11);
v_preferReleaseBuild_1916_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28 + 2);
v_testDriver_1917_ = lean_ctor_get(v_cfg_1901_, 12);
v_testDriverArgs_1918_ = lean_ctor_get(v_cfg_1901_, 13);
v_lintDriver_1919_ = lean_ctor_get(v_cfg_1901_, 14);
v_lintDriverArgs_1920_ = lean_ctor_get(v_cfg_1901_, 15);
v_version_1921_ = lean_ctor_get(v_cfg_1901_, 16);
v_versionTags_1922_ = lean_ctor_get(v_cfg_1901_, 17);
v_description_1923_ = lean_ctor_get(v_cfg_1901_, 18);
v_keywords_1924_ = lean_ctor_get(v_cfg_1901_, 19);
v_homepage_1925_ = lean_ctor_get(v_cfg_1901_, 20);
v_license_1926_ = lean_ctor_get(v_cfg_1901_, 21);
v_licenseFiles_1927_ = lean_ctor_get(v_cfg_1901_, 22);
v_readmeFile_1928_ = lean_ctor_get(v_cfg_1901_, 23);
v_reservoir_1929_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1930_ = lean_ctor_get(v_cfg_1901_, 24);
v_restoreAllArtifacts_x3f_1931_ = lean_ctor_get(v_cfg_1901_, 25);
v_libPrefixOnWindows_1932_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28 + 4);
v_allowImportAll_1933_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_1934_ = lean_ctor_get(v_cfg_1901_, 26);
v_checks_1935_ = lean_ctor_get(v_cfg_1901_, 27);
v_fixedToolchain_1936_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*28 + 6);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_cfg_1901_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v_cfg_1901_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_checks_1935_);
lean_inc(v_builtinLint_x3f_1934_);
lean_inc(v_restoreAllArtifacts_x3f_1931_);
lean_inc(v_enableArtifactCache_x3f_1930_);
lean_inc(v_readmeFile_1928_);
lean_inc(v_licenseFiles_1927_);
lean_inc(v_license_1926_);
lean_inc(v_homepage_1925_);
lean_inc(v_keywords_1924_);
lean_inc(v_description_1923_);
lean_inc(v_versionTags_1922_);
lean_inc(v_version_1921_);
lean_inc(v_lintDriverArgs_1920_);
lean_inc(v_lintDriver_1919_);
lean_inc(v_testDriverArgs_1918_);
lean_inc(v_testDriver_1917_);
lean_inc(v_buildArchive_1915_);
lean_inc(v_releaseRepo_1914_);
lean_inc(v_irDir_1913_);
lean_inc(v_binDir_1912_);
lean_inc(v_nativeLibDir_1911_);
lean_inc(v_leanLibDir_1910_);
lean_inc(v_buildDir_1909_);
lean_inc(v_srcDir_1908_);
lean_inc(v_moreGlobalServerArgs_1907_);
lean_inc(v_extraDepTargets_1905_);
lean_inc(v_toLeanConfig_1903_);
lean_inc(v_toWorkspaceConfig_1902_);
lean_dec(v_cfg_1901_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_apply_1(v_f_1900_, v_lintDriver_1919_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 14, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_toWorkspaceConfig_1902_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_toLeanConfig_1903_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_extraDepTargets_1905_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_moreGlobalServerArgs_1907_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_srcDir_1908_);
lean_ctor_set(v_reuseFailAlloc_1943_, 5, v_buildDir_1909_);
lean_ctor_set(v_reuseFailAlloc_1943_, 6, v_leanLibDir_1910_);
lean_ctor_set(v_reuseFailAlloc_1943_, 7, v_nativeLibDir_1911_);
lean_ctor_set(v_reuseFailAlloc_1943_, 8, v_binDir_1912_);
lean_ctor_set(v_reuseFailAlloc_1943_, 9, v_irDir_1913_);
lean_ctor_set(v_reuseFailAlloc_1943_, 10, v_releaseRepo_1914_);
lean_ctor_set(v_reuseFailAlloc_1943_, 11, v_buildArchive_1915_);
lean_ctor_set(v_reuseFailAlloc_1943_, 12, v_testDriver_1917_);
lean_ctor_set(v_reuseFailAlloc_1943_, 13, v_testDriverArgs_1918_);
lean_ctor_set(v_reuseFailAlloc_1943_, 14, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1943_, 15, v_lintDriverArgs_1920_);
lean_ctor_set(v_reuseFailAlloc_1943_, 16, v_version_1921_);
lean_ctor_set(v_reuseFailAlloc_1943_, 17, v_versionTags_1922_);
lean_ctor_set(v_reuseFailAlloc_1943_, 18, v_description_1923_);
lean_ctor_set(v_reuseFailAlloc_1943_, 19, v_keywords_1924_);
lean_ctor_set(v_reuseFailAlloc_1943_, 20, v_homepage_1925_);
lean_ctor_set(v_reuseFailAlloc_1943_, 21, v_license_1926_);
lean_ctor_set(v_reuseFailAlloc_1943_, 22, v_licenseFiles_1927_);
lean_ctor_set(v_reuseFailAlloc_1943_, 23, v_readmeFile_1928_);
lean_ctor_set(v_reuseFailAlloc_1943_, 24, v_enableArtifactCache_x3f_1930_);
lean_ctor_set(v_reuseFailAlloc_1943_, 25, v_restoreAllArtifacts_x3f_1931_);
lean_ctor_set(v_reuseFailAlloc_1943_, 26, v_builtinLint_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1943_, 27, v_checks_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28, v_bootstrap_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28 + 1, v_precompileModules_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28 + 3, v_reservoir_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28 + 5, v_allowImportAll_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*28 + 6, v_fixedToolchain_1936_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_1953_, lean_object* v_n_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___closed__3));
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_1956_, lean_object* v_n_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1956_, v_n_1957_);
lean_dec(v_n_1957_);
lean_dec(v_p_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_1959_, lean_object* v_n_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lake_PackageConfig_lintDriver___proj(v_p_1959_, v_n_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_1962_, lean_object* v_n_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_1962_, v_n_1963_);
lean_dec(v_n_1963_);
lean_dec(v_p_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(lean_object* v_cfg_1965_){
_start:
{
lean_object* v_lintDriverArgs_1966_; 
v_lintDriverArgs_1966_ = lean_ctor_get(v_cfg_1965_, 15);
lean_inc_ref(v_lintDriverArgs_1966_);
return v_lintDriverArgs_1966_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__0___boxed(lean_object* v_cfg_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lake_PackageConfig_lintDriverArgs___proj___lam__0(v_cfg_1967_);
lean_dec_ref(v_cfg_1967_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__1(lean_object* v_val_1969_, lean_object* v_cfg_1970_){
_start:
{
lean_object* v_toWorkspaceConfig_1971_; lean_object* v_toLeanConfig_1972_; uint8_t v_bootstrap_1973_; lean_object* v_extraDepTargets_1974_; uint8_t v_precompileModules_1975_; lean_object* v_moreGlobalServerArgs_1976_; lean_object* v_srcDir_1977_; lean_object* v_buildDir_1978_; lean_object* v_leanLibDir_1979_; lean_object* v_nativeLibDir_1980_; lean_object* v_binDir_1981_; lean_object* v_irDir_1982_; lean_object* v_releaseRepo_1983_; lean_object* v_buildArchive_1984_; uint8_t v_preferReleaseBuild_1985_; lean_object* v_testDriver_1986_; lean_object* v_testDriverArgs_1987_; lean_object* v_lintDriver_1988_; lean_object* v_version_1989_; lean_object* v_versionTags_1990_; lean_object* v_description_1991_; lean_object* v_keywords_1992_; lean_object* v_homepage_1993_; lean_object* v_license_1994_; lean_object* v_licenseFiles_1995_; lean_object* v_readmeFile_1996_; uint8_t v_reservoir_1997_; lean_object* v_enableArtifactCache_x3f_1998_; lean_object* v_restoreAllArtifacts_x3f_1999_; uint8_t v_libPrefixOnWindows_2000_; uint8_t v_allowImportAll_2001_; lean_object* v_builtinLint_x3f_2002_; lean_object* v_checks_2003_; uint8_t v_fixedToolchain_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_toWorkspaceConfig_1971_ = lean_ctor_get(v_cfg_1970_, 0);
v_toLeanConfig_1972_ = lean_ctor_get(v_cfg_1970_, 1);
v_bootstrap_1973_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28);
v_extraDepTargets_1974_ = lean_ctor_get(v_cfg_1970_, 2);
v_precompileModules_1975_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_1976_ = lean_ctor_get(v_cfg_1970_, 3);
v_srcDir_1977_ = lean_ctor_get(v_cfg_1970_, 4);
v_buildDir_1978_ = lean_ctor_get(v_cfg_1970_, 5);
v_leanLibDir_1979_ = lean_ctor_get(v_cfg_1970_, 6);
v_nativeLibDir_1980_ = lean_ctor_get(v_cfg_1970_, 7);
v_binDir_1981_ = lean_ctor_get(v_cfg_1970_, 8);
v_irDir_1982_ = lean_ctor_get(v_cfg_1970_, 9);
v_releaseRepo_1983_ = lean_ctor_get(v_cfg_1970_, 10);
v_buildArchive_1984_ = lean_ctor_get(v_cfg_1970_, 11);
v_preferReleaseBuild_1985_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28 + 2);
v_testDriver_1986_ = lean_ctor_get(v_cfg_1970_, 12);
v_testDriverArgs_1987_ = lean_ctor_get(v_cfg_1970_, 13);
v_lintDriver_1988_ = lean_ctor_get(v_cfg_1970_, 14);
v_version_1989_ = lean_ctor_get(v_cfg_1970_, 16);
v_versionTags_1990_ = lean_ctor_get(v_cfg_1970_, 17);
v_description_1991_ = lean_ctor_get(v_cfg_1970_, 18);
v_keywords_1992_ = lean_ctor_get(v_cfg_1970_, 19);
v_homepage_1993_ = lean_ctor_get(v_cfg_1970_, 20);
v_license_1994_ = lean_ctor_get(v_cfg_1970_, 21);
v_licenseFiles_1995_ = lean_ctor_get(v_cfg_1970_, 22);
v_readmeFile_1996_ = lean_ctor_get(v_cfg_1970_, 23);
v_reservoir_1997_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_1998_ = lean_ctor_get(v_cfg_1970_, 24);
v_restoreAllArtifacts_x3f_1999_ = lean_ctor_get(v_cfg_1970_, 25);
v_libPrefixOnWindows_2000_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28 + 4);
v_allowImportAll_2001_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2002_ = lean_ctor_get(v_cfg_1970_, 26);
v_checks_2003_ = lean_ctor_get(v_cfg_1970_, 27);
v_fixedToolchain_2004_ = lean_ctor_get_uint8(v_cfg_1970_, sizeof(void*)*28 + 6);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_cfg_1970_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_cfg_1970_, 15);
lean_dec(v_unused_2012_);
v___x_2006_ = v_cfg_1970_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_checks_2003_);
lean_inc(v_builtinLint_x3f_2002_);
lean_inc(v_restoreAllArtifacts_x3f_1999_);
lean_inc(v_enableArtifactCache_x3f_1998_);
lean_inc(v_readmeFile_1996_);
lean_inc(v_licenseFiles_1995_);
lean_inc(v_license_1994_);
lean_inc(v_homepage_1993_);
lean_inc(v_keywords_1992_);
lean_inc(v_description_1991_);
lean_inc(v_versionTags_1990_);
lean_inc(v_version_1989_);
lean_inc(v_lintDriver_1988_);
lean_inc(v_testDriverArgs_1987_);
lean_inc(v_testDriver_1986_);
lean_inc(v_buildArchive_1984_);
lean_inc(v_releaseRepo_1983_);
lean_inc(v_irDir_1982_);
lean_inc(v_binDir_1981_);
lean_inc(v_nativeLibDir_1980_);
lean_inc(v_leanLibDir_1979_);
lean_inc(v_buildDir_1978_);
lean_inc(v_srcDir_1977_);
lean_inc(v_moreGlobalServerArgs_1976_);
lean_inc(v_extraDepTargets_1974_);
lean_inc(v_toLeanConfig_1972_);
lean_inc(v_toWorkspaceConfig_1971_);
lean_dec(v_cfg_1970_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 15, v_val_1969_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_toWorkspaceConfig_1971_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_toLeanConfig_1972_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_extraDepTargets_1974_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_moreGlobalServerArgs_1976_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_srcDir_1977_);
lean_ctor_set(v_reuseFailAlloc_2010_, 5, v_buildDir_1978_);
lean_ctor_set(v_reuseFailAlloc_2010_, 6, v_leanLibDir_1979_);
lean_ctor_set(v_reuseFailAlloc_2010_, 7, v_nativeLibDir_1980_);
lean_ctor_set(v_reuseFailAlloc_2010_, 8, v_binDir_1981_);
lean_ctor_set(v_reuseFailAlloc_2010_, 9, v_irDir_1982_);
lean_ctor_set(v_reuseFailAlloc_2010_, 10, v_releaseRepo_1983_);
lean_ctor_set(v_reuseFailAlloc_2010_, 11, v_buildArchive_1984_);
lean_ctor_set(v_reuseFailAlloc_2010_, 12, v_testDriver_1986_);
lean_ctor_set(v_reuseFailAlloc_2010_, 13, v_testDriverArgs_1987_);
lean_ctor_set(v_reuseFailAlloc_2010_, 14, v_lintDriver_1988_);
lean_ctor_set(v_reuseFailAlloc_2010_, 15, v_val_1969_);
lean_ctor_set(v_reuseFailAlloc_2010_, 16, v_version_1989_);
lean_ctor_set(v_reuseFailAlloc_2010_, 17, v_versionTags_1990_);
lean_ctor_set(v_reuseFailAlloc_2010_, 18, v_description_1991_);
lean_ctor_set(v_reuseFailAlloc_2010_, 19, v_keywords_1992_);
lean_ctor_set(v_reuseFailAlloc_2010_, 20, v_homepage_1993_);
lean_ctor_set(v_reuseFailAlloc_2010_, 21, v_license_1994_);
lean_ctor_set(v_reuseFailAlloc_2010_, 22, v_licenseFiles_1995_);
lean_ctor_set(v_reuseFailAlloc_2010_, 23, v_readmeFile_1996_);
lean_ctor_set(v_reuseFailAlloc_2010_, 24, v_enableArtifactCache_x3f_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 25, v_restoreAllArtifacts_x3f_1999_);
lean_ctor_set(v_reuseFailAlloc_2010_, 26, v_builtinLint_x3f_2002_);
lean_ctor_set(v_reuseFailAlloc_2010_, 27, v_checks_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28, v_bootstrap_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28 + 1, v_precompileModules_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28 + 2, v_preferReleaseBuild_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28 + 3, v_reservoir_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28 + 5, v_allowImportAll_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*28 + 6, v_fixedToolchain_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___lam__2(lean_object* v_f_2013_, lean_object* v_cfg_2014_){
_start:
{
lean_object* v_toWorkspaceConfig_2015_; lean_object* v_toLeanConfig_2016_; uint8_t v_bootstrap_2017_; lean_object* v_extraDepTargets_2018_; uint8_t v_precompileModules_2019_; lean_object* v_moreGlobalServerArgs_2020_; lean_object* v_srcDir_2021_; lean_object* v_buildDir_2022_; lean_object* v_leanLibDir_2023_; lean_object* v_nativeLibDir_2024_; lean_object* v_binDir_2025_; lean_object* v_irDir_2026_; lean_object* v_releaseRepo_2027_; lean_object* v_buildArchive_2028_; uint8_t v_preferReleaseBuild_2029_; lean_object* v_testDriver_2030_; lean_object* v_testDriverArgs_2031_; lean_object* v_lintDriver_2032_; lean_object* v_lintDriverArgs_2033_; lean_object* v_version_2034_; lean_object* v_versionTags_2035_; lean_object* v_description_2036_; lean_object* v_keywords_2037_; lean_object* v_homepage_2038_; lean_object* v_license_2039_; lean_object* v_licenseFiles_2040_; lean_object* v_readmeFile_2041_; uint8_t v_reservoir_2042_; lean_object* v_enableArtifactCache_x3f_2043_; lean_object* v_restoreAllArtifacts_x3f_2044_; uint8_t v_libPrefixOnWindows_2045_; uint8_t v_allowImportAll_2046_; lean_object* v_builtinLint_x3f_2047_; lean_object* v_checks_2048_; uint8_t v_fixedToolchain_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
v_toWorkspaceConfig_2015_ = lean_ctor_get(v_cfg_2014_, 0);
v_toLeanConfig_2016_ = lean_ctor_get(v_cfg_2014_, 1);
v_bootstrap_2017_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28);
v_extraDepTargets_2018_ = lean_ctor_get(v_cfg_2014_, 2);
v_precompileModules_2019_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2020_ = lean_ctor_get(v_cfg_2014_, 3);
v_srcDir_2021_ = lean_ctor_get(v_cfg_2014_, 4);
v_buildDir_2022_ = lean_ctor_get(v_cfg_2014_, 5);
v_leanLibDir_2023_ = lean_ctor_get(v_cfg_2014_, 6);
v_nativeLibDir_2024_ = lean_ctor_get(v_cfg_2014_, 7);
v_binDir_2025_ = lean_ctor_get(v_cfg_2014_, 8);
v_irDir_2026_ = lean_ctor_get(v_cfg_2014_, 9);
v_releaseRepo_2027_ = lean_ctor_get(v_cfg_2014_, 10);
v_buildArchive_2028_ = lean_ctor_get(v_cfg_2014_, 11);
v_preferReleaseBuild_2029_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28 + 2);
v_testDriver_2030_ = lean_ctor_get(v_cfg_2014_, 12);
v_testDriverArgs_2031_ = lean_ctor_get(v_cfg_2014_, 13);
v_lintDriver_2032_ = lean_ctor_get(v_cfg_2014_, 14);
v_lintDriverArgs_2033_ = lean_ctor_get(v_cfg_2014_, 15);
v_version_2034_ = lean_ctor_get(v_cfg_2014_, 16);
v_versionTags_2035_ = lean_ctor_get(v_cfg_2014_, 17);
v_description_2036_ = lean_ctor_get(v_cfg_2014_, 18);
v_keywords_2037_ = lean_ctor_get(v_cfg_2014_, 19);
v_homepage_2038_ = lean_ctor_get(v_cfg_2014_, 20);
v_license_2039_ = lean_ctor_get(v_cfg_2014_, 21);
v_licenseFiles_2040_ = lean_ctor_get(v_cfg_2014_, 22);
v_readmeFile_2041_ = lean_ctor_get(v_cfg_2014_, 23);
v_reservoir_2042_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2043_ = lean_ctor_get(v_cfg_2014_, 24);
v_restoreAllArtifacts_x3f_2044_ = lean_ctor_get(v_cfg_2014_, 25);
v_libPrefixOnWindows_2045_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28 + 4);
v_allowImportAll_2046_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2047_ = lean_ctor_get(v_cfg_2014_, 26);
v_checks_2048_ = lean_ctor_get(v_cfg_2014_, 27);
v_fixedToolchain_2049_ = lean_ctor_get_uint8(v_cfg_2014_, sizeof(void*)*28 + 6);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_cfg_2014_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2051_ = v_cfg_2014_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_checks_2048_);
lean_inc(v_builtinLint_x3f_2047_);
lean_inc(v_restoreAllArtifacts_x3f_2044_);
lean_inc(v_enableArtifactCache_x3f_2043_);
lean_inc(v_readmeFile_2041_);
lean_inc(v_licenseFiles_2040_);
lean_inc(v_license_2039_);
lean_inc(v_homepage_2038_);
lean_inc(v_keywords_2037_);
lean_inc(v_description_2036_);
lean_inc(v_versionTags_2035_);
lean_inc(v_version_2034_);
lean_inc(v_lintDriverArgs_2033_);
lean_inc(v_lintDriver_2032_);
lean_inc(v_testDriverArgs_2031_);
lean_inc(v_testDriver_2030_);
lean_inc(v_buildArchive_2028_);
lean_inc(v_releaseRepo_2027_);
lean_inc(v_irDir_2026_);
lean_inc(v_binDir_2025_);
lean_inc(v_nativeLibDir_2024_);
lean_inc(v_leanLibDir_2023_);
lean_inc(v_buildDir_2022_);
lean_inc(v_srcDir_2021_);
lean_inc(v_moreGlobalServerArgs_2020_);
lean_inc(v_extraDepTargets_2018_);
lean_inc(v_toLeanConfig_2016_);
lean_inc(v_toWorkspaceConfig_2015_);
lean_dec(v_cfg_2014_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_apply_1(v_f_2013_, v_lintDriverArgs_2033_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 15, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_toWorkspaceConfig_2015_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_toLeanConfig_2016_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_extraDepTargets_2018_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_moreGlobalServerArgs_2020_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_srcDir_2021_);
lean_ctor_set(v_reuseFailAlloc_2056_, 5, v_buildDir_2022_);
lean_ctor_set(v_reuseFailAlloc_2056_, 6, v_leanLibDir_2023_);
lean_ctor_set(v_reuseFailAlloc_2056_, 7, v_nativeLibDir_2024_);
lean_ctor_set(v_reuseFailAlloc_2056_, 8, v_binDir_2025_);
lean_ctor_set(v_reuseFailAlloc_2056_, 9, v_irDir_2026_);
lean_ctor_set(v_reuseFailAlloc_2056_, 10, v_releaseRepo_2027_);
lean_ctor_set(v_reuseFailAlloc_2056_, 11, v_buildArchive_2028_);
lean_ctor_set(v_reuseFailAlloc_2056_, 12, v_testDriver_2030_);
lean_ctor_set(v_reuseFailAlloc_2056_, 13, v_testDriverArgs_2031_);
lean_ctor_set(v_reuseFailAlloc_2056_, 14, v_lintDriver_2032_);
lean_ctor_set(v_reuseFailAlloc_2056_, 15, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2056_, 16, v_version_2034_);
lean_ctor_set(v_reuseFailAlloc_2056_, 17, v_versionTags_2035_);
lean_ctor_set(v_reuseFailAlloc_2056_, 18, v_description_2036_);
lean_ctor_set(v_reuseFailAlloc_2056_, 19, v_keywords_2037_);
lean_ctor_set(v_reuseFailAlloc_2056_, 20, v_homepage_2038_);
lean_ctor_set(v_reuseFailAlloc_2056_, 21, v_license_2039_);
lean_ctor_set(v_reuseFailAlloc_2056_, 22, v_licenseFiles_2040_);
lean_ctor_set(v_reuseFailAlloc_2056_, 23, v_readmeFile_2041_);
lean_ctor_set(v_reuseFailAlloc_2056_, 24, v_enableArtifactCache_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2056_, 25, v_restoreAllArtifacts_x3f_2044_);
lean_ctor_set(v_reuseFailAlloc_2056_, 26, v_builtinLint_x3f_2047_);
lean_ctor_set(v_reuseFailAlloc_2056_, 27, v_checks_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28, v_bootstrap_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28 + 1, v_precompileModules_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28 + 3, v_reservoir_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28 + 5, v_allowImportAll_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*28 + 6, v_fixedToolchain_2049_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2066_, lean_object* v_n_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___closed__3));
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2069_, lean_object* v_n_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2069_, v_n_2070_);
lean_dec(v_n_2070_);
lean_dec(v_p_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2072_, lean_object* v_n_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2072_, v_n_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2075_, lean_object* v_n_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2075_, v_n_2076_);
lean_dec(v_n_2076_);
lean_dec(v_p_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0(lean_object* v_cfg_2078_){
_start:
{
lean_object* v_version_2079_; 
v_version_2079_ = lean_ctor_get(v_cfg_2078_, 16);
lean_inc_ref(v_version_2079_);
return v_version_2079_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__0___boxed(lean_object* v_cfg_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lake_PackageConfig_version___proj___lam__0(v_cfg_2080_);
lean_dec_ref(v_cfg_2080_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__1(lean_object* v_val_2082_, lean_object* v_cfg_2083_){
_start:
{
lean_object* v_toWorkspaceConfig_2084_; lean_object* v_toLeanConfig_2085_; uint8_t v_bootstrap_2086_; lean_object* v_extraDepTargets_2087_; uint8_t v_precompileModules_2088_; lean_object* v_moreGlobalServerArgs_2089_; lean_object* v_srcDir_2090_; lean_object* v_buildDir_2091_; lean_object* v_leanLibDir_2092_; lean_object* v_nativeLibDir_2093_; lean_object* v_binDir_2094_; lean_object* v_irDir_2095_; lean_object* v_releaseRepo_2096_; lean_object* v_buildArchive_2097_; uint8_t v_preferReleaseBuild_2098_; lean_object* v_testDriver_2099_; lean_object* v_testDriverArgs_2100_; lean_object* v_lintDriver_2101_; lean_object* v_lintDriverArgs_2102_; lean_object* v_versionTags_2103_; lean_object* v_description_2104_; lean_object* v_keywords_2105_; lean_object* v_homepage_2106_; lean_object* v_license_2107_; lean_object* v_licenseFiles_2108_; lean_object* v_readmeFile_2109_; uint8_t v_reservoir_2110_; lean_object* v_enableArtifactCache_x3f_2111_; lean_object* v_restoreAllArtifacts_x3f_2112_; uint8_t v_libPrefixOnWindows_2113_; uint8_t v_allowImportAll_2114_; lean_object* v_builtinLint_x3f_2115_; lean_object* v_checks_2116_; uint8_t v_fixedToolchain_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_toWorkspaceConfig_2084_ = lean_ctor_get(v_cfg_2083_, 0);
v_toLeanConfig_2085_ = lean_ctor_get(v_cfg_2083_, 1);
v_bootstrap_2086_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28);
v_extraDepTargets_2087_ = lean_ctor_get(v_cfg_2083_, 2);
v_precompileModules_2088_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2089_ = lean_ctor_get(v_cfg_2083_, 3);
v_srcDir_2090_ = lean_ctor_get(v_cfg_2083_, 4);
v_buildDir_2091_ = lean_ctor_get(v_cfg_2083_, 5);
v_leanLibDir_2092_ = lean_ctor_get(v_cfg_2083_, 6);
v_nativeLibDir_2093_ = lean_ctor_get(v_cfg_2083_, 7);
v_binDir_2094_ = lean_ctor_get(v_cfg_2083_, 8);
v_irDir_2095_ = lean_ctor_get(v_cfg_2083_, 9);
v_releaseRepo_2096_ = lean_ctor_get(v_cfg_2083_, 10);
v_buildArchive_2097_ = lean_ctor_get(v_cfg_2083_, 11);
v_preferReleaseBuild_2098_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28 + 2);
v_testDriver_2099_ = lean_ctor_get(v_cfg_2083_, 12);
v_testDriverArgs_2100_ = lean_ctor_get(v_cfg_2083_, 13);
v_lintDriver_2101_ = lean_ctor_get(v_cfg_2083_, 14);
v_lintDriverArgs_2102_ = lean_ctor_get(v_cfg_2083_, 15);
v_versionTags_2103_ = lean_ctor_get(v_cfg_2083_, 17);
v_description_2104_ = lean_ctor_get(v_cfg_2083_, 18);
v_keywords_2105_ = lean_ctor_get(v_cfg_2083_, 19);
v_homepage_2106_ = lean_ctor_get(v_cfg_2083_, 20);
v_license_2107_ = lean_ctor_get(v_cfg_2083_, 21);
v_licenseFiles_2108_ = lean_ctor_get(v_cfg_2083_, 22);
v_readmeFile_2109_ = lean_ctor_get(v_cfg_2083_, 23);
v_reservoir_2110_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2111_ = lean_ctor_get(v_cfg_2083_, 24);
v_restoreAllArtifacts_x3f_2112_ = lean_ctor_get(v_cfg_2083_, 25);
v_libPrefixOnWindows_2113_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28 + 4);
v_allowImportAll_2114_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2115_ = lean_ctor_get(v_cfg_2083_, 26);
v_checks_2116_ = lean_ctor_get(v_cfg_2083_, 27);
v_fixedToolchain_2117_ = lean_ctor_get_uint8(v_cfg_2083_, sizeof(void*)*28 + 6);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_cfg_2083_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v_cfg_2083_, 16);
lean_dec(v_unused_2125_);
v___x_2119_ = v_cfg_2083_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_checks_2116_);
lean_inc(v_builtinLint_x3f_2115_);
lean_inc(v_restoreAllArtifacts_x3f_2112_);
lean_inc(v_enableArtifactCache_x3f_2111_);
lean_inc(v_readmeFile_2109_);
lean_inc(v_licenseFiles_2108_);
lean_inc(v_license_2107_);
lean_inc(v_homepage_2106_);
lean_inc(v_keywords_2105_);
lean_inc(v_description_2104_);
lean_inc(v_versionTags_2103_);
lean_inc(v_lintDriverArgs_2102_);
lean_inc(v_lintDriver_2101_);
lean_inc(v_testDriverArgs_2100_);
lean_inc(v_testDriver_2099_);
lean_inc(v_buildArchive_2097_);
lean_inc(v_releaseRepo_2096_);
lean_inc(v_irDir_2095_);
lean_inc(v_binDir_2094_);
lean_inc(v_nativeLibDir_2093_);
lean_inc(v_leanLibDir_2092_);
lean_inc(v_buildDir_2091_);
lean_inc(v_srcDir_2090_);
lean_inc(v_moreGlobalServerArgs_2089_);
lean_inc(v_extraDepTargets_2087_);
lean_inc(v_toLeanConfig_2085_);
lean_inc(v_toWorkspaceConfig_2084_);
lean_dec(v_cfg_2083_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 16, v_val_2082_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_toWorkspaceConfig_2084_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_toLeanConfig_2085_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_extraDepTargets_2087_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_moreGlobalServerArgs_2089_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v_srcDir_2090_);
lean_ctor_set(v_reuseFailAlloc_2123_, 5, v_buildDir_2091_);
lean_ctor_set(v_reuseFailAlloc_2123_, 6, v_leanLibDir_2092_);
lean_ctor_set(v_reuseFailAlloc_2123_, 7, v_nativeLibDir_2093_);
lean_ctor_set(v_reuseFailAlloc_2123_, 8, v_binDir_2094_);
lean_ctor_set(v_reuseFailAlloc_2123_, 9, v_irDir_2095_);
lean_ctor_set(v_reuseFailAlloc_2123_, 10, v_releaseRepo_2096_);
lean_ctor_set(v_reuseFailAlloc_2123_, 11, v_buildArchive_2097_);
lean_ctor_set(v_reuseFailAlloc_2123_, 12, v_testDriver_2099_);
lean_ctor_set(v_reuseFailAlloc_2123_, 13, v_testDriverArgs_2100_);
lean_ctor_set(v_reuseFailAlloc_2123_, 14, v_lintDriver_2101_);
lean_ctor_set(v_reuseFailAlloc_2123_, 15, v_lintDriverArgs_2102_);
lean_ctor_set(v_reuseFailAlloc_2123_, 16, v_val_2082_);
lean_ctor_set(v_reuseFailAlloc_2123_, 17, v_versionTags_2103_);
lean_ctor_set(v_reuseFailAlloc_2123_, 18, v_description_2104_);
lean_ctor_set(v_reuseFailAlloc_2123_, 19, v_keywords_2105_);
lean_ctor_set(v_reuseFailAlloc_2123_, 20, v_homepage_2106_);
lean_ctor_set(v_reuseFailAlloc_2123_, 21, v_license_2107_);
lean_ctor_set(v_reuseFailAlloc_2123_, 22, v_licenseFiles_2108_);
lean_ctor_set(v_reuseFailAlloc_2123_, 23, v_readmeFile_2109_);
lean_ctor_set(v_reuseFailAlloc_2123_, 24, v_enableArtifactCache_x3f_2111_);
lean_ctor_set(v_reuseFailAlloc_2123_, 25, v_restoreAllArtifacts_x3f_2112_);
lean_ctor_set(v_reuseFailAlloc_2123_, 26, v_builtinLint_x3f_2115_);
lean_ctor_set(v_reuseFailAlloc_2123_, 27, v_checks_2116_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28, v_bootstrap_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28 + 1, v_precompileModules_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28 + 3, v_reservoir_2110_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2113_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28 + 5, v_allowImportAll_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*28 + 6, v_fixedToolchain_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__2(lean_object* v_f_2126_, lean_object* v_cfg_2127_){
_start:
{
lean_object* v_toWorkspaceConfig_2128_; lean_object* v_toLeanConfig_2129_; uint8_t v_bootstrap_2130_; lean_object* v_extraDepTargets_2131_; uint8_t v_precompileModules_2132_; lean_object* v_moreGlobalServerArgs_2133_; lean_object* v_srcDir_2134_; lean_object* v_buildDir_2135_; lean_object* v_leanLibDir_2136_; lean_object* v_nativeLibDir_2137_; lean_object* v_binDir_2138_; lean_object* v_irDir_2139_; lean_object* v_releaseRepo_2140_; lean_object* v_buildArchive_2141_; uint8_t v_preferReleaseBuild_2142_; lean_object* v_testDriver_2143_; lean_object* v_testDriverArgs_2144_; lean_object* v_lintDriver_2145_; lean_object* v_lintDriverArgs_2146_; lean_object* v_version_2147_; lean_object* v_versionTags_2148_; lean_object* v_description_2149_; lean_object* v_keywords_2150_; lean_object* v_homepage_2151_; lean_object* v_license_2152_; lean_object* v_licenseFiles_2153_; lean_object* v_readmeFile_2154_; uint8_t v_reservoir_2155_; lean_object* v_enableArtifactCache_x3f_2156_; lean_object* v_restoreAllArtifacts_x3f_2157_; uint8_t v_libPrefixOnWindows_2158_; uint8_t v_allowImportAll_2159_; lean_object* v_builtinLint_x3f_2160_; lean_object* v_checks_2161_; uint8_t v_fixedToolchain_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_toWorkspaceConfig_2128_ = lean_ctor_get(v_cfg_2127_, 0);
v_toLeanConfig_2129_ = lean_ctor_get(v_cfg_2127_, 1);
v_bootstrap_2130_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28);
v_extraDepTargets_2131_ = lean_ctor_get(v_cfg_2127_, 2);
v_precompileModules_2132_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2133_ = lean_ctor_get(v_cfg_2127_, 3);
v_srcDir_2134_ = lean_ctor_get(v_cfg_2127_, 4);
v_buildDir_2135_ = lean_ctor_get(v_cfg_2127_, 5);
v_leanLibDir_2136_ = lean_ctor_get(v_cfg_2127_, 6);
v_nativeLibDir_2137_ = lean_ctor_get(v_cfg_2127_, 7);
v_binDir_2138_ = lean_ctor_get(v_cfg_2127_, 8);
v_irDir_2139_ = lean_ctor_get(v_cfg_2127_, 9);
v_releaseRepo_2140_ = lean_ctor_get(v_cfg_2127_, 10);
v_buildArchive_2141_ = lean_ctor_get(v_cfg_2127_, 11);
v_preferReleaseBuild_2142_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28 + 2);
v_testDriver_2143_ = lean_ctor_get(v_cfg_2127_, 12);
v_testDriverArgs_2144_ = lean_ctor_get(v_cfg_2127_, 13);
v_lintDriver_2145_ = lean_ctor_get(v_cfg_2127_, 14);
v_lintDriverArgs_2146_ = lean_ctor_get(v_cfg_2127_, 15);
v_version_2147_ = lean_ctor_get(v_cfg_2127_, 16);
v_versionTags_2148_ = lean_ctor_get(v_cfg_2127_, 17);
v_description_2149_ = lean_ctor_get(v_cfg_2127_, 18);
v_keywords_2150_ = lean_ctor_get(v_cfg_2127_, 19);
v_homepage_2151_ = lean_ctor_get(v_cfg_2127_, 20);
v_license_2152_ = lean_ctor_get(v_cfg_2127_, 21);
v_licenseFiles_2153_ = lean_ctor_get(v_cfg_2127_, 22);
v_readmeFile_2154_ = lean_ctor_get(v_cfg_2127_, 23);
v_reservoir_2155_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2156_ = lean_ctor_get(v_cfg_2127_, 24);
v_restoreAllArtifacts_x3f_2157_ = lean_ctor_get(v_cfg_2127_, 25);
v_libPrefixOnWindows_2158_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28 + 4);
v_allowImportAll_2159_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2160_ = lean_ctor_get(v_cfg_2127_, 26);
v_checks_2161_ = lean_ctor_get(v_cfg_2127_, 27);
v_fixedToolchain_2162_ = lean_ctor_get_uint8(v_cfg_2127_, sizeof(void*)*28 + 6);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_cfg_2127_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2164_ = v_cfg_2127_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_checks_2161_);
lean_inc(v_builtinLint_x3f_2160_);
lean_inc(v_restoreAllArtifacts_x3f_2157_);
lean_inc(v_enableArtifactCache_x3f_2156_);
lean_inc(v_readmeFile_2154_);
lean_inc(v_licenseFiles_2153_);
lean_inc(v_license_2152_);
lean_inc(v_homepage_2151_);
lean_inc(v_keywords_2150_);
lean_inc(v_description_2149_);
lean_inc(v_versionTags_2148_);
lean_inc(v_version_2147_);
lean_inc(v_lintDriverArgs_2146_);
lean_inc(v_lintDriver_2145_);
lean_inc(v_testDriverArgs_2144_);
lean_inc(v_testDriver_2143_);
lean_inc(v_buildArchive_2141_);
lean_inc(v_releaseRepo_2140_);
lean_inc(v_irDir_2139_);
lean_inc(v_binDir_2138_);
lean_inc(v_nativeLibDir_2137_);
lean_inc(v_leanLibDir_2136_);
lean_inc(v_buildDir_2135_);
lean_inc(v_srcDir_2134_);
lean_inc(v_moreGlobalServerArgs_2133_);
lean_inc(v_extraDepTargets_2131_);
lean_inc(v_toLeanConfig_2129_);
lean_inc(v_toWorkspaceConfig_2128_);
lean_dec(v_cfg_2127_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_apply_1(v_f_2126_, v_version_2147_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 16, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_toWorkspaceConfig_2128_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_toLeanConfig_2129_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_extraDepTargets_2131_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_moreGlobalServerArgs_2133_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_srcDir_2134_);
lean_ctor_set(v_reuseFailAlloc_2169_, 5, v_buildDir_2135_);
lean_ctor_set(v_reuseFailAlloc_2169_, 6, v_leanLibDir_2136_);
lean_ctor_set(v_reuseFailAlloc_2169_, 7, v_nativeLibDir_2137_);
lean_ctor_set(v_reuseFailAlloc_2169_, 8, v_binDir_2138_);
lean_ctor_set(v_reuseFailAlloc_2169_, 9, v_irDir_2139_);
lean_ctor_set(v_reuseFailAlloc_2169_, 10, v_releaseRepo_2140_);
lean_ctor_set(v_reuseFailAlloc_2169_, 11, v_buildArchive_2141_);
lean_ctor_set(v_reuseFailAlloc_2169_, 12, v_testDriver_2143_);
lean_ctor_set(v_reuseFailAlloc_2169_, 13, v_testDriverArgs_2144_);
lean_ctor_set(v_reuseFailAlloc_2169_, 14, v_lintDriver_2145_);
lean_ctor_set(v_reuseFailAlloc_2169_, 15, v_lintDriverArgs_2146_);
lean_ctor_set(v_reuseFailAlloc_2169_, 16, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2169_, 17, v_versionTags_2148_);
lean_ctor_set(v_reuseFailAlloc_2169_, 18, v_description_2149_);
lean_ctor_set(v_reuseFailAlloc_2169_, 19, v_keywords_2150_);
lean_ctor_set(v_reuseFailAlloc_2169_, 20, v_homepage_2151_);
lean_ctor_set(v_reuseFailAlloc_2169_, 21, v_license_2152_);
lean_ctor_set(v_reuseFailAlloc_2169_, 22, v_licenseFiles_2153_);
lean_ctor_set(v_reuseFailAlloc_2169_, 23, v_readmeFile_2154_);
lean_ctor_set(v_reuseFailAlloc_2169_, 24, v_enableArtifactCache_x3f_2156_);
lean_ctor_set(v_reuseFailAlloc_2169_, 25, v_restoreAllArtifacts_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2169_, 26, v_builtinLint_x3f_2160_);
lean_ctor_set(v_reuseFailAlloc_2169_, 27, v_checks_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28, v_bootstrap_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28 + 1, v_precompileModules_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28 + 3, v_reservoir_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28 + 5, v_allowImportAll_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*28 + 6, v_fixedToolchain_2162_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3(lean_object* v_x_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___lam__3___boxed(lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lake_PackageConfig_version___proj___lam__3(v_x_2173_);
lean_dec_ref(v_x_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2184_, lean_object* v_n_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___closed__4));
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2187_, lean_object* v_n_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lake_PackageConfig_version___proj(v_p_2187_, v_n_2188_);
lean_dec(v_n_2188_);
lean_dec(v_p_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2190_, lean_object* v_n_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lake_PackageConfig_version___proj(v_p_2190_, v_n_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2193_, lean_object* v_n_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lake_PackageConfig_version_instConfigField(v_p_2193_, v_n_2194_);
lean_dec(v_n_2194_);
lean_dec(v_p_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0(lean_object* v_cfg_2196_){
_start:
{
lean_object* v_versionTags_2197_; 
v_versionTags_2197_ = lean_ctor_get(v_cfg_2196_, 17);
lean_inc_ref(v_versionTags_2197_);
return v_versionTags_2197_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__0___boxed(lean_object* v_cfg_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lake_PackageConfig_versionTags___proj___lam__0(v_cfg_2198_);
lean_dec_ref(v_cfg_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__1(lean_object* v_val_2200_, lean_object* v_cfg_2201_){
_start:
{
lean_object* v_toWorkspaceConfig_2202_; lean_object* v_toLeanConfig_2203_; uint8_t v_bootstrap_2204_; lean_object* v_extraDepTargets_2205_; uint8_t v_precompileModules_2206_; lean_object* v_moreGlobalServerArgs_2207_; lean_object* v_srcDir_2208_; lean_object* v_buildDir_2209_; lean_object* v_leanLibDir_2210_; lean_object* v_nativeLibDir_2211_; lean_object* v_binDir_2212_; lean_object* v_irDir_2213_; lean_object* v_releaseRepo_2214_; lean_object* v_buildArchive_2215_; uint8_t v_preferReleaseBuild_2216_; lean_object* v_testDriver_2217_; lean_object* v_testDriverArgs_2218_; lean_object* v_lintDriver_2219_; lean_object* v_lintDriverArgs_2220_; lean_object* v_version_2221_; lean_object* v_description_2222_; lean_object* v_keywords_2223_; lean_object* v_homepage_2224_; lean_object* v_license_2225_; lean_object* v_licenseFiles_2226_; lean_object* v_readmeFile_2227_; uint8_t v_reservoir_2228_; lean_object* v_enableArtifactCache_x3f_2229_; lean_object* v_restoreAllArtifacts_x3f_2230_; uint8_t v_libPrefixOnWindows_2231_; uint8_t v_allowImportAll_2232_; lean_object* v_builtinLint_x3f_2233_; lean_object* v_checks_2234_; uint8_t v_fixedToolchain_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_toWorkspaceConfig_2202_ = lean_ctor_get(v_cfg_2201_, 0);
v_toLeanConfig_2203_ = lean_ctor_get(v_cfg_2201_, 1);
v_bootstrap_2204_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28);
v_extraDepTargets_2205_ = lean_ctor_get(v_cfg_2201_, 2);
v_precompileModules_2206_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2207_ = lean_ctor_get(v_cfg_2201_, 3);
v_srcDir_2208_ = lean_ctor_get(v_cfg_2201_, 4);
v_buildDir_2209_ = lean_ctor_get(v_cfg_2201_, 5);
v_leanLibDir_2210_ = lean_ctor_get(v_cfg_2201_, 6);
v_nativeLibDir_2211_ = lean_ctor_get(v_cfg_2201_, 7);
v_binDir_2212_ = lean_ctor_get(v_cfg_2201_, 8);
v_irDir_2213_ = lean_ctor_get(v_cfg_2201_, 9);
v_releaseRepo_2214_ = lean_ctor_get(v_cfg_2201_, 10);
v_buildArchive_2215_ = lean_ctor_get(v_cfg_2201_, 11);
v_preferReleaseBuild_2216_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28 + 2);
v_testDriver_2217_ = lean_ctor_get(v_cfg_2201_, 12);
v_testDriverArgs_2218_ = lean_ctor_get(v_cfg_2201_, 13);
v_lintDriver_2219_ = lean_ctor_get(v_cfg_2201_, 14);
v_lintDriverArgs_2220_ = lean_ctor_get(v_cfg_2201_, 15);
v_version_2221_ = lean_ctor_get(v_cfg_2201_, 16);
v_description_2222_ = lean_ctor_get(v_cfg_2201_, 18);
v_keywords_2223_ = lean_ctor_get(v_cfg_2201_, 19);
v_homepage_2224_ = lean_ctor_get(v_cfg_2201_, 20);
v_license_2225_ = lean_ctor_get(v_cfg_2201_, 21);
v_licenseFiles_2226_ = lean_ctor_get(v_cfg_2201_, 22);
v_readmeFile_2227_ = lean_ctor_get(v_cfg_2201_, 23);
v_reservoir_2228_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2229_ = lean_ctor_get(v_cfg_2201_, 24);
v_restoreAllArtifacts_x3f_2230_ = lean_ctor_get(v_cfg_2201_, 25);
v_libPrefixOnWindows_2231_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28 + 4);
v_allowImportAll_2232_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2233_ = lean_ctor_get(v_cfg_2201_, 26);
v_checks_2234_ = lean_ctor_get(v_cfg_2201_, 27);
v_fixedToolchain_2235_ = lean_ctor_get_uint8(v_cfg_2201_, sizeof(void*)*28 + 6);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_cfg_2201_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_cfg_2201_, 17);
lean_dec(v_unused_2243_);
v___x_2237_ = v_cfg_2201_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_checks_2234_);
lean_inc(v_builtinLint_x3f_2233_);
lean_inc(v_restoreAllArtifacts_x3f_2230_);
lean_inc(v_enableArtifactCache_x3f_2229_);
lean_inc(v_readmeFile_2227_);
lean_inc(v_licenseFiles_2226_);
lean_inc(v_license_2225_);
lean_inc(v_homepage_2224_);
lean_inc(v_keywords_2223_);
lean_inc(v_description_2222_);
lean_inc(v_version_2221_);
lean_inc(v_lintDriverArgs_2220_);
lean_inc(v_lintDriver_2219_);
lean_inc(v_testDriverArgs_2218_);
lean_inc(v_testDriver_2217_);
lean_inc(v_buildArchive_2215_);
lean_inc(v_releaseRepo_2214_);
lean_inc(v_irDir_2213_);
lean_inc(v_binDir_2212_);
lean_inc(v_nativeLibDir_2211_);
lean_inc(v_leanLibDir_2210_);
lean_inc(v_buildDir_2209_);
lean_inc(v_srcDir_2208_);
lean_inc(v_moreGlobalServerArgs_2207_);
lean_inc(v_extraDepTargets_2205_);
lean_inc(v_toLeanConfig_2203_);
lean_inc(v_toWorkspaceConfig_2202_);
lean_dec(v_cfg_2201_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 17, v_val_2200_);
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_toWorkspaceConfig_2202_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_toLeanConfig_2203_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_extraDepTargets_2205_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_moreGlobalServerArgs_2207_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_srcDir_2208_);
lean_ctor_set(v_reuseFailAlloc_2241_, 5, v_buildDir_2209_);
lean_ctor_set(v_reuseFailAlloc_2241_, 6, v_leanLibDir_2210_);
lean_ctor_set(v_reuseFailAlloc_2241_, 7, v_nativeLibDir_2211_);
lean_ctor_set(v_reuseFailAlloc_2241_, 8, v_binDir_2212_);
lean_ctor_set(v_reuseFailAlloc_2241_, 9, v_irDir_2213_);
lean_ctor_set(v_reuseFailAlloc_2241_, 10, v_releaseRepo_2214_);
lean_ctor_set(v_reuseFailAlloc_2241_, 11, v_buildArchive_2215_);
lean_ctor_set(v_reuseFailAlloc_2241_, 12, v_testDriver_2217_);
lean_ctor_set(v_reuseFailAlloc_2241_, 13, v_testDriverArgs_2218_);
lean_ctor_set(v_reuseFailAlloc_2241_, 14, v_lintDriver_2219_);
lean_ctor_set(v_reuseFailAlloc_2241_, 15, v_lintDriverArgs_2220_);
lean_ctor_set(v_reuseFailAlloc_2241_, 16, v_version_2221_);
lean_ctor_set(v_reuseFailAlloc_2241_, 17, v_val_2200_);
lean_ctor_set(v_reuseFailAlloc_2241_, 18, v_description_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 19, v_keywords_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 20, v_homepage_2224_);
lean_ctor_set(v_reuseFailAlloc_2241_, 21, v_license_2225_);
lean_ctor_set(v_reuseFailAlloc_2241_, 22, v_licenseFiles_2226_);
lean_ctor_set(v_reuseFailAlloc_2241_, 23, v_readmeFile_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 24, v_enableArtifactCache_x3f_2229_);
lean_ctor_set(v_reuseFailAlloc_2241_, 25, v_restoreAllArtifacts_x3f_2230_);
lean_ctor_set(v_reuseFailAlloc_2241_, 26, v_builtinLint_x3f_2233_);
lean_ctor_set(v_reuseFailAlloc_2241_, 27, v_checks_2234_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28, v_bootstrap_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28 + 1, v_precompileModules_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28 + 3, v_reservoir_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28 + 5, v_allowImportAll_2232_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*28 + 6, v_fixedToolchain_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__2(lean_object* v_f_2244_, lean_object* v_cfg_2245_){
_start:
{
lean_object* v_toWorkspaceConfig_2246_; lean_object* v_toLeanConfig_2247_; uint8_t v_bootstrap_2248_; lean_object* v_extraDepTargets_2249_; uint8_t v_precompileModules_2250_; lean_object* v_moreGlobalServerArgs_2251_; lean_object* v_srcDir_2252_; lean_object* v_buildDir_2253_; lean_object* v_leanLibDir_2254_; lean_object* v_nativeLibDir_2255_; lean_object* v_binDir_2256_; lean_object* v_irDir_2257_; lean_object* v_releaseRepo_2258_; lean_object* v_buildArchive_2259_; uint8_t v_preferReleaseBuild_2260_; lean_object* v_testDriver_2261_; lean_object* v_testDriverArgs_2262_; lean_object* v_lintDriver_2263_; lean_object* v_lintDriverArgs_2264_; lean_object* v_version_2265_; lean_object* v_versionTags_2266_; lean_object* v_description_2267_; lean_object* v_keywords_2268_; lean_object* v_homepage_2269_; lean_object* v_license_2270_; lean_object* v_licenseFiles_2271_; lean_object* v_readmeFile_2272_; uint8_t v_reservoir_2273_; lean_object* v_enableArtifactCache_x3f_2274_; lean_object* v_restoreAllArtifacts_x3f_2275_; uint8_t v_libPrefixOnWindows_2276_; uint8_t v_allowImportAll_2277_; lean_object* v_builtinLint_x3f_2278_; lean_object* v_checks_2279_; uint8_t v_fixedToolchain_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2288_; 
v_toWorkspaceConfig_2246_ = lean_ctor_get(v_cfg_2245_, 0);
v_toLeanConfig_2247_ = lean_ctor_get(v_cfg_2245_, 1);
v_bootstrap_2248_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28);
v_extraDepTargets_2249_ = lean_ctor_get(v_cfg_2245_, 2);
v_precompileModules_2250_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2251_ = lean_ctor_get(v_cfg_2245_, 3);
v_srcDir_2252_ = lean_ctor_get(v_cfg_2245_, 4);
v_buildDir_2253_ = lean_ctor_get(v_cfg_2245_, 5);
v_leanLibDir_2254_ = lean_ctor_get(v_cfg_2245_, 6);
v_nativeLibDir_2255_ = lean_ctor_get(v_cfg_2245_, 7);
v_binDir_2256_ = lean_ctor_get(v_cfg_2245_, 8);
v_irDir_2257_ = lean_ctor_get(v_cfg_2245_, 9);
v_releaseRepo_2258_ = lean_ctor_get(v_cfg_2245_, 10);
v_buildArchive_2259_ = lean_ctor_get(v_cfg_2245_, 11);
v_preferReleaseBuild_2260_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28 + 2);
v_testDriver_2261_ = lean_ctor_get(v_cfg_2245_, 12);
v_testDriverArgs_2262_ = lean_ctor_get(v_cfg_2245_, 13);
v_lintDriver_2263_ = lean_ctor_get(v_cfg_2245_, 14);
v_lintDriverArgs_2264_ = lean_ctor_get(v_cfg_2245_, 15);
v_version_2265_ = lean_ctor_get(v_cfg_2245_, 16);
v_versionTags_2266_ = lean_ctor_get(v_cfg_2245_, 17);
v_description_2267_ = lean_ctor_get(v_cfg_2245_, 18);
v_keywords_2268_ = lean_ctor_get(v_cfg_2245_, 19);
v_homepage_2269_ = lean_ctor_get(v_cfg_2245_, 20);
v_license_2270_ = lean_ctor_get(v_cfg_2245_, 21);
v_licenseFiles_2271_ = lean_ctor_get(v_cfg_2245_, 22);
v_readmeFile_2272_ = lean_ctor_get(v_cfg_2245_, 23);
v_reservoir_2273_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2274_ = lean_ctor_get(v_cfg_2245_, 24);
v_restoreAllArtifacts_x3f_2275_ = lean_ctor_get(v_cfg_2245_, 25);
v_libPrefixOnWindows_2276_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28 + 4);
v_allowImportAll_2277_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2278_ = lean_ctor_get(v_cfg_2245_, 26);
v_checks_2279_ = lean_ctor_get(v_cfg_2245_, 27);
v_fixedToolchain_2280_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*28 + 6);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_cfg_2245_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2282_ = v_cfg_2245_;
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_checks_2279_);
lean_inc(v_builtinLint_x3f_2278_);
lean_inc(v_restoreAllArtifacts_x3f_2275_);
lean_inc(v_enableArtifactCache_x3f_2274_);
lean_inc(v_readmeFile_2272_);
lean_inc(v_licenseFiles_2271_);
lean_inc(v_license_2270_);
lean_inc(v_homepage_2269_);
lean_inc(v_keywords_2268_);
lean_inc(v_description_2267_);
lean_inc(v_versionTags_2266_);
lean_inc(v_version_2265_);
lean_inc(v_lintDriverArgs_2264_);
lean_inc(v_lintDriver_2263_);
lean_inc(v_testDriverArgs_2262_);
lean_inc(v_testDriver_2261_);
lean_inc(v_buildArchive_2259_);
lean_inc(v_releaseRepo_2258_);
lean_inc(v_irDir_2257_);
lean_inc(v_binDir_2256_);
lean_inc(v_nativeLibDir_2255_);
lean_inc(v_leanLibDir_2254_);
lean_inc(v_buildDir_2253_);
lean_inc(v_srcDir_2252_);
lean_inc(v_moreGlobalServerArgs_2251_);
lean_inc(v_extraDepTargets_2249_);
lean_inc(v_toLeanConfig_2247_);
lean_inc(v_toWorkspaceConfig_2246_);
lean_dec(v_cfg_2245_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_apply_1(v_f_2244_, v_versionTags_2266_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 17, v___x_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_toWorkspaceConfig_2246_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_toLeanConfig_2247_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_extraDepTargets_2249_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_moreGlobalServerArgs_2251_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v_srcDir_2252_);
lean_ctor_set(v_reuseFailAlloc_2287_, 5, v_buildDir_2253_);
lean_ctor_set(v_reuseFailAlloc_2287_, 6, v_leanLibDir_2254_);
lean_ctor_set(v_reuseFailAlloc_2287_, 7, v_nativeLibDir_2255_);
lean_ctor_set(v_reuseFailAlloc_2287_, 8, v_binDir_2256_);
lean_ctor_set(v_reuseFailAlloc_2287_, 9, v_irDir_2257_);
lean_ctor_set(v_reuseFailAlloc_2287_, 10, v_releaseRepo_2258_);
lean_ctor_set(v_reuseFailAlloc_2287_, 11, v_buildArchive_2259_);
lean_ctor_set(v_reuseFailAlloc_2287_, 12, v_testDriver_2261_);
lean_ctor_set(v_reuseFailAlloc_2287_, 13, v_testDriverArgs_2262_);
lean_ctor_set(v_reuseFailAlloc_2287_, 14, v_lintDriver_2263_);
lean_ctor_set(v_reuseFailAlloc_2287_, 15, v_lintDriverArgs_2264_);
lean_ctor_set(v_reuseFailAlloc_2287_, 16, v_version_2265_);
lean_ctor_set(v_reuseFailAlloc_2287_, 17, v___x_2284_);
lean_ctor_set(v_reuseFailAlloc_2287_, 18, v_description_2267_);
lean_ctor_set(v_reuseFailAlloc_2287_, 19, v_keywords_2268_);
lean_ctor_set(v_reuseFailAlloc_2287_, 20, v_homepage_2269_);
lean_ctor_set(v_reuseFailAlloc_2287_, 21, v_license_2270_);
lean_ctor_set(v_reuseFailAlloc_2287_, 22, v_licenseFiles_2271_);
lean_ctor_set(v_reuseFailAlloc_2287_, 23, v_readmeFile_2272_);
lean_ctor_set(v_reuseFailAlloc_2287_, 24, v_enableArtifactCache_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2287_, 25, v_restoreAllArtifacts_x3f_2275_);
lean_ctor_set(v_reuseFailAlloc_2287_, 26, v_builtinLint_x3f_2278_);
lean_ctor_set(v_reuseFailAlloc_2287_, 27, v_checks_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28, v_bootstrap_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28 + 1, v_precompileModules_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28 + 3, v_reservoir_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28 + 5, v_allowImportAll_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*28 + 6, v_fixedToolchain_2280_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3(lean_object* v_x_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lake_defaultVersionTags;
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___lam__3___boxed(lean_object* v_x_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lake_PackageConfig_versionTags___proj___lam__3(v_x_2291_);
lean_dec_ref(v_x_2291_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2302_, lean_object* v_n_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___closed__4));
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2305_, lean_object* v_n_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lake_PackageConfig_versionTags___proj(v_p_2305_, v_n_2306_);
lean_dec(v_n_2306_);
lean_dec(v_p_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2308_, lean_object* v_n_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lake_PackageConfig_versionTags___proj(v_p_2308_, v_n_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2311_, lean_object* v_n_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2311_, v_n_2312_);
lean_dec(v_n_2312_);
lean_dec(v_p_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0(lean_object* v_cfg_2314_){
_start:
{
lean_object* v_description_2315_; 
v_description_2315_ = lean_ctor_get(v_cfg_2314_, 18);
lean_inc_ref(v_description_2315_);
return v_description_2315_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__0___boxed(lean_object* v_cfg_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lake_PackageConfig_description___proj___lam__0(v_cfg_2316_);
lean_dec_ref(v_cfg_2316_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__1(lean_object* v_val_2318_, lean_object* v_cfg_2319_){
_start:
{
lean_object* v_toWorkspaceConfig_2320_; lean_object* v_toLeanConfig_2321_; uint8_t v_bootstrap_2322_; lean_object* v_extraDepTargets_2323_; uint8_t v_precompileModules_2324_; lean_object* v_moreGlobalServerArgs_2325_; lean_object* v_srcDir_2326_; lean_object* v_buildDir_2327_; lean_object* v_leanLibDir_2328_; lean_object* v_nativeLibDir_2329_; lean_object* v_binDir_2330_; lean_object* v_irDir_2331_; lean_object* v_releaseRepo_2332_; lean_object* v_buildArchive_2333_; uint8_t v_preferReleaseBuild_2334_; lean_object* v_testDriver_2335_; lean_object* v_testDriverArgs_2336_; lean_object* v_lintDriver_2337_; lean_object* v_lintDriverArgs_2338_; lean_object* v_version_2339_; lean_object* v_versionTags_2340_; lean_object* v_keywords_2341_; lean_object* v_homepage_2342_; lean_object* v_license_2343_; lean_object* v_licenseFiles_2344_; lean_object* v_readmeFile_2345_; uint8_t v_reservoir_2346_; lean_object* v_enableArtifactCache_x3f_2347_; lean_object* v_restoreAllArtifacts_x3f_2348_; uint8_t v_libPrefixOnWindows_2349_; uint8_t v_allowImportAll_2350_; lean_object* v_builtinLint_x3f_2351_; lean_object* v_checks_2352_; uint8_t v_fixedToolchain_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_toWorkspaceConfig_2320_ = lean_ctor_get(v_cfg_2319_, 0);
v_toLeanConfig_2321_ = lean_ctor_get(v_cfg_2319_, 1);
v_bootstrap_2322_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28);
v_extraDepTargets_2323_ = lean_ctor_get(v_cfg_2319_, 2);
v_precompileModules_2324_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2325_ = lean_ctor_get(v_cfg_2319_, 3);
v_srcDir_2326_ = lean_ctor_get(v_cfg_2319_, 4);
v_buildDir_2327_ = lean_ctor_get(v_cfg_2319_, 5);
v_leanLibDir_2328_ = lean_ctor_get(v_cfg_2319_, 6);
v_nativeLibDir_2329_ = lean_ctor_get(v_cfg_2319_, 7);
v_binDir_2330_ = lean_ctor_get(v_cfg_2319_, 8);
v_irDir_2331_ = lean_ctor_get(v_cfg_2319_, 9);
v_releaseRepo_2332_ = lean_ctor_get(v_cfg_2319_, 10);
v_buildArchive_2333_ = lean_ctor_get(v_cfg_2319_, 11);
v_preferReleaseBuild_2334_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28 + 2);
v_testDriver_2335_ = lean_ctor_get(v_cfg_2319_, 12);
v_testDriverArgs_2336_ = lean_ctor_get(v_cfg_2319_, 13);
v_lintDriver_2337_ = lean_ctor_get(v_cfg_2319_, 14);
v_lintDriverArgs_2338_ = lean_ctor_get(v_cfg_2319_, 15);
v_version_2339_ = lean_ctor_get(v_cfg_2319_, 16);
v_versionTags_2340_ = lean_ctor_get(v_cfg_2319_, 17);
v_keywords_2341_ = lean_ctor_get(v_cfg_2319_, 19);
v_homepage_2342_ = lean_ctor_get(v_cfg_2319_, 20);
v_license_2343_ = lean_ctor_get(v_cfg_2319_, 21);
v_licenseFiles_2344_ = lean_ctor_get(v_cfg_2319_, 22);
v_readmeFile_2345_ = lean_ctor_get(v_cfg_2319_, 23);
v_reservoir_2346_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2347_ = lean_ctor_get(v_cfg_2319_, 24);
v_restoreAllArtifacts_x3f_2348_ = lean_ctor_get(v_cfg_2319_, 25);
v_libPrefixOnWindows_2349_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28 + 4);
v_allowImportAll_2350_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2351_ = lean_ctor_get(v_cfg_2319_, 26);
v_checks_2352_ = lean_ctor_get(v_cfg_2319_, 27);
v_fixedToolchain_2353_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*28 + 6);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_cfg_2319_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v_cfg_2319_, 18);
lean_dec(v_unused_2361_);
v___x_2355_ = v_cfg_2319_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_checks_2352_);
lean_inc(v_builtinLint_x3f_2351_);
lean_inc(v_restoreAllArtifacts_x3f_2348_);
lean_inc(v_enableArtifactCache_x3f_2347_);
lean_inc(v_readmeFile_2345_);
lean_inc(v_licenseFiles_2344_);
lean_inc(v_license_2343_);
lean_inc(v_homepage_2342_);
lean_inc(v_keywords_2341_);
lean_inc(v_versionTags_2340_);
lean_inc(v_version_2339_);
lean_inc(v_lintDriverArgs_2338_);
lean_inc(v_lintDriver_2337_);
lean_inc(v_testDriverArgs_2336_);
lean_inc(v_testDriver_2335_);
lean_inc(v_buildArchive_2333_);
lean_inc(v_releaseRepo_2332_);
lean_inc(v_irDir_2331_);
lean_inc(v_binDir_2330_);
lean_inc(v_nativeLibDir_2329_);
lean_inc(v_leanLibDir_2328_);
lean_inc(v_buildDir_2327_);
lean_inc(v_srcDir_2326_);
lean_inc(v_moreGlobalServerArgs_2325_);
lean_inc(v_extraDepTargets_2323_);
lean_inc(v_toLeanConfig_2321_);
lean_inc(v_toWorkspaceConfig_2320_);
lean_dec(v_cfg_2319_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 18, v_val_2318_);
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_toWorkspaceConfig_2320_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_toLeanConfig_2321_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_extraDepTargets_2323_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_moreGlobalServerArgs_2325_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_srcDir_2326_);
lean_ctor_set(v_reuseFailAlloc_2359_, 5, v_buildDir_2327_);
lean_ctor_set(v_reuseFailAlloc_2359_, 6, v_leanLibDir_2328_);
lean_ctor_set(v_reuseFailAlloc_2359_, 7, v_nativeLibDir_2329_);
lean_ctor_set(v_reuseFailAlloc_2359_, 8, v_binDir_2330_);
lean_ctor_set(v_reuseFailAlloc_2359_, 9, v_irDir_2331_);
lean_ctor_set(v_reuseFailAlloc_2359_, 10, v_releaseRepo_2332_);
lean_ctor_set(v_reuseFailAlloc_2359_, 11, v_buildArchive_2333_);
lean_ctor_set(v_reuseFailAlloc_2359_, 12, v_testDriver_2335_);
lean_ctor_set(v_reuseFailAlloc_2359_, 13, v_testDriverArgs_2336_);
lean_ctor_set(v_reuseFailAlloc_2359_, 14, v_lintDriver_2337_);
lean_ctor_set(v_reuseFailAlloc_2359_, 15, v_lintDriverArgs_2338_);
lean_ctor_set(v_reuseFailAlloc_2359_, 16, v_version_2339_);
lean_ctor_set(v_reuseFailAlloc_2359_, 17, v_versionTags_2340_);
lean_ctor_set(v_reuseFailAlloc_2359_, 18, v_val_2318_);
lean_ctor_set(v_reuseFailAlloc_2359_, 19, v_keywords_2341_);
lean_ctor_set(v_reuseFailAlloc_2359_, 20, v_homepage_2342_);
lean_ctor_set(v_reuseFailAlloc_2359_, 21, v_license_2343_);
lean_ctor_set(v_reuseFailAlloc_2359_, 22, v_licenseFiles_2344_);
lean_ctor_set(v_reuseFailAlloc_2359_, 23, v_readmeFile_2345_);
lean_ctor_set(v_reuseFailAlloc_2359_, 24, v_enableArtifactCache_x3f_2347_);
lean_ctor_set(v_reuseFailAlloc_2359_, 25, v_restoreAllArtifacts_x3f_2348_);
lean_ctor_set(v_reuseFailAlloc_2359_, 26, v_builtinLint_x3f_2351_);
lean_ctor_set(v_reuseFailAlloc_2359_, 27, v_checks_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28, v_bootstrap_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28 + 1, v_precompileModules_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28 + 3, v_reservoir_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28 + 5, v_allowImportAll_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2359_, sizeof(void*)*28 + 6, v_fixedToolchain_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___lam__2(lean_object* v_f_2362_, lean_object* v_cfg_2363_){
_start:
{
lean_object* v_toWorkspaceConfig_2364_; lean_object* v_toLeanConfig_2365_; uint8_t v_bootstrap_2366_; lean_object* v_extraDepTargets_2367_; uint8_t v_precompileModules_2368_; lean_object* v_moreGlobalServerArgs_2369_; lean_object* v_srcDir_2370_; lean_object* v_buildDir_2371_; lean_object* v_leanLibDir_2372_; lean_object* v_nativeLibDir_2373_; lean_object* v_binDir_2374_; lean_object* v_irDir_2375_; lean_object* v_releaseRepo_2376_; lean_object* v_buildArchive_2377_; uint8_t v_preferReleaseBuild_2378_; lean_object* v_testDriver_2379_; lean_object* v_testDriverArgs_2380_; lean_object* v_lintDriver_2381_; lean_object* v_lintDriverArgs_2382_; lean_object* v_version_2383_; lean_object* v_versionTags_2384_; lean_object* v_description_2385_; lean_object* v_keywords_2386_; lean_object* v_homepage_2387_; lean_object* v_license_2388_; lean_object* v_licenseFiles_2389_; lean_object* v_readmeFile_2390_; uint8_t v_reservoir_2391_; lean_object* v_enableArtifactCache_x3f_2392_; lean_object* v_restoreAllArtifacts_x3f_2393_; uint8_t v_libPrefixOnWindows_2394_; uint8_t v_allowImportAll_2395_; lean_object* v_builtinLint_x3f_2396_; lean_object* v_checks_2397_; uint8_t v_fixedToolchain_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_toWorkspaceConfig_2364_ = lean_ctor_get(v_cfg_2363_, 0);
v_toLeanConfig_2365_ = lean_ctor_get(v_cfg_2363_, 1);
v_bootstrap_2366_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28);
v_extraDepTargets_2367_ = lean_ctor_get(v_cfg_2363_, 2);
v_precompileModules_2368_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2369_ = lean_ctor_get(v_cfg_2363_, 3);
v_srcDir_2370_ = lean_ctor_get(v_cfg_2363_, 4);
v_buildDir_2371_ = lean_ctor_get(v_cfg_2363_, 5);
v_leanLibDir_2372_ = lean_ctor_get(v_cfg_2363_, 6);
v_nativeLibDir_2373_ = lean_ctor_get(v_cfg_2363_, 7);
v_binDir_2374_ = lean_ctor_get(v_cfg_2363_, 8);
v_irDir_2375_ = lean_ctor_get(v_cfg_2363_, 9);
v_releaseRepo_2376_ = lean_ctor_get(v_cfg_2363_, 10);
v_buildArchive_2377_ = lean_ctor_get(v_cfg_2363_, 11);
v_preferReleaseBuild_2378_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28 + 2);
v_testDriver_2379_ = lean_ctor_get(v_cfg_2363_, 12);
v_testDriverArgs_2380_ = lean_ctor_get(v_cfg_2363_, 13);
v_lintDriver_2381_ = lean_ctor_get(v_cfg_2363_, 14);
v_lintDriverArgs_2382_ = lean_ctor_get(v_cfg_2363_, 15);
v_version_2383_ = lean_ctor_get(v_cfg_2363_, 16);
v_versionTags_2384_ = lean_ctor_get(v_cfg_2363_, 17);
v_description_2385_ = lean_ctor_get(v_cfg_2363_, 18);
v_keywords_2386_ = lean_ctor_get(v_cfg_2363_, 19);
v_homepage_2387_ = lean_ctor_get(v_cfg_2363_, 20);
v_license_2388_ = lean_ctor_get(v_cfg_2363_, 21);
v_licenseFiles_2389_ = lean_ctor_get(v_cfg_2363_, 22);
v_readmeFile_2390_ = lean_ctor_get(v_cfg_2363_, 23);
v_reservoir_2391_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2392_ = lean_ctor_get(v_cfg_2363_, 24);
v_restoreAllArtifacts_x3f_2393_ = lean_ctor_get(v_cfg_2363_, 25);
v_libPrefixOnWindows_2394_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28 + 4);
v_allowImportAll_2395_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2396_ = lean_ctor_get(v_cfg_2363_, 26);
v_checks_2397_ = lean_ctor_get(v_cfg_2363_, 27);
v_fixedToolchain_2398_ = lean_ctor_get_uint8(v_cfg_2363_, sizeof(void*)*28 + 6);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_cfg_2363_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v_cfg_2363_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_checks_2397_);
lean_inc(v_builtinLint_x3f_2396_);
lean_inc(v_restoreAllArtifacts_x3f_2393_);
lean_inc(v_enableArtifactCache_x3f_2392_);
lean_inc(v_readmeFile_2390_);
lean_inc(v_licenseFiles_2389_);
lean_inc(v_license_2388_);
lean_inc(v_homepage_2387_);
lean_inc(v_keywords_2386_);
lean_inc(v_description_2385_);
lean_inc(v_versionTags_2384_);
lean_inc(v_version_2383_);
lean_inc(v_lintDriverArgs_2382_);
lean_inc(v_lintDriver_2381_);
lean_inc(v_testDriverArgs_2380_);
lean_inc(v_testDriver_2379_);
lean_inc(v_buildArchive_2377_);
lean_inc(v_releaseRepo_2376_);
lean_inc(v_irDir_2375_);
lean_inc(v_binDir_2374_);
lean_inc(v_nativeLibDir_2373_);
lean_inc(v_leanLibDir_2372_);
lean_inc(v_buildDir_2371_);
lean_inc(v_srcDir_2370_);
lean_inc(v_moreGlobalServerArgs_2369_);
lean_inc(v_extraDepTargets_2367_);
lean_inc(v_toLeanConfig_2365_);
lean_inc(v_toWorkspaceConfig_2364_);
lean_dec(v_cfg_2363_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = lean_apply_1(v_f_2362_, v_description_2385_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 18, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_toWorkspaceConfig_2364_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_toLeanConfig_2365_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_extraDepTargets_2367_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_moreGlobalServerArgs_2369_);
lean_ctor_set(v_reuseFailAlloc_2405_, 4, v_srcDir_2370_);
lean_ctor_set(v_reuseFailAlloc_2405_, 5, v_buildDir_2371_);
lean_ctor_set(v_reuseFailAlloc_2405_, 6, v_leanLibDir_2372_);
lean_ctor_set(v_reuseFailAlloc_2405_, 7, v_nativeLibDir_2373_);
lean_ctor_set(v_reuseFailAlloc_2405_, 8, v_binDir_2374_);
lean_ctor_set(v_reuseFailAlloc_2405_, 9, v_irDir_2375_);
lean_ctor_set(v_reuseFailAlloc_2405_, 10, v_releaseRepo_2376_);
lean_ctor_set(v_reuseFailAlloc_2405_, 11, v_buildArchive_2377_);
lean_ctor_set(v_reuseFailAlloc_2405_, 12, v_testDriver_2379_);
lean_ctor_set(v_reuseFailAlloc_2405_, 13, v_testDriverArgs_2380_);
lean_ctor_set(v_reuseFailAlloc_2405_, 14, v_lintDriver_2381_);
lean_ctor_set(v_reuseFailAlloc_2405_, 15, v_lintDriverArgs_2382_);
lean_ctor_set(v_reuseFailAlloc_2405_, 16, v_version_2383_);
lean_ctor_set(v_reuseFailAlloc_2405_, 17, v_versionTags_2384_);
lean_ctor_set(v_reuseFailAlloc_2405_, 18, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 19, v_keywords_2386_);
lean_ctor_set(v_reuseFailAlloc_2405_, 20, v_homepage_2387_);
lean_ctor_set(v_reuseFailAlloc_2405_, 21, v_license_2388_);
lean_ctor_set(v_reuseFailAlloc_2405_, 22, v_licenseFiles_2389_);
lean_ctor_set(v_reuseFailAlloc_2405_, 23, v_readmeFile_2390_);
lean_ctor_set(v_reuseFailAlloc_2405_, 24, v_enableArtifactCache_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2405_, 25, v_restoreAllArtifacts_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2405_, 26, v_builtinLint_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2405_, 27, v_checks_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28, v_bootstrap_2366_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28 + 1, v_precompileModules_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2378_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28 + 3, v_reservoir_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28 + 5, v_allowImportAll_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*28 + 6, v_fixedToolchain_2398_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2415_, lean_object* v_n_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___closed__3));
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2418_, lean_object* v_n_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lake_PackageConfig_description___proj(v_p_2418_, v_n_2419_);
lean_dec(v_n_2419_);
lean_dec(v_p_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2421_, lean_object* v_n_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lake_PackageConfig_description___proj(v_p_2421_, v_n_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2424_, lean_object* v_n_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lake_PackageConfig_description_instConfigField(v_p_2424_, v_n_2425_);
lean_dec(v_n_2425_);
lean_dec(v_p_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0(lean_object* v_cfg_2427_){
_start:
{
lean_object* v_keywords_2428_; 
v_keywords_2428_ = lean_ctor_get(v_cfg_2427_, 19);
lean_inc_ref(v_keywords_2428_);
return v_keywords_2428_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__0___boxed(lean_object* v_cfg_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lake_PackageConfig_keywords___proj___lam__0(v_cfg_2429_);
lean_dec_ref(v_cfg_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__1(lean_object* v_val_2431_, lean_object* v_cfg_2432_){
_start:
{
lean_object* v_toWorkspaceConfig_2433_; lean_object* v_toLeanConfig_2434_; uint8_t v_bootstrap_2435_; lean_object* v_extraDepTargets_2436_; uint8_t v_precompileModules_2437_; lean_object* v_moreGlobalServerArgs_2438_; lean_object* v_srcDir_2439_; lean_object* v_buildDir_2440_; lean_object* v_leanLibDir_2441_; lean_object* v_nativeLibDir_2442_; lean_object* v_binDir_2443_; lean_object* v_irDir_2444_; lean_object* v_releaseRepo_2445_; lean_object* v_buildArchive_2446_; uint8_t v_preferReleaseBuild_2447_; lean_object* v_testDriver_2448_; lean_object* v_testDriverArgs_2449_; lean_object* v_lintDriver_2450_; lean_object* v_lintDriverArgs_2451_; lean_object* v_version_2452_; lean_object* v_versionTags_2453_; lean_object* v_description_2454_; lean_object* v_homepage_2455_; lean_object* v_license_2456_; lean_object* v_licenseFiles_2457_; lean_object* v_readmeFile_2458_; uint8_t v_reservoir_2459_; lean_object* v_enableArtifactCache_x3f_2460_; lean_object* v_restoreAllArtifacts_x3f_2461_; uint8_t v_libPrefixOnWindows_2462_; uint8_t v_allowImportAll_2463_; lean_object* v_builtinLint_x3f_2464_; lean_object* v_checks_2465_; uint8_t v_fixedToolchain_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_toWorkspaceConfig_2433_ = lean_ctor_get(v_cfg_2432_, 0);
v_toLeanConfig_2434_ = lean_ctor_get(v_cfg_2432_, 1);
v_bootstrap_2435_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28);
v_extraDepTargets_2436_ = lean_ctor_get(v_cfg_2432_, 2);
v_precompileModules_2437_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2438_ = lean_ctor_get(v_cfg_2432_, 3);
v_srcDir_2439_ = lean_ctor_get(v_cfg_2432_, 4);
v_buildDir_2440_ = lean_ctor_get(v_cfg_2432_, 5);
v_leanLibDir_2441_ = lean_ctor_get(v_cfg_2432_, 6);
v_nativeLibDir_2442_ = lean_ctor_get(v_cfg_2432_, 7);
v_binDir_2443_ = lean_ctor_get(v_cfg_2432_, 8);
v_irDir_2444_ = lean_ctor_get(v_cfg_2432_, 9);
v_releaseRepo_2445_ = lean_ctor_get(v_cfg_2432_, 10);
v_buildArchive_2446_ = lean_ctor_get(v_cfg_2432_, 11);
v_preferReleaseBuild_2447_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 2);
v_testDriver_2448_ = lean_ctor_get(v_cfg_2432_, 12);
v_testDriverArgs_2449_ = lean_ctor_get(v_cfg_2432_, 13);
v_lintDriver_2450_ = lean_ctor_get(v_cfg_2432_, 14);
v_lintDriverArgs_2451_ = lean_ctor_get(v_cfg_2432_, 15);
v_version_2452_ = lean_ctor_get(v_cfg_2432_, 16);
v_versionTags_2453_ = lean_ctor_get(v_cfg_2432_, 17);
v_description_2454_ = lean_ctor_get(v_cfg_2432_, 18);
v_homepage_2455_ = lean_ctor_get(v_cfg_2432_, 20);
v_license_2456_ = lean_ctor_get(v_cfg_2432_, 21);
v_licenseFiles_2457_ = lean_ctor_get(v_cfg_2432_, 22);
v_readmeFile_2458_ = lean_ctor_get(v_cfg_2432_, 23);
v_reservoir_2459_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2460_ = lean_ctor_get(v_cfg_2432_, 24);
v_restoreAllArtifacts_x3f_2461_ = lean_ctor_get(v_cfg_2432_, 25);
v_libPrefixOnWindows_2462_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 4);
v_allowImportAll_2463_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2464_ = lean_ctor_get(v_cfg_2432_, 26);
v_checks_2465_ = lean_ctor_get(v_cfg_2432_, 27);
v_fixedToolchain_2466_ = lean_ctor_get_uint8(v_cfg_2432_, sizeof(void*)*28 + 6);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_cfg_2432_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v_cfg_2432_, 19);
lean_dec(v_unused_2474_);
v___x_2468_ = v_cfg_2432_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_checks_2465_);
lean_inc(v_builtinLint_x3f_2464_);
lean_inc(v_restoreAllArtifacts_x3f_2461_);
lean_inc(v_enableArtifactCache_x3f_2460_);
lean_inc(v_readmeFile_2458_);
lean_inc(v_licenseFiles_2457_);
lean_inc(v_license_2456_);
lean_inc(v_homepage_2455_);
lean_inc(v_description_2454_);
lean_inc(v_versionTags_2453_);
lean_inc(v_version_2452_);
lean_inc(v_lintDriverArgs_2451_);
lean_inc(v_lintDriver_2450_);
lean_inc(v_testDriverArgs_2449_);
lean_inc(v_testDriver_2448_);
lean_inc(v_buildArchive_2446_);
lean_inc(v_releaseRepo_2445_);
lean_inc(v_irDir_2444_);
lean_inc(v_binDir_2443_);
lean_inc(v_nativeLibDir_2442_);
lean_inc(v_leanLibDir_2441_);
lean_inc(v_buildDir_2440_);
lean_inc(v_srcDir_2439_);
lean_inc(v_moreGlobalServerArgs_2438_);
lean_inc(v_extraDepTargets_2436_);
lean_inc(v_toLeanConfig_2434_);
lean_inc(v_toWorkspaceConfig_2433_);
lean_dec(v_cfg_2432_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 19, v_val_2431_);
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_toWorkspaceConfig_2433_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_toLeanConfig_2434_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_extraDepTargets_2436_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_moreGlobalServerArgs_2438_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_srcDir_2439_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v_buildDir_2440_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_leanLibDir_2441_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_nativeLibDir_2442_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_binDir_2443_);
lean_ctor_set(v_reuseFailAlloc_2472_, 9, v_irDir_2444_);
lean_ctor_set(v_reuseFailAlloc_2472_, 10, v_releaseRepo_2445_);
lean_ctor_set(v_reuseFailAlloc_2472_, 11, v_buildArchive_2446_);
lean_ctor_set(v_reuseFailAlloc_2472_, 12, v_testDriver_2448_);
lean_ctor_set(v_reuseFailAlloc_2472_, 13, v_testDriverArgs_2449_);
lean_ctor_set(v_reuseFailAlloc_2472_, 14, v_lintDriver_2450_);
lean_ctor_set(v_reuseFailAlloc_2472_, 15, v_lintDriverArgs_2451_);
lean_ctor_set(v_reuseFailAlloc_2472_, 16, v_version_2452_);
lean_ctor_set(v_reuseFailAlloc_2472_, 17, v_versionTags_2453_);
lean_ctor_set(v_reuseFailAlloc_2472_, 18, v_description_2454_);
lean_ctor_set(v_reuseFailAlloc_2472_, 19, v_val_2431_);
lean_ctor_set(v_reuseFailAlloc_2472_, 20, v_homepage_2455_);
lean_ctor_set(v_reuseFailAlloc_2472_, 21, v_license_2456_);
lean_ctor_set(v_reuseFailAlloc_2472_, 22, v_licenseFiles_2457_);
lean_ctor_set(v_reuseFailAlloc_2472_, 23, v_readmeFile_2458_);
lean_ctor_set(v_reuseFailAlloc_2472_, 24, v_enableArtifactCache_x3f_2460_);
lean_ctor_set(v_reuseFailAlloc_2472_, 25, v_restoreAllArtifacts_x3f_2461_);
lean_ctor_set(v_reuseFailAlloc_2472_, 26, v_builtinLint_x3f_2464_);
lean_ctor_set(v_reuseFailAlloc_2472_, 27, v_checks_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28, v_bootstrap_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28 + 1, v_precompileModules_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28 + 3, v_reservoir_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28 + 5, v_allowImportAll_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*28 + 6, v_fixedToolchain_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___lam__2(lean_object* v_f_2475_, lean_object* v_cfg_2476_){
_start:
{
lean_object* v_toWorkspaceConfig_2477_; lean_object* v_toLeanConfig_2478_; uint8_t v_bootstrap_2479_; lean_object* v_extraDepTargets_2480_; uint8_t v_precompileModules_2481_; lean_object* v_moreGlobalServerArgs_2482_; lean_object* v_srcDir_2483_; lean_object* v_buildDir_2484_; lean_object* v_leanLibDir_2485_; lean_object* v_nativeLibDir_2486_; lean_object* v_binDir_2487_; lean_object* v_irDir_2488_; lean_object* v_releaseRepo_2489_; lean_object* v_buildArchive_2490_; uint8_t v_preferReleaseBuild_2491_; lean_object* v_testDriver_2492_; lean_object* v_testDriverArgs_2493_; lean_object* v_lintDriver_2494_; lean_object* v_lintDriverArgs_2495_; lean_object* v_version_2496_; lean_object* v_versionTags_2497_; lean_object* v_description_2498_; lean_object* v_keywords_2499_; lean_object* v_homepage_2500_; lean_object* v_license_2501_; lean_object* v_licenseFiles_2502_; lean_object* v_readmeFile_2503_; uint8_t v_reservoir_2504_; lean_object* v_enableArtifactCache_x3f_2505_; lean_object* v_restoreAllArtifacts_x3f_2506_; uint8_t v_libPrefixOnWindows_2507_; uint8_t v_allowImportAll_2508_; lean_object* v_builtinLint_x3f_2509_; lean_object* v_checks_2510_; uint8_t v_fixedToolchain_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2519_; 
v_toWorkspaceConfig_2477_ = lean_ctor_get(v_cfg_2476_, 0);
v_toLeanConfig_2478_ = lean_ctor_get(v_cfg_2476_, 1);
v_bootstrap_2479_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28);
v_extraDepTargets_2480_ = lean_ctor_get(v_cfg_2476_, 2);
v_precompileModules_2481_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2482_ = lean_ctor_get(v_cfg_2476_, 3);
v_srcDir_2483_ = lean_ctor_get(v_cfg_2476_, 4);
v_buildDir_2484_ = lean_ctor_get(v_cfg_2476_, 5);
v_leanLibDir_2485_ = lean_ctor_get(v_cfg_2476_, 6);
v_nativeLibDir_2486_ = lean_ctor_get(v_cfg_2476_, 7);
v_binDir_2487_ = lean_ctor_get(v_cfg_2476_, 8);
v_irDir_2488_ = lean_ctor_get(v_cfg_2476_, 9);
v_releaseRepo_2489_ = lean_ctor_get(v_cfg_2476_, 10);
v_buildArchive_2490_ = lean_ctor_get(v_cfg_2476_, 11);
v_preferReleaseBuild_2491_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28 + 2);
v_testDriver_2492_ = lean_ctor_get(v_cfg_2476_, 12);
v_testDriverArgs_2493_ = lean_ctor_get(v_cfg_2476_, 13);
v_lintDriver_2494_ = lean_ctor_get(v_cfg_2476_, 14);
v_lintDriverArgs_2495_ = lean_ctor_get(v_cfg_2476_, 15);
v_version_2496_ = lean_ctor_get(v_cfg_2476_, 16);
v_versionTags_2497_ = lean_ctor_get(v_cfg_2476_, 17);
v_description_2498_ = lean_ctor_get(v_cfg_2476_, 18);
v_keywords_2499_ = lean_ctor_get(v_cfg_2476_, 19);
v_homepage_2500_ = lean_ctor_get(v_cfg_2476_, 20);
v_license_2501_ = lean_ctor_get(v_cfg_2476_, 21);
v_licenseFiles_2502_ = lean_ctor_get(v_cfg_2476_, 22);
v_readmeFile_2503_ = lean_ctor_get(v_cfg_2476_, 23);
v_reservoir_2504_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2505_ = lean_ctor_get(v_cfg_2476_, 24);
v_restoreAllArtifacts_x3f_2506_ = lean_ctor_get(v_cfg_2476_, 25);
v_libPrefixOnWindows_2507_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28 + 4);
v_allowImportAll_2508_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2509_ = lean_ctor_get(v_cfg_2476_, 26);
v_checks_2510_ = lean_ctor_get(v_cfg_2476_, 27);
v_fixedToolchain_2511_ = lean_ctor_get_uint8(v_cfg_2476_, sizeof(void*)*28 + 6);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_cfg_2476_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2513_ = v_cfg_2476_;
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_checks_2510_);
lean_inc(v_builtinLint_x3f_2509_);
lean_inc(v_restoreAllArtifacts_x3f_2506_);
lean_inc(v_enableArtifactCache_x3f_2505_);
lean_inc(v_readmeFile_2503_);
lean_inc(v_licenseFiles_2502_);
lean_inc(v_license_2501_);
lean_inc(v_homepage_2500_);
lean_inc(v_keywords_2499_);
lean_inc(v_description_2498_);
lean_inc(v_versionTags_2497_);
lean_inc(v_version_2496_);
lean_inc(v_lintDriverArgs_2495_);
lean_inc(v_lintDriver_2494_);
lean_inc(v_testDriverArgs_2493_);
lean_inc(v_testDriver_2492_);
lean_inc(v_buildArchive_2490_);
lean_inc(v_releaseRepo_2489_);
lean_inc(v_irDir_2488_);
lean_inc(v_binDir_2487_);
lean_inc(v_nativeLibDir_2486_);
lean_inc(v_leanLibDir_2485_);
lean_inc(v_buildDir_2484_);
lean_inc(v_srcDir_2483_);
lean_inc(v_moreGlobalServerArgs_2482_);
lean_inc(v_extraDepTargets_2480_);
lean_inc(v_toLeanConfig_2478_);
lean_inc(v_toWorkspaceConfig_2477_);
lean_dec(v_cfg_2476_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = lean_apply_1(v_f_2475_, v_keywords_2499_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 19, v___x_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_toWorkspaceConfig_2477_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_toLeanConfig_2478_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_extraDepTargets_2480_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_moreGlobalServerArgs_2482_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_srcDir_2483_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v_buildDir_2484_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_leanLibDir_2485_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_nativeLibDir_2486_);
lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_binDir_2487_);
lean_ctor_set(v_reuseFailAlloc_2518_, 9, v_irDir_2488_);
lean_ctor_set(v_reuseFailAlloc_2518_, 10, v_releaseRepo_2489_);
lean_ctor_set(v_reuseFailAlloc_2518_, 11, v_buildArchive_2490_);
lean_ctor_set(v_reuseFailAlloc_2518_, 12, v_testDriver_2492_);
lean_ctor_set(v_reuseFailAlloc_2518_, 13, v_testDriverArgs_2493_);
lean_ctor_set(v_reuseFailAlloc_2518_, 14, v_lintDriver_2494_);
lean_ctor_set(v_reuseFailAlloc_2518_, 15, v_lintDriverArgs_2495_);
lean_ctor_set(v_reuseFailAlloc_2518_, 16, v_version_2496_);
lean_ctor_set(v_reuseFailAlloc_2518_, 17, v_versionTags_2497_);
lean_ctor_set(v_reuseFailAlloc_2518_, 18, v_description_2498_);
lean_ctor_set(v_reuseFailAlloc_2518_, 19, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2518_, 20, v_homepage_2500_);
lean_ctor_set(v_reuseFailAlloc_2518_, 21, v_license_2501_);
lean_ctor_set(v_reuseFailAlloc_2518_, 22, v_licenseFiles_2502_);
lean_ctor_set(v_reuseFailAlloc_2518_, 23, v_readmeFile_2503_);
lean_ctor_set(v_reuseFailAlloc_2518_, 24, v_enableArtifactCache_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2518_, 25, v_restoreAllArtifacts_x3f_2506_);
lean_ctor_set(v_reuseFailAlloc_2518_, 26, v_builtinLint_x3f_2509_);
lean_ctor_set(v_reuseFailAlloc_2518_, 27, v_checks_2510_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28, v_bootstrap_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28 + 1, v_precompileModules_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28 + 3, v_reservoir_2504_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28 + 5, v_allowImportAll_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*28 + 6, v_fixedToolchain_2511_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2528_, lean_object* v_n_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___closed__3));
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2531_, lean_object* v_n_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lake_PackageConfig_keywords___proj(v_p_2531_, v_n_2532_);
lean_dec(v_n_2532_);
lean_dec(v_p_2531_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2534_, lean_object* v_n_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lake_PackageConfig_keywords___proj(v_p_2534_, v_n_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2537_, lean_object* v_n_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2537_, v_n_2538_);
lean_dec(v_n_2538_);
lean_dec(v_p_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0(lean_object* v_cfg_2540_){
_start:
{
lean_object* v_homepage_2541_; 
v_homepage_2541_ = lean_ctor_get(v_cfg_2540_, 20);
lean_inc_ref(v_homepage_2541_);
return v_homepage_2541_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__0___boxed(lean_object* v_cfg_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lake_PackageConfig_homepage___proj___lam__0(v_cfg_2542_);
lean_dec_ref(v_cfg_2542_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__1(lean_object* v_val_2544_, lean_object* v_cfg_2545_){
_start:
{
lean_object* v_toWorkspaceConfig_2546_; lean_object* v_toLeanConfig_2547_; uint8_t v_bootstrap_2548_; lean_object* v_extraDepTargets_2549_; uint8_t v_precompileModules_2550_; lean_object* v_moreGlobalServerArgs_2551_; lean_object* v_srcDir_2552_; lean_object* v_buildDir_2553_; lean_object* v_leanLibDir_2554_; lean_object* v_nativeLibDir_2555_; lean_object* v_binDir_2556_; lean_object* v_irDir_2557_; lean_object* v_releaseRepo_2558_; lean_object* v_buildArchive_2559_; uint8_t v_preferReleaseBuild_2560_; lean_object* v_testDriver_2561_; lean_object* v_testDriverArgs_2562_; lean_object* v_lintDriver_2563_; lean_object* v_lintDriverArgs_2564_; lean_object* v_version_2565_; lean_object* v_versionTags_2566_; lean_object* v_description_2567_; lean_object* v_keywords_2568_; lean_object* v_license_2569_; lean_object* v_licenseFiles_2570_; lean_object* v_readmeFile_2571_; uint8_t v_reservoir_2572_; lean_object* v_enableArtifactCache_x3f_2573_; lean_object* v_restoreAllArtifacts_x3f_2574_; uint8_t v_libPrefixOnWindows_2575_; uint8_t v_allowImportAll_2576_; lean_object* v_builtinLint_x3f_2577_; lean_object* v_checks_2578_; uint8_t v_fixedToolchain_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
v_toWorkspaceConfig_2546_ = lean_ctor_get(v_cfg_2545_, 0);
v_toLeanConfig_2547_ = lean_ctor_get(v_cfg_2545_, 1);
v_bootstrap_2548_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28);
v_extraDepTargets_2549_ = lean_ctor_get(v_cfg_2545_, 2);
v_precompileModules_2550_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2551_ = lean_ctor_get(v_cfg_2545_, 3);
v_srcDir_2552_ = lean_ctor_get(v_cfg_2545_, 4);
v_buildDir_2553_ = lean_ctor_get(v_cfg_2545_, 5);
v_leanLibDir_2554_ = lean_ctor_get(v_cfg_2545_, 6);
v_nativeLibDir_2555_ = lean_ctor_get(v_cfg_2545_, 7);
v_binDir_2556_ = lean_ctor_get(v_cfg_2545_, 8);
v_irDir_2557_ = lean_ctor_get(v_cfg_2545_, 9);
v_releaseRepo_2558_ = lean_ctor_get(v_cfg_2545_, 10);
v_buildArchive_2559_ = lean_ctor_get(v_cfg_2545_, 11);
v_preferReleaseBuild_2560_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28 + 2);
v_testDriver_2561_ = lean_ctor_get(v_cfg_2545_, 12);
v_testDriverArgs_2562_ = lean_ctor_get(v_cfg_2545_, 13);
v_lintDriver_2563_ = lean_ctor_get(v_cfg_2545_, 14);
v_lintDriverArgs_2564_ = lean_ctor_get(v_cfg_2545_, 15);
v_version_2565_ = lean_ctor_get(v_cfg_2545_, 16);
v_versionTags_2566_ = lean_ctor_get(v_cfg_2545_, 17);
v_description_2567_ = lean_ctor_get(v_cfg_2545_, 18);
v_keywords_2568_ = lean_ctor_get(v_cfg_2545_, 19);
v_license_2569_ = lean_ctor_get(v_cfg_2545_, 21);
v_licenseFiles_2570_ = lean_ctor_get(v_cfg_2545_, 22);
v_readmeFile_2571_ = lean_ctor_get(v_cfg_2545_, 23);
v_reservoir_2572_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2573_ = lean_ctor_get(v_cfg_2545_, 24);
v_restoreAllArtifacts_x3f_2574_ = lean_ctor_get(v_cfg_2545_, 25);
v_libPrefixOnWindows_2575_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28 + 4);
v_allowImportAll_2576_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2577_ = lean_ctor_get(v_cfg_2545_, 26);
v_checks_2578_ = lean_ctor_get(v_cfg_2545_, 27);
v_fixedToolchain_2579_ = lean_ctor_get_uint8(v_cfg_2545_, sizeof(void*)*28 + 6);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_cfg_2545_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v_cfg_2545_, 20);
lean_dec(v_unused_2587_);
v___x_2581_ = v_cfg_2545_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_checks_2578_);
lean_inc(v_builtinLint_x3f_2577_);
lean_inc(v_restoreAllArtifacts_x3f_2574_);
lean_inc(v_enableArtifactCache_x3f_2573_);
lean_inc(v_readmeFile_2571_);
lean_inc(v_licenseFiles_2570_);
lean_inc(v_license_2569_);
lean_inc(v_keywords_2568_);
lean_inc(v_description_2567_);
lean_inc(v_versionTags_2566_);
lean_inc(v_version_2565_);
lean_inc(v_lintDriverArgs_2564_);
lean_inc(v_lintDriver_2563_);
lean_inc(v_testDriverArgs_2562_);
lean_inc(v_testDriver_2561_);
lean_inc(v_buildArchive_2559_);
lean_inc(v_releaseRepo_2558_);
lean_inc(v_irDir_2557_);
lean_inc(v_binDir_2556_);
lean_inc(v_nativeLibDir_2555_);
lean_inc(v_leanLibDir_2554_);
lean_inc(v_buildDir_2553_);
lean_inc(v_srcDir_2552_);
lean_inc(v_moreGlobalServerArgs_2551_);
lean_inc(v_extraDepTargets_2549_);
lean_inc(v_toLeanConfig_2547_);
lean_inc(v_toWorkspaceConfig_2546_);
lean_dec(v_cfg_2545_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 20, v_val_2544_);
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_toWorkspaceConfig_2546_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_toLeanConfig_2547_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_extraDepTargets_2549_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_moreGlobalServerArgs_2551_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_srcDir_2552_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v_buildDir_2553_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v_leanLibDir_2554_);
lean_ctor_set(v_reuseFailAlloc_2585_, 7, v_nativeLibDir_2555_);
lean_ctor_set(v_reuseFailAlloc_2585_, 8, v_binDir_2556_);
lean_ctor_set(v_reuseFailAlloc_2585_, 9, v_irDir_2557_);
lean_ctor_set(v_reuseFailAlloc_2585_, 10, v_releaseRepo_2558_);
lean_ctor_set(v_reuseFailAlloc_2585_, 11, v_buildArchive_2559_);
lean_ctor_set(v_reuseFailAlloc_2585_, 12, v_testDriver_2561_);
lean_ctor_set(v_reuseFailAlloc_2585_, 13, v_testDriverArgs_2562_);
lean_ctor_set(v_reuseFailAlloc_2585_, 14, v_lintDriver_2563_);
lean_ctor_set(v_reuseFailAlloc_2585_, 15, v_lintDriverArgs_2564_);
lean_ctor_set(v_reuseFailAlloc_2585_, 16, v_version_2565_);
lean_ctor_set(v_reuseFailAlloc_2585_, 17, v_versionTags_2566_);
lean_ctor_set(v_reuseFailAlloc_2585_, 18, v_description_2567_);
lean_ctor_set(v_reuseFailAlloc_2585_, 19, v_keywords_2568_);
lean_ctor_set(v_reuseFailAlloc_2585_, 20, v_val_2544_);
lean_ctor_set(v_reuseFailAlloc_2585_, 21, v_license_2569_);
lean_ctor_set(v_reuseFailAlloc_2585_, 22, v_licenseFiles_2570_);
lean_ctor_set(v_reuseFailAlloc_2585_, 23, v_readmeFile_2571_);
lean_ctor_set(v_reuseFailAlloc_2585_, 24, v_enableArtifactCache_x3f_2573_);
lean_ctor_set(v_reuseFailAlloc_2585_, 25, v_restoreAllArtifacts_x3f_2574_);
lean_ctor_set(v_reuseFailAlloc_2585_, 26, v_builtinLint_x3f_2577_);
lean_ctor_set(v_reuseFailAlloc_2585_, 27, v_checks_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28, v_bootstrap_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28 + 1, v_precompileModules_2550_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2560_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28 + 3, v_reservoir_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28 + 5, v_allowImportAll_2576_);
lean_ctor_set_uint8(v_reuseFailAlloc_2585_, sizeof(void*)*28 + 6, v_fixedToolchain_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___lam__2(lean_object* v_f_2588_, lean_object* v_cfg_2589_){
_start:
{
lean_object* v_toWorkspaceConfig_2590_; lean_object* v_toLeanConfig_2591_; uint8_t v_bootstrap_2592_; lean_object* v_extraDepTargets_2593_; uint8_t v_precompileModules_2594_; lean_object* v_moreGlobalServerArgs_2595_; lean_object* v_srcDir_2596_; lean_object* v_buildDir_2597_; lean_object* v_leanLibDir_2598_; lean_object* v_nativeLibDir_2599_; lean_object* v_binDir_2600_; lean_object* v_irDir_2601_; lean_object* v_releaseRepo_2602_; lean_object* v_buildArchive_2603_; uint8_t v_preferReleaseBuild_2604_; lean_object* v_testDriver_2605_; lean_object* v_testDriverArgs_2606_; lean_object* v_lintDriver_2607_; lean_object* v_lintDriverArgs_2608_; lean_object* v_version_2609_; lean_object* v_versionTags_2610_; lean_object* v_description_2611_; lean_object* v_keywords_2612_; lean_object* v_homepage_2613_; lean_object* v_license_2614_; lean_object* v_licenseFiles_2615_; lean_object* v_readmeFile_2616_; uint8_t v_reservoir_2617_; lean_object* v_enableArtifactCache_x3f_2618_; lean_object* v_restoreAllArtifacts_x3f_2619_; uint8_t v_libPrefixOnWindows_2620_; uint8_t v_allowImportAll_2621_; lean_object* v_builtinLint_x3f_2622_; lean_object* v_checks_2623_; uint8_t v_fixedToolchain_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2632_; 
v_toWorkspaceConfig_2590_ = lean_ctor_get(v_cfg_2589_, 0);
v_toLeanConfig_2591_ = lean_ctor_get(v_cfg_2589_, 1);
v_bootstrap_2592_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28);
v_extraDepTargets_2593_ = lean_ctor_get(v_cfg_2589_, 2);
v_precompileModules_2594_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2595_ = lean_ctor_get(v_cfg_2589_, 3);
v_srcDir_2596_ = lean_ctor_get(v_cfg_2589_, 4);
v_buildDir_2597_ = lean_ctor_get(v_cfg_2589_, 5);
v_leanLibDir_2598_ = lean_ctor_get(v_cfg_2589_, 6);
v_nativeLibDir_2599_ = lean_ctor_get(v_cfg_2589_, 7);
v_binDir_2600_ = lean_ctor_get(v_cfg_2589_, 8);
v_irDir_2601_ = lean_ctor_get(v_cfg_2589_, 9);
v_releaseRepo_2602_ = lean_ctor_get(v_cfg_2589_, 10);
v_buildArchive_2603_ = lean_ctor_get(v_cfg_2589_, 11);
v_preferReleaseBuild_2604_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28 + 2);
v_testDriver_2605_ = lean_ctor_get(v_cfg_2589_, 12);
v_testDriverArgs_2606_ = lean_ctor_get(v_cfg_2589_, 13);
v_lintDriver_2607_ = lean_ctor_get(v_cfg_2589_, 14);
v_lintDriverArgs_2608_ = lean_ctor_get(v_cfg_2589_, 15);
v_version_2609_ = lean_ctor_get(v_cfg_2589_, 16);
v_versionTags_2610_ = lean_ctor_get(v_cfg_2589_, 17);
v_description_2611_ = lean_ctor_get(v_cfg_2589_, 18);
v_keywords_2612_ = lean_ctor_get(v_cfg_2589_, 19);
v_homepage_2613_ = lean_ctor_get(v_cfg_2589_, 20);
v_license_2614_ = lean_ctor_get(v_cfg_2589_, 21);
v_licenseFiles_2615_ = lean_ctor_get(v_cfg_2589_, 22);
v_readmeFile_2616_ = lean_ctor_get(v_cfg_2589_, 23);
v_reservoir_2617_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2618_ = lean_ctor_get(v_cfg_2589_, 24);
v_restoreAllArtifacts_x3f_2619_ = lean_ctor_get(v_cfg_2589_, 25);
v_libPrefixOnWindows_2620_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28 + 4);
v_allowImportAll_2621_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2622_ = lean_ctor_get(v_cfg_2589_, 26);
v_checks_2623_ = lean_ctor_get(v_cfg_2589_, 27);
v_fixedToolchain_2624_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*28 + 6);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_cfg_2589_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2626_ = v_cfg_2589_;
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_checks_2623_);
lean_inc(v_builtinLint_x3f_2622_);
lean_inc(v_restoreAllArtifacts_x3f_2619_);
lean_inc(v_enableArtifactCache_x3f_2618_);
lean_inc(v_readmeFile_2616_);
lean_inc(v_licenseFiles_2615_);
lean_inc(v_license_2614_);
lean_inc(v_homepage_2613_);
lean_inc(v_keywords_2612_);
lean_inc(v_description_2611_);
lean_inc(v_versionTags_2610_);
lean_inc(v_version_2609_);
lean_inc(v_lintDriverArgs_2608_);
lean_inc(v_lintDriver_2607_);
lean_inc(v_testDriverArgs_2606_);
lean_inc(v_testDriver_2605_);
lean_inc(v_buildArchive_2603_);
lean_inc(v_releaseRepo_2602_);
lean_inc(v_irDir_2601_);
lean_inc(v_binDir_2600_);
lean_inc(v_nativeLibDir_2599_);
lean_inc(v_leanLibDir_2598_);
lean_inc(v_buildDir_2597_);
lean_inc(v_srcDir_2596_);
lean_inc(v_moreGlobalServerArgs_2595_);
lean_inc(v_extraDepTargets_2593_);
lean_inc(v_toLeanConfig_2591_);
lean_inc(v_toWorkspaceConfig_2590_);
lean_dec(v_cfg_2589_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2628_ = lean_apply_1(v_f_2588_, v_homepage_2613_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 20, v___x_2628_);
v___x_2630_ = v___x_2626_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_toWorkspaceConfig_2590_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_toLeanConfig_2591_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_extraDepTargets_2593_);
lean_ctor_set(v_reuseFailAlloc_2631_, 3, v_moreGlobalServerArgs_2595_);
lean_ctor_set(v_reuseFailAlloc_2631_, 4, v_srcDir_2596_);
lean_ctor_set(v_reuseFailAlloc_2631_, 5, v_buildDir_2597_);
lean_ctor_set(v_reuseFailAlloc_2631_, 6, v_leanLibDir_2598_);
lean_ctor_set(v_reuseFailAlloc_2631_, 7, v_nativeLibDir_2599_);
lean_ctor_set(v_reuseFailAlloc_2631_, 8, v_binDir_2600_);
lean_ctor_set(v_reuseFailAlloc_2631_, 9, v_irDir_2601_);
lean_ctor_set(v_reuseFailAlloc_2631_, 10, v_releaseRepo_2602_);
lean_ctor_set(v_reuseFailAlloc_2631_, 11, v_buildArchive_2603_);
lean_ctor_set(v_reuseFailAlloc_2631_, 12, v_testDriver_2605_);
lean_ctor_set(v_reuseFailAlloc_2631_, 13, v_testDriverArgs_2606_);
lean_ctor_set(v_reuseFailAlloc_2631_, 14, v_lintDriver_2607_);
lean_ctor_set(v_reuseFailAlloc_2631_, 15, v_lintDriverArgs_2608_);
lean_ctor_set(v_reuseFailAlloc_2631_, 16, v_version_2609_);
lean_ctor_set(v_reuseFailAlloc_2631_, 17, v_versionTags_2610_);
lean_ctor_set(v_reuseFailAlloc_2631_, 18, v_description_2611_);
lean_ctor_set(v_reuseFailAlloc_2631_, 19, v_keywords_2612_);
lean_ctor_set(v_reuseFailAlloc_2631_, 20, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2631_, 21, v_license_2614_);
lean_ctor_set(v_reuseFailAlloc_2631_, 22, v_licenseFiles_2615_);
lean_ctor_set(v_reuseFailAlloc_2631_, 23, v_readmeFile_2616_);
lean_ctor_set(v_reuseFailAlloc_2631_, 24, v_enableArtifactCache_x3f_2618_);
lean_ctor_set(v_reuseFailAlloc_2631_, 25, v_restoreAllArtifacts_x3f_2619_);
lean_ctor_set(v_reuseFailAlloc_2631_, 26, v_builtinLint_x3f_2622_);
lean_ctor_set(v_reuseFailAlloc_2631_, 27, v_checks_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28, v_bootstrap_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28 + 1, v_precompileModules_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28 + 3, v_reservoir_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28 + 5, v_allowImportAll_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*28 + 6, v_fixedToolchain_2624_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_2641_, lean_object* v_n_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___closed__3));
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_2644_, lean_object* v_n_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lake_PackageConfig_homepage___proj(v_p_2644_, v_n_2645_);
lean_dec(v_n_2645_);
lean_dec(v_p_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_2647_, lean_object* v_n_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lake_PackageConfig_homepage___proj(v_p_2647_, v_n_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_2650_, lean_object* v_n_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_2650_, v_n_2651_);
lean_dec(v_n_2651_);
lean_dec(v_p_2650_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0(lean_object* v_cfg_2653_){
_start:
{
lean_object* v_license_2654_; 
v_license_2654_ = lean_ctor_get(v_cfg_2653_, 21);
lean_inc_ref(v_license_2654_);
return v_license_2654_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__0___boxed(lean_object* v_cfg_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lake_PackageConfig_license___proj___lam__0(v_cfg_2655_);
lean_dec_ref(v_cfg_2655_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__1(lean_object* v_val_2657_, lean_object* v_cfg_2658_){
_start:
{
lean_object* v_toWorkspaceConfig_2659_; lean_object* v_toLeanConfig_2660_; uint8_t v_bootstrap_2661_; lean_object* v_extraDepTargets_2662_; uint8_t v_precompileModules_2663_; lean_object* v_moreGlobalServerArgs_2664_; lean_object* v_srcDir_2665_; lean_object* v_buildDir_2666_; lean_object* v_leanLibDir_2667_; lean_object* v_nativeLibDir_2668_; lean_object* v_binDir_2669_; lean_object* v_irDir_2670_; lean_object* v_releaseRepo_2671_; lean_object* v_buildArchive_2672_; uint8_t v_preferReleaseBuild_2673_; lean_object* v_testDriver_2674_; lean_object* v_testDriverArgs_2675_; lean_object* v_lintDriver_2676_; lean_object* v_lintDriverArgs_2677_; lean_object* v_version_2678_; lean_object* v_versionTags_2679_; lean_object* v_description_2680_; lean_object* v_keywords_2681_; lean_object* v_homepage_2682_; lean_object* v_licenseFiles_2683_; lean_object* v_readmeFile_2684_; uint8_t v_reservoir_2685_; lean_object* v_enableArtifactCache_x3f_2686_; lean_object* v_restoreAllArtifacts_x3f_2687_; uint8_t v_libPrefixOnWindows_2688_; uint8_t v_allowImportAll_2689_; lean_object* v_builtinLint_x3f_2690_; lean_object* v_checks_2691_; uint8_t v_fixedToolchain_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_toWorkspaceConfig_2659_ = lean_ctor_get(v_cfg_2658_, 0);
v_toLeanConfig_2660_ = lean_ctor_get(v_cfg_2658_, 1);
v_bootstrap_2661_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28);
v_extraDepTargets_2662_ = lean_ctor_get(v_cfg_2658_, 2);
v_precompileModules_2663_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2664_ = lean_ctor_get(v_cfg_2658_, 3);
v_srcDir_2665_ = lean_ctor_get(v_cfg_2658_, 4);
v_buildDir_2666_ = lean_ctor_get(v_cfg_2658_, 5);
v_leanLibDir_2667_ = lean_ctor_get(v_cfg_2658_, 6);
v_nativeLibDir_2668_ = lean_ctor_get(v_cfg_2658_, 7);
v_binDir_2669_ = lean_ctor_get(v_cfg_2658_, 8);
v_irDir_2670_ = lean_ctor_get(v_cfg_2658_, 9);
v_releaseRepo_2671_ = lean_ctor_get(v_cfg_2658_, 10);
v_buildArchive_2672_ = lean_ctor_get(v_cfg_2658_, 11);
v_preferReleaseBuild_2673_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28 + 2);
v_testDriver_2674_ = lean_ctor_get(v_cfg_2658_, 12);
v_testDriverArgs_2675_ = lean_ctor_get(v_cfg_2658_, 13);
v_lintDriver_2676_ = lean_ctor_get(v_cfg_2658_, 14);
v_lintDriverArgs_2677_ = lean_ctor_get(v_cfg_2658_, 15);
v_version_2678_ = lean_ctor_get(v_cfg_2658_, 16);
v_versionTags_2679_ = lean_ctor_get(v_cfg_2658_, 17);
v_description_2680_ = lean_ctor_get(v_cfg_2658_, 18);
v_keywords_2681_ = lean_ctor_get(v_cfg_2658_, 19);
v_homepage_2682_ = lean_ctor_get(v_cfg_2658_, 20);
v_licenseFiles_2683_ = lean_ctor_get(v_cfg_2658_, 22);
v_readmeFile_2684_ = lean_ctor_get(v_cfg_2658_, 23);
v_reservoir_2685_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2686_ = lean_ctor_get(v_cfg_2658_, 24);
v_restoreAllArtifacts_x3f_2687_ = lean_ctor_get(v_cfg_2658_, 25);
v_libPrefixOnWindows_2688_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28 + 4);
v_allowImportAll_2689_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2690_ = lean_ctor_get(v_cfg_2658_, 26);
v_checks_2691_ = lean_ctor_get(v_cfg_2658_, 27);
v_fixedToolchain_2692_ = lean_ctor_get_uint8(v_cfg_2658_, sizeof(void*)*28 + 6);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_cfg_2658_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v_cfg_2658_, 21);
lean_dec(v_unused_2700_);
v___x_2694_ = v_cfg_2658_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_checks_2691_);
lean_inc(v_builtinLint_x3f_2690_);
lean_inc(v_restoreAllArtifacts_x3f_2687_);
lean_inc(v_enableArtifactCache_x3f_2686_);
lean_inc(v_readmeFile_2684_);
lean_inc(v_licenseFiles_2683_);
lean_inc(v_homepage_2682_);
lean_inc(v_keywords_2681_);
lean_inc(v_description_2680_);
lean_inc(v_versionTags_2679_);
lean_inc(v_version_2678_);
lean_inc(v_lintDriverArgs_2677_);
lean_inc(v_lintDriver_2676_);
lean_inc(v_testDriverArgs_2675_);
lean_inc(v_testDriver_2674_);
lean_inc(v_buildArchive_2672_);
lean_inc(v_releaseRepo_2671_);
lean_inc(v_irDir_2670_);
lean_inc(v_binDir_2669_);
lean_inc(v_nativeLibDir_2668_);
lean_inc(v_leanLibDir_2667_);
lean_inc(v_buildDir_2666_);
lean_inc(v_srcDir_2665_);
lean_inc(v_moreGlobalServerArgs_2664_);
lean_inc(v_extraDepTargets_2662_);
lean_inc(v_toLeanConfig_2660_);
lean_inc(v_toWorkspaceConfig_2659_);
lean_dec(v_cfg_2658_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 21, v_val_2657_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_toWorkspaceConfig_2659_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_toLeanConfig_2660_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_extraDepTargets_2662_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_moreGlobalServerArgs_2664_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_srcDir_2665_);
lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_buildDir_2666_);
lean_ctor_set(v_reuseFailAlloc_2698_, 6, v_leanLibDir_2667_);
lean_ctor_set(v_reuseFailAlloc_2698_, 7, v_nativeLibDir_2668_);
lean_ctor_set(v_reuseFailAlloc_2698_, 8, v_binDir_2669_);
lean_ctor_set(v_reuseFailAlloc_2698_, 9, v_irDir_2670_);
lean_ctor_set(v_reuseFailAlloc_2698_, 10, v_releaseRepo_2671_);
lean_ctor_set(v_reuseFailAlloc_2698_, 11, v_buildArchive_2672_);
lean_ctor_set(v_reuseFailAlloc_2698_, 12, v_testDriver_2674_);
lean_ctor_set(v_reuseFailAlloc_2698_, 13, v_testDriverArgs_2675_);
lean_ctor_set(v_reuseFailAlloc_2698_, 14, v_lintDriver_2676_);
lean_ctor_set(v_reuseFailAlloc_2698_, 15, v_lintDriverArgs_2677_);
lean_ctor_set(v_reuseFailAlloc_2698_, 16, v_version_2678_);
lean_ctor_set(v_reuseFailAlloc_2698_, 17, v_versionTags_2679_);
lean_ctor_set(v_reuseFailAlloc_2698_, 18, v_description_2680_);
lean_ctor_set(v_reuseFailAlloc_2698_, 19, v_keywords_2681_);
lean_ctor_set(v_reuseFailAlloc_2698_, 20, v_homepage_2682_);
lean_ctor_set(v_reuseFailAlloc_2698_, 21, v_val_2657_);
lean_ctor_set(v_reuseFailAlloc_2698_, 22, v_licenseFiles_2683_);
lean_ctor_set(v_reuseFailAlloc_2698_, 23, v_readmeFile_2684_);
lean_ctor_set(v_reuseFailAlloc_2698_, 24, v_enableArtifactCache_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2698_, 25, v_restoreAllArtifacts_x3f_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 26, v_builtinLint_x3f_2690_);
lean_ctor_set(v_reuseFailAlloc_2698_, 27, v_checks_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28, v_bootstrap_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28 + 1, v_precompileModules_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28 + 3, v_reservoir_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28 + 5, v_allowImportAll_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2698_, sizeof(void*)*28 + 6, v_fixedToolchain_2692_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___lam__2(lean_object* v_f_2701_, lean_object* v_cfg_2702_){
_start:
{
lean_object* v_toWorkspaceConfig_2703_; lean_object* v_toLeanConfig_2704_; uint8_t v_bootstrap_2705_; lean_object* v_extraDepTargets_2706_; uint8_t v_precompileModules_2707_; lean_object* v_moreGlobalServerArgs_2708_; lean_object* v_srcDir_2709_; lean_object* v_buildDir_2710_; lean_object* v_leanLibDir_2711_; lean_object* v_nativeLibDir_2712_; lean_object* v_binDir_2713_; lean_object* v_irDir_2714_; lean_object* v_releaseRepo_2715_; lean_object* v_buildArchive_2716_; uint8_t v_preferReleaseBuild_2717_; lean_object* v_testDriver_2718_; lean_object* v_testDriverArgs_2719_; lean_object* v_lintDriver_2720_; lean_object* v_lintDriverArgs_2721_; lean_object* v_version_2722_; lean_object* v_versionTags_2723_; lean_object* v_description_2724_; lean_object* v_keywords_2725_; lean_object* v_homepage_2726_; lean_object* v_license_2727_; lean_object* v_licenseFiles_2728_; lean_object* v_readmeFile_2729_; uint8_t v_reservoir_2730_; lean_object* v_enableArtifactCache_x3f_2731_; lean_object* v_restoreAllArtifacts_x3f_2732_; uint8_t v_libPrefixOnWindows_2733_; uint8_t v_allowImportAll_2734_; lean_object* v_builtinLint_x3f_2735_; lean_object* v_checks_2736_; uint8_t v_fixedToolchain_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2745_; 
v_toWorkspaceConfig_2703_ = lean_ctor_get(v_cfg_2702_, 0);
v_toLeanConfig_2704_ = lean_ctor_get(v_cfg_2702_, 1);
v_bootstrap_2705_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28);
v_extraDepTargets_2706_ = lean_ctor_get(v_cfg_2702_, 2);
v_precompileModules_2707_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2708_ = lean_ctor_get(v_cfg_2702_, 3);
v_srcDir_2709_ = lean_ctor_get(v_cfg_2702_, 4);
v_buildDir_2710_ = lean_ctor_get(v_cfg_2702_, 5);
v_leanLibDir_2711_ = lean_ctor_get(v_cfg_2702_, 6);
v_nativeLibDir_2712_ = lean_ctor_get(v_cfg_2702_, 7);
v_binDir_2713_ = lean_ctor_get(v_cfg_2702_, 8);
v_irDir_2714_ = lean_ctor_get(v_cfg_2702_, 9);
v_releaseRepo_2715_ = lean_ctor_get(v_cfg_2702_, 10);
v_buildArchive_2716_ = lean_ctor_get(v_cfg_2702_, 11);
v_preferReleaseBuild_2717_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28 + 2);
v_testDriver_2718_ = lean_ctor_get(v_cfg_2702_, 12);
v_testDriverArgs_2719_ = lean_ctor_get(v_cfg_2702_, 13);
v_lintDriver_2720_ = lean_ctor_get(v_cfg_2702_, 14);
v_lintDriverArgs_2721_ = lean_ctor_get(v_cfg_2702_, 15);
v_version_2722_ = lean_ctor_get(v_cfg_2702_, 16);
v_versionTags_2723_ = lean_ctor_get(v_cfg_2702_, 17);
v_description_2724_ = lean_ctor_get(v_cfg_2702_, 18);
v_keywords_2725_ = lean_ctor_get(v_cfg_2702_, 19);
v_homepage_2726_ = lean_ctor_get(v_cfg_2702_, 20);
v_license_2727_ = lean_ctor_get(v_cfg_2702_, 21);
v_licenseFiles_2728_ = lean_ctor_get(v_cfg_2702_, 22);
v_readmeFile_2729_ = lean_ctor_get(v_cfg_2702_, 23);
v_reservoir_2730_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2731_ = lean_ctor_get(v_cfg_2702_, 24);
v_restoreAllArtifacts_x3f_2732_ = lean_ctor_get(v_cfg_2702_, 25);
v_libPrefixOnWindows_2733_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28 + 4);
v_allowImportAll_2734_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2735_ = lean_ctor_get(v_cfg_2702_, 26);
v_checks_2736_ = lean_ctor_get(v_cfg_2702_, 27);
v_fixedToolchain_2737_ = lean_ctor_get_uint8(v_cfg_2702_, sizeof(void*)*28 + 6);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_cfg_2702_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2739_ = v_cfg_2702_;
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_checks_2736_);
lean_inc(v_builtinLint_x3f_2735_);
lean_inc(v_restoreAllArtifacts_x3f_2732_);
lean_inc(v_enableArtifactCache_x3f_2731_);
lean_inc(v_readmeFile_2729_);
lean_inc(v_licenseFiles_2728_);
lean_inc(v_license_2727_);
lean_inc(v_homepage_2726_);
lean_inc(v_keywords_2725_);
lean_inc(v_description_2724_);
lean_inc(v_versionTags_2723_);
lean_inc(v_version_2722_);
lean_inc(v_lintDriverArgs_2721_);
lean_inc(v_lintDriver_2720_);
lean_inc(v_testDriverArgs_2719_);
lean_inc(v_testDriver_2718_);
lean_inc(v_buildArchive_2716_);
lean_inc(v_releaseRepo_2715_);
lean_inc(v_irDir_2714_);
lean_inc(v_binDir_2713_);
lean_inc(v_nativeLibDir_2712_);
lean_inc(v_leanLibDir_2711_);
lean_inc(v_buildDir_2710_);
lean_inc(v_srcDir_2709_);
lean_inc(v_moreGlobalServerArgs_2708_);
lean_inc(v_extraDepTargets_2706_);
lean_inc(v_toLeanConfig_2704_);
lean_inc(v_toWorkspaceConfig_2703_);
lean_dec(v_cfg_2702_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_apply_1(v_f_2701_, v_license_2727_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 21, v___x_2741_);
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_toWorkspaceConfig_2703_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_toLeanConfig_2704_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_extraDepTargets_2706_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_moreGlobalServerArgs_2708_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_srcDir_2709_);
lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_buildDir_2710_);
lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_leanLibDir_2711_);
lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_nativeLibDir_2712_);
lean_ctor_set(v_reuseFailAlloc_2744_, 8, v_binDir_2713_);
lean_ctor_set(v_reuseFailAlloc_2744_, 9, v_irDir_2714_);
lean_ctor_set(v_reuseFailAlloc_2744_, 10, v_releaseRepo_2715_);
lean_ctor_set(v_reuseFailAlloc_2744_, 11, v_buildArchive_2716_);
lean_ctor_set(v_reuseFailAlloc_2744_, 12, v_testDriver_2718_);
lean_ctor_set(v_reuseFailAlloc_2744_, 13, v_testDriverArgs_2719_);
lean_ctor_set(v_reuseFailAlloc_2744_, 14, v_lintDriver_2720_);
lean_ctor_set(v_reuseFailAlloc_2744_, 15, v_lintDriverArgs_2721_);
lean_ctor_set(v_reuseFailAlloc_2744_, 16, v_version_2722_);
lean_ctor_set(v_reuseFailAlloc_2744_, 17, v_versionTags_2723_);
lean_ctor_set(v_reuseFailAlloc_2744_, 18, v_description_2724_);
lean_ctor_set(v_reuseFailAlloc_2744_, 19, v_keywords_2725_);
lean_ctor_set(v_reuseFailAlloc_2744_, 20, v_homepage_2726_);
lean_ctor_set(v_reuseFailAlloc_2744_, 21, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 22, v_licenseFiles_2728_);
lean_ctor_set(v_reuseFailAlloc_2744_, 23, v_readmeFile_2729_);
lean_ctor_set(v_reuseFailAlloc_2744_, 24, v_enableArtifactCache_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2744_, 25, v_restoreAllArtifacts_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2744_, 26, v_builtinLint_x3f_2735_);
lean_ctor_set(v_reuseFailAlloc_2744_, 27, v_checks_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28, v_bootstrap_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28 + 1, v_precompileModules_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28 + 3, v_reservoir_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28 + 5, v_allowImportAll_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*28 + 6, v_fixedToolchain_2737_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_2754_, lean_object* v_n_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___closed__3));
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_2757_, lean_object* v_n_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lake_PackageConfig_license___proj(v_p_2757_, v_n_2758_);
lean_dec(v_n_2758_);
lean_dec(v_p_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_2760_, lean_object* v_n_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lake_PackageConfig_license___proj(v_p_2760_, v_n_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_2763_, lean_object* v_n_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lake_PackageConfig_license_instConfigField(v_p_2763_, v_n_2764_);
lean_dec(v_n_2764_);
lean_dec(v_p_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0(lean_object* v_cfg_2766_){
_start:
{
lean_object* v_licenseFiles_2767_; 
v_licenseFiles_2767_ = lean_ctor_get(v_cfg_2766_, 22);
lean_inc_ref(v_licenseFiles_2767_);
return v_licenseFiles_2767_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__0___boxed(lean_object* v_cfg_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lake_PackageConfig_licenseFiles___proj___lam__0(v_cfg_2768_);
lean_dec_ref(v_cfg_2768_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__1(lean_object* v_val_2770_, lean_object* v_cfg_2771_){
_start:
{
lean_object* v_toWorkspaceConfig_2772_; lean_object* v_toLeanConfig_2773_; uint8_t v_bootstrap_2774_; lean_object* v_extraDepTargets_2775_; uint8_t v_precompileModules_2776_; lean_object* v_moreGlobalServerArgs_2777_; lean_object* v_srcDir_2778_; lean_object* v_buildDir_2779_; lean_object* v_leanLibDir_2780_; lean_object* v_nativeLibDir_2781_; lean_object* v_binDir_2782_; lean_object* v_irDir_2783_; lean_object* v_releaseRepo_2784_; lean_object* v_buildArchive_2785_; uint8_t v_preferReleaseBuild_2786_; lean_object* v_testDriver_2787_; lean_object* v_testDriverArgs_2788_; lean_object* v_lintDriver_2789_; lean_object* v_lintDriverArgs_2790_; lean_object* v_version_2791_; lean_object* v_versionTags_2792_; lean_object* v_description_2793_; lean_object* v_keywords_2794_; lean_object* v_homepage_2795_; lean_object* v_license_2796_; lean_object* v_readmeFile_2797_; uint8_t v_reservoir_2798_; lean_object* v_enableArtifactCache_x3f_2799_; lean_object* v_restoreAllArtifacts_x3f_2800_; uint8_t v_libPrefixOnWindows_2801_; uint8_t v_allowImportAll_2802_; lean_object* v_builtinLint_x3f_2803_; lean_object* v_checks_2804_; uint8_t v_fixedToolchain_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_toWorkspaceConfig_2772_ = lean_ctor_get(v_cfg_2771_, 0);
v_toLeanConfig_2773_ = lean_ctor_get(v_cfg_2771_, 1);
v_bootstrap_2774_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28);
v_extraDepTargets_2775_ = lean_ctor_get(v_cfg_2771_, 2);
v_precompileModules_2776_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2777_ = lean_ctor_get(v_cfg_2771_, 3);
v_srcDir_2778_ = lean_ctor_get(v_cfg_2771_, 4);
v_buildDir_2779_ = lean_ctor_get(v_cfg_2771_, 5);
v_leanLibDir_2780_ = lean_ctor_get(v_cfg_2771_, 6);
v_nativeLibDir_2781_ = lean_ctor_get(v_cfg_2771_, 7);
v_binDir_2782_ = lean_ctor_get(v_cfg_2771_, 8);
v_irDir_2783_ = lean_ctor_get(v_cfg_2771_, 9);
v_releaseRepo_2784_ = lean_ctor_get(v_cfg_2771_, 10);
v_buildArchive_2785_ = lean_ctor_get(v_cfg_2771_, 11);
v_preferReleaseBuild_2786_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28 + 2);
v_testDriver_2787_ = lean_ctor_get(v_cfg_2771_, 12);
v_testDriverArgs_2788_ = lean_ctor_get(v_cfg_2771_, 13);
v_lintDriver_2789_ = lean_ctor_get(v_cfg_2771_, 14);
v_lintDriverArgs_2790_ = lean_ctor_get(v_cfg_2771_, 15);
v_version_2791_ = lean_ctor_get(v_cfg_2771_, 16);
v_versionTags_2792_ = lean_ctor_get(v_cfg_2771_, 17);
v_description_2793_ = lean_ctor_get(v_cfg_2771_, 18);
v_keywords_2794_ = lean_ctor_get(v_cfg_2771_, 19);
v_homepage_2795_ = lean_ctor_get(v_cfg_2771_, 20);
v_license_2796_ = lean_ctor_get(v_cfg_2771_, 21);
v_readmeFile_2797_ = lean_ctor_get(v_cfg_2771_, 23);
v_reservoir_2798_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2799_ = lean_ctor_get(v_cfg_2771_, 24);
v_restoreAllArtifacts_x3f_2800_ = lean_ctor_get(v_cfg_2771_, 25);
v_libPrefixOnWindows_2801_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28 + 4);
v_allowImportAll_2802_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2803_ = lean_ctor_get(v_cfg_2771_, 26);
v_checks_2804_ = lean_ctor_get(v_cfg_2771_, 27);
v_fixedToolchain_2805_ = lean_ctor_get_uint8(v_cfg_2771_, sizeof(void*)*28 + 6);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_cfg_2771_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v_cfg_2771_, 22);
lean_dec(v_unused_2813_);
v___x_2807_ = v_cfg_2771_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_checks_2804_);
lean_inc(v_builtinLint_x3f_2803_);
lean_inc(v_restoreAllArtifacts_x3f_2800_);
lean_inc(v_enableArtifactCache_x3f_2799_);
lean_inc(v_readmeFile_2797_);
lean_inc(v_license_2796_);
lean_inc(v_homepage_2795_);
lean_inc(v_keywords_2794_);
lean_inc(v_description_2793_);
lean_inc(v_versionTags_2792_);
lean_inc(v_version_2791_);
lean_inc(v_lintDriverArgs_2790_);
lean_inc(v_lintDriver_2789_);
lean_inc(v_testDriverArgs_2788_);
lean_inc(v_testDriver_2787_);
lean_inc(v_buildArchive_2785_);
lean_inc(v_releaseRepo_2784_);
lean_inc(v_irDir_2783_);
lean_inc(v_binDir_2782_);
lean_inc(v_nativeLibDir_2781_);
lean_inc(v_leanLibDir_2780_);
lean_inc(v_buildDir_2779_);
lean_inc(v_srcDir_2778_);
lean_inc(v_moreGlobalServerArgs_2777_);
lean_inc(v_extraDepTargets_2775_);
lean_inc(v_toLeanConfig_2773_);
lean_inc(v_toWorkspaceConfig_2772_);
lean_dec(v_cfg_2771_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 22, v_val_2770_);
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_toWorkspaceConfig_2772_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_toLeanConfig_2773_);
lean_ctor_set(v_reuseFailAlloc_2811_, 2, v_extraDepTargets_2775_);
lean_ctor_set(v_reuseFailAlloc_2811_, 3, v_moreGlobalServerArgs_2777_);
lean_ctor_set(v_reuseFailAlloc_2811_, 4, v_srcDir_2778_);
lean_ctor_set(v_reuseFailAlloc_2811_, 5, v_buildDir_2779_);
lean_ctor_set(v_reuseFailAlloc_2811_, 6, v_leanLibDir_2780_);
lean_ctor_set(v_reuseFailAlloc_2811_, 7, v_nativeLibDir_2781_);
lean_ctor_set(v_reuseFailAlloc_2811_, 8, v_binDir_2782_);
lean_ctor_set(v_reuseFailAlloc_2811_, 9, v_irDir_2783_);
lean_ctor_set(v_reuseFailAlloc_2811_, 10, v_releaseRepo_2784_);
lean_ctor_set(v_reuseFailAlloc_2811_, 11, v_buildArchive_2785_);
lean_ctor_set(v_reuseFailAlloc_2811_, 12, v_testDriver_2787_);
lean_ctor_set(v_reuseFailAlloc_2811_, 13, v_testDriverArgs_2788_);
lean_ctor_set(v_reuseFailAlloc_2811_, 14, v_lintDriver_2789_);
lean_ctor_set(v_reuseFailAlloc_2811_, 15, v_lintDriverArgs_2790_);
lean_ctor_set(v_reuseFailAlloc_2811_, 16, v_version_2791_);
lean_ctor_set(v_reuseFailAlloc_2811_, 17, v_versionTags_2792_);
lean_ctor_set(v_reuseFailAlloc_2811_, 18, v_description_2793_);
lean_ctor_set(v_reuseFailAlloc_2811_, 19, v_keywords_2794_);
lean_ctor_set(v_reuseFailAlloc_2811_, 20, v_homepage_2795_);
lean_ctor_set(v_reuseFailAlloc_2811_, 21, v_license_2796_);
lean_ctor_set(v_reuseFailAlloc_2811_, 22, v_val_2770_);
lean_ctor_set(v_reuseFailAlloc_2811_, 23, v_readmeFile_2797_);
lean_ctor_set(v_reuseFailAlloc_2811_, 24, v_enableArtifactCache_x3f_2799_);
lean_ctor_set(v_reuseFailAlloc_2811_, 25, v_restoreAllArtifacts_x3f_2800_);
lean_ctor_set(v_reuseFailAlloc_2811_, 26, v_builtinLint_x3f_2803_);
lean_ctor_set(v_reuseFailAlloc_2811_, 27, v_checks_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28, v_bootstrap_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28 + 1, v_precompileModules_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28 + 3, v_reservoir_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28 + 5, v_allowImportAll_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*28 + 6, v_fixedToolchain_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__2(lean_object* v_f_2814_, lean_object* v_cfg_2815_){
_start:
{
lean_object* v_toWorkspaceConfig_2816_; lean_object* v_toLeanConfig_2817_; uint8_t v_bootstrap_2818_; lean_object* v_extraDepTargets_2819_; uint8_t v_precompileModules_2820_; lean_object* v_moreGlobalServerArgs_2821_; lean_object* v_srcDir_2822_; lean_object* v_buildDir_2823_; lean_object* v_leanLibDir_2824_; lean_object* v_nativeLibDir_2825_; lean_object* v_binDir_2826_; lean_object* v_irDir_2827_; lean_object* v_releaseRepo_2828_; lean_object* v_buildArchive_2829_; uint8_t v_preferReleaseBuild_2830_; lean_object* v_testDriver_2831_; lean_object* v_testDriverArgs_2832_; lean_object* v_lintDriver_2833_; lean_object* v_lintDriverArgs_2834_; lean_object* v_version_2835_; lean_object* v_versionTags_2836_; lean_object* v_description_2837_; lean_object* v_keywords_2838_; lean_object* v_homepage_2839_; lean_object* v_license_2840_; lean_object* v_licenseFiles_2841_; lean_object* v_readmeFile_2842_; uint8_t v_reservoir_2843_; lean_object* v_enableArtifactCache_x3f_2844_; lean_object* v_restoreAllArtifacts_x3f_2845_; uint8_t v_libPrefixOnWindows_2846_; uint8_t v_allowImportAll_2847_; lean_object* v_builtinLint_x3f_2848_; lean_object* v_checks_2849_; uint8_t v_fixedToolchain_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2858_; 
v_toWorkspaceConfig_2816_ = lean_ctor_get(v_cfg_2815_, 0);
v_toLeanConfig_2817_ = lean_ctor_get(v_cfg_2815_, 1);
v_bootstrap_2818_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28);
v_extraDepTargets_2819_ = lean_ctor_get(v_cfg_2815_, 2);
v_precompileModules_2820_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2821_ = lean_ctor_get(v_cfg_2815_, 3);
v_srcDir_2822_ = lean_ctor_get(v_cfg_2815_, 4);
v_buildDir_2823_ = lean_ctor_get(v_cfg_2815_, 5);
v_leanLibDir_2824_ = lean_ctor_get(v_cfg_2815_, 6);
v_nativeLibDir_2825_ = lean_ctor_get(v_cfg_2815_, 7);
v_binDir_2826_ = lean_ctor_get(v_cfg_2815_, 8);
v_irDir_2827_ = lean_ctor_get(v_cfg_2815_, 9);
v_releaseRepo_2828_ = lean_ctor_get(v_cfg_2815_, 10);
v_buildArchive_2829_ = lean_ctor_get(v_cfg_2815_, 11);
v_preferReleaseBuild_2830_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28 + 2);
v_testDriver_2831_ = lean_ctor_get(v_cfg_2815_, 12);
v_testDriverArgs_2832_ = lean_ctor_get(v_cfg_2815_, 13);
v_lintDriver_2833_ = lean_ctor_get(v_cfg_2815_, 14);
v_lintDriverArgs_2834_ = lean_ctor_get(v_cfg_2815_, 15);
v_version_2835_ = lean_ctor_get(v_cfg_2815_, 16);
v_versionTags_2836_ = lean_ctor_get(v_cfg_2815_, 17);
v_description_2837_ = lean_ctor_get(v_cfg_2815_, 18);
v_keywords_2838_ = lean_ctor_get(v_cfg_2815_, 19);
v_homepage_2839_ = lean_ctor_get(v_cfg_2815_, 20);
v_license_2840_ = lean_ctor_get(v_cfg_2815_, 21);
v_licenseFiles_2841_ = lean_ctor_get(v_cfg_2815_, 22);
v_readmeFile_2842_ = lean_ctor_get(v_cfg_2815_, 23);
v_reservoir_2843_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2844_ = lean_ctor_get(v_cfg_2815_, 24);
v_restoreAllArtifacts_x3f_2845_ = lean_ctor_get(v_cfg_2815_, 25);
v_libPrefixOnWindows_2846_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28 + 4);
v_allowImportAll_2847_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2848_ = lean_ctor_get(v_cfg_2815_, 26);
v_checks_2849_ = lean_ctor_get(v_cfg_2815_, 27);
v_fixedToolchain_2850_ = lean_ctor_get_uint8(v_cfg_2815_, sizeof(void*)*28 + 6);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_cfg_2815_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2852_ = v_cfg_2815_;
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_checks_2849_);
lean_inc(v_builtinLint_x3f_2848_);
lean_inc(v_restoreAllArtifacts_x3f_2845_);
lean_inc(v_enableArtifactCache_x3f_2844_);
lean_inc(v_readmeFile_2842_);
lean_inc(v_licenseFiles_2841_);
lean_inc(v_license_2840_);
lean_inc(v_homepage_2839_);
lean_inc(v_keywords_2838_);
lean_inc(v_description_2837_);
lean_inc(v_versionTags_2836_);
lean_inc(v_version_2835_);
lean_inc(v_lintDriverArgs_2834_);
lean_inc(v_lintDriver_2833_);
lean_inc(v_testDriverArgs_2832_);
lean_inc(v_testDriver_2831_);
lean_inc(v_buildArchive_2829_);
lean_inc(v_releaseRepo_2828_);
lean_inc(v_irDir_2827_);
lean_inc(v_binDir_2826_);
lean_inc(v_nativeLibDir_2825_);
lean_inc(v_leanLibDir_2824_);
lean_inc(v_buildDir_2823_);
lean_inc(v_srcDir_2822_);
lean_inc(v_moreGlobalServerArgs_2821_);
lean_inc(v_extraDepTargets_2819_);
lean_inc(v_toLeanConfig_2817_);
lean_inc(v_toWorkspaceConfig_2816_);
lean_dec(v_cfg_2815_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = lean_apply_1(v_f_2814_, v_licenseFiles_2841_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 22, v___x_2854_);
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_toWorkspaceConfig_2816_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_toLeanConfig_2817_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_extraDepTargets_2819_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_moreGlobalServerArgs_2821_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_srcDir_2822_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v_buildDir_2823_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_leanLibDir_2824_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_nativeLibDir_2825_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_binDir_2826_);
lean_ctor_set(v_reuseFailAlloc_2857_, 9, v_irDir_2827_);
lean_ctor_set(v_reuseFailAlloc_2857_, 10, v_releaseRepo_2828_);
lean_ctor_set(v_reuseFailAlloc_2857_, 11, v_buildArchive_2829_);
lean_ctor_set(v_reuseFailAlloc_2857_, 12, v_testDriver_2831_);
lean_ctor_set(v_reuseFailAlloc_2857_, 13, v_testDriverArgs_2832_);
lean_ctor_set(v_reuseFailAlloc_2857_, 14, v_lintDriver_2833_);
lean_ctor_set(v_reuseFailAlloc_2857_, 15, v_lintDriverArgs_2834_);
lean_ctor_set(v_reuseFailAlloc_2857_, 16, v_version_2835_);
lean_ctor_set(v_reuseFailAlloc_2857_, 17, v_versionTags_2836_);
lean_ctor_set(v_reuseFailAlloc_2857_, 18, v_description_2837_);
lean_ctor_set(v_reuseFailAlloc_2857_, 19, v_keywords_2838_);
lean_ctor_set(v_reuseFailAlloc_2857_, 20, v_homepage_2839_);
lean_ctor_set(v_reuseFailAlloc_2857_, 21, v_license_2840_);
lean_ctor_set(v_reuseFailAlloc_2857_, 22, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2857_, 23, v_readmeFile_2842_);
lean_ctor_set(v_reuseFailAlloc_2857_, 24, v_enableArtifactCache_x3f_2844_);
lean_ctor_set(v_reuseFailAlloc_2857_, 25, v_restoreAllArtifacts_x3f_2845_);
lean_ctor_set(v_reuseFailAlloc_2857_, 26, v_builtinLint_x3f_2848_);
lean_ctor_set(v_reuseFailAlloc_2857_, 27, v_checks_2849_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28, v_bootstrap_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28 + 1, v_precompileModules_2820_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2830_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28 + 3, v_reservoir_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28 + 5, v_allowImportAll_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2857_, sizeof(void*)*28 + 6, v_fixedToolchain_2850_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3(lean_object* v_x_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2860_ = lean_unsigned_to_nat(1u);
v___x_2861_ = lean_mk_empty_array_with_capacity(v___x_2860_);
lean_dec_ref(v___x_2861_);
v___x_2862_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___lam__3___boxed(lean_object* v_x_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lake_PackageConfig_licenseFiles___proj___lam__3(v_x_2863_);
lean_dec_ref(v_x_2863_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_2874_, lean_object* v_n_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___closed__4));
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_2877_, lean_object* v_n_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2877_, v_n_2878_);
lean_dec(v_n_2878_);
lean_dec(v_p_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_2880_, lean_object* v_n_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_2880_, v_n_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_2883_, lean_object* v_n_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_2883_, v_n_2884_);
lean_dec(v_n_2884_);
lean_dec(v_p_2883_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0(lean_object* v_cfg_2886_){
_start:
{
lean_object* v_readmeFile_2887_; 
v_readmeFile_2887_ = lean_ctor_get(v_cfg_2886_, 23);
lean_inc_ref(v_readmeFile_2887_);
return v_readmeFile_2887_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__0___boxed(lean_object* v_cfg_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lake_PackageConfig_readmeFile___proj___lam__0(v_cfg_2888_);
lean_dec_ref(v_cfg_2888_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__1(lean_object* v_val_2890_, lean_object* v_cfg_2891_){
_start:
{
lean_object* v_toWorkspaceConfig_2892_; lean_object* v_toLeanConfig_2893_; uint8_t v_bootstrap_2894_; lean_object* v_extraDepTargets_2895_; uint8_t v_precompileModules_2896_; lean_object* v_moreGlobalServerArgs_2897_; lean_object* v_srcDir_2898_; lean_object* v_buildDir_2899_; lean_object* v_leanLibDir_2900_; lean_object* v_nativeLibDir_2901_; lean_object* v_binDir_2902_; lean_object* v_irDir_2903_; lean_object* v_releaseRepo_2904_; lean_object* v_buildArchive_2905_; uint8_t v_preferReleaseBuild_2906_; lean_object* v_testDriver_2907_; lean_object* v_testDriverArgs_2908_; lean_object* v_lintDriver_2909_; lean_object* v_lintDriverArgs_2910_; lean_object* v_version_2911_; lean_object* v_versionTags_2912_; lean_object* v_description_2913_; lean_object* v_keywords_2914_; lean_object* v_homepage_2915_; lean_object* v_license_2916_; lean_object* v_licenseFiles_2917_; uint8_t v_reservoir_2918_; lean_object* v_enableArtifactCache_x3f_2919_; lean_object* v_restoreAllArtifacts_x3f_2920_; uint8_t v_libPrefixOnWindows_2921_; uint8_t v_allowImportAll_2922_; lean_object* v_builtinLint_x3f_2923_; lean_object* v_checks_2924_; uint8_t v_fixedToolchain_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_toWorkspaceConfig_2892_ = lean_ctor_get(v_cfg_2891_, 0);
v_toLeanConfig_2893_ = lean_ctor_get(v_cfg_2891_, 1);
v_bootstrap_2894_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28);
v_extraDepTargets_2895_ = lean_ctor_get(v_cfg_2891_, 2);
v_precompileModules_2896_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2897_ = lean_ctor_get(v_cfg_2891_, 3);
v_srcDir_2898_ = lean_ctor_get(v_cfg_2891_, 4);
v_buildDir_2899_ = lean_ctor_get(v_cfg_2891_, 5);
v_leanLibDir_2900_ = lean_ctor_get(v_cfg_2891_, 6);
v_nativeLibDir_2901_ = lean_ctor_get(v_cfg_2891_, 7);
v_binDir_2902_ = lean_ctor_get(v_cfg_2891_, 8);
v_irDir_2903_ = lean_ctor_get(v_cfg_2891_, 9);
v_releaseRepo_2904_ = lean_ctor_get(v_cfg_2891_, 10);
v_buildArchive_2905_ = lean_ctor_get(v_cfg_2891_, 11);
v_preferReleaseBuild_2906_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28 + 2);
v_testDriver_2907_ = lean_ctor_get(v_cfg_2891_, 12);
v_testDriverArgs_2908_ = lean_ctor_get(v_cfg_2891_, 13);
v_lintDriver_2909_ = lean_ctor_get(v_cfg_2891_, 14);
v_lintDriverArgs_2910_ = lean_ctor_get(v_cfg_2891_, 15);
v_version_2911_ = lean_ctor_get(v_cfg_2891_, 16);
v_versionTags_2912_ = lean_ctor_get(v_cfg_2891_, 17);
v_description_2913_ = lean_ctor_get(v_cfg_2891_, 18);
v_keywords_2914_ = lean_ctor_get(v_cfg_2891_, 19);
v_homepage_2915_ = lean_ctor_get(v_cfg_2891_, 20);
v_license_2916_ = lean_ctor_get(v_cfg_2891_, 21);
v_licenseFiles_2917_ = lean_ctor_get(v_cfg_2891_, 22);
v_reservoir_2918_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2919_ = lean_ctor_get(v_cfg_2891_, 24);
v_restoreAllArtifacts_x3f_2920_ = lean_ctor_get(v_cfg_2891_, 25);
v_libPrefixOnWindows_2921_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28 + 4);
v_allowImportAll_2922_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2923_ = lean_ctor_get(v_cfg_2891_, 26);
v_checks_2924_ = lean_ctor_get(v_cfg_2891_, 27);
v_fixedToolchain_2925_ = lean_ctor_get_uint8(v_cfg_2891_, sizeof(void*)*28 + 6);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_cfg_2891_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v_cfg_2891_, 23);
lean_dec(v_unused_2933_);
v___x_2927_ = v_cfg_2891_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_checks_2924_);
lean_inc(v_builtinLint_x3f_2923_);
lean_inc(v_restoreAllArtifacts_x3f_2920_);
lean_inc(v_enableArtifactCache_x3f_2919_);
lean_inc(v_licenseFiles_2917_);
lean_inc(v_license_2916_);
lean_inc(v_homepage_2915_);
lean_inc(v_keywords_2914_);
lean_inc(v_description_2913_);
lean_inc(v_versionTags_2912_);
lean_inc(v_version_2911_);
lean_inc(v_lintDriverArgs_2910_);
lean_inc(v_lintDriver_2909_);
lean_inc(v_testDriverArgs_2908_);
lean_inc(v_testDriver_2907_);
lean_inc(v_buildArchive_2905_);
lean_inc(v_releaseRepo_2904_);
lean_inc(v_irDir_2903_);
lean_inc(v_binDir_2902_);
lean_inc(v_nativeLibDir_2901_);
lean_inc(v_leanLibDir_2900_);
lean_inc(v_buildDir_2899_);
lean_inc(v_srcDir_2898_);
lean_inc(v_moreGlobalServerArgs_2897_);
lean_inc(v_extraDepTargets_2895_);
lean_inc(v_toLeanConfig_2893_);
lean_inc(v_toWorkspaceConfig_2892_);
lean_dec(v_cfg_2891_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 23, v_val_2890_);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_toWorkspaceConfig_2892_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_toLeanConfig_2893_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_extraDepTargets_2895_);
lean_ctor_set(v_reuseFailAlloc_2931_, 3, v_moreGlobalServerArgs_2897_);
lean_ctor_set(v_reuseFailAlloc_2931_, 4, v_srcDir_2898_);
lean_ctor_set(v_reuseFailAlloc_2931_, 5, v_buildDir_2899_);
lean_ctor_set(v_reuseFailAlloc_2931_, 6, v_leanLibDir_2900_);
lean_ctor_set(v_reuseFailAlloc_2931_, 7, v_nativeLibDir_2901_);
lean_ctor_set(v_reuseFailAlloc_2931_, 8, v_binDir_2902_);
lean_ctor_set(v_reuseFailAlloc_2931_, 9, v_irDir_2903_);
lean_ctor_set(v_reuseFailAlloc_2931_, 10, v_releaseRepo_2904_);
lean_ctor_set(v_reuseFailAlloc_2931_, 11, v_buildArchive_2905_);
lean_ctor_set(v_reuseFailAlloc_2931_, 12, v_testDriver_2907_);
lean_ctor_set(v_reuseFailAlloc_2931_, 13, v_testDriverArgs_2908_);
lean_ctor_set(v_reuseFailAlloc_2931_, 14, v_lintDriver_2909_);
lean_ctor_set(v_reuseFailAlloc_2931_, 15, v_lintDriverArgs_2910_);
lean_ctor_set(v_reuseFailAlloc_2931_, 16, v_version_2911_);
lean_ctor_set(v_reuseFailAlloc_2931_, 17, v_versionTags_2912_);
lean_ctor_set(v_reuseFailAlloc_2931_, 18, v_description_2913_);
lean_ctor_set(v_reuseFailAlloc_2931_, 19, v_keywords_2914_);
lean_ctor_set(v_reuseFailAlloc_2931_, 20, v_homepage_2915_);
lean_ctor_set(v_reuseFailAlloc_2931_, 21, v_license_2916_);
lean_ctor_set(v_reuseFailAlloc_2931_, 22, v_licenseFiles_2917_);
lean_ctor_set(v_reuseFailAlloc_2931_, 23, v_val_2890_);
lean_ctor_set(v_reuseFailAlloc_2931_, 24, v_enableArtifactCache_x3f_2919_);
lean_ctor_set(v_reuseFailAlloc_2931_, 25, v_restoreAllArtifacts_x3f_2920_);
lean_ctor_set(v_reuseFailAlloc_2931_, 26, v_builtinLint_x3f_2923_);
lean_ctor_set(v_reuseFailAlloc_2931_, 27, v_checks_2924_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28, v_bootstrap_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28 + 1, v_precompileModules_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2906_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28 + 3, v_reservoir_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2921_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28 + 5, v_allowImportAll_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*28 + 6, v_fixedToolchain_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__2(lean_object* v_f_2934_, lean_object* v_cfg_2935_){
_start:
{
lean_object* v_toWorkspaceConfig_2936_; lean_object* v_toLeanConfig_2937_; uint8_t v_bootstrap_2938_; lean_object* v_extraDepTargets_2939_; uint8_t v_precompileModules_2940_; lean_object* v_moreGlobalServerArgs_2941_; lean_object* v_srcDir_2942_; lean_object* v_buildDir_2943_; lean_object* v_leanLibDir_2944_; lean_object* v_nativeLibDir_2945_; lean_object* v_binDir_2946_; lean_object* v_irDir_2947_; lean_object* v_releaseRepo_2948_; lean_object* v_buildArchive_2949_; uint8_t v_preferReleaseBuild_2950_; lean_object* v_testDriver_2951_; lean_object* v_testDriverArgs_2952_; lean_object* v_lintDriver_2953_; lean_object* v_lintDriverArgs_2954_; lean_object* v_version_2955_; lean_object* v_versionTags_2956_; lean_object* v_description_2957_; lean_object* v_keywords_2958_; lean_object* v_homepage_2959_; lean_object* v_license_2960_; lean_object* v_licenseFiles_2961_; lean_object* v_readmeFile_2962_; uint8_t v_reservoir_2963_; lean_object* v_enableArtifactCache_x3f_2964_; lean_object* v_restoreAllArtifacts_x3f_2965_; uint8_t v_libPrefixOnWindows_2966_; uint8_t v_allowImportAll_2967_; lean_object* v_builtinLint_x3f_2968_; lean_object* v_checks_2969_; uint8_t v_fixedToolchain_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2978_; 
v_toWorkspaceConfig_2936_ = lean_ctor_get(v_cfg_2935_, 0);
v_toLeanConfig_2937_ = lean_ctor_get(v_cfg_2935_, 1);
v_bootstrap_2938_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28);
v_extraDepTargets_2939_ = lean_ctor_get(v_cfg_2935_, 2);
v_precompileModules_2940_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_2941_ = lean_ctor_get(v_cfg_2935_, 3);
v_srcDir_2942_ = lean_ctor_get(v_cfg_2935_, 4);
v_buildDir_2943_ = lean_ctor_get(v_cfg_2935_, 5);
v_leanLibDir_2944_ = lean_ctor_get(v_cfg_2935_, 6);
v_nativeLibDir_2945_ = lean_ctor_get(v_cfg_2935_, 7);
v_binDir_2946_ = lean_ctor_get(v_cfg_2935_, 8);
v_irDir_2947_ = lean_ctor_get(v_cfg_2935_, 9);
v_releaseRepo_2948_ = lean_ctor_get(v_cfg_2935_, 10);
v_buildArchive_2949_ = lean_ctor_get(v_cfg_2935_, 11);
v_preferReleaseBuild_2950_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28 + 2);
v_testDriver_2951_ = lean_ctor_get(v_cfg_2935_, 12);
v_testDriverArgs_2952_ = lean_ctor_get(v_cfg_2935_, 13);
v_lintDriver_2953_ = lean_ctor_get(v_cfg_2935_, 14);
v_lintDriverArgs_2954_ = lean_ctor_get(v_cfg_2935_, 15);
v_version_2955_ = lean_ctor_get(v_cfg_2935_, 16);
v_versionTags_2956_ = lean_ctor_get(v_cfg_2935_, 17);
v_description_2957_ = lean_ctor_get(v_cfg_2935_, 18);
v_keywords_2958_ = lean_ctor_get(v_cfg_2935_, 19);
v_homepage_2959_ = lean_ctor_get(v_cfg_2935_, 20);
v_license_2960_ = lean_ctor_get(v_cfg_2935_, 21);
v_licenseFiles_2961_ = lean_ctor_get(v_cfg_2935_, 22);
v_readmeFile_2962_ = lean_ctor_get(v_cfg_2935_, 23);
v_reservoir_2963_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_2964_ = lean_ctor_get(v_cfg_2935_, 24);
v_restoreAllArtifacts_x3f_2965_ = lean_ctor_get(v_cfg_2935_, 25);
v_libPrefixOnWindows_2966_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28 + 4);
v_allowImportAll_2967_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_2968_ = lean_ctor_get(v_cfg_2935_, 26);
v_checks_2969_ = lean_ctor_get(v_cfg_2935_, 27);
v_fixedToolchain_2970_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*28 + 6);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_cfg_2935_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2972_ = v_cfg_2935_;
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_checks_2969_);
lean_inc(v_builtinLint_x3f_2968_);
lean_inc(v_restoreAllArtifacts_x3f_2965_);
lean_inc(v_enableArtifactCache_x3f_2964_);
lean_inc(v_readmeFile_2962_);
lean_inc(v_licenseFiles_2961_);
lean_inc(v_license_2960_);
lean_inc(v_homepage_2959_);
lean_inc(v_keywords_2958_);
lean_inc(v_description_2957_);
lean_inc(v_versionTags_2956_);
lean_inc(v_version_2955_);
lean_inc(v_lintDriverArgs_2954_);
lean_inc(v_lintDriver_2953_);
lean_inc(v_testDriverArgs_2952_);
lean_inc(v_testDriver_2951_);
lean_inc(v_buildArchive_2949_);
lean_inc(v_releaseRepo_2948_);
lean_inc(v_irDir_2947_);
lean_inc(v_binDir_2946_);
lean_inc(v_nativeLibDir_2945_);
lean_inc(v_leanLibDir_2944_);
lean_inc(v_buildDir_2943_);
lean_inc(v_srcDir_2942_);
lean_inc(v_moreGlobalServerArgs_2941_);
lean_inc(v_extraDepTargets_2939_);
lean_inc(v_toLeanConfig_2937_);
lean_inc(v_toWorkspaceConfig_2936_);
lean_dec(v_cfg_2935_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2974_ = lean_apply_1(v_f_2934_, v_readmeFile_2962_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 23, v___x_2974_);
v___x_2976_ = v___x_2972_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_toWorkspaceConfig_2936_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_toLeanConfig_2937_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_extraDepTargets_2939_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_moreGlobalServerArgs_2941_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v_srcDir_2942_);
lean_ctor_set(v_reuseFailAlloc_2977_, 5, v_buildDir_2943_);
lean_ctor_set(v_reuseFailAlloc_2977_, 6, v_leanLibDir_2944_);
lean_ctor_set(v_reuseFailAlloc_2977_, 7, v_nativeLibDir_2945_);
lean_ctor_set(v_reuseFailAlloc_2977_, 8, v_binDir_2946_);
lean_ctor_set(v_reuseFailAlloc_2977_, 9, v_irDir_2947_);
lean_ctor_set(v_reuseFailAlloc_2977_, 10, v_releaseRepo_2948_);
lean_ctor_set(v_reuseFailAlloc_2977_, 11, v_buildArchive_2949_);
lean_ctor_set(v_reuseFailAlloc_2977_, 12, v_testDriver_2951_);
lean_ctor_set(v_reuseFailAlloc_2977_, 13, v_testDriverArgs_2952_);
lean_ctor_set(v_reuseFailAlloc_2977_, 14, v_lintDriver_2953_);
lean_ctor_set(v_reuseFailAlloc_2977_, 15, v_lintDriverArgs_2954_);
lean_ctor_set(v_reuseFailAlloc_2977_, 16, v_version_2955_);
lean_ctor_set(v_reuseFailAlloc_2977_, 17, v_versionTags_2956_);
lean_ctor_set(v_reuseFailAlloc_2977_, 18, v_description_2957_);
lean_ctor_set(v_reuseFailAlloc_2977_, 19, v_keywords_2958_);
lean_ctor_set(v_reuseFailAlloc_2977_, 20, v_homepage_2959_);
lean_ctor_set(v_reuseFailAlloc_2977_, 21, v_license_2960_);
lean_ctor_set(v_reuseFailAlloc_2977_, 22, v_licenseFiles_2961_);
lean_ctor_set(v_reuseFailAlloc_2977_, 23, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2977_, 24, v_enableArtifactCache_x3f_2964_);
lean_ctor_set(v_reuseFailAlloc_2977_, 25, v_restoreAllArtifacts_x3f_2965_);
lean_ctor_set(v_reuseFailAlloc_2977_, 26, v_builtinLint_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_2977_, 27, v_checks_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28, v_bootstrap_2938_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28 + 1, v_precompileModules_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28 + 2, v_preferReleaseBuild_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28 + 3, v_reservoir_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28 + 5, v_allowImportAll_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*28 + 6, v_fixedToolchain_2970_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3(lean_object* v_x_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___lam__3___boxed(lean_object* v_x_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lake_PackageConfig_readmeFile___proj___lam__3(v_x_2981_);
lean_dec_ref(v_x_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_2992_, lean_object* v_n_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___closed__4));
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_2995_, lean_object* v_n_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2995_, v_n_2996_);
lean_dec(v_n_2996_);
lean_dec(v_p_2995_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_2998_, lean_object* v_n_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lake_PackageConfig_readmeFile___proj(v_p_2998_, v_n_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_3001_, lean_object* v_n_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_3001_, v_n_3002_);
lean_dec(v_n_3002_);
lean_dec(v_p_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__0(lean_object* v_cfg_3004_){
_start:
{
uint8_t v_reservoir_3005_; 
v_reservoir_3005_ = lean_ctor_get_uint8(v_cfg_3004_, sizeof(void*)*28 + 3);
return v_reservoir_3005_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__0___boxed(lean_object* v_cfg_3006_){
_start:
{
uint8_t v_res_3007_; lean_object* v_r_3008_; 
v_res_3007_ = l_Lake_PackageConfig_reservoir___proj___lam__0(v_cfg_3006_);
lean_dec_ref(v_cfg_3006_);
v_r_3008_ = lean_box(v_res_3007_);
return v_r_3008_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1(uint8_t v_val_3009_, lean_object* v_cfg_3010_){
_start:
{
lean_object* v_toWorkspaceConfig_3011_; lean_object* v_toLeanConfig_3012_; uint8_t v_bootstrap_3013_; lean_object* v_extraDepTargets_3014_; uint8_t v_precompileModules_3015_; lean_object* v_moreGlobalServerArgs_3016_; lean_object* v_srcDir_3017_; lean_object* v_buildDir_3018_; lean_object* v_leanLibDir_3019_; lean_object* v_nativeLibDir_3020_; lean_object* v_binDir_3021_; lean_object* v_irDir_3022_; lean_object* v_releaseRepo_3023_; lean_object* v_buildArchive_3024_; uint8_t v_preferReleaseBuild_3025_; lean_object* v_testDriver_3026_; lean_object* v_testDriverArgs_3027_; lean_object* v_lintDriver_3028_; lean_object* v_lintDriverArgs_3029_; lean_object* v_version_3030_; lean_object* v_versionTags_3031_; lean_object* v_description_3032_; lean_object* v_keywords_3033_; lean_object* v_homepage_3034_; lean_object* v_license_3035_; lean_object* v_licenseFiles_3036_; lean_object* v_readmeFile_3037_; lean_object* v_enableArtifactCache_x3f_3038_; lean_object* v_restoreAllArtifacts_x3f_3039_; uint8_t v_libPrefixOnWindows_3040_; uint8_t v_allowImportAll_3041_; lean_object* v_builtinLint_x3f_3042_; lean_object* v_checks_3043_; uint8_t v_fixedToolchain_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_toWorkspaceConfig_3011_ = lean_ctor_get(v_cfg_3010_, 0);
v_toLeanConfig_3012_ = lean_ctor_get(v_cfg_3010_, 1);
v_bootstrap_3013_ = lean_ctor_get_uint8(v_cfg_3010_, sizeof(void*)*28);
v_extraDepTargets_3014_ = lean_ctor_get(v_cfg_3010_, 2);
v_precompileModules_3015_ = lean_ctor_get_uint8(v_cfg_3010_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3016_ = lean_ctor_get(v_cfg_3010_, 3);
v_srcDir_3017_ = lean_ctor_get(v_cfg_3010_, 4);
v_buildDir_3018_ = lean_ctor_get(v_cfg_3010_, 5);
v_leanLibDir_3019_ = lean_ctor_get(v_cfg_3010_, 6);
v_nativeLibDir_3020_ = lean_ctor_get(v_cfg_3010_, 7);
v_binDir_3021_ = lean_ctor_get(v_cfg_3010_, 8);
v_irDir_3022_ = lean_ctor_get(v_cfg_3010_, 9);
v_releaseRepo_3023_ = lean_ctor_get(v_cfg_3010_, 10);
v_buildArchive_3024_ = lean_ctor_get(v_cfg_3010_, 11);
v_preferReleaseBuild_3025_ = lean_ctor_get_uint8(v_cfg_3010_, sizeof(void*)*28 + 2);
v_testDriver_3026_ = lean_ctor_get(v_cfg_3010_, 12);
v_testDriverArgs_3027_ = lean_ctor_get(v_cfg_3010_, 13);
v_lintDriver_3028_ = lean_ctor_get(v_cfg_3010_, 14);
v_lintDriverArgs_3029_ = lean_ctor_get(v_cfg_3010_, 15);
v_version_3030_ = lean_ctor_get(v_cfg_3010_, 16);
v_versionTags_3031_ = lean_ctor_get(v_cfg_3010_, 17);
v_description_3032_ = lean_ctor_get(v_cfg_3010_, 18);
v_keywords_3033_ = lean_ctor_get(v_cfg_3010_, 19);
v_homepage_3034_ = lean_ctor_get(v_cfg_3010_, 20);
v_license_3035_ = lean_ctor_get(v_cfg_3010_, 21);
v_licenseFiles_3036_ = lean_ctor_get(v_cfg_3010_, 22);
v_readmeFile_3037_ = lean_ctor_get(v_cfg_3010_, 23);
v_enableArtifactCache_x3f_3038_ = lean_ctor_get(v_cfg_3010_, 24);
v_restoreAllArtifacts_x3f_3039_ = lean_ctor_get(v_cfg_3010_, 25);
v_libPrefixOnWindows_3040_ = lean_ctor_get_uint8(v_cfg_3010_, sizeof(void*)*28 + 4);
v_allowImportAll_3041_ = lean_ctor_get_uint8(v_cfg_3010_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3042_ = lean_ctor_get(v_cfg_3010_, 26);
v_checks_3043_ = lean_ctor_get(v_cfg_3010_, 27);
v_fixedToolchain_3044_ = lean_ctor_get_uint8(v_cfg_3010_, sizeof(void*)*28 + 6);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_cfg_3010_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v_cfg_3010_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_checks_3043_);
lean_inc(v_builtinLint_x3f_3042_);
lean_inc(v_restoreAllArtifacts_x3f_3039_);
lean_inc(v_enableArtifactCache_x3f_3038_);
lean_inc(v_readmeFile_3037_);
lean_inc(v_licenseFiles_3036_);
lean_inc(v_license_3035_);
lean_inc(v_homepage_3034_);
lean_inc(v_keywords_3033_);
lean_inc(v_description_3032_);
lean_inc(v_versionTags_3031_);
lean_inc(v_version_3030_);
lean_inc(v_lintDriverArgs_3029_);
lean_inc(v_lintDriver_3028_);
lean_inc(v_testDriverArgs_3027_);
lean_inc(v_testDriver_3026_);
lean_inc(v_buildArchive_3024_);
lean_inc(v_releaseRepo_3023_);
lean_inc(v_irDir_3022_);
lean_inc(v_binDir_3021_);
lean_inc(v_nativeLibDir_3020_);
lean_inc(v_leanLibDir_3019_);
lean_inc(v_buildDir_3018_);
lean_inc(v_srcDir_3017_);
lean_inc(v_moreGlobalServerArgs_3016_);
lean_inc(v_extraDepTargets_3014_);
lean_inc(v_toLeanConfig_3012_);
lean_inc(v_toWorkspaceConfig_3011_);
lean_dec(v_cfg_3010_);
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
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_toWorkspaceConfig_3011_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_toLeanConfig_3012_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v_extraDepTargets_3014_);
lean_ctor_set(v_reuseFailAlloc_3050_, 3, v_moreGlobalServerArgs_3016_);
lean_ctor_set(v_reuseFailAlloc_3050_, 4, v_srcDir_3017_);
lean_ctor_set(v_reuseFailAlloc_3050_, 5, v_buildDir_3018_);
lean_ctor_set(v_reuseFailAlloc_3050_, 6, v_leanLibDir_3019_);
lean_ctor_set(v_reuseFailAlloc_3050_, 7, v_nativeLibDir_3020_);
lean_ctor_set(v_reuseFailAlloc_3050_, 8, v_binDir_3021_);
lean_ctor_set(v_reuseFailAlloc_3050_, 9, v_irDir_3022_);
lean_ctor_set(v_reuseFailAlloc_3050_, 10, v_releaseRepo_3023_);
lean_ctor_set(v_reuseFailAlloc_3050_, 11, v_buildArchive_3024_);
lean_ctor_set(v_reuseFailAlloc_3050_, 12, v_testDriver_3026_);
lean_ctor_set(v_reuseFailAlloc_3050_, 13, v_testDriverArgs_3027_);
lean_ctor_set(v_reuseFailAlloc_3050_, 14, v_lintDriver_3028_);
lean_ctor_set(v_reuseFailAlloc_3050_, 15, v_lintDriverArgs_3029_);
lean_ctor_set(v_reuseFailAlloc_3050_, 16, v_version_3030_);
lean_ctor_set(v_reuseFailAlloc_3050_, 17, v_versionTags_3031_);
lean_ctor_set(v_reuseFailAlloc_3050_, 18, v_description_3032_);
lean_ctor_set(v_reuseFailAlloc_3050_, 19, v_keywords_3033_);
lean_ctor_set(v_reuseFailAlloc_3050_, 20, v_homepage_3034_);
lean_ctor_set(v_reuseFailAlloc_3050_, 21, v_license_3035_);
lean_ctor_set(v_reuseFailAlloc_3050_, 22, v_licenseFiles_3036_);
lean_ctor_set(v_reuseFailAlloc_3050_, 23, v_readmeFile_3037_);
lean_ctor_set(v_reuseFailAlloc_3050_, 24, v_enableArtifactCache_x3f_3038_);
lean_ctor_set(v_reuseFailAlloc_3050_, 25, v_restoreAllArtifacts_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3050_, 26, v_builtinLint_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3050_, 27, v_checks_3043_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*28, v_bootstrap_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*28 + 1, v_precompileModules_3015_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3025_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*28 + 5, v_allowImportAll_3041_);
lean_ctor_set_uint8(v_reuseFailAlloc_3050_, sizeof(void*)*28 + 6, v_fixedToolchain_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*28 + 3, v_val_3009_);
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__1___boxed(lean_object* v_val_3052_, lean_object* v_cfg_3053_){
_start:
{
uint8_t v_val_140__boxed_3054_; lean_object* v_res_3055_; 
v_val_140__boxed_3054_ = lean_unbox(v_val_3052_);
v_res_3055_ = l_Lake_PackageConfig_reservoir___proj___lam__1(v_val_140__boxed_3054_, v_cfg_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__2(lean_object* v_f_3056_, lean_object* v_cfg_3057_){
_start:
{
lean_object* v_toWorkspaceConfig_3058_; lean_object* v_toLeanConfig_3059_; uint8_t v_bootstrap_3060_; lean_object* v_extraDepTargets_3061_; uint8_t v_precompileModules_3062_; lean_object* v_moreGlobalServerArgs_3063_; lean_object* v_srcDir_3064_; lean_object* v_buildDir_3065_; lean_object* v_leanLibDir_3066_; lean_object* v_nativeLibDir_3067_; lean_object* v_binDir_3068_; lean_object* v_irDir_3069_; lean_object* v_releaseRepo_3070_; lean_object* v_buildArchive_3071_; uint8_t v_preferReleaseBuild_3072_; lean_object* v_testDriver_3073_; lean_object* v_testDriverArgs_3074_; lean_object* v_lintDriver_3075_; lean_object* v_lintDriverArgs_3076_; lean_object* v_version_3077_; lean_object* v_versionTags_3078_; lean_object* v_description_3079_; lean_object* v_keywords_3080_; lean_object* v_homepage_3081_; lean_object* v_license_3082_; lean_object* v_licenseFiles_3083_; lean_object* v_readmeFile_3084_; uint8_t v_reservoir_3085_; lean_object* v_enableArtifactCache_x3f_3086_; lean_object* v_restoreAllArtifacts_x3f_3087_; uint8_t v_libPrefixOnWindows_3088_; uint8_t v_allowImportAll_3089_; lean_object* v_builtinLint_x3f_3090_; lean_object* v_checks_3091_; uint8_t v_fixedToolchain_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3102_; 
v_toWorkspaceConfig_3058_ = lean_ctor_get(v_cfg_3057_, 0);
v_toLeanConfig_3059_ = lean_ctor_get(v_cfg_3057_, 1);
v_bootstrap_3060_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28);
v_extraDepTargets_3061_ = lean_ctor_get(v_cfg_3057_, 2);
v_precompileModules_3062_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3063_ = lean_ctor_get(v_cfg_3057_, 3);
v_srcDir_3064_ = lean_ctor_get(v_cfg_3057_, 4);
v_buildDir_3065_ = lean_ctor_get(v_cfg_3057_, 5);
v_leanLibDir_3066_ = lean_ctor_get(v_cfg_3057_, 6);
v_nativeLibDir_3067_ = lean_ctor_get(v_cfg_3057_, 7);
v_binDir_3068_ = lean_ctor_get(v_cfg_3057_, 8);
v_irDir_3069_ = lean_ctor_get(v_cfg_3057_, 9);
v_releaseRepo_3070_ = lean_ctor_get(v_cfg_3057_, 10);
v_buildArchive_3071_ = lean_ctor_get(v_cfg_3057_, 11);
v_preferReleaseBuild_3072_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28 + 2);
v_testDriver_3073_ = lean_ctor_get(v_cfg_3057_, 12);
v_testDriverArgs_3074_ = lean_ctor_get(v_cfg_3057_, 13);
v_lintDriver_3075_ = lean_ctor_get(v_cfg_3057_, 14);
v_lintDriverArgs_3076_ = lean_ctor_get(v_cfg_3057_, 15);
v_version_3077_ = lean_ctor_get(v_cfg_3057_, 16);
v_versionTags_3078_ = lean_ctor_get(v_cfg_3057_, 17);
v_description_3079_ = lean_ctor_get(v_cfg_3057_, 18);
v_keywords_3080_ = lean_ctor_get(v_cfg_3057_, 19);
v_homepage_3081_ = lean_ctor_get(v_cfg_3057_, 20);
v_license_3082_ = lean_ctor_get(v_cfg_3057_, 21);
v_licenseFiles_3083_ = lean_ctor_get(v_cfg_3057_, 22);
v_readmeFile_3084_ = lean_ctor_get(v_cfg_3057_, 23);
v_reservoir_3085_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3086_ = lean_ctor_get(v_cfg_3057_, 24);
v_restoreAllArtifacts_x3f_3087_ = lean_ctor_get(v_cfg_3057_, 25);
v_libPrefixOnWindows_3088_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28 + 4);
v_allowImportAll_3089_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3090_ = lean_ctor_get(v_cfg_3057_, 26);
v_checks_3091_ = lean_ctor_get(v_cfg_3057_, 27);
v_fixedToolchain_3092_ = lean_ctor_get_uint8(v_cfg_3057_, sizeof(void*)*28 + 6);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_cfg_3057_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3094_ = v_cfg_3057_;
v_isShared_3095_ = v_isSharedCheck_3102_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_checks_3091_);
lean_inc(v_builtinLint_x3f_3090_);
lean_inc(v_restoreAllArtifacts_x3f_3087_);
lean_inc(v_enableArtifactCache_x3f_3086_);
lean_inc(v_readmeFile_3084_);
lean_inc(v_licenseFiles_3083_);
lean_inc(v_license_3082_);
lean_inc(v_homepage_3081_);
lean_inc(v_keywords_3080_);
lean_inc(v_description_3079_);
lean_inc(v_versionTags_3078_);
lean_inc(v_version_3077_);
lean_inc(v_lintDriverArgs_3076_);
lean_inc(v_lintDriver_3075_);
lean_inc(v_testDriverArgs_3074_);
lean_inc(v_testDriver_3073_);
lean_inc(v_buildArchive_3071_);
lean_inc(v_releaseRepo_3070_);
lean_inc(v_irDir_3069_);
lean_inc(v_binDir_3068_);
lean_inc(v_nativeLibDir_3067_);
lean_inc(v_leanLibDir_3066_);
lean_inc(v_buildDir_3065_);
lean_inc(v_srcDir_3064_);
lean_inc(v_moreGlobalServerArgs_3063_);
lean_inc(v_extraDepTargets_3061_);
lean_inc(v_toLeanConfig_3059_);
lean_inc(v_toWorkspaceConfig_3058_);
lean_dec(v_cfg_3057_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3102_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3096_ = lean_box(v_reservoir_3085_);
v___x_3097_ = lean_apply_1(v_f_3056_, v___x_3096_);
if (v_isShared_3095_ == 0)
{
v___x_3099_ = v___x_3094_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_toWorkspaceConfig_3058_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_toLeanConfig_3059_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_extraDepTargets_3061_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_moreGlobalServerArgs_3063_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v_srcDir_3064_);
lean_ctor_set(v_reuseFailAlloc_3101_, 5, v_buildDir_3065_);
lean_ctor_set(v_reuseFailAlloc_3101_, 6, v_leanLibDir_3066_);
lean_ctor_set(v_reuseFailAlloc_3101_, 7, v_nativeLibDir_3067_);
lean_ctor_set(v_reuseFailAlloc_3101_, 8, v_binDir_3068_);
lean_ctor_set(v_reuseFailAlloc_3101_, 9, v_irDir_3069_);
lean_ctor_set(v_reuseFailAlloc_3101_, 10, v_releaseRepo_3070_);
lean_ctor_set(v_reuseFailAlloc_3101_, 11, v_buildArchive_3071_);
lean_ctor_set(v_reuseFailAlloc_3101_, 12, v_testDriver_3073_);
lean_ctor_set(v_reuseFailAlloc_3101_, 13, v_testDriverArgs_3074_);
lean_ctor_set(v_reuseFailAlloc_3101_, 14, v_lintDriver_3075_);
lean_ctor_set(v_reuseFailAlloc_3101_, 15, v_lintDriverArgs_3076_);
lean_ctor_set(v_reuseFailAlloc_3101_, 16, v_version_3077_);
lean_ctor_set(v_reuseFailAlloc_3101_, 17, v_versionTags_3078_);
lean_ctor_set(v_reuseFailAlloc_3101_, 18, v_description_3079_);
lean_ctor_set(v_reuseFailAlloc_3101_, 19, v_keywords_3080_);
lean_ctor_set(v_reuseFailAlloc_3101_, 20, v_homepage_3081_);
lean_ctor_set(v_reuseFailAlloc_3101_, 21, v_license_3082_);
lean_ctor_set(v_reuseFailAlloc_3101_, 22, v_licenseFiles_3083_);
lean_ctor_set(v_reuseFailAlloc_3101_, 23, v_readmeFile_3084_);
lean_ctor_set(v_reuseFailAlloc_3101_, 24, v_enableArtifactCache_x3f_3086_);
lean_ctor_set(v_reuseFailAlloc_3101_, 25, v_restoreAllArtifacts_x3f_3087_);
lean_ctor_set(v_reuseFailAlloc_3101_, 26, v_builtinLint_x3f_3090_);
lean_ctor_set(v_reuseFailAlloc_3101_, 27, v_checks_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, sizeof(void*)*28, v_bootstrap_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, sizeof(void*)*28 + 1, v_precompileModules_3062_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3072_);
v___x_3099_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_unbox(v___x_3097_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*28 + 3, v___x_3100_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3088_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*28 + 5, v_allowImportAll_3089_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*28 + 6, v_fixedToolchain_3092_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___lam__3(lean_object* v_x_3103_){
_start:
{
uint8_t v___x_3104_; 
v___x_3104_ = 1;
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___lam__3___boxed(lean_object* v_x_3105_){
_start:
{
uint8_t v_res_3106_; lean_object* v_r_3107_; 
v_res_3106_ = l_Lake_PackageConfig_reservoir___proj___lam__3(v_x_3105_);
lean_dec_ref(v_x_3105_);
v_r_3107_ = lean_box(v_res_3106_);
return v_r_3107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3117_, lean_object* v_n_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___closed__4));
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3120_, lean_object* v_n_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lake_PackageConfig_reservoir___proj(v_p_3120_, v_n_3121_);
lean_dec(v_n_3121_);
lean_dec(v_p_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3123_, lean_object* v_n_3124_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lake_PackageConfig_reservoir___proj(v_p_3123_, v_n_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3126_, lean_object* v_n_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3126_, v_n_3127_);
lean_dec(v_n_3127_);
lean_dec(v_p_3126_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(lean_object* v_cfg_3129_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3130_; 
v_enableArtifactCache_x3f_3130_ = lean_ctor_get(v_cfg_3129_, 24);
lean_inc(v_enableArtifactCache_x3f_3130_);
return v_enableArtifactCache_x3f_3130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0___boxed(lean_object* v_cfg_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__0(v_cfg_3131_);
lean_dec_ref(v_cfg_3131_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__1(lean_object* v_val_3133_, lean_object* v_cfg_3134_){
_start:
{
lean_object* v_toWorkspaceConfig_3135_; lean_object* v_toLeanConfig_3136_; uint8_t v_bootstrap_3137_; lean_object* v_extraDepTargets_3138_; uint8_t v_precompileModules_3139_; lean_object* v_moreGlobalServerArgs_3140_; lean_object* v_srcDir_3141_; lean_object* v_buildDir_3142_; lean_object* v_leanLibDir_3143_; lean_object* v_nativeLibDir_3144_; lean_object* v_binDir_3145_; lean_object* v_irDir_3146_; lean_object* v_releaseRepo_3147_; lean_object* v_buildArchive_3148_; uint8_t v_preferReleaseBuild_3149_; lean_object* v_testDriver_3150_; lean_object* v_testDriverArgs_3151_; lean_object* v_lintDriver_3152_; lean_object* v_lintDriverArgs_3153_; lean_object* v_version_3154_; lean_object* v_versionTags_3155_; lean_object* v_description_3156_; lean_object* v_keywords_3157_; lean_object* v_homepage_3158_; lean_object* v_license_3159_; lean_object* v_licenseFiles_3160_; lean_object* v_readmeFile_3161_; uint8_t v_reservoir_3162_; lean_object* v_restoreAllArtifacts_x3f_3163_; uint8_t v_libPrefixOnWindows_3164_; uint8_t v_allowImportAll_3165_; lean_object* v_builtinLint_x3f_3166_; lean_object* v_checks_3167_; uint8_t v_fixedToolchain_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_toWorkspaceConfig_3135_ = lean_ctor_get(v_cfg_3134_, 0);
v_toLeanConfig_3136_ = lean_ctor_get(v_cfg_3134_, 1);
v_bootstrap_3137_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28);
v_extraDepTargets_3138_ = lean_ctor_get(v_cfg_3134_, 2);
v_precompileModules_3139_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3140_ = lean_ctor_get(v_cfg_3134_, 3);
v_srcDir_3141_ = lean_ctor_get(v_cfg_3134_, 4);
v_buildDir_3142_ = lean_ctor_get(v_cfg_3134_, 5);
v_leanLibDir_3143_ = lean_ctor_get(v_cfg_3134_, 6);
v_nativeLibDir_3144_ = lean_ctor_get(v_cfg_3134_, 7);
v_binDir_3145_ = lean_ctor_get(v_cfg_3134_, 8);
v_irDir_3146_ = lean_ctor_get(v_cfg_3134_, 9);
v_releaseRepo_3147_ = lean_ctor_get(v_cfg_3134_, 10);
v_buildArchive_3148_ = lean_ctor_get(v_cfg_3134_, 11);
v_preferReleaseBuild_3149_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28 + 2);
v_testDriver_3150_ = lean_ctor_get(v_cfg_3134_, 12);
v_testDriverArgs_3151_ = lean_ctor_get(v_cfg_3134_, 13);
v_lintDriver_3152_ = lean_ctor_get(v_cfg_3134_, 14);
v_lintDriverArgs_3153_ = lean_ctor_get(v_cfg_3134_, 15);
v_version_3154_ = lean_ctor_get(v_cfg_3134_, 16);
v_versionTags_3155_ = lean_ctor_get(v_cfg_3134_, 17);
v_description_3156_ = lean_ctor_get(v_cfg_3134_, 18);
v_keywords_3157_ = lean_ctor_get(v_cfg_3134_, 19);
v_homepage_3158_ = lean_ctor_get(v_cfg_3134_, 20);
v_license_3159_ = lean_ctor_get(v_cfg_3134_, 21);
v_licenseFiles_3160_ = lean_ctor_get(v_cfg_3134_, 22);
v_readmeFile_3161_ = lean_ctor_get(v_cfg_3134_, 23);
v_reservoir_3162_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28 + 3);
v_restoreAllArtifacts_x3f_3163_ = lean_ctor_get(v_cfg_3134_, 25);
v_libPrefixOnWindows_3164_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28 + 4);
v_allowImportAll_3165_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3166_ = lean_ctor_get(v_cfg_3134_, 26);
v_checks_3167_ = lean_ctor_get(v_cfg_3134_, 27);
v_fixedToolchain_3168_ = lean_ctor_get_uint8(v_cfg_3134_, sizeof(void*)*28 + 6);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_cfg_3134_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v_cfg_3134_, 24);
lean_dec(v_unused_3176_);
v___x_3170_ = v_cfg_3134_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_checks_3167_);
lean_inc(v_builtinLint_x3f_3166_);
lean_inc(v_restoreAllArtifacts_x3f_3163_);
lean_inc(v_readmeFile_3161_);
lean_inc(v_licenseFiles_3160_);
lean_inc(v_license_3159_);
lean_inc(v_homepage_3158_);
lean_inc(v_keywords_3157_);
lean_inc(v_description_3156_);
lean_inc(v_versionTags_3155_);
lean_inc(v_version_3154_);
lean_inc(v_lintDriverArgs_3153_);
lean_inc(v_lintDriver_3152_);
lean_inc(v_testDriverArgs_3151_);
lean_inc(v_testDriver_3150_);
lean_inc(v_buildArchive_3148_);
lean_inc(v_releaseRepo_3147_);
lean_inc(v_irDir_3146_);
lean_inc(v_binDir_3145_);
lean_inc(v_nativeLibDir_3144_);
lean_inc(v_leanLibDir_3143_);
lean_inc(v_buildDir_3142_);
lean_inc(v_srcDir_3141_);
lean_inc(v_moreGlobalServerArgs_3140_);
lean_inc(v_extraDepTargets_3138_);
lean_inc(v_toLeanConfig_3136_);
lean_inc(v_toWorkspaceConfig_3135_);
lean_dec(v_cfg_3134_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 24, v_val_3133_);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_toWorkspaceConfig_3135_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_toLeanConfig_3136_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_extraDepTargets_3138_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_moreGlobalServerArgs_3140_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_srcDir_3141_);
lean_ctor_set(v_reuseFailAlloc_3174_, 5, v_buildDir_3142_);
lean_ctor_set(v_reuseFailAlloc_3174_, 6, v_leanLibDir_3143_);
lean_ctor_set(v_reuseFailAlloc_3174_, 7, v_nativeLibDir_3144_);
lean_ctor_set(v_reuseFailAlloc_3174_, 8, v_binDir_3145_);
lean_ctor_set(v_reuseFailAlloc_3174_, 9, v_irDir_3146_);
lean_ctor_set(v_reuseFailAlloc_3174_, 10, v_releaseRepo_3147_);
lean_ctor_set(v_reuseFailAlloc_3174_, 11, v_buildArchive_3148_);
lean_ctor_set(v_reuseFailAlloc_3174_, 12, v_testDriver_3150_);
lean_ctor_set(v_reuseFailAlloc_3174_, 13, v_testDriverArgs_3151_);
lean_ctor_set(v_reuseFailAlloc_3174_, 14, v_lintDriver_3152_);
lean_ctor_set(v_reuseFailAlloc_3174_, 15, v_lintDriverArgs_3153_);
lean_ctor_set(v_reuseFailAlloc_3174_, 16, v_version_3154_);
lean_ctor_set(v_reuseFailAlloc_3174_, 17, v_versionTags_3155_);
lean_ctor_set(v_reuseFailAlloc_3174_, 18, v_description_3156_);
lean_ctor_set(v_reuseFailAlloc_3174_, 19, v_keywords_3157_);
lean_ctor_set(v_reuseFailAlloc_3174_, 20, v_homepage_3158_);
lean_ctor_set(v_reuseFailAlloc_3174_, 21, v_license_3159_);
lean_ctor_set(v_reuseFailAlloc_3174_, 22, v_licenseFiles_3160_);
lean_ctor_set(v_reuseFailAlloc_3174_, 23, v_readmeFile_3161_);
lean_ctor_set(v_reuseFailAlloc_3174_, 24, v_val_3133_);
lean_ctor_set(v_reuseFailAlloc_3174_, 25, v_restoreAllArtifacts_x3f_3163_);
lean_ctor_set(v_reuseFailAlloc_3174_, 26, v_builtinLint_x3f_3166_);
lean_ctor_set(v_reuseFailAlloc_3174_, 27, v_checks_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28, v_bootstrap_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28 + 1, v_precompileModules_3139_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3149_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28 + 3, v_reservoir_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3164_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28 + 5, v_allowImportAll_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*28 + 6, v_fixedToolchain_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__2(lean_object* v_f_3177_, lean_object* v_cfg_3178_){
_start:
{
lean_object* v_toWorkspaceConfig_3179_; lean_object* v_toLeanConfig_3180_; uint8_t v_bootstrap_3181_; lean_object* v_extraDepTargets_3182_; uint8_t v_precompileModules_3183_; lean_object* v_moreGlobalServerArgs_3184_; lean_object* v_srcDir_3185_; lean_object* v_buildDir_3186_; lean_object* v_leanLibDir_3187_; lean_object* v_nativeLibDir_3188_; lean_object* v_binDir_3189_; lean_object* v_irDir_3190_; lean_object* v_releaseRepo_3191_; lean_object* v_buildArchive_3192_; uint8_t v_preferReleaseBuild_3193_; lean_object* v_testDriver_3194_; lean_object* v_testDriverArgs_3195_; lean_object* v_lintDriver_3196_; lean_object* v_lintDriverArgs_3197_; lean_object* v_version_3198_; lean_object* v_versionTags_3199_; lean_object* v_description_3200_; lean_object* v_keywords_3201_; lean_object* v_homepage_3202_; lean_object* v_license_3203_; lean_object* v_licenseFiles_3204_; lean_object* v_readmeFile_3205_; uint8_t v_reservoir_3206_; lean_object* v_enableArtifactCache_x3f_3207_; lean_object* v_restoreAllArtifacts_x3f_3208_; uint8_t v_libPrefixOnWindows_3209_; uint8_t v_allowImportAll_3210_; lean_object* v_builtinLint_x3f_3211_; lean_object* v_checks_3212_; uint8_t v_fixedToolchain_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3221_; 
v_toWorkspaceConfig_3179_ = lean_ctor_get(v_cfg_3178_, 0);
v_toLeanConfig_3180_ = lean_ctor_get(v_cfg_3178_, 1);
v_bootstrap_3181_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28);
v_extraDepTargets_3182_ = lean_ctor_get(v_cfg_3178_, 2);
v_precompileModules_3183_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3184_ = lean_ctor_get(v_cfg_3178_, 3);
v_srcDir_3185_ = lean_ctor_get(v_cfg_3178_, 4);
v_buildDir_3186_ = lean_ctor_get(v_cfg_3178_, 5);
v_leanLibDir_3187_ = lean_ctor_get(v_cfg_3178_, 6);
v_nativeLibDir_3188_ = lean_ctor_get(v_cfg_3178_, 7);
v_binDir_3189_ = lean_ctor_get(v_cfg_3178_, 8);
v_irDir_3190_ = lean_ctor_get(v_cfg_3178_, 9);
v_releaseRepo_3191_ = lean_ctor_get(v_cfg_3178_, 10);
v_buildArchive_3192_ = lean_ctor_get(v_cfg_3178_, 11);
v_preferReleaseBuild_3193_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28 + 2);
v_testDriver_3194_ = lean_ctor_get(v_cfg_3178_, 12);
v_testDriverArgs_3195_ = lean_ctor_get(v_cfg_3178_, 13);
v_lintDriver_3196_ = lean_ctor_get(v_cfg_3178_, 14);
v_lintDriverArgs_3197_ = lean_ctor_get(v_cfg_3178_, 15);
v_version_3198_ = lean_ctor_get(v_cfg_3178_, 16);
v_versionTags_3199_ = lean_ctor_get(v_cfg_3178_, 17);
v_description_3200_ = lean_ctor_get(v_cfg_3178_, 18);
v_keywords_3201_ = lean_ctor_get(v_cfg_3178_, 19);
v_homepage_3202_ = lean_ctor_get(v_cfg_3178_, 20);
v_license_3203_ = lean_ctor_get(v_cfg_3178_, 21);
v_licenseFiles_3204_ = lean_ctor_get(v_cfg_3178_, 22);
v_readmeFile_3205_ = lean_ctor_get(v_cfg_3178_, 23);
v_reservoir_3206_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3207_ = lean_ctor_get(v_cfg_3178_, 24);
v_restoreAllArtifacts_x3f_3208_ = lean_ctor_get(v_cfg_3178_, 25);
v_libPrefixOnWindows_3209_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28 + 4);
v_allowImportAll_3210_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3211_ = lean_ctor_get(v_cfg_3178_, 26);
v_checks_3212_ = lean_ctor_get(v_cfg_3178_, 27);
v_fixedToolchain_3213_ = lean_ctor_get_uint8(v_cfg_3178_, sizeof(void*)*28 + 6);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_cfg_3178_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3215_ = v_cfg_3178_;
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_checks_3212_);
lean_inc(v_builtinLint_x3f_3211_);
lean_inc(v_restoreAllArtifacts_x3f_3208_);
lean_inc(v_enableArtifactCache_x3f_3207_);
lean_inc(v_readmeFile_3205_);
lean_inc(v_licenseFiles_3204_);
lean_inc(v_license_3203_);
lean_inc(v_homepage_3202_);
lean_inc(v_keywords_3201_);
lean_inc(v_description_3200_);
lean_inc(v_versionTags_3199_);
lean_inc(v_version_3198_);
lean_inc(v_lintDriverArgs_3197_);
lean_inc(v_lintDriver_3196_);
lean_inc(v_testDriverArgs_3195_);
lean_inc(v_testDriver_3194_);
lean_inc(v_buildArchive_3192_);
lean_inc(v_releaseRepo_3191_);
lean_inc(v_irDir_3190_);
lean_inc(v_binDir_3189_);
lean_inc(v_nativeLibDir_3188_);
lean_inc(v_leanLibDir_3187_);
lean_inc(v_buildDir_3186_);
lean_inc(v_srcDir_3185_);
lean_inc(v_moreGlobalServerArgs_3184_);
lean_inc(v_extraDepTargets_3182_);
lean_inc(v_toLeanConfig_3180_);
lean_inc(v_toWorkspaceConfig_3179_);
lean_dec(v_cfg_3178_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_apply_1(v_f_3177_, v_enableArtifactCache_x3f_3207_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 24, v___x_3217_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_toWorkspaceConfig_3179_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_toLeanConfig_3180_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_extraDepTargets_3182_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_moreGlobalServerArgs_3184_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_srcDir_3185_);
lean_ctor_set(v_reuseFailAlloc_3220_, 5, v_buildDir_3186_);
lean_ctor_set(v_reuseFailAlloc_3220_, 6, v_leanLibDir_3187_);
lean_ctor_set(v_reuseFailAlloc_3220_, 7, v_nativeLibDir_3188_);
lean_ctor_set(v_reuseFailAlloc_3220_, 8, v_binDir_3189_);
lean_ctor_set(v_reuseFailAlloc_3220_, 9, v_irDir_3190_);
lean_ctor_set(v_reuseFailAlloc_3220_, 10, v_releaseRepo_3191_);
lean_ctor_set(v_reuseFailAlloc_3220_, 11, v_buildArchive_3192_);
lean_ctor_set(v_reuseFailAlloc_3220_, 12, v_testDriver_3194_);
lean_ctor_set(v_reuseFailAlloc_3220_, 13, v_testDriverArgs_3195_);
lean_ctor_set(v_reuseFailAlloc_3220_, 14, v_lintDriver_3196_);
lean_ctor_set(v_reuseFailAlloc_3220_, 15, v_lintDriverArgs_3197_);
lean_ctor_set(v_reuseFailAlloc_3220_, 16, v_version_3198_);
lean_ctor_set(v_reuseFailAlloc_3220_, 17, v_versionTags_3199_);
lean_ctor_set(v_reuseFailAlloc_3220_, 18, v_description_3200_);
lean_ctor_set(v_reuseFailAlloc_3220_, 19, v_keywords_3201_);
lean_ctor_set(v_reuseFailAlloc_3220_, 20, v_homepage_3202_);
lean_ctor_set(v_reuseFailAlloc_3220_, 21, v_license_3203_);
lean_ctor_set(v_reuseFailAlloc_3220_, 22, v_licenseFiles_3204_);
lean_ctor_set(v_reuseFailAlloc_3220_, 23, v_readmeFile_3205_);
lean_ctor_set(v_reuseFailAlloc_3220_, 24, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3220_, 25, v_restoreAllArtifacts_x3f_3208_);
lean_ctor_set(v_reuseFailAlloc_3220_, 26, v_builtinLint_x3f_3211_);
lean_ctor_set(v_reuseFailAlloc_3220_, 27, v_checks_3212_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28, v_bootstrap_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28 + 1, v_precompileModules_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28 + 3, v_reservoir_3206_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3209_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28 + 5, v_allowImportAll_3210_);
lean_ctor_set_uint8(v_reuseFailAlloc_3220_, sizeof(void*)*28 + 6, v_fixedToolchain_3213_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(lean_object* v_x_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_box(0);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3___boxed(lean_object* v_x_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___lam__3(v_x_3224_);
lean_dec_ref(v_x_3224_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3235_, lean_object* v_n_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__4));
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3238_, lean_object* v_n_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3238_, v_n_3239_);
lean_dec(v_n_3239_);
lean_dec(v_p_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3241_, lean_object* v_n_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3241_, v_n_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3244_, lean_object* v_n_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3244_, v_n_3245_);
lean_dec(v_n_3245_);
lean_dec(v_p_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3247_, lean_object* v_n_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3247_, v_n_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3250_, lean_object* v_n_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3250_, v_n_3251_);
lean_dec(v_n_3251_);
lean_dec(v_p_3250_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(lean_object* v_cfg_3253_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3254_; 
v_restoreAllArtifacts_x3f_3254_ = lean_ctor_get(v_cfg_3253_, 25);
lean_inc(v_restoreAllArtifacts_x3f_3254_);
return v_restoreAllArtifacts_x3f_3254_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0___boxed(lean_object* v_cfg_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__0(v_cfg_3255_);
lean_dec_ref(v_cfg_3255_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__1(lean_object* v_val_3257_, lean_object* v_cfg_3258_){
_start:
{
lean_object* v_toWorkspaceConfig_3259_; lean_object* v_toLeanConfig_3260_; uint8_t v_bootstrap_3261_; lean_object* v_extraDepTargets_3262_; uint8_t v_precompileModules_3263_; lean_object* v_moreGlobalServerArgs_3264_; lean_object* v_srcDir_3265_; lean_object* v_buildDir_3266_; lean_object* v_leanLibDir_3267_; lean_object* v_nativeLibDir_3268_; lean_object* v_binDir_3269_; lean_object* v_irDir_3270_; lean_object* v_releaseRepo_3271_; lean_object* v_buildArchive_3272_; uint8_t v_preferReleaseBuild_3273_; lean_object* v_testDriver_3274_; lean_object* v_testDriverArgs_3275_; lean_object* v_lintDriver_3276_; lean_object* v_lintDriverArgs_3277_; lean_object* v_version_3278_; lean_object* v_versionTags_3279_; lean_object* v_description_3280_; lean_object* v_keywords_3281_; lean_object* v_homepage_3282_; lean_object* v_license_3283_; lean_object* v_licenseFiles_3284_; lean_object* v_readmeFile_3285_; uint8_t v_reservoir_3286_; lean_object* v_enableArtifactCache_x3f_3287_; uint8_t v_libPrefixOnWindows_3288_; uint8_t v_allowImportAll_3289_; lean_object* v_builtinLint_x3f_3290_; lean_object* v_checks_3291_; uint8_t v_fixedToolchain_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_toWorkspaceConfig_3259_ = lean_ctor_get(v_cfg_3258_, 0);
v_toLeanConfig_3260_ = lean_ctor_get(v_cfg_3258_, 1);
v_bootstrap_3261_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28);
v_extraDepTargets_3262_ = lean_ctor_get(v_cfg_3258_, 2);
v_precompileModules_3263_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3264_ = lean_ctor_get(v_cfg_3258_, 3);
v_srcDir_3265_ = lean_ctor_get(v_cfg_3258_, 4);
v_buildDir_3266_ = lean_ctor_get(v_cfg_3258_, 5);
v_leanLibDir_3267_ = lean_ctor_get(v_cfg_3258_, 6);
v_nativeLibDir_3268_ = lean_ctor_get(v_cfg_3258_, 7);
v_binDir_3269_ = lean_ctor_get(v_cfg_3258_, 8);
v_irDir_3270_ = lean_ctor_get(v_cfg_3258_, 9);
v_releaseRepo_3271_ = lean_ctor_get(v_cfg_3258_, 10);
v_buildArchive_3272_ = lean_ctor_get(v_cfg_3258_, 11);
v_preferReleaseBuild_3273_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28 + 2);
v_testDriver_3274_ = lean_ctor_get(v_cfg_3258_, 12);
v_testDriverArgs_3275_ = lean_ctor_get(v_cfg_3258_, 13);
v_lintDriver_3276_ = lean_ctor_get(v_cfg_3258_, 14);
v_lintDriverArgs_3277_ = lean_ctor_get(v_cfg_3258_, 15);
v_version_3278_ = lean_ctor_get(v_cfg_3258_, 16);
v_versionTags_3279_ = lean_ctor_get(v_cfg_3258_, 17);
v_description_3280_ = lean_ctor_get(v_cfg_3258_, 18);
v_keywords_3281_ = lean_ctor_get(v_cfg_3258_, 19);
v_homepage_3282_ = lean_ctor_get(v_cfg_3258_, 20);
v_license_3283_ = lean_ctor_get(v_cfg_3258_, 21);
v_licenseFiles_3284_ = lean_ctor_get(v_cfg_3258_, 22);
v_readmeFile_3285_ = lean_ctor_get(v_cfg_3258_, 23);
v_reservoir_3286_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3287_ = lean_ctor_get(v_cfg_3258_, 24);
v_libPrefixOnWindows_3288_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28 + 4);
v_allowImportAll_3289_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3290_ = lean_ctor_get(v_cfg_3258_, 26);
v_checks_3291_ = lean_ctor_get(v_cfg_3258_, 27);
v_fixedToolchain_3292_ = lean_ctor_get_uint8(v_cfg_3258_, sizeof(void*)*28 + 6);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_cfg_3258_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; 
v_unused_3300_ = lean_ctor_get(v_cfg_3258_, 25);
lean_dec(v_unused_3300_);
v___x_3294_ = v_cfg_3258_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_checks_3291_);
lean_inc(v_builtinLint_x3f_3290_);
lean_inc(v_enableArtifactCache_x3f_3287_);
lean_inc(v_readmeFile_3285_);
lean_inc(v_licenseFiles_3284_);
lean_inc(v_license_3283_);
lean_inc(v_homepage_3282_);
lean_inc(v_keywords_3281_);
lean_inc(v_description_3280_);
lean_inc(v_versionTags_3279_);
lean_inc(v_version_3278_);
lean_inc(v_lintDriverArgs_3277_);
lean_inc(v_lintDriver_3276_);
lean_inc(v_testDriverArgs_3275_);
lean_inc(v_testDriver_3274_);
lean_inc(v_buildArchive_3272_);
lean_inc(v_releaseRepo_3271_);
lean_inc(v_irDir_3270_);
lean_inc(v_binDir_3269_);
lean_inc(v_nativeLibDir_3268_);
lean_inc(v_leanLibDir_3267_);
lean_inc(v_buildDir_3266_);
lean_inc(v_srcDir_3265_);
lean_inc(v_moreGlobalServerArgs_3264_);
lean_inc(v_extraDepTargets_3262_);
lean_inc(v_toLeanConfig_3260_);
lean_inc(v_toWorkspaceConfig_3259_);
lean_dec(v_cfg_3258_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 25, v_val_3257_);
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_toWorkspaceConfig_3259_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_toLeanConfig_3260_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_extraDepTargets_3262_);
lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_moreGlobalServerArgs_3264_);
lean_ctor_set(v_reuseFailAlloc_3298_, 4, v_srcDir_3265_);
lean_ctor_set(v_reuseFailAlloc_3298_, 5, v_buildDir_3266_);
lean_ctor_set(v_reuseFailAlloc_3298_, 6, v_leanLibDir_3267_);
lean_ctor_set(v_reuseFailAlloc_3298_, 7, v_nativeLibDir_3268_);
lean_ctor_set(v_reuseFailAlloc_3298_, 8, v_binDir_3269_);
lean_ctor_set(v_reuseFailAlloc_3298_, 9, v_irDir_3270_);
lean_ctor_set(v_reuseFailAlloc_3298_, 10, v_releaseRepo_3271_);
lean_ctor_set(v_reuseFailAlloc_3298_, 11, v_buildArchive_3272_);
lean_ctor_set(v_reuseFailAlloc_3298_, 12, v_testDriver_3274_);
lean_ctor_set(v_reuseFailAlloc_3298_, 13, v_testDriverArgs_3275_);
lean_ctor_set(v_reuseFailAlloc_3298_, 14, v_lintDriver_3276_);
lean_ctor_set(v_reuseFailAlloc_3298_, 15, v_lintDriverArgs_3277_);
lean_ctor_set(v_reuseFailAlloc_3298_, 16, v_version_3278_);
lean_ctor_set(v_reuseFailAlloc_3298_, 17, v_versionTags_3279_);
lean_ctor_set(v_reuseFailAlloc_3298_, 18, v_description_3280_);
lean_ctor_set(v_reuseFailAlloc_3298_, 19, v_keywords_3281_);
lean_ctor_set(v_reuseFailAlloc_3298_, 20, v_homepage_3282_);
lean_ctor_set(v_reuseFailAlloc_3298_, 21, v_license_3283_);
lean_ctor_set(v_reuseFailAlloc_3298_, 22, v_licenseFiles_3284_);
lean_ctor_set(v_reuseFailAlloc_3298_, 23, v_readmeFile_3285_);
lean_ctor_set(v_reuseFailAlloc_3298_, 24, v_enableArtifactCache_x3f_3287_);
lean_ctor_set(v_reuseFailAlloc_3298_, 25, v_val_3257_);
lean_ctor_set(v_reuseFailAlloc_3298_, 26, v_builtinLint_x3f_3290_);
lean_ctor_set(v_reuseFailAlloc_3298_, 27, v_checks_3291_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28, v_bootstrap_3261_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28 + 1, v_precompileModules_3263_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3273_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28 + 3, v_reservoir_3286_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3288_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28 + 5, v_allowImportAll_3289_);
lean_ctor_set_uint8(v_reuseFailAlloc_3298_, sizeof(void*)*28 + 6, v_fixedToolchain_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___lam__2(lean_object* v_f_3301_, lean_object* v_cfg_3302_){
_start:
{
lean_object* v_toWorkspaceConfig_3303_; lean_object* v_toLeanConfig_3304_; uint8_t v_bootstrap_3305_; lean_object* v_extraDepTargets_3306_; uint8_t v_precompileModules_3307_; lean_object* v_moreGlobalServerArgs_3308_; lean_object* v_srcDir_3309_; lean_object* v_buildDir_3310_; lean_object* v_leanLibDir_3311_; lean_object* v_nativeLibDir_3312_; lean_object* v_binDir_3313_; lean_object* v_irDir_3314_; lean_object* v_releaseRepo_3315_; lean_object* v_buildArchive_3316_; uint8_t v_preferReleaseBuild_3317_; lean_object* v_testDriver_3318_; lean_object* v_testDriverArgs_3319_; lean_object* v_lintDriver_3320_; lean_object* v_lintDriverArgs_3321_; lean_object* v_version_3322_; lean_object* v_versionTags_3323_; lean_object* v_description_3324_; lean_object* v_keywords_3325_; lean_object* v_homepage_3326_; lean_object* v_license_3327_; lean_object* v_licenseFiles_3328_; lean_object* v_readmeFile_3329_; uint8_t v_reservoir_3330_; lean_object* v_enableArtifactCache_x3f_3331_; lean_object* v_restoreAllArtifacts_x3f_3332_; uint8_t v_libPrefixOnWindows_3333_; uint8_t v_allowImportAll_3334_; lean_object* v_builtinLint_x3f_3335_; lean_object* v_checks_3336_; uint8_t v_fixedToolchain_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3345_; 
v_toWorkspaceConfig_3303_ = lean_ctor_get(v_cfg_3302_, 0);
v_toLeanConfig_3304_ = lean_ctor_get(v_cfg_3302_, 1);
v_bootstrap_3305_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28);
v_extraDepTargets_3306_ = lean_ctor_get(v_cfg_3302_, 2);
v_precompileModules_3307_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3308_ = lean_ctor_get(v_cfg_3302_, 3);
v_srcDir_3309_ = lean_ctor_get(v_cfg_3302_, 4);
v_buildDir_3310_ = lean_ctor_get(v_cfg_3302_, 5);
v_leanLibDir_3311_ = lean_ctor_get(v_cfg_3302_, 6);
v_nativeLibDir_3312_ = lean_ctor_get(v_cfg_3302_, 7);
v_binDir_3313_ = lean_ctor_get(v_cfg_3302_, 8);
v_irDir_3314_ = lean_ctor_get(v_cfg_3302_, 9);
v_releaseRepo_3315_ = lean_ctor_get(v_cfg_3302_, 10);
v_buildArchive_3316_ = lean_ctor_get(v_cfg_3302_, 11);
v_preferReleaseBuild_3317_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28 + 2);
v_testDriver_3318_ = lean_ctor_get(v_cfg_3302_, 12);
v_testDriverArgs_3319_ = lean_ctor_get(v_cfg_3302_, 13);
v_lintDriver_3320_ = lean_ctor_get(v_cfg_3302_, 14);
v_lintDriverArgs_3321_ = lean_ctor_get(v_cfg_3302_, 15);
v_version_3322_ = lean_ctor_get(v_cfg_3302_, 16);
v_versionTags_3323_ = lean_ctor_get(v_cfg_3302_, 17);
v_description_3324_ = lean_ctor_get(v_cfg_3302_, 18);
v_keywords_3325_ = lean_ctor_get(v_cfg_3302_, 19);
v_homepage_3326_ = lean_ctor_get(v_cfg_3302_, 20);
v_license_3327_ = lean_ctor_get(v_cfg_3302_, 21);
v_licenseFiles_3328_ = lean_ctor_get(v_cfg_3302_, 22);
v_readmeFile_3329_ = lean_ctor_get(v_cfg_3302_, 23);
v_reservoir_3330_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3331_ = lean_ctor_get(v_cfg_3302_, 24);
v_restoreAllArtifacts_x3f_3332_ = lean_ctor_get(v_cfg_3302_, 25);
v_libPrefixOnWindows_3333_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28 + 4);
v_allowImportAll_3334_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3335_ = lean_ctor_get(v_cfg_3302_, 26);
v_checks_3336_ = lean_ctor_get(v_cfg_3302_, 27);
v_fixedToolchain_3337_ = lean_ctor_get_uint8(v_cfg_3302_, sizeof(void*)*28 + 6);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_cfg_3302_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3339_ = v_cfg_3302_;
v_isShared_3340_ = v_isSharedCheck_3345_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_checks_3336_);
lean_inc(v_builtinLint_x3f_3335_);
lean_inc(v_restoreAllArtifacts_x3f_3332_);
lean_inc(v_enableArtifactCache_x3f_3331_);
lean_inc(v_readmeFile_3329_);
lean_inc(v_licenseFiles_3328_);
lean_inc(v_license_3327_);
lean_inc(v_homepage_3326_);
lean_inc(v_keywords_3325_);
lean_inc(v_description_3324_);
lean_inc(v_versionTags_3323_);
lean_inc(v_version_3322_);
lean_inc(v_lintDriverArgs_3321_);
lean_inc(v_lintDriver_3320_);
lean_inc(v_testDriverArgs_3319_);
lean_inc(v_testDriver_3318_);
lean_inc(v_buildArchive_3316_);
lean_inc(v_releaseRepo_3315_);
lean_inc(v_irDir_3314_);
lean_inc(v_binDir_3313_);
lean_inc(v_nativeLibDir_3312_);
lean_inc(v_leanLibDir_3311_);
lean_inc(v_buildDir_3310_);
lean_inc(v_srcDir_3309_);
lean_inc(v_moreGlobalServerArgs_3308_);
lean_inc(v_extraDepTargets_3306_);
lean_inc(v_toLeanConfig_3304_);
lean_inc(v_toWorkspaceConfig_3303_);
lean_dec(v_cfg_3302_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3345_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3341_ = lean_apply_1(v_f_3301_, v_restoreAllArtifacts_x3f_3332_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 25, v___x_3341_);
v___x_3343_ = v___x_3339_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_toWorkspaceConfig_3303_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_toLeanConfig_3304_);
lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_extraDepTargets_3306_);
lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_moreGlobalServerArgs_3308_);
lean_ctor_set(v_reuseFailAlloc_3344_, 4, v_srcDir_3309_);
lean_ctor_set(v_reuseFailAlloc_3344_, 5, v_buildDir_3310_);
lean_ctor_set(v_reuseFailAlloc_3344_, 6, v_leanLibDir_3311_);
lean_ctor_set(v_reuseFailAlloc_3344_, 7, v_nativeLibDir_3312_);
lean_ctor_set(v_reuseFailAlloc_3344_, 8, v_binDir_3313_);
lean_ctor_set(v_reuseFailAlloc_3344_, 9, v_irDir_3314_);
lean_ctor_set(v_reuseFailAlloc_3344_, 10, v_releaseRepo_3315_);
lean_ctor_set(v_reuseFailAlloc_3344_, 11, v_buildArchive_3316_);
lean_ctor_set(v_reuseFailAlloc_3344_, 12, v_testDriver_3318_);
lean_ctor_set(v_reuseFailAlloc_3344_, 13, v_testDriverArgs_3319_);
lean_ctor_set(v_reuseFailAlloc_3344_, 14, v_lintDriver_3320_);
lean_ctor_set(v_reuseFailAlloc_3344_, 15, v_lintDriverArgs_3321_);
lean_ctor_set(v_reuseFailAlloc_3344_, 16, v_version_3322_);
lean_ctor_set(v_reuseFailAlloc_3344_, 17, v_versionTags_3323_);
lean_ctor_set(v_reuseFailAlloc_3344_, 18, v_description_3324_);
lean_ctor_set(v_reuseFailAlloc_3344_, 19, v_keywords_3325_);
lean_ctor_set(v_reuseFailAlloc_3344_, 20, v_homepage_3326_);
lean_ctor_set(v_reuseFailAlloc_3344_, 21, v_license_3327_);
lean_ctor_set(v_reuseFailAlloc_3344_, 22, v_licenseFiles_3328_);
lean_ctor_set(v_reuseFailAlloc_3344_, 23, v_readmeFile_3329_);
lean_ctor_set(v_reuseFailAlloc_3344_, 24, v_enableArtifactCache_x3f_3331_);
lean_ctor_set(v_reuseFailAlloc_3344_, 25, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3344_, 26, v_builtinLint_x3f_3335_);
lean_ctor_set(v_reuseFailAlloc_3344_, 27, v_checks_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28, v_bootstrap_3305_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28 + 1, v_precompileModules_3307_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3317_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28 + 3, v_reservoir_3330_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3333_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28 + 5, v_allowImportAll_3334_);
lean_ctor_set_uint8(v_reuseFailAlloc_3344_, sizeof(void*)*28 + 6, v_fixedToolchain_3337_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3354_, lean_object* v_n_3355_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__3));
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3357_, lean_object* v_n_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3357_, v_n_3358_);
lean_dec(v_n_3358_);
lean_dec(v_p_3357_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3360_, lean_object* v_n_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3360_, v_n_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3363_, lean_object* v_n_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3363_, v_n_3364_);
lean_dec(v_n_3364_);
lean_dec(v_p_3363_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3366_, lean_object* v_n_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3366_, v_n_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3369_, lean_object* v_n_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3369_, v_n_3370_);
lean_dec(v_n_3370_);
lean_dec(v_p_3369_);
return v_res_3371_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(lean_object* v_cfg_3372_){
_start:
{
uint8_t v_libPrefixOnWindows_3373_; 
v_libPrefixOnWindows_3373_ = lean_ctor_get_uint8(v_cfg_3372_, sizeof(void*)*28 + 4);
return v_libPrefixOnWindows_3373_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0___boxed(lean_object* v_cfg_3374_){
_start:
{
uint8_t v_res_3375_; lean_object* v_r_3376_; 
v_res_3375_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__0(v_cfg_3374_);
lean_dec_ref(v_cfg_3374_);
v_r_3376_ = lean_box(v_res_3375_);
return v_r_3376_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(uint8_t v_val_3377_, lean_object* v_cfg_3378_){
_start:
{
lean_object* v_toWorkspaceConfig_3379_; lean_object* v_toLeanConfig_3380_; uint8_t v_bootstrap_3381_; lean_object* v_extraDepTargets_3382_; uint8_t v_precompileModules_3383_; lean_object* v_moreGlobalServerArgs_3384_; lean_object* v_srcDir_3385_; lean_object* v_buildDir_3386_; lean_object* v_leanLibDir_3387_; lean_object* v_nativeLibDir_3388_; lean_object* v_binDir_3389_; lean_object* v_irDir_3390_; lean_object* v_releaseRepo_3391_; lean_object* v_buildArchive_3392_; uint8_t v_preferReleaseBuild_3393_; lean_object* v_testDriver_3394_; lean_object* v_testDriverArgs_3395_; lean_object* v_lintDriver_3396_; lean_object* v_lintDriverArgs_3397_; lean_object* v_version_3398_; lean_object* v_versionTags_3399_; lean_object* v_description_3400_; lean_object* v_keywords_3401_; lean_object* v_homepage_3402_; lean_object* v_license_3403_; lean_object* v_licenseFiles_3404_; lean_object* v_readmeFile_3405_; uint8_t v_reservoir_3406_; lean_object* v_enableArtifactCache_x3f_3407_; lean_object* v_restoreAllArtifacts_x3f_3408_; uint8_t v_allowImportAll_3409_; lean_object* v_builtinLint_x3f_3410_; lean_object* v_checks_3411_; uint8_t v_fixedToolchain_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
v_toWorkspaceConfig_3379_ = lean_ctor_get(v_cfg_3378_, 0);
v_toLeanConfig_3380_ = lean_ctor_get(v_cfg_3378_, 1);
v_bootstrap_3381_ = lean_ctor_get_uint8(v_cfg_3378_, sizeof(void*)*28);
v_extraDepTargets_3382_ = lean_ctor_get(v_cfg_3378_, 2);
v_precompileModules_3383_ = lean_ctor_get_uint8(v_cfg_3378_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3384_ = lean_ctor_get(v_cfg_3378_, 3);
v_srcDir_3385_ = lean_ctor_get(v_cfg_3378_, 4);
v_buildDir_3386_ = lean_ctor_get(v_cfg_3378_, 5);
v_leanLibDir_3387_ = lean_ctor_get(v_cfg_3378_, 6);
v_nativeLibDir_3388_ = lean_ctor_get(v_cfg_3378_, 7);
v_binDir_3389_ = lean_ctor_get(v_cfg_3378_, 8);
v_irDir_3390_ = lean_ctor_get(v_cfg_3378_, 9);
v_releaseRepo_3391_ = lean_ctor_get(v_cfg_3378_, 10);
v_buildArchive_3392_ = lean_ctor_get(v_cfg_3378_, 11);
v_preferReleaseBuild_3393_ = lean_ctor_get_uint8(v_cfg_3378_, sizeof(void*)*28 + 2);
v_testDriver_3394_ = lean_ctor_get(v_cfg_3378_, 12);
v_testDriverArgs_3395_ = lean_ctor_get(v_cfg_3378_, 13);
v_lintDriver_3396_ = lean_ctor_get(v_cfg_3378_, 14);
v_lintDriverArgs_3397_ = lean_ctor_get(v_cfg_3378_, 15);
v_version_3398_ = lean_ctor_get(v_cfg_3378_, 16);
v_versionTags_3399_ = lean_ctor_get(v_cfg_3378_, 17);
v_description_3400_ = lean_ctor_get(v_cfg_3378_, 18);
v_keywords_3401_ = lean_ctor_get(v_cfg_3378_, 19);
v_homepage_3402_ = lean_ctor_get(v_cfg_3378_, 20);
v_license_3403_ = lean_ctor_get(v_cfg_3378_, 21);
v_licenseFiles_3404_ = lean_ctor_get(v_cfg_3378_, 22);
v_readmeFile_3405_ = lean_ctor_get(v_cfg_3378_, 23);
v_reservoir_3406_ = lean_ctor_get_uint8(v_cfg_3378_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3407_ = lean_ctor_get(v_cfg_3378_, 24);
v_restoreAllArtifacts_x3f_3408_ = lean_ctor_get(v_cfg_3378_, 25);
v_allowImportAll_3409_ = lean_ctor_get_uint8(v_cfg_3378_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3410_ = lean_ctor_get(v_cfg_3378_, 26);
v_checks_3411_ = lean_ctor_get(v_cfg_3378_, 27);
v_fixedToolchain_3412_ = lean_ctor_get_uint8(v_cfg_3378_, sizeof(void*)*28 + 6);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_cfg_3378_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v_cfg_3378_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_checks_3411_);
lean_inc(v_builtinLint_x3f_3410_);
lean_inc(v_restoreAllArtifacts_x3f_3408_);
lean_inc(v_enableArtifactCache_x3f_3407_);
lean_inc(v_readmeFile_3405_);
lean_inc(v_licenseFiles_3404_);
lean_inc(v_license_3403_);
lean_inc(v_homepage_3402_);
lean_inc(v_keywords_3401_);
lean_inc(v_description_3400_);
lean_inc(v_versionTags_3399_);
lean_inc(v_version_3398_);
lean_inc(v_lintDriverArgs_3397_);
lean_inc(v_lintDriver_3396_);
lean_inc(v_testDriverArgs_3395_);
lean_inc(v_testDriver_3394_);
lean_inc(v_buildArchive_3392_);
lean_inc(v_releaseRepo_3391_);
lean_inc(v_irDir_3390_);
lean_inc(v_binDir_3389_);
lean_inc(v_nativeLibDir_3388_);
lean_inc(v_leanLibDir_3387_);
lean_inc(v_buildDir_3386_);
lean_inc(v_srcDir_3385_);
lean_inc(v_moreGlobalServerArgs_3384_);
lean_inc(v_extraDepTargets_3382_);
lean_inc(v_toLeanConfig_3380_);
lean_inc(v_toWorkspaceConfig_3379_);
lean_dec(v_cfg_3378_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_toWorkspaceConfig_3379_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_toLeanConfig_3380_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_extraDepTargets_3382_);
lean_ctor_set(v_reuseFailAlloc_3418_, 3, v_moreGlobalServerArgs_3384_);
lean_ctor_set(v_reuseFailAlloc_3418_, 4, v_srcDir_3385_);
lean_ctor_set(v_reuseFailAlloc_3418_, 5, v_buildDir_3386_);
lean_ctor_set(v_reuseFailAlloc_3418_, 6, v_leanLibDir_3387_);
lean_ctor_set(v_reuseFailAlloc_3418_, 7, v_nativeLibDir_3388_);
lean_ctor_set(v_reuseFailAlloc_3418_, 8, v_binDir_3389_);
lean_ctor_set(v_reuseFailAlloc_3418_, 9, v_irDir_3390_);
lean_ctor_set(v_reuseFailAlloc_3418_, 10, v_releaseRepo_3391_);
lean_ctor_set(v_reuseFailAlloc_3418_, 11, v_buildArchive_3392_);
lean_ctor_set(v_reuseFailAlloc_3418_, 12, v_testDriver_3394_);
lean_ctor_set(v_reuseFailAlloc_3418_, 13, v_testDriverArgs_3395_);
lean_ctor_set(v_reuseFailAlloc_3418_, 14, v_lintDriver_3396_);
lean_ctor_set(v_reuseFailAlloc_3418_, 15, v_lintDriverArgs_3397_);
lean_ctor_set(v_reuseFailAlloc_3418_, 16, v_version_3398_);
lean_ctor_set(v_reuseFailAlloc_3418_, 17, v_versionTags_3399_);
lean_ctor_set(v_reuseFailAlloc_3418_, 18, v_description_3400_);
lean_ctor_set(v_reuseFailAlloc_3418_, 19, v_keywords_3401_);
lean_ctor_set(v_reuseFailAlloc_3418_, 20, v_homepage_3402_);
lean_ctor_set(v_reuseFailAlloc_3418_, 21, v_license_3403_);
lean_ctor_set(v_reuseFailAlloc_3418_, 22, v_licenseFiles_3404_);
lean_ctor_set(v_reuseFailAlloc_3418_, 23, v_readmeFile_3405_);
lean_ctor_set(v_reuseFailAlloc_3418_, 24, v_enableArtifactCache_x3f_3407_);
lean_ctor_set(v_reuseFailAlloc_3418_, 25, v_restoreAllArtifacts_x3f_3408_);
lean_ctor_set(v_reuseFailAlloc_3418_, 26, v_builtinLint_x3f_3410_);
lean_ctor_set(v_reuseFailAlloc_3418_, 27, v_checks_3411_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*28, v_bootstrap_3381_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*28 + 1, v_precompileModules_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3393_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*28 + 3, v_reservoir_3406_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*28 + 5, v_allowImportAll_3409_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*28 + 6, v_fixedToolchain_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*28 + 4, v_val_3377_);
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1___boxed(lean_object* v_val_3420_, lean_object* v_cfg_3421_){
_start:
{
uint8_t v_val_140__boxed_3422_; lean_object* v_res_3423_; 
v_val_140__boxed_3422_ = lean_unbox(v_val_3420_);
v_res_3423_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__1(v_val_140__boxed_3422_, v_cfg_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___lam__2(lean_object* v_f_3424_, lean_object* v_cfg_3425_){
_start:
{
lean_object* v_toWorkspaceConfig_3426_; lean_object* v_toLeanConfig_3427_; uint8_t v_bootstrap_3428_; lean_object* v_extraDepTargets_3429_; uint8_t v_precompileModules_3430_; lean_object* v_moreGlobalServerArgs_3431_; lean_object* v_srcDir_3432_; lean_object* v_buildDir_3433_; lean_object* v_leanLibDir_3434_; lean_object* v_nativeLibDir_3435_; lean_object* v_binDir_3436_; lean_object* v_irDir_3437_; lean_object* v_releaseRepo_3438_; lean_object* v_buildArchive_3439_; uint8_t v_preferReleaseBuild_3440_; lean_object* v_testDriver_3441_; lean_object* v_testDriverArgs_3442_; lean_object* v_lintDriver_3443_; lean_object* v_lintDriverArgs_3444_; lean_object* v_version_3445_; lean_object* v_versionTags_3446_; lean_object* v_description_3447_; lean_object* v_keywords_3448_; lean_object* v_homepage_3449_; lean_object* v_license_3450_; lean_object* v_licenseFiles_3451_; lean_object* v_readmeFile_3452_; uint8_t v_reservoir_3453_; lean_object* v_enableArtifactCache_x3f_3454_; lean_object* v_restoreAllArtifacts_x3f_3455_; uint8_t v_libPrefixOnWindows_3456_; uint8_t v_allowImportAll_3457_; lean_object* v_builtinLint_x3f_3458_; lean_object* v_checks_3459_; uint8_t v_fixedToolchain_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3470_; 
v_toWorkspaceConfig_3426_ = lean_ctor_get(v_cfg_3425_, 0);
v_toLeanConfig_3427_ = lean_ctor_get(v_cfg_3425_, 1);
v_bootstrap_3428_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28);
v_extraDepTargets_3429_ = lean_ctor_get(v_cfg_3425_, 2);
v_precompileModules_3430_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3431_ = lean_ctor_get(v_cfg_3425_, 3);
v_srcDir_3432_ = lean_ctor_get(v_cfg_3425_, 4);
v_buildDir_3433_ = lean_ctor_get(v_cfg_3425_, 5);
v_leanLibDir_3434_ = lean_ctor_get(v_cfg_3425_, 6);
v_nativeLibDir_3435_ = lean_ctor_get(v_cfg_3425_, 7);
v_binDir_3436_ = lean_ctor_get(v_cfg_3425_, 8);
v_irDir_3437_ = lean_ctor_get(v_cfg_3425_, 9);
v_releaseRepo_3438_ = lean_ctor_get(v_cfg_3425_, 10);
v_buildArchive_3439_ = lean_ctor_get(v_cfg_3425_, 11);
v_preferReleaseBuild_3440_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28 + 2);
v_testDriver_3441_ = lean_ctor_get(v_cfg_3425_, 12);
v_testDriverArgs_3442_ = lean_ctor_get(v_cfg_3425_, 13);
v_lintDriver_3443_ = lean_ctor_get(v_cfg_3425_, 14);
v_lintDriverArgs_3444_ = lean_ctor_get(v_cfg_3425_, 15);
v_version_3445_ = lean_ctor_get(v_cfg_3425_, 16);
v_versionTags_3446_ = lean_ctor_get(v_cfg_3425_, 17);
v_description_3447_ = lean_ctor_get(v_cfg_3425_, 18);
v_keywords_3448_ = lean_ctor_get(v_cfg_3425_, 19);
v_homepage_3449_ = lean_ctor_get(v_cfg_3425_, 20);
v_license_3450_ = lean_ctor_get(v_cfg_3425_, 21);
v_licenseFiles_3451_ = lean_ctor_get(v_cfg_3425_, 22);
v_readmeFile_3452_ = lean_ctor_get(v_cfg_3425_, 23);
v_reservoir_3453_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3454_ = lean_ctor_get(v_cfg_3425_, 24);
v_restoreAllArtifacts_x3f_3455_ = lean_ctor_get(v_cfg_3425_, 25);
v_libPrefixOnWindows_3456_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28 + 4);
v_allowImportAll_3457_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3458_ = lean_ctor_get(v_cfg_3425_, 26);
v_checks_3459_ = lean_ctor_get(v_cfg_3425_, 27);
v_fixedToolchain_3460_ = lean_ctor_get_uint8(v_cfg_3425_, sizeof(void*)*28 + 6);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_cfg_3425_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3462_ = v_cfg_3425_;
v_isShared_3463_ = v_isSharedCheck_3470_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_checks_3459_);
lean_inc(v_builtinLint_x3f_3458_);
lean_inc(v_restoreAllArtifacts_x3f_3455_);
lean_inc(v_enableArtifactCache_x3f_3454_);
lean_inc(v_readmeFile_3452_);
lean_inc(v_licenseFiles_3451_);
lean_inc(v_license_3450_);
lean_inc(v_homepage_3449_);
lean_inc(v_keywords_3448_);
lean_inc(v_description_3447_);
lean_inc(v_versionTags_3446_);
lean_inc(v_version_3445_);
lean_inc(v_lintDriverArgs_3444_);
lean_inc(v_lintDriver_3443_);
lean_inc(v_testDriverArgs_3442_);
lean_inc(v_testDriver_3441_);
lean_inc(v_buildArchive_3439_);
lean_inc(v_releaseRepo_3438_);
lean_inc(v_irDir_3437_);
lean_inc(v_binDir_3436_);
lean_inc(v_nativeLibDir_3435_);
lean_inc(v_leanLibDir_3434_);
lean_inc(v_buildDir_3433_);
lean_inc(v_srcDir_3432_);
lean_inc(v_moreGlobalServerArgs_3431_);
lean_inc(v_extraDepTargets_3429_);
lean_inc(v_toLeanConfig_3427_);
lean_inc(v_toWorkspaceConfig_3426_);
lean_dec(v_cfg_3425_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3470_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3464_ = lean_box(v_libPrefixOnWindows_3456_);
v___x_3465_ = lean_apply_1(v_f_3424_, v___x_3464_);
if (v_isShared_3463_ == 0)
{
v___x_3467_ = v___x_3462_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_toWorkspaceConfig_3426_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_toLeanConfig_3427_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_extraDepTargets_3429_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_moreGlobalServerArgs_3431_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_srcDir_3432_);
lean_ctor_set(v_reuseFailAlloc_3469_, 5, v_buildDir_3433_);
lean_ctor_set(v_reuseFailAlloc_3469_, 6, v_leanLibDir_3434_);
lean_ctor_set(v_reuseFailAlloc_3469_, 7, v_nativeLibDir_3435_);
lean_ctor_set(v_reuseFailAlloc_3469_, 8, v_binDir_3436_);
lean_ctor_set(v_reuseFailAlloc_3469_, 9, v_irDir_3437_);
lean_ctor_set(v_reuseFailAlloc_3469_, 10, v_releaseRepo_3438_);
lean_ctor_set(v_reuseFailAlloc_3469_, 11, v_buildArchive_3439_);
lean_ctor_set(v_reuseFailAlloc_3469_, 12, v_testDriver_3441_);
lean_ctor_set(v_reuseFailAlloc_3469_, 13, v_testDriverArgs_3442_);
lean_ctor_set(v_reuseFailAlloc_3469_, 14, v_lintDriver_3443_);
lean_ctor_set(v_reuseFailAlloc_3469_, 15, v_lintDriverArgs_3444_);
lean_ctor_set(v_reuseFailAlloc_3469_, 16, v_version_3445_);
lean_ctor_set(v_reuseFailAlloc_3469_, 17, v_versionTags_3446_);
lean_ctor_set(v_reuseFailAlloc_3469_, 18, v_description_3447_);
lean_ctor_set(v_reuseFailAlloc_3469_, 19, v_keywords_3448_);
lean_ctor_set(v_reuseFailAlloc_3469_, 20, v_homepage_3449_);
lean_ctor_set(v_reuseFailAlloc_3469_, 21, v_license_3450_);
lean_ctor_set(v_reuseFailAlloc_3469_, 22, v_licenseFiles_3451_);
lean_ctor_set(v_reuseFailAlloc_3469_, 23, v_readmeFile_3452_);
lean_ctor_set(v_reuseFailAlloc_3469_, 24, v_enableArtifactCache_x3f_3454_);
lean_ctor_set(v_reuseFailAlloc_3469_, 25, v_restoreAllArtifacts_x3f_3455_);
lean_ctor_set(v_reuseFailAlloc_3469_, 26, v_builtinLint_x3f_3458_);
lean_ctor_set(v_reuseFailAlloc_3469_, 27, v_checks_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3469_, sizeof(void*)*28, v_bootstrap_3428_);
lean_ctor_set_uint8(v_reuseFailAlloc_3469_, sizeof(void*)*28 + 1, v_precompileModules_3430_);
lean_ctor_set_uint8(v_reuseFailAlloc_3469_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3440_);
lean_ctor_set_uint8(v_reuseFailAlloc_3469_, sizeof(void*)*28 + 3, v_reservoir_3453_);
v___x_3467_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
uint8_t v___x_3468_; 
v___x_3468_ = lean_unbox(v___x_3465_);
lean_ctor_set_uint8(v___x_3467_, sizeof(void*)*28 + 4, v___x_3468_);
lean_ctor_set_uint8(v___x_3467_, sizeof(void*)*28 + 5, v_allowImportAll_3457_);
lean_ctor_set_uint8(v___x_3467_, sizeof(void*)*28 + 6, v_fixedToolchain_3460_);
return v___x_3467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3479_, lean_object* v_n_3480_){
_start:
{
lean_object* v___x_3481_; 
v___x_3481_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__3));
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3482_, lean_object* v_n_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3482_, v_n_3483_);
lean_dec(v_n_3483_);
lean_dec(v_p_3482_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3485_, lean_object* v_n_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3485_, v_n_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3488_, lean_object* v_n_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3488_, v_n_3489_);
lean_dec(v_n_3489_);
lean_dec(v_p_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___lam__0(lean_object* v_cfg_3491_){
_start:
{
uint8_t v_allowImportAll_3492_; 
v_allowImportAll_3492_ = lean_ctor_get_uint8(v_cfg_3491_, sizeof(void*)*28 + 5);
return v_allowImportAll_3492_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__0___boxed(lean_object* v_cfg_3493_){
_start:
{
uint8_t v_res_3494_; lean_object* v_r_3495_; 
v_res_3494_ = l_Lake_PackageConfig_allowImportAll___proj___lam__0(v_cfg_3493_);
lean_dec_ref(v_cfg_3493_);
v_r_3495_ = lean_box(v_res_3494_);
return v_r_3495_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1(uint8_t v_val_3496_, lean_object* v_cfg_3497_){
_start:
{
lean_object* v_toWorkspaceConfig_3498_; lean_object* v_toLeanConfig_3499_; uint8_t v_bootstrap_3500_; lean_object* v_extraDepTargets_3501_; uint8_t v_precompileModules_3502_; lean_object* v_moreGlobalServerArgs_3503_; lean_object* v_srcDir_3504_; lean_object* v_buildDir_3505_; lean_object* v_leanLibDir_3506_; lean_object* v_nativeLibDir_3507_; lean_object* v_binDir_3508_; lean_object* v_irDir_3509_; lean_object* v_releaseRepo_3510_; lean_object* v_buildArchive_3511_; uint8_t v_preferReleaseBuild_3512_; lean_object* v_testDriver_3513_; lean_object* v_testDriverArgs_3514_; lean_object* v_lintDriver_3515_; lean_object* v_lintDriverArgs_3516_; lean_object* v_version_3517_; lean_object* v_versionTags_3518_; lean_object* v_description_3519_; lean_object* v_keywords_3520_; lean_object* v_homepage_3521_; lean_object* v_license_3522_; lean_object* v_licenseFiles_3523_; lean_object* v_readmeFile_3524_; uint8_t v_reservoir_3525_; lean_object* v_enableArtifactCache_x3f_3526_; lean_object* v_restoreAllArtifacts_x3f_3527_; uint8_t v_libPrefixOnWindows_3528_; lean_object* v_builtinLint_x3f_3529_; lean_object* v_checks_3530_; uint8_t v_fixedToolchain_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_toWorkspaceConfig_3498_ = lean_ctor_get(v_cfg_3497_, 0);
v_toLeanConfig_3499_ = lean_ctor_get(v_cfg_3497_, 1);
v_bootstrap_3500_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*28);
v_extraDepTargets_3501_ = lean_ctor_get(v_cfg_3497_, 2);
v_precompileModules_3502_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3503_ = lean_ctor_get(v_cfg_3497_, 3);
v_srcDir_3504_ = lean_ctor_get(v_cfg_3497_, 4);
v_buildDir_3505_ = lean_ctor_get(v_cfg_3497_, 5);
v_leanLibDir_3506_ = lean_ctor_get(v_cfg_3497_, 6);
v_nativeLibDir_3507_ = lean_ctor_get(v_cfg_3497_, 7);
v_binDir_3508_ = lean_ctor_get(v_cfg_3497_, 8);
v_irDir_3509_ = lean_ctor_get(v_cfg_3497_, 9);
v_releaseRepo_3510_ = lean_ctor_get(v_cfg_3497_, 10);
v_buildArchive_3511_ = lean_ctor_get(v_cfg_3497_, 11);
v_preferReleaseBuild_3512_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*28 + 2);
v_testDriver_3513_ = lean_ctor_get(v_cfg_3497_, 12);
v_testDriverArgs_3514_ = lean_ctor_get(v_cfg_3497_, 13);
v_lintDriver_3515_ = lean_ctor_get(v_cfg_3497_, 14);
v_lintDriverArgs_3516_ = lean_ctor_get(v_cfg_3497_, 15);
v_version_3517_ = lean_ctor_get(v_cfg_3497_, 16);
v_versionTags_3518_ = lean_ctor_get(v_cfg_3497_, 17);
v_description_3519_ = lean_ctor_get(v_cfg_3497_, 18);
v_keywords_3520_ = lean_ctor_get(v_cfg_3497_, 19);
v_homepage_3521_ = lean_ctor_get(v_cfg_3497_, 20);
v_license_3522_ = lean_ctor_get(v_cfg_3497_, 21);
v_licenseFiles_3523_ = lean_ctor_get(v_cfg_3497_, 22);
v_readmeFile_3524_ = lean_ctor_get(v_cfg_3497_, 23);
v_reservoir_3525_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3526_ = lean_ctor_get(v_cfg_3497_, 24);
v_restoreAllArtifacts_x3f_3527_ = lean_ctor_get(v_cfg_3497_, 25);
v_libPrefixOnWindows_3528_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*28 + 4);
v_builtinLint_x3f_3529_ = lean_ctor_get(v_cfg_3497_, 26);
v_checks_3530_ = lean_ctor_get(v_cfg_3497_, 27);
v_fixedToolchain_3531_ = lean_ctor_get_uint8(v_cfg_3497_, sizeof(void*)*28 + 6);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_cfg_3497_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v_cfg_3497_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_checks_3530_);
lean_inc(v_builtinLint_x3f_3529_);
lean_inc(v_restoreAllArtifacts_x3f_3527_);
lean_inc(v_enableArtifactCache_x3f_3526_);
lean_inc(v_readmeFile_3524_);
lean_inc(v_licenseFiles_3523_);
lean_inc(v_license_3522_);
lean_inc(v_homepage_3521_);
lean_inc(v_keywords_3520_);
lean_inc(v_description_3519_);
lean_inc(v_versionTags_3518_);
lean_inc(v_version_3517_);
lean_inc(v_lintDriverArgs_3516_);
lean_inc(v_lintDriver_3515_);
lean_inc(v_testDriverArgs_3514_);
lean_inc(v_testDriver_3513_);
lean_inc(v_buildArchive_3511_);
lean_inc(v_releaseRepo_3510_);
lean_inc(v_irDir_3509_);
lean_inc(v_binDir_3508_);
lean_inc(v_nativeLibDir_3507_);
lean_inc(v_leanLibDir_3506_);
lean_inc(v_buildDir_3505_);
lean_inc(v_srcDir_3504_);
lean_inc(v_moreGlobalServerArgs_3503_);
lean_inc(v_extraDepTargets_3501_);
lean_inc(v_toLeanConfig_3499_);
lean_inc(v_toWorkspaceConfig_3498_);
lean_dec(v_cfg_3497_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_toWorkspaceConfig_3498_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_toLeanConfig_3499_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_extraDepTargets_3501_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_moreGlobalServerArgs_3503_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_srcDir_3504_);
lean_ctor_set(v_reuseFailAlloc_3537_, 5, v_buildDir_3505_);
lean_ctor_set(v_reuseFailAlloc_3537_, 6, v_leanLibDir_3506_);
lean_ctor_set(v_reuseFailAlloc_3537_, 7, v_nativeLibDir_3507_);
lean_ctor_set(v_reuseFailAlloc_3537_, 8, v_binDir_3508_);
lean_ctor_set(v_reuseFailAlloc_3537_, 9, v_irDir_3509_);
lean_ctor_set(v_reuseFailAlloc_3537_, 10, v_releaseRepo_3510_);
lean_ctor_set(v_reuseFailAlloc_3537_, 11, v_buildArchive_3511_);
lean_ctor_set(v_reuseFailAlloc_3537_, 12, v_testDriver_3513_);
lean_ctor_set(v_reuseFailAlloc_3537_, 13, v_testDriverArgs_3514_);
lean_ctor_set(v_reuseFailAlloc_3537_, 14, v_lintDriver_3515_);
lean_ctor_set(v_reuseFailAlloc_3537_, 15, v_lintDriverArgs_3516_);
lean_ctor_set(v_reuseFailAlloc_3537_, 16, v_version_3517_);
lean_ctor_set(v_reuseFailAlloc_3537_, 17, v_versionTags_3518_);
lean_ctor_set(v_reuseFailAlloc_3537_, 18, v_description_3519_);
lean_ctor_set(v_reuseFailAlloc_3537_, 19, v_keywords_3520_);
lean_ctor_set(v_reuseFailAlloc_3537_, 20, v_homepage_3521_);
lean_ctor_set(v_reuseFailAlloc_3537_, 21, v_license_3522_);
lean_ctor_set(v_reuseFailAlloc_3537_, 22, v_licenseFiles_3523_);
lean_ctor_set(v_reuseFailAlloc_3537_, 23, v_readmeFile_3524_);
lean_ctor_set(v_reuseFailAlloc_3537_, 24, v_enableArtifactCache_x3f_3526_);
lean_ctor_set(v_reuseFailAlloc_3537_, 25, v_restoreAllArtifacts_x3f_3527_);
lean_ctor_set(v_reuseFailAlloc_3537_, 26, v_builtinLint_x3f_3529_);
lean_ctor_set(v_reuseFailAlloc_3537_, 27, v_checks_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*28, v_bootstrap_3500_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*28 + 1, v_precompileModules_3502_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3512_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*28 + 3, v_reservoir_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*28 + 6, v_fixedToolchain_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*28 + 5, v_val_3496_);
return v___x_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__1___boxed(lean_object* v_val_3539_, lean_object* v_cfg_3540_){
_start:
{
uint8_t v_val_140__boxed_3541_; lean_object* v_res_3542_; 
v_val_140__boxed_3541_ = lean_unbox(v_val_3539_);
v_res_3542_ = l_Lake_PackageConfig_allowImportAll___proj___lam__1(v_val_140__boxed_3541_, v_cfg_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___lam__2(lean_object* v_f_3543_, lean_object* v_cfg_3544_){
_start:
{
lean_object* v_toWorkspaceConfig_3545_; lean_object* v_toLeanConfig_3546_; uint8_t v_bootstrap_3547_; lean_object* v_extraDepTargets_3548_; uint8_t v_precompileModules_3549_; lean_object* v_moreGlobalServerArgs_3550_; lean_object* v_srcDir_3551_; lean_object* v_buildDir_3552_; lean_object* v_leanLibDir_3553_; lean_object* v_nativeLibDir_3554_; lean_object* v_binDir_3555_; lean_object* v_irDir_3556_; lean_object* v_releaseRepo_3557_; lean_object* v_buildArchive_3558_; uint8_t v_preferReleaseBuild_3559_; lean_object* v_testDriver_3560_; lean_object* v_testDriverArgs_3561_; lean_object* v_lintDriver_3562_; lean_object* v_lintDriverArgs_3563_; lean_object* v_version_3564_; lean_object* v_versionTags_3565_; lean_object* v_description_3566_; lean_object* v_keywords_3567_; lean_object* v_homepage_3568_; lean_object* v_license_3569_; lean_object* v_licenseFiles_3570_; lean_object* v_readmeFile_3571_; uint8_t v_reservoir_3572_; lean_object* v_enableArtifactCache_x3f_3573_; lean_object* v_restoreAllArtifacts_x3f_3574_; uint8_t v_libPrefixOnWindows_3575_; uint8_t v_allowImportAll_3576_; lean_object* v_builtinLint_x3f_3577_; lean_object* v_checks_3578_; uint8_t v_fixedToolchain_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3589_; 
v_toWorkspaceConfig_3545_ = lean_ctor_get(v_cfg_3544_, 0);
v_toLeanConfig_3546_ = lean_ctor_get(v_cfg_3544_, 1);
v_bootstrap_3547_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28);
v_extraDepTargets_3548_ = lean_ctor_get(v_cfg_3544_, 2);
v_precompileModules_3549_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3550_ = lean_ctor_get(v_cfg_3544_, 3);
v_srcDir_3551_ = lean_ctor_get(v_cfg_3544_, 4);
v_buildDir_3552_ = lean_ctor_get(v_cfg_3544_, 5);
v_leanLibDir_3553_ = lean_ctor_get(v_cfg_3544_, 6);
v_nativeLibDir_3554_ = lean_ctor_get(v_cfg_3544_, 7);
v_binDir_3555_ = lean_ctor_get(v_cfg_3544_, 8);
v_irDir_3556_ = lean_ctor_get(v_cfg_3544_, 9);
v_releaseRepo_3557_ = lean_ctor_get(v_cfg_3544_, 10);
v_buildArchive_3558_ = lean_ctor_get(v_cfg_3544_, 11);
v_preferReleaseBuild_3559_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28 + 2);
v_testDriver_3560_ = lean_ctor_get(v_cfg_3544_, 12);
v_testDriverArgs_3561_ = lean_ctor_get(v_cfg_3544_, 13);
v_lintDriver_3562_ = lean_ctor_get(v_cfg_3544_, 14);
v_lintDriverArgs_3563_ = lean_ctor_get(v_cfg_3544_, 15);
v_version_3564_ = lean_ctor_get(v_cfg_3544_, 16);
v_versionTags_3565_ = lean_ctor_get(v_cfg_3544_, 17);
v_description_3566_ = lean_ctor_get(v_cfg_3544_, 18);
v_keywords_3567_ = lean_ctor_get(v_cfg_3544_, 19);
v_homepage_3568_ = lean_ctor_get(v_cfg_3544_, 20);
v_license_3569_ = lean_ctor_get(v_cfg_3544_, 21);
v_licenseFiles_3570_ = lean_ctor_get(v_cfg_3544_, 22);
v_readmeFile_3571_ = lean_ctor_get(v_cfg_3544_, 23);
v_reservoir_3572_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3573_ = lean_ctor_get(v_cfg_3544_, 24);
v_restoreAllArtifacts_x3f_3574_ = lean_ctor_get(v_cfg_3544_, 25);
v_libPrefixOnWindows_3575_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28 + 4);
v_allowImportAll_3576_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3577_ = lean_ctor_get(v_cfg_3544_, 26);
v_checks_3578_ = lean_ctor_get(v_cfg_3544_, 27);
v_fixedToolchain_3579_ = lean_ctor_get_uint8(v_cfg_3544_, sizeof(void*)*28 + 6);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_cfg_3544_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3581_ = v_cfg_3544_;
v_isShared_3582_ = v_isSharedCheck_3589_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_checks_3578_);
lean_inc(v_builtinLint_x3f_3577_);
lean_inc(v_restoreAllArtifacts_x3f_3574_);
lean_inc(v_enableArtifactCache_x3f_3573_);
lean_inc(v_readmeFile_3571_);
lean_inc(v_licenseFiles_3570_);
lean_inc(v_license_3569_);
lean_inc(v_homepage_3568_);
lean_inc(v_keywords_3567_);
lean_inc(v_description_3566_);
lean_inc(v_versionTags_3565_);
lean_inc(v_version_3564_);
lean_inc(v_lintDriverArgs_3563_);
lean_inc(v_lintDriver_3562_);
lean_inc(v_testDriverArgs_3561_);
lean_inc(v_testDriver_3560_);
lean_inc(v_buildArchive_3558_);
lean_inc(v_releaseRepo_3557_);
lean_inc(v_irDir_3556_);
lean_inc(v_binDir_3555_);
lean_inc(v_nativeLibDir_3554_);
lean_inc(v_leanLibDir_3553_);
lean_inc(v_buildDir_3552_);
lean_inc(v_srcDir_3551_);
lean_inc(v_moreGlobalServerArgs_3550_);
lean_inc(v_extraDepTargets_3548_);
lean_inc(v_toLeanConfig_3546_);
lean_inc(v_toWorkspaceConfig_3545_);
lean_dec(v_cfg_3544_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3589_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3583_ = lean_box(v_allowImportAll_3576_);
v___x_3584_ = lean_apply_1(v_f_3543_, v___x_3583_);
if (v_isShared_3582_ == 0)
{
v___x_3586_ = v___x_3581_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_toWorkspaceConfig_3545_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_toLeanConfig_3546_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_extraDepTargets_3548_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_moreGlobalServerArgs_3550_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_srcDir_3551_);
lean_ctor_set(v_reuseFailAlloc_3588_, 5, v_buildDir_3552_);
lean_ctor_set(v_reuseFailAlloc_3588_, 6, v_leanLibDir_3553_);
lean_ctor_set(v_reuseFailAlloc_3588_, 7, v_nativeLibDir_3554_);
lean_ctor_set(v_reuseFailAlloc_3588_, 8, v_binDir_3555_);
lean_ctor_set(v_reuseFailAlloc_3588_, 9, v_irDir_3556_);
lean_ctor_set(v_reuseFailAlloc_3588_, 10, v_releaseRepo_3557_);
lean_ctor_set(v_reuseFailAlloc_3588_, 11, v_buildArchive_3558_);
lean_ctor_set(v_reuseFailAlloc_3588_, 12, v_testDriver_3560_);
lean_ctor_set(v_reuseFailAlloc_3588_, 13, v_testDriverArgs_3561_);
lean_ctor_set(v_reuseFailAlloc_3588_, 14, v_lintDriver_3562_);
lean_ctor_set(v_reuseFailAlloc_3588_, 15, v_lintDriverArgs_3563_);
lean_ctor_set(v_reuseFailAlloc_3588_, 16, v_version_3564_);
lean_ctor_set(v_reuseFailAlloc_3588_, 17, v_versionTags_3565_);
lean_ctor_set(v_reuseFailAlloc_3588_, 18, v_description_3566_);
lean_ctor_set(v_reuseFailAlloc_3588_, 19, v_keywords_3567_);
lean_ctor_set(v_reuseFailAlloc_3588_, 20, v_homepage_3568_);
lean_ctor_set(v_reuseFailAlloc_3588_, 21, v_license_3569_);
lean_ctor_set(v_reuseFailAlloc_3588_, 22, v_licenseFiles_3570_);
lean_ctor_set(v_reuseFailAlloc_3588_, 23, v_readmeFile_3571_);
lean_ctor_set(v_reuseFailAlloc_3588_, 24, v_enableArtifactCache_x3f_3573_);
lean_ctor_set(v_reuseFailAlloc_3588_, 25, v_restoreAllArtifacts_x3f_3574_);
lean_ctor_set(v_reuseFailAlloc_3588_, 26, v_builtinLint_x3f_3577_);
lean_ctor_set(v_reuseFailAlloc_3588_, 27, v_checks_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3588_, sizeof(void*)*28, v_bootstrap_3547_);
lean_ctor_set_uint8(v_reuseFailAlloc_3588_, sizeof(void*)*28 + 1, v_precompileModules_3549_);
lean_ctor_set_uint8(v_reuseFailAlloc_3588_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3588_, sizeof(void*)*28 + 3, v_reservoir_3572_);
lean_ctor_set_uint8(v_reuseFailAlloc_3588_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3575_);
v___x_3586_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
uint8_t v___x_3587_; 
v___x_3587_ = lean_unbox(v___x_3584_);
lean_ctor_set_uint8(v___x_3586_, sizeof(void*)*28 + 5, v___x_3587_);
lean_ctor_set_uint8(v___x_3586_, sizeof(void*)*28 + 6, v_fixedToolchain_3579_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_3598_, lean_object* v_n_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___closed__3));
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_3601_, lean_object* v_n_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3601_, v_n_3602_);
lean_dec(v_n_3602_);
lean_dec(v_p_3601_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_3604_, lean_object* v_n_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_3604_, v_n_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_3607_, lean_object* v_n_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_3607_, v_n_3608_);
lean_dec(v_n_3608_);
lean_dec(v_p_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0(lean_object* v_cfg_3610_){
_start:
{
lean_object* v_builtinLint_x3f_3611_; 
v_builtinLint_x3f_3611_ = lean_ctor_get(v_cfg_3610_, 26);
lean_inc(v_builtinLint_x3f_3611_);
return v_builtinLint_x3f_3611_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0___boxed(lean_object* v_cfg_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lake_PackageConfig_builtinLint_x3f___proj___lam__0(v_cfg_3612_);
lean_dec_ref(v_cfg_3612_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__1(lean_object* v_val_3614_, lean_object* v_cfg_3615_){
_start:
{
lean_object* v_toWorkspaceConfig_3616_; lean_object* v_toLeanConfig_3617_; uint8_t v_bootstrap_3618_; lean_object* v_extraDepTargets_3619_; uint8_t v_precompileModules_3620_; lean_object* v_moreGlobalServerArgs_3621_; lean_object* v_srcDir_3622_; lean_object* v_buildDir_3623_; lean_object* v_leanLibDir_3624_; lean_object* v_nativeLibDir_3625_; lean_object* v_binDir_3626_; lean_object* v_irDir_3627_; lean_object* v_releaseRepo_3628_; lean_object* v_buildArchive_3629_; uint8_t v_preferReleaseBuild_3630_; lean_object* v_testDriver_3631_; lean_object* v_testDriverArgs_3632_; lean_object* v_lintDriver_3633_; lean_object* v_lintDriverArgs_3634_; lean_object* v_version_3635_; lean_object* v_versionTags_3636_; lean_object* v_description_3637_; lean_object* v_keywords_3638_; lean_object* v_homepage_3639_; lean_object* v_license_3640_; lean_object* v_licenseFiles_3641_; lean_object* v_readmeFile_3642_; uint8_t v_reservoir_3643_; lean_object* v_enableArtifactCache_x3f_3644_; lean_object* v_restoreAllArtifacts_x3f_3645_; uint8_t v_libPrefixOnWindows_3646_; uint8_t v_allowImportAll_3647_; lean_object* v_checks_3648_; uint8_t v_fixedToolchain_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
v_toWorkspaceConfig_3616_ = lean_ctor_get(v_cfg_3615_, 0);
v_toLeanConfig_3617_ = lean_ctor_get(v_cfg_3615_, 1);
v_bootstrap_3618_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28);
v_extraDepTargets_3619_ = lean_ctor_get(v_cfg_3615_, 2);
v_precompileModules_3620_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3621_ = lean_ctor_get(v_cfg_3615_, 3);
v_srcDir_3622_ = lean_ctor_get(v_cfg_3615_, 4);
v_buildDir_3623_ = lean_ctor_get(v_cfg_3615_, 5);
v_leanLibDir_3624_ = lean_ctor_get(v_cfg_3615_, 6);
v_nativeLibDir_3625_ = lean_ctor_get(v_cfg_3615_, 7);
v_binDir_3626_ = lean_ctor_get(v_cfg_3615_, 8);
v_irDir_3627_ = lean_ctor_get(v_cfg_3615_, 9);
v_releaseRepo_3628_ = lean_ctor_get(v_cfg_3615_, 10);
v_buildArchive_3629_ = lean_ctor_get(v_cfg_3615_, 11);
v_preferReleaseBuild_3630_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28 + 2);
v_testDriver_3631_ = lean_ctor_get(v_cfg_3615_, 12);
v_testDriverArgs_3632_ = lean_ctor_get(v_cfg_3615_, 13);
v_lintDriver_3633_ = lean_ctor_get(v_cfg_3615_, 14);
v_lintDriverArgs_3634_ = lean_ctor_get(v_cfg_3615_, 15);
v_version_3635_ = lean_ctor_get(v_cfg_3615_, 16);
v_versionTags_3636_ = lean_ctor_get(v_cfg_3615_, 17);
v_description_3637_ = lean_ctor_get(v_cfg_3615_, 18);
v_keywords_3638_ = lean_ctor_get(v_cfg_3615_, 19);
v_homepage_3639_ = lean_ctor_get(v_cfg_3615_, 20);
v_license_3640_ = lean_ctor_get(v_cfg_3615_, 21);
v_licenseFiles_3641_ = lean_ctor_get(v_cfg_3615_, 22);
v_readmeFile_3642_ = lean_ctor_get(v_cfg_3615_, 23);
v_reservoir_3643_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3644_ = lean_ctor_get(v_cfg_3615_, 24);
v_restoreAllArtifacts_x3f_3645_ = lean_ctor_get(v_cfg_3615_, 25);
v_libPrefixOnWindows_3646_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28 + 4);
v_allowImportAll_3647_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28 + 5);
v_checks_3648_ = lean_ctor_get(v_cfg_3615_, 27);
v_fixedToolchain_3649_ = lean_ctor_get_uint8(v_cfg_3615_, sizeof(void*)*28 + 6);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_cfg_3615_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v_cfg_3615_, 26);
lean_dec(v_unused_3657_);
v___x_3651_ = v_cfg_3615_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_checks_3648_);
lean_inc(v_restoreAllArtifacts_x3f_3645_);
lean_inc(v_enableArtifactCache_x3f_3644_);
lean_inc(v_readmeFile_3642_);
lean_inc(v_licenseFiles_3641_);
lean_inc(v_license_3640_);
lean_inc(v_homepage_3639_);
lean_inc(v_keywords_3638_);
lean_inc(v_description_3637_);
lean_inc(v_versionTags_3636_);
lean_inc(v_version_3635_);
lean_inc(v_lintDriverArgs_3634_);
lean_inc(v_lintDriver_3633_);
lean_inc(v_testDriverArgs_3632_);
lean_inc(v_testDriver_3631_);
lean_inc(v_buildArchive_3629_);
lean_inc(v_releaseRepo_3628_);
lean_inc(v_irDir_3627_);
lean_inc(v_binDir_3626_);
lean_inc(v_nativeLibDir_3625_);
lean_inc(v_leanLibDir_3624_);
lean_inc(v_buildDir_3623_);
lean_inc(v_srcDir_3622_);
lean_inc(v_moreGlobalServerArgs_3621_);
lean_inc(v_extraDepTargets_3619_);
lean_inc(v_toLeanConfig_3617_);
lean_inc(v_toWorkspaceConfig_3616_);
lean_dec(v_cfg_3615_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 26, v_val_3614_);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_toWorkspaceConfig_3616_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_toLeanConfig_3617_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v_extraDepTargets_3619_);
lean_ctor_set(v_reuseFailAlloc_3655_, 3, v_moreGlobalServerArgs_3621_);
lean_ctor_set(v_reuseFailAlloc_3655_, 4, v_srcDir_3622_);
lean_ctor_set(v_reuseFailAlloc_3655_, 5, v_buildDir_3623_);
lean_ctor_set(v_reuseFailAlloc_3655_, 6, v_leanLibDir_3624_);
lean_ctor_set(v_reuseFailAlloc_3655_, 7, v_nativeLibDir_3625_);
lean_ctor_set(v_reuseFailAlloc_3655_, 8, v_binDir_3626_);
lean_ctor_set(v_reuseFailAlloc_3655_, 9, v_irDir_3627_);
lean_ctor_set(v_reuseFailAlloc_3655_, 10, v_releaseRepo_3628_);
lean_ctor_set(v_reuseFailAlloc_3655_, 11, v_buildArchive_3629_);
lean_ctor_set(v_reuseFailAlloc_3655_, 12, v_testDriver_3631_);
lean_ctor_set(v_reuseFailAlloc_3655_, 13, v_testDriverArgs_3632_);
lean_ctor_set(v_reuseFailAlloc_3655_, 14, v_lintDriver_3633_);
lean_ctor_set(v_reuseFailAlloc_3655_, 15, v_lintDriverArgs_3634_);
lean_ctor_set(v_reuseFailAlloc_3655_, 16, v_version_3635_);
lean_ctor_set(v_reuseFailAlloc_3655_, 17, v_versionTags_3636_);
lean_ctor_set(v_reuseFailAlloc_3655_, 18, v_description_3637_);
lean_ctor_set(v_reuseFailAlloc_3655_, 19, v_keywords_3638_);
lean_ctor_set(v_reuseFailAlloc_3655_, 20, v_homepage_3639_);
lean_ctor_set(v_reuseFailAlloc_3655_, 21, v_license_3640_);
lean_ctor_set(v_reuseFailAlloc_3655_, 22, v_licenseFiles_3641_);
lean_ctor_set(v_reuseFailAlloc_3655_, 23, v_readmeFile_3642_);
lean_ctor_set(v_reuseFailAlloc_3655_, 24, v_enableArtifactCache_x3f_3644_);
lean_ctor_set(v_reuseFailAlloc_3655_, 25, v_restoreAllArtifacts_x3f_3645_);
lean_ctor_set(v_reuseFailAlloc_3655_, 26, v_val_3614_);
lean_ctor_set(v_reuseFailAlloc_3655_, 27, v_checks_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28, v_bootstrap_3618_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28 + 1, v_precompileModules_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28 + 3, v_reservoir_3643_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28 + 5, v_allowImportAll_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, sizeof(void*)*28 + 6, v_fixedToolchain_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___lam__2(lean_object* v_f_3658_, lean_object* v_cfg_3659_){
_start:
{
lean_object* v_toWorkspaceConfig_3660_; lean_object* v_toLeanConfig_3661_; uint8_t v_bootstrap_3662_; lean_object* v_extraDepTargets_3663_; uint8_t v_precompileModules_3664_; lean_object* v_moreGlobalServerArgs_3665_; lean_object* v_srcDir_3666_; lean_object* v_buildDir_3667_; lean_object* v_leanLibDir_3668_; lean_object* v_nativeLibDir_3669_; lean_object* v_binDir_3670_; lean_object* v_irDir_3671_; lean_object* v_releaseRepo_3672_; lean_object* v_buildArchive_3673_; uint8_t v_preferReleaseBuild_3674_; lean_object* v_testDriver_3675_; lean_object* v_testDriverArgs_3676_; lean_object* v_lintDriver_3677_; lean_object* v_lintDriverArgs_3678_; lean_object* v_version_3679_; lean_object* v_versionTags_3680_; lean_object* v_description_3681_; lean_object* v_keywords_3682_; lean_object* v_homepage_3683_; lean_object* v_license_3684_; lean_object* v_licenseFiles_3685_; lean_object* v_readmeFile_3686_; uint8_t v_reservoir_3687_; lean_object* v_enableArtifactCache_x3f_3688_; lean_object* v_restoreAllArtifacts_x3f_3689_; uint8_t v_libPrefixOnWindows_3690_; uint8_t v_allowImportAll_3691_; lean_object* v_builtinLint_x3f_3692_; lean_object* v_checks_3693_; uint8_t v_fixedToolchain_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3702_; 
v_toWorkspaceConfig_3660_ = lean_ctor_get(v_cfg_3659_, 0);
v_toLeanConfig_3661_ = lean_ctor_get(v_cfg_3659_, 1);
v_bootstrap_3662_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28);
v_extraDepTargets_3663_ = lean_ctor_get(v_cfg_3659_, 2);
v_precompileModules_3664_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3665_ = lean_ctor_get(v_cfg_3659_, 3);
v_srcDir_3666_ = lean_ctor_get(v_cfg_3659_, 4);
v_buildDir_3667_ = lean_ctor_get(v_cfg_3659_, 5);
v_leanLibDir_3668_ = lean_ctor_get(v_cfg_3659_, 6);
v_nativeLibDir_3669_ = lean_ctor_get(v_cfg_3659_, 7);
v_binDir_3670_ = lean_ctor_get(v_cfg_3659_, 8);
v_irDir_3671_ = lean_ctor_get(v_cfg_3659_, 9);
v_releaseRepo_3672_ = lean_ctor_get(v_cfg_3659_, 10);
v_buildArchive_3673_ = lean_ctor_get(v_cfg_3659_, 11);
v_preferReleaseBuild_3674_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28 + 2);
v_testDriver_3675_ = lean_ctor_get(v_cfg_3659_, 12);
v_testDriverArgs_3676_ = lean_ctor_get(v_cfg_3659_, 13);
v_lintDriver_3677_ = lean_ctor_get(v_cfg_3659_, 14);
v_lintDriverArgs_3678_ = lean_ctor_get(v_cfg_3659_, 15);
v_version_3679_ = lean_ctor_get(v_cfg_3659_, 16);
v_versionTags_3680_ = lean_ctor_get(v_cfg_3659_, 17);
v_description_3681_ = lean_ctor_get(v_cfg_3659_, 18);
v_keywords_3682_ = lean_ctor_get(v_cfg_3659_, 19);
v_homepage_3683_ = lean_ctor_get(v_cfg_3659_, 20);
v_license_3684_ = lean_ctor_get(v_cfg_3659_, 21);
v_licenseFiles_3685_ = lean_ctor_get(v_cfg_3659_, 22);
v_readmeFile_3686_ = lean_ctor_get(v_cfg_3659_, 23);
v_reservoir_3687_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3688_ = lean_ctor_get(v_cfg_3659_, 24);
v_restoreAllArtifacts_x3f_3689_ = lean_ctor_get(v_cfg_3659_, 25);
v_libPrefixOnWindows_3690_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28 + 4);
v_allowImportAll_3691_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3692_ = lean_ctor_get(v_cfg_3659_, 26);
v_checks_3693_ = lean_ctor_get(v_cfg_3659_, 27);
v_fixedToolchain_3694_ = lean_ctor_get_uint8(v_cfg_3659_, sizeof(void*)*28 + 6);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_cfg_3659_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3696_ = v_cfg_3659_;
v_isShared_3697_ = v_isSharedCheck_3702_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_checks_3693_);
lean_inc(v_builtinLint_x3f_3692_);
lean_inc(v_restoreAllArtifacts_x3f_3689_);
lean_inc(v_enableArtifactCache_x3f_3688_);
lean_inc(v_readmeFile_3686_);
lean_inc(v_licenseFiles_3685_);
lean_inc(v_license_3684_);
lean_inc(v_homepage_3683_);
lean_inc(v_keywords_3682_);
lean_inc(v_description_3681_);
lean_inc(v_versionTags_3680_);
lean_inc(v_version_3679_);
lean_inc(v_lintDriverArgs_3678_);
lean_inc(v_lintDriver_3677_);
lean_inc(v_testDriverArgs_3676_);
lean_inc(v_testDriver_3675_);
lean_inc(v_buildArchive_3673_);
lean_inc(v_releaseRepo_3672_);
lean_inc(v_irDir_3671_);
lean_inc(v_binDir_3670_);
lean_inc(v_nativeLibDir_3669_);
lean_inc(v_leanLibDir_3668_);
lean_inc(v_buildDir_3667_);
lean_inc(v_srcDir_3666_);
lean_inc(v_moreGlobalServerArgs_3665_);
lean_inc(v_extraDepTargets_3663_);
lean_inc(v_toLeanConfig_3661_);
lean_inc(v_toWorkspaceConfig_3660_);
lean_dec(v_cfg_3659_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3702_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3698_ = lean_apply_1(v_f_3658_, v_builtinLint_x3f_3692_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 26, v___x_3698_);
v___x_3700_ = v___x_3696_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_toWorkspaceConfig_3660_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_toLeanConfig_3661_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v_extraDepTargets_3663_);
lean_ctor_set(v_reuseFailAlloc_3701_, 3, v_moreGlobalServerArgs_3665_);
lean_ctor_set(v_reuseFailAlloc_3701_, 4, v_srcDir_3666_);
lean_ctor_set(v_reuseFailAlloc_3701_, 5, v_buildDir_3667_);
lean_ctor_set(v_reuseFailAlloc_3701_, 6, v_leanLibDir_3668_);
lean_ctor_set(v_reuseFailAlloc_3701_, 7, v_nativeLibDir_3669_);
lean_ctor_set(v_reuseFailAlloc_3701_, 8, v_binDir_3670_);
lean_ctor_set(v_reuseFailAlloc_3701_, 9, v_irDir_3671_);
lean_ctor_set(v_reuseFailAlloc_3701_, 10, v_releaseRepo_3672_);
lean_ctor_set(v_reuseFailAlloc_3701_, 11, v_buildArchive_3673_);
lean_ctor_set(v_reuseFailAlloc_3701_, 12, v_testDriver_3675_);
lean_ctor_set(v_reuseFailAlloc_3701_, 13, v_testDriverArgs_3676_);
lean_ctor_set(v_reuseFailAlloc_3701_, 14, v_lintDriver_3677_);
lean_ctor_set(v_reuseFailAlloc_3701_, 15, v_lintDriverArgs_3678_);
lean_ctor_set(v_reuseFailAlloc_3701_, 16, v_version_3679_);
lean_ctor_set(v_reuseFailAlloc_3701_, 17, v_versionTags_3680_);
lean_ctor_set(v_reuseFailAlloc_3701_, 18, v_description_3681_);
lean_ctor_set(v_reuseFailAlloc_3701_, 19, v_keywords_3682_);
lean_ctor_set(v_reuseFailAlloc_3701_, 20, v_homepage_3683_);
lean_ctor_set(v_reuseFailAlloc_3701_, 21, v_license_3684_);
lean_ctor_set(v_reuseFailAlloc_3701_, 22, v_licenseFiles_3685_);
lean_ctor_set(v_reuseFailAlloc_3701_, 23, v_readmeFile_3686_);
lean_ctor_set(v_reuseFailAlloc_3701_, 24, v_enableArtifactCache_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3701_, 25, v_restoreAllArtifacts_x3f_3689_);
lean_ctor_set(v_reuseFailAlloc_3701_, 26, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3701_, 27, v_checks_3693_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28, v_bootstrap_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28 + 1, v_precompileModules_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28 + 3, v_reservoir_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28 + 5, v_allowImportAll_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*28 + 6, v_fixedToolchain_3694_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object* v_p_3711_, lean_object* v_n_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = ((lean_object*)(l_Lake_PackageConfig_builtinLint_x3f___proj___closed__3));
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object* v_p_3714_, lean_object* v_n_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_3714_, v_n_3715_);
lean_dec(v_n_3715_);
lean_dec(v_p_3714_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object* v_p_3717_, lean_object* v_n_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_3717_, v_n_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object* v_p_3720_, lean_object* v_n_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField(v_p_3720_, v_n_3721_);
lean_dec(v_n_3721_);
lean_dec(v_p_3720_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object* v_p_3723_, lean_object* v_n_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_3723_, v_n_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object* v_p_3726_, lean_object* v_n_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lake_PackageConfig_builtinLint_instConfigField(v_p_3726_, v_n_3727_);
lean_dec(v_n_3727_);
lean_dec(v_p_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__0(lean_object* v_cfg_3729_){
_start:
{
lean_object* v_checks_3730_; 
v_checks_3730_ = lean_ctor_get(v_cfg_3729_, 27);
lean_inc_ref(v_checks_3730_);
return v_checks_3730_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__0___boxed(lean_object* v_cfg_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lake_PackageConfig_checks___proj___lam__0(v_cfg_3731_);
lean_dec_ref(v_cfg_3731_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__1(lean_object* v_val_3733_, lean_object* v_cfg_3734_){
_start:
{
lean_object* v_toWorkspaceConfig_3735_; lean_object* v_toLeanConfig_3736_; uint8_t v_bootstrap_3737_; lean_object* v_extraDepTargets_3738_; uint8_t v_precompileModules_3739_; lean_object* v_moreGlobalServerArgs_3740_; lean_object* v_srcDir_3741_; lean_object* v_buildDir_3742_; lean_object* v_leanLibDir_3743_; lean_object* v_nativeLibDir_3744_; lean_object* v_binDir_3745_; lean_object* v_irDir_3746_; lean_object* v_releaseRepo_3747_; lean_object* v_buildArchive_3748_; uint8_t v_preferReleaseBuild_3749_; lean_object* v_testDriver_3750_; lean_object* v_testDriverArgs_3751_; lean_object* v_lintDriver_3752_; lean_object* v_lintDriverArgs_3753_; lean_object* v_version_3754_; lean_object* v_versionTags_3755_; lean_object* v_description_3756_; lean_object* v_keywords_3757_; lean_object* v_homepage_3758_; lean_object* v_license_3759_; lean_object* v_licenseFiles_3760_; lean_object* v_readmeFile_3761_; uint8_t v_reservoir_3762_; lean_object* v_enableArtifactCache_x3f_3763_; lean_object* v_restoreAllArtifacts_x3f_3764_; uint8_t v_libPrefixOnWindows_3765_; uint8_t v_allowImportAll_3766_; lean_object* v_builtinLint_x3f_3767_; uint8_t v_fixedToolchain_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
v_toWorkspaceConfig_3735_ = lean_ctor_get(v_cfg_3734_, 0);
v_toLeanConfig_3736_ = lean_ctor_get(v_cfg_3734_, 1);
v_bootstrap_3737_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28);
v_extraDepTargets_3738_ = lean_ctor_get(v_cfg_3734_, 2);
v_precompileModules_3739_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3740_ = lean_ctor_get(v_cfg_3734_, 3);
v_srcDir_3741_ = lean_ctor_get(v_cfg_3734_, 4);
v_buildDir_3742_ = lean_ctor_get(v_cfg_3734_, 5);
v_leanLibDir_3743_ = lean_ctor_get(v_cfg_3734_, 6);
v_nativeLibDir_3744_ = lean_ctor_get(v_cfg_3734_, 7);
v_binDir_3745_ = lean_ctor_get(v_cfg_3734_, 8);
v_irDir_3746_ = lean_ctor_get(v_cfg_3734_, 9);
v_releaseRepo_3747_ = lean_ctor_get(v_cfg_3734_, 10);
v_buildArchive_3748_ = lean_ctor_get(v_cfg_3734_, 11);
v_preferReleaseBuild_3749_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28 + 2);
v_testDriver_3750_ = lean_ctor_get(v_cfg_3734_, 12);
v_testDriverArgs_3751_ = lean_ctor_get(v_cfg_3734_, 13);
v_lintDriver_3752_ = lean_ctor_get(v_cfg_3734_, 14);
v_lintDriverArgs_3753_ = lean_ctor_get(v_cfg_3734_, 15);
v_version_3754_ = lean_ctor_get(v_cfg_3734_, 16);
v_versionTags_3755_ = lean_ctor_get(v_cfg_3734_, 17);
v_description_3756_ = lean_ctor_get(v_cfg_3734_, 18);
v_keywords_3757_ = lean_ctor_get(v_cfg_3734_, 19);
v_homepage_3758_ = lean_ctor_get(v_cfg_3734_, 20);
v_license_3759_ = lean_ctor_get(v_cfg_3734_, 21);
v_licenseFiles_3760_ = lean_ctor_get(v_cfg_3734_, 22);
v_readmeFile_3761_ = lean_ctor_get(v_cfg_3734_, 23);
v_reservoir_3762_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3763_ = lean_ctor_get(v_cfg_3734_, 24);
v_restoreAllArtifacts_x3f_3764_ = lean_ctor_get(v_cfg_3734_, 25);
v_libPrefixOnWindows_3765_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28 + 4);
v_allowImportAll_3766_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3767_ = lean_ctor_get(v_cfg_3734_, 26);
v_fixedToolchain_3768_ = lean_ctor_get_uint8(v_cfg_3734_, sizeof(void*)*28 + 6);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_cfg_3734_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v_cfg_3734_, 27);
lean_dec(v_unused_3776_);
v___x_3770_ = v_cfg_3734_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_builtinLint_x3f_3767_);
lean_inc(v_restoreAllArtifacts_x3f_3764_);
lean_inc(v_enableArtifactCache_x3f_3763_);
lean_inc(v_readmeFile_3761_);
lean_inc(v_licenseFiles_3760_);
lean_inc(v_license_3759_);
lean_inc(v_homepage_3758_);
lean_inc(v_keywords_3757_);
lean_inc(v_description_3756_);
lean_inc(v_versionTags_3755_);
lean_inc(v_version_3754_);
lean_inc(v_lintDriverArgs_3753_);
lean_inc(v_lintDriver_3752_);
lean_inc(v_testDriverArgs_3751_);
lean_inc(v_testDriver_3750_);
lean_inc(v_buildArchive_3748_);
lean_inc(v_releaseRepo_3747_);
lean_inc(v_irDir_3746_);
lean_inc(v_binDir_3745_);
lean_inc(v_nativeLibDir_3744_);
lean_inc(v_leanLibDir_3743_);
lean_inc(v_buildDir_3742_);
lean_inc(v_srcDir_3741_);
lean_inc(v_moreGlobalServerArgs_3740_);
lean_inc(v_extraDepTargets_3738_);
lean_inc(v_toLeanConfig_3736_);
lean_inc(v_toWorkspaceConfig_3735_);
lean_dec(v_cfg_3734_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 27, v_val_3733_);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_toWorkspaceConfig_3735_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_toLeanConfig_3736_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_extraDepTargets_3738_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_moreGlobalServerArgs_3740_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_srcDir_3741_);
lean_ctor_set(v_reuseFailAlloc_3774_, 5, v_buildDir_3742_);
lean_ctor_set(v_reuseFailAlloc_3774_, 6, v_leanLibDir_3743_);
lean_ctor_set(v_reuseFailAlloc_3774_, 7, v_nativeLibDir_3744_);
lean_ctor_set(v_reuseFailAlloc_3774_, 8, v_binDir_3745_);
lean_ctor_set(v_reuseFailAlloc_3774_, 9, v_irDir_3746_);
lean_ctor_set(v_reuseFailAlloc_3774_, 10, v_releaseRepo_3747_);
lean_ctor_set(v_reuseFailAlloc_3774_, 11, v_buildArchive_3748_);
lean_ctor_set(v_reuseFailAlloc_3774_, 12, v_testDriver_3750_);
lean_ctor_set(v_reuseFailAlloc_3774_, 13, v_testDriverArgs_3751_);
lean_ctor_set(v_reuseFailAlloc_3774_, 14, v_lintDriver_3752_);
lean_ctor_set(v_reuseFailAlloc_3774_, 15, v_lintDriverArgs_3753_);
lean_ctor_set(v_reuseFailAlloc_3774_, 16, v_version_3754_);
lean_ctor_set(v_reuseFailAlloc_3774_, 17, v_versionTags_3755_);
lean_ctor_set(v_reuseFailAlloc_3774_, 18, v_description_3756_);
lean_ctor_set(v_reuseFailAlloc_3774_, 19, v_keywords_3757_);
lean_ctor_set(v_reuseFailAlloc_3774_, 20, v_homepage_3758_);
lean_ctor_set(v_reuseFailAlloc_3774_, 21, v_license_3759_);
lean_ctor_set(v_reuseFailAlloc_3774_, 22, v_licenseFiles_3760_);
lean_ctor_set(v_reuseFailAlloc_3774_, 23, v_readmeFile_3761_);
lean_ctor_set(v_reuseFailAlloc_3774_, 24, v_enableArtifactCache_x3f_3763_);
lean_ctor_set(v_reuseFailAlloc_3774_, 25, v_restoreAllArtifacts_x3f_3764_);
lean_ctor_set(v_reuseFailAlloc_3774_, 26, v_builtinLint_x3f_3767_);
lean_ctor_set(v_reuseFailAlloc_3774_, 27, v_val_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28, v_bootstrap_3737_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28 + 1, v_precompileModules_3739_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3749_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28 + 3, v_reservoir_3762_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3765_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28 + 5, v_allowImportAll_3766_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, sizeof(void*)*28 + 6, v_fixedToolchain_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___lam__2(lean_object* v_f_3777_, lean_object* v_cfg_3778_){
_start:
{
lean_object* v_toWorkspaceConfig_3779_; lean_object* v_toLeanConfig_3780_; uint8_t v_bootstrap_3781_; lean_object* v_extraDepTargets_3782_; uint8_t v_precompileModules_3783_; lean_object* v_moreGlobalServerArgs_3784_; lean_object* v_srcDir_3785_; lean_object* v_buildDir_3786_; lean_object* v_leanLibDir_3787_; lean_object* v_nativeLibDir_3788_; lean_object* v_binDir_3789_; lean_object* v_irDir_3790_; lean_object* v_releaseRepo_3791_; lean_object* v_buildArchive_3792_; uint8_t v_preferReleaseBuild_3793_; lean_object* v_testDriver_3794_; lean_object* v_testDriverArgs_3795_; lean_object* v_lintDriver_3796_; lean_object* v_lintDriverArgs_3797_; lean_object* v_version_3798_; lean_object* v_versionTags_3799_; lean_object* v_description_3800_; lean_object* v_keywords_3801_; lean_object* v_homepage_3802_; lean_object* v_license_3803_; lean_object* v_licenseFiles_3804_; lean_object* v_readmeFile_3805_; uint8_t v_reservoir_3806_; lean_object* v_enableArtifactCache_x3f_3807_; lean_object* v_restoreAllArtifacts_x3f_3808_; uint8_t v_libPrefixOnWindows_3809_; uint8_t v_allowImportAll_3810_; lean_object* v_builtinLint_x3f_3811_; lean_object* v_checks_3812_; uint8_t v_fixedToolchain_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3821_; 
v_toWorkspaceConfig_3779_ = lean_ctor_get(v_cfg_3778_, 0);
v_toLeanConfig_3780_ = lean_ctor_get(v_cfg_3778_, 1);
v_bootstrap_3781_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28);
v_extraDepTargets_3782_ = lean_ctor_get(v_cfg_3778_, 2);
v_precompileModules_3783_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3784_ = lean_ctor_get(v_cfg_3778_, 3);
v_srcDir_3785_ = lean_ctor_get(v_cfg_3778_, 4);
v_buildDir_3786_ = lean_ctor_get(v_cfg_3778_, 5);
v_leanLibDir_3787_ = lean_ctor_get(v_cfg_3778_, 6);
v_nativeLibDir_3788_ = lean_ctor_get(v_cfg_3778_, 7);
v_binDir_3789_ = lean_ctor_get(v_cfg_3778_, 8);
v_irDir_3790_ = lean_ctor_get(v_cfg_3778_, 9);
v_releaseRepo_3791_ = lean_ctor_get(v_cfg_3778_, 10);
v_buildArchive_3792_ = lean_ctor_get(v_cfg_3778_, 11);
v_preferReleaseBuild_3793_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28 + 2);
v_testDriver_3794_ = lean_ctor_get(v_cfg_3778_, 12);
v_testDriverArgs_3795_ = lean_ctor_get(v_cfg_3778_, 13);
v_lintDriver_3796_ = lean_ctor_get(v_cfg_3778_, 14);
v_lintDriverArgs_3797_ = lean_ctor_get(v_cfg_3778_, 15);
v_version_3798_ = lean_ctor_get(v_cfg_3778_, 16);
v_versionTags_3799_ = lean_ctor_get(v_cfg_3778_, 17);
v_description_3800_ = lean_ctor_get(v_cfg_3778_, 18);
v_keywords_3801_ = lean_ctor_get(v_cfg_3778_, 19);
v_homepage_3802_ = lean_ctor_get(v_cfg_3778_, 20);
v_license_3803_ = lean_ctor_get(v_cfg_3778_, 21);
v_licenseFiles_3804_ = lean_ctor_get(v_cfg_3778_, 22);
v_readmeFile_3805_ = lean_ctor_get(v_cfg_3778_, 23);
v_reservoir_3806_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3807_ = lean_ctor_get(v_cfg_3778_, 24);
v_restoreAllArtifacts_x3f_3808_ = lean_ctor_get(v_cfg_3778_, 25);
v_libPrefixOnWindows_3809_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28 + 4);
v_allowImportAll_3810_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3811_ = lean_ctor_get(v_cfg_3778_, 26);
v_checks_3812_ = lean_ctor_get(v_cfg_3778_, 27);
v_fixedToolchain_3813_ = lean_ctor_get_uint8(v_cfg_3778_, sizeof(void*)*28 + 6);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_cfg_3778_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3815_ = v_cfg_3778_;
v_isShared_3816_ = v_isSharedCheck_3821_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_checks_3812_);
lean_inc(v_builtinLint_x3f_3811_);
lean_inc(v_restoreAllArtifacts_x3f_3808_);
lean_inc(v_enableArtifactCache_x3f_3807_);
lean_inc(v_readmeFile_3805_);
lean_inc(v_licenseFiles_3804_);
lean_inc(v_license_3803_);
lean_inc(v_homepage_3802_);
lean_inc(v_keywords_3801_);
lean_inc(v_description_3800_);
lean_inc(v_versionTags_3799_);
lean_inc(v_version_3798_);
lean_inc(v_lintDriverArgs_3797_);
lean_inc(v_lintDriver_3796_);
lean_inc(v_testDriverArgs_3795_);
lean_inc(v_testDriver_3794_);
lean_inc(v_buildArchive_3792_);
lean_inc(v_releaseRepo_3791_);
lean_inc(v_irDir_3790_);
lean_inc(v_binDir_3789_);
lean_inc(v_nativeLibDir_3788_);
lean_inc(v_leanLibDir_3787_);
lean_inc(v_buildDir_3786_);
lean_inc(v_srcDir_3785_);
lean_inc(v_moreGlobalServerArgs_3784_);
lean_inc(v_extraDepTargets_3782_);
lean_inc(v_toLeanConfig_3780_);
lean_inc(v_toWorkspaceConfig_3779_);
lean_dec(v_cfg_3778_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3821_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3817_ = lean_apply_1(v_f_3777_, v_checks_3812_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 27, v___x_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_toWorkspaceConfig_3779_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_toLeanConfig_3780_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_extraDepTargets_3782_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_moreGlobalServerArgs_3784_);
lean_ctor_set(v_reuseFailAlloc_3820_, 4, v_srcDir_3785_);
lean_ctor_set(v_reuseFailAlloc_3820_, 5, v_buildDir_3786_);
lean_ctor_set(v_reuseFailAlloc_3820_, 6, v_leanLibDir_3787_);
lean_ctor_set(v_reuseFailAlloc_3820_, 7, v_nativeLibDir_3788_);
lean_ctor_set(v_reuseFailAlloc_3820_, 8, v_binDir_3789_);
lean_ctor_set(v_reuseFailAlloc_3820_, 9, v_irDir_3790_);
lean_ctor_set(v_reuseFailAlloc_3820_, 10, v_releaseRepo_3791_);
lean_ctor_set(v_reuseFailAlloc_3820_, 11, v_buildArchive_3792_);
lean_ctor_set(v_reuseFailAlloc_3820_, 12, v_testDriver_3794_);
lean_ctor_set(v_reuseFailAlloc_3820_, 13, v_testDriverArgs_3795_);
lean_ctor_set(v_reuseFailAlloc_3820_, 14, v_lintDriver_3796_);
lean_ctor_set(v_reuseFailAlloc_3820_, 15, v_lintDriverArgs_3797_);
lean_ctor_set(v_reuseFailAlloc_3820_, 16, v_version_3798_);
lean_ctor_set(v_reuseFailAlloc_3820_, 17, v_versionTags_3799_);
lean_ctor_set(v_reuseFailAlloc_3820_, 18, v_description_3800_);
lean_ctor_set(v_reuseFailAlloc_3820_, 19, v_keywords_3801_);
lean_ctor_set(v_reuseFailAlloc_3820_, 20, v_homepage_3802_);
lean_ctor_set(v_reuseFailAlloc_3820_, 21, v_license_3803_);
lean_ctor_set(v_reuseFailAlloc_3820_, 22, v_licenseFiles_3804_);
lean_ctor_set(v_reuseFailAlloc_3820_, 23, v_readmeFile_3805_);
lean_ctor_set(v_reuseFailAlloc_3820_, 24, v_enableArtifactCache_x3f_3807_);
lean_ctor_set(v_reuseFailAlloc_3820_, 25, v_restoreAllArtifacts_x3f_3808_);
lean_ctor_set(v_reuseFailAlloc_3820_, 26, v_builtinLint_x3f_3811_);
lean_ctor_set(v_reuseFailAlloc_3820_, 27, v___x_3817_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28, v_bootstrap_3781_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28 + 1, v_precompileModules_3783_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3793_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28 + 3, v_reservoir_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28 + 5, v_allowImportAll_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*28 + 6, v_fixedToolchain_3813_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj(lean_object* v_p_3830_, lean_object* v_n_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = ((lean_object*)(l_Lake_PackageConfig_checks___proj___closed__3));
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___boxed(lean_object* v_p_3833_, lean_object* v_n_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lake_PackageConfig_checks___proj(v_p_3833_, v_n_3834_);
lean_dec(v_n_3834_);
lean_dec(v_p_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField(lean_object* v_p_3836_, lean_object* v_n_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lake_PackageConfig_checks___proj(v_p_3836_, v_n_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___boxed(lean_object* v_p_3839_, lean_object* v_n_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lake_PackageConfig_checks_instConfigField(v_p_3839_, v_n_3840_);
lean_dec(v_n_3840_);
lean_dec(v_p_3839_);
return v_res_3841_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___lam__0(lean_object* v_cfg_3842_){
_start:
{
uint8_t v_fixedToolchain_3843_; 
v_fixedToolchain_3843_ = lean_ctor_get_uint8(v_cfg_3842_, sizeof(void*)*28 + 6);
return v_fixedToolchain_3843_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__0___boxed(lean_object* v_cfg_3844_){
_start:
{
uint8_t v_res_3845_; lean_object* v_r_3846_; 
v_res_3845_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__0(v_cfg_3844_);
lean_dec_ref(v_cfg_3844_);
v_r_3846_ = lean_box(v_res_3845_);
return v_r_3846_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1(uint8_t v_val_3847_, lean_object* v_cfg_3848_){
_start:
{
lean_object* v_toWorkspaceConfig_3849_; lean_object* v_toLeanConfig_3850_; uint8_t v_bootstrap_3851_; lean_object* v_extraDepTargets_3852_; uint8_t v_precompileModules_3853_; lean_object* v_moreGlobalServerArgs_3854_; lean_object* v_srcDir_3855_; lean_object* v_buildDir_3856_; lean_object* v_leanLibDir_3857_; lean_object* v_nativeLibDir_3858_; lean_object* v_binDir_3859_; lean_object* v_irDir_3860_; lean_object* v_releaseRepo_3861_; lean_object* v_buildArchive_3862_; uint8_t v_preferReleaseBuild_3863_; lean_object* v_testDriver_3864_; lean_object* v_testDriverArgs_3865_; lean_object* v_lintDriver_3866_; lean_object* v_lintDriverArgs_3867_; lean_object* v_version_3868_; lean_object* v_versionTags_3869_; lean_object* v_description_3870_; lean_object* v_keywords_3871_; lean_object* v_homepage_3872_; lean_object* v_license_3873_; lean_object* v_licenseFiles_3874_; lean_object* v_readmeFile_3875_; uint8_t v_reservoir_3876_; lean_object* v_enableArtifactCache_x3f_3877_; lean_object* v_restoreAllArtifacts_x3f_3878_; uint8_t v_libPrefixOnWindows_3879_; uint8_t v_allowImportAll_3880_; lean_object* v_builtinLint_x3f_3881_; lean_object* v_checks_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_toWorkspaceConfig_3849_ = lean_ctor_get(v_cfg_3848_, 0);
v_toLeanConfig_3850_ = lean_ctor_get(v_cfg_3848_, 1);
v_bootstrap_3851_ = lean_ctor_get_uint8(v_cfg_3848_, sizeof(void*)*28);
v_extraDepTargets_3852_ = lean_ctor_get(v_cfg_3848_, 2);
v_precompileModules_3853_ = lean_ctor_get_uint8(v_cfg_3848_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3854_ = lean_ctor_get(v_cfg_3848_, 3);
v_srcDir_3855_ = lean_ctor_get(v_cfg_3848_, 4);
v_buildDir_3856_ = lean_ctor_get(v_cfg_3848_, 5);
v_leanLibDir_3857_ = lean_ctor_get(v_cfg_3848_, 6);
v_nativeLibDir_3858_ = lean_ctor_get(v_cfg_3848_, 7);
v_binDir_3859_ = lean_ctor_get(v_cfg_3848_, 8);
v_irDir_3860_ = lean_ctor_get(v_cfg_3848_, 9);
v_releaseRepo_3861_ = lean_ctor_get(v_cfg_3848_, 10);
v_buildArchive_3862_ = lean_ctor_get(v_cfg_3848_, 11);
v_preferReleaseBuild_3863_ = lean_ctor_get_uint8(v_cfg_3848_, sizeof(void*)*28 + 2);
v_testDriver_3864_ = lean_ctor_get(v_cfg_3848_, 12);
v_testDriverArgs_3865_ = lean_ctor_get(v_cfg_3848_, 13);
v_lintDriver_3866_ = lean_ctor_get(v_cfg_3848_, 14);
v_lintDriverArgs_3867_ = lean_ctor_get(v_cfg_3848_, 15);
v_version_3868_ = lean_ctor_get(v_cfg_3848_, 16);
v_versionTags_3869_ = lean_ctor_get(v_cfg_3848_, 17);
v_description_3870_ = lean_ctor_get(v_cfg_3848_, 18);
v_keywords_3871_ = lean_ctor_get(v_cfg_3848_, 19);
v_homepage_3872_ = lean_ctor_get(v_cfg_3848_, 20);
v_license_3873_ = lean_ctor_get(v_cfg_3848_, 21);
v_licenseFiles_3874_ = lean_ctor_get(v_cfg_3848_, 22);
v_readmeFile_3875_ = lean_ctor_get(v_cfg_3848_, 23);
v_reservoir_3876_ = lean_ctor_get_uint8(v_cfg_3848_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3877_ = lean_ctor_get(v_cfg_3848_, 24);
v_restoreAllArtifacts_x3f_3878_ = lean_ctor_get(v_cfg_3848_, 25);
v_libPrefixOnWindows_3879_ = lean_ctor_get_uint8(v_cfg_3848_, sizeof(void*)*28 + 4);
v_allowImportAll_3880_ = lean_ctor_get_uint8(v_cfg_3848_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3881_ = lean_ctor_get(v_cfg_3848_, 26);
v_checks_3882_ = lean_ctor_get(v_cfg_3848_, 27);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_cfg_3848_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v_cfg_3848_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_checks_3882_);
lean_inc(v_builtinLint_x3f_3881_);
lean_inc(v_restoreAllArtifacts_x3f_3878_);
lean_inc(v_enableArtifactCache_x3f_3877_);
lean_inc(v_readmeFile_3875_);
lean_inc(v_licenseFiles_3874_);
lean_inc(v_license_3873_);
lean_inc(v_homepage_3872_);
lean_inc(v_keywords_3871_);
lean_inc(v_description_3870_);
lean_inc(v_versionTags_3869_);
lean_inc(v_version_3868_);
lean_inc(v_lintDriverArgs_3867_);
lean_inc(v_lintDriver_3866_);
lean_inc(v_testDriverArgs_3865_);
lean_inc(v_testDriver_3864_);
lean_inc(v_buildArchive_3862_);
lean_inc(v_releaseRepo_3861_);
lean_inc(v_irDir_3860_);
lean_inc(v_binDir_3859_);
lean_inc(v_nativeLibDir_3858_);
lean_inc(v_leanLibDir_3857_);
lean_inc(v_buildDir_3856_);
lean_inc(v_srcDir_3855_);
lean_inc(v_moreGlobalServerArgs_3854_);
lean_inc(v_extraDepTargets_3852_);
lean_inc(v_toLeanConfig_3850_);
lean_inc(v_toWorkspaceConfig_3849_);
lean_dec(v_cfg_3848_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_toWorkspaceConfig_3849_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_toLeanConfig_3850_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v_extraDepTargets_3852_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v_moreGlobalServerArgs_3854_);
lean_ctor_set(v_reuseFailAlloc_3888_, 4, v_srcDir_3855_);
lean_ctor_set(v_reuseFailAlloc_3888_, 5, v_buildDir_3856_);
lean_ctor_set(v_reuseFailAlloc_3888_, 6, v_leanLibDir_3857_);
lean_ctor_set(v_reuseFailAlloc_3888_, 7, v_nativeLibDir_3858_);
lean_ctor_set(v_reuseFailAlloc_3888_, 8, v_binDir_3859_);
lean_ctor_set(v_reuseFailAlloc_3888_, 9, v_irDir_3860_);
lean_ctor_set(v_reuseFailAlloc_3888_, 10, v_releaseRepo_3861_);
lean_ctor_set(v_reuseFailAlloc_3888_, 11, v_buildArchive_3862_);
lean_ctor_set(v_reuseFailAlloc_3888_, 12, v_testDriver_3864_);
lean_ctor_set(v_reuseFailAlloc_3888_, 13, v_testDriverArgs_3865_);
lean_ctor_set(v_reuseFailAlloc_3888_, 14, v_lintDriver_3866_);
lean_ctor_set(v_reuseFailAlloc_3888_, 15, v_lintDriverArgs_3867_);
lean_ctor_set(v_reuseFailAlloc_3888_, 16, v_version_3868_);
lean_ctor_set(v_reuseFailAlloc_3888_, 17, v_versionTags_3869_);
lean_ctor_set(v_reuseFailAlloc_3888_, 18, v_description_3870_);
lean_ctor_set(v_reuseFailAlloc_3888_, 19, v_keywords_3871_);
lean_ctor_set(v_reuseFailAlloc_3888_, 20, v_homepage_3872_);
lean_ctor_set(v_reuseFailAlloc_3888_, 21, v_license_3873_);
lean_ctor_set(v_reuseFailAlloc_3888_, 22, v_licenseFiles_3874_);
lean_ctor_set(v_reuseFailAlloc_3888_, 23, v_readmeFile_3875_);
lean_ctor_set(v_reuseFailAlloc_3888_, 24, v_enableArtifactCache_x3f_3877_);
lean_ctor_set(v_reuseFailAlloc_3888_, 25, v_restoreAllArtifacts_x3f_3878_);
lean_ctor_set(v_reuseFailAlloc_3888_, 26, v_builtinLint_x3f_3881_);
lean_ctor_set(v_reuseFailAlloc_3888_, 27, v_checks_3882_);
lean_ctor_set_uint8(v_reuseFailAlloc_3888_, sizeof(void*)*28, v_bootstrap_3851_);
lean_ctor_set_uint8(v_reuseFailAlloc_3888_, sizeof(void*)*28 + 1, v_precompileModules_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3888_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3863_);
lean_ctor_set_uint8(v_reuseFailAlloc_3888_, sizeof(void*)*28 + 3, v_reservoir_3876_);
lean_ctor_set_uint8(v_reuseFailAlloc_3888_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3879_);
lean_ctor_set_uint8(v_reuseFailAlloc_3888_, sizeof(void*)*28 + 5, v_allowImportAll_3880_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_ctor_set_uint8(v___x_3887_, sizeof(void*)*28 + 6, v_val_3847_);
return v___x_3887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__1___boxed(lean_object* v_val_3890_, lean_object* v_cfg_3891_){
_start:
{
uint8_t v_val_140__boxed_3892_; lean_object* v_res_3893_; 
v_val_140__boxed_3892_ = lean_unbox(v_val_3890_);
v_res_3893_ = l_Lake_PackageConfig_fixedToolchain___proj___lam__1(v_val_140__boxed_3892_, v_cfg_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___lam__2(lean_object* v_f_3894_, lean_object* v_cfg_3895_){
_start:
{
lean_object* v_toWorkspaceConfig_3896_; lean_object* v_toLeanConfig_3897_; uint8_t v_bootstrap_3898_; lean_object* v_extraDepTargets_3899_; uint8_t v_precompileModules_3900_; lean_object* v_moreGlobalServerArgs_3901_; lean_object* v_srcDir_3902_; lean_object* v_buildDir_3903_; lean_object* v_leanLibDir_3904_; lean_object* v_nativeLibDir_3905_; lean_object* v_binDir_3906_; lean_object* v_irDir_3907_; lean_object* v_releaseRepo_3908_; lean_object* v_buildArchive_3909_; uint8_t v_preferReleaseBuild_3910_; lean_object* v_testDriver_3911_; lean_object* v_testDriverArgs_3912_; lean_object* v_lintDriver_3913_; lean_object* v_lintDriverArgs_3914_; lean_object* v_version_3915_; lean_object* v_versionTags_3916_; lean_object* v_description_3917_; lean_object* v_keywords_3918_; lean_object* v_homepage_3919_; lean_object* v_license_3920_; lean_object* v_licenseFiles_3921_; lean_object* v_readmeFile_3922_; uint8_t v_reservoir_3923_; lean_object* v_enableArtifactCache_x3f_3924_; lean_object* v_restoreAllArtifacts_x3f_3925_; uint8_t v_libPrefixOnWindows_3926_; uint8_t v_allowImportAll_3927_; lean_object* v_builtinLint_x3f_3928_; lean_object* v_checks_3929_; uint8_t v_fixedToolchain_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3940_; 
v_toWorkspaceConfig_3896_ = lean_ctor_get(v_cfg_3895_, 0);
v_toLeanConfig_3897_ = lean_ctor_get(v_cfg_3895_, 1);
v_bootstrap_3898_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28);
v_extraDepTargets_3899_ = lean_ctor_get(v_cfg_3895_, 2);
v_precompileModules_3900_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3901_ = lean_ctor_get(v_cfg_3895_, 3);
v_srcDir_3902_ = lean_ctor_get(v_cfg_3895_, 4);
v_buildDir_3903_ = lean_ctor_get(v_cfg_3895_, 5);
v_leanLibDir_3904_ = lean_ctor_get(v_cfg_3895_, 6);
v_nativeLibDir_3905_ = lean_ctor_get(v_cfg_3895_, 7);
v_binDir_3906_ = lean_ctor_get(v_cfg_3895_, 8);
v_irDir_3907_ = lean_ctor_get(v_cfg_3895_, 9);
v_releaseRepo_3908_ = lean_ctor_get(v_cfg_3895_, 10);
v_buildArchive_3909_ = lean_ctor_get(v_cfg_3895_, 11);
v_preferReleaseBuild_3910_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28 + 2);
v_testDriver_3911_ = lean_ctor_get(v_cfg_3895_, 12);
v_testDriverArgs_3912_ = lean_ctor_get(v_cfg_3895_, 13);
v_lintDriver_3913_ = lean_ctor_get(v_cfg_3895_, 14);
v_lintDriverArgs_3914_ = lean_ctor_get(v_cfg_3895_, 15);
v_version_3915_ = lean_ctor_get(v_cfg_3895_, 16);
v_versionTags_3916_ = lean_ctor_get(v_cfg_3895_, 17);
v_description_3917_ = lean_ctor_get(v_cfg_3895_, 18);
v_keywords_3918_ = lean_ctor_get(v_cfg_3895_, 19);
v_homepage_3919_ = lean_ctor_get(v_cfg_3895_, 20);
v_license_3920_ = lean_ctor_get(v_cfg_3895_, 21);
v_licenseFiles_3921_ = lean_ctor_get(v_cfg_3895_, 22);
v_readmeFile_3922_ = lean_ctor_get(v_cfg_3895_, 23);
v_reservoir_3923_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3924_ = lean_ctor_get(v_cfg_3895_, 24);
v_restoreAllArtifacts_x3f_3925_ = lean_ctor_get(v_cfg_3895_, 25);
v_libPrefixOnWindows_3926_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28 + 4);
v_allowImportAll_3927_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3928_ = lean_ctor_get(v_cfg_3895_, 26);
v_checks_3929_ = lean_ctor_get(v_cfg_3895_, 27);
v_fixedToolchain_3930_ = lean_ctor_get_uint8(v_cfg_3895_, sizeof(void*)*28 + 6);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_cfg_3895_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3932_ = v_cfg_3895_;
v_isShared_3933_ = v_isSharedCheck_3940_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_checks_3929_);
lean_inc(v_builtinLint_x3f_3928_);
lean_inc(v_restoreAllArtifacts_x3f_3925_);
lean_inc(v_enableArtifactCache_x3f_3924_);
lean_inc(v_readmeFile_3922_);
lean_inc(v_licenseFiles_3921_);
lean_inc(v_license_3920_);
lean_inc(v_homepage_3919_);
lean_inc(v_keywords_3918_);
lean_inc(v_description_3917_);
lean_inc(v_versionTags_3916_);
lean_inc(v_version_3915_);
lean_inc(v_lintDriverArgs_3914_);
lean_inc(v_lintDriver_3913_);
lean_inc(v_testDriverArgs_3912_);
lean_inc(v_testDriver_3911_);
lean_inc(v_buildArchive_3909_);
lean_inc(v_releaseRepo_3908_);
lean_inc(v_irDir_3907_);
lean_inc(v_binDir_3906_);
lean_inc(v_nativeLibDir_3905_);
lean_inc(v_leanLibDir_3904_);
lean_inc(v_buildDir_3903_);
lean_inc(v_srcDir_3902_);
lean_inc(v_moreGlobalServerArgs_3901_);
lean_inc(v_extraDepTargets_3899_);
lean_inc(v_toLeanConfig_3897_);
lean_inc(v_toWorkspaceConfig_3896_);
lean_dec(v_cfg_3895_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3940_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3934_ = lean_box(v_fixedToolchain_3930_);
v___x_3935_ = lean_apply_1(v_f_3894_, v___x_3934_);
if (v_isShared_3933_ == 0)
{
v___x_3937_ = v___x_3932_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_toWorkspaceConfig_3896_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_toLeanConfig_3897_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_extraDepTargets_3899_);
lean_ctor_set(v_reuseFailAlloc_3939_, 3, v_moreGlobalServerArgs_3901_);
lean_ctor_set(v_reuseFailAlloc_3939_, 4, v_srcDir_3902_);
lean_ctor_set(v_reuseFailAlloc_3939_, 5, v_buildDir_3903_);
lean_ctor_set(v_reuseFailAlloc_3939_, 6, v_leanLibDir_3904_);
lean_ctor_set(v_reuseFailAlloc_3939_, 7, v_nativeLibDir_3905_);
lean_ctor_set(v_reuseFailAlloc_3939_, 8, v_binDir_3906_);
lean_ctor_set(v_reuseFailAlloc_3939_, 9, v_irDir_3907_);
lean_ctor_set(v_reuseFailAlloc_3939_, 10, v_releaseRepo_3908_);
lean_ctor_set(v_reuseFailAlloc_3939_, 11, v_buildArchive_3909_);
lean_ctor_set(v_reuseFailAlloc_3939_, 12, v_testDriver_3911_);
lean_ctor_set(v_reuseFailAlloc_3939_, 13, v_testDriverArgs_3912_);
lean_ctor_set(v_reuseFailAlloc_3939_, 14, v_lintDriver_3913_);
lean_ctor_set(v_reuseFailAlloc_3939_, 15, v_lintDriverArgs_3914_);
lean_ctor_set(v_reuseFailAlloc_3939_, 16, v_version_3915_);
lean_ctor_set(v_reuseFailAlloc_3939_, 17, v_versionTags_3916_);
lean_ctor_set(v_reuseFailAlloc_3939_, 18, v_description_3917_);
lean_ctor_set(v_reuseFailAlloc_3939_, 19, v_keywords_3918_);
lean_ctor_set(v_reuseFailAlloc_3939_, 20, v_homepage_3919_);
lean_ctor_set(v_reuseFailAlloc_3939_, 21, v_license_3920_);
lean_ctor_set(v_reuseFailAlloc_3939_, 22, v_licenseFiles_3921_);
lean_ctor_set(v_reuseFailAlloc_3939_, 23, v_readmeFile_3922_);
lean_ctor_set(v_reuseFailAlloc_3939_, 24, v_enableArtifactCache_x3f_3924_);
lean_ctor_set(v_reuseFailAlloc_3939_, 25, v_restoreAllArtifacts_x3f_3925_);
lean_ctor_set(v_reuseFailAlloc_3939_, 26, v_builtinLint_x3f_3928_);
lean_ctor_set(v_reuseFailAlloc_3939_, 27, v_checks_3929_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*28, v_bootstrap_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*28 + 1, v_precompileModules_3900_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3910_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*28 + 3, v_reservoir_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3926_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*28 + 5, v_allowImportAll_3927_);
v___x_3937_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_unbox(v___x_3935_);
lean_ctor_set_uint8(v___x_3937_, sizeof(void*)*28 + 6, v___x_3938_);
return v___x_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_3949_, lean_object* v_n_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___closed__3));
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_3952_, lean_object* v_n_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3952_, v_n_3953_);
lean_dec(v_n_3953_);
lean_dec(v_p_3952_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_3955_, lean_object* v_n_3956_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_3955_, v_n_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_3958_, lean_object* v_n_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_3958_, v_n_3959_);
lean_dec(v_n_3959_);
lean_dec(v_p_3958_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(lean_object* v_cfg_3961_){
_start:
{
lean_object* v_toWorkspaceConfig_3962_; 
v_toWorkspaceConfig_3962_ = lean_ctor_get(v_cfg_3961_, 0);
lean_inc_ref(v_toWorkspaceConfig_3962_);
return v_toWorkspaceConfig_3962_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0___boxed(lean_object* v_cfg_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__0(v_cfg_3963_);
lean_dec_ref(v_cfg_3963_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__1(lean_object* v_val_3965_, lean_object* v_cfg_3966_){
_start:
{
lean_object* v_toLeanConfig_3967_; uint8_t v_bootstrap_3968_; lean_object* v_extraDepTargets_3969_; uint8_t v_precompileModules_3970_; lean_object* v_moreGlobalServerArgs_3971_; lean_object* v_srcDir_3972_; lean_object* v_buildDir_3973_; lean_object* v_leanLibDir_3974_; lean_object* v_nativeLibDir_3975_; lean_object* v_binDir_3976_; lean_object* v_irDir_3977_; lean_object* v_releaseRepo_3978_; lean_object* v_buildArchive_3979_; uint8_t v_preferReleaseBuild_3980_; lean_object* v_testDriver_3981_; lean_object* v_testDriverArgs_3982_; lean_object* v_lintDriver_3983_; lean_object* v_lintDriverArgs_3984_; lean_object* v_version_3985_; lean_object* v_versionTags_3986_; lean_object* v_description_3987_; lean_object* v_keywords_3988_; lean_object* v_homepage_3989_; lean_object* v_license_3990_; lean_object* v_licenseFiles_3991_; lean_object* v_readmeFile_3992_; uint8_t v_reservoir_3993_; lean_object* v_enableArtifactCache_x3f_3994_; lean_object* v_restoreAllArtifacts_x3f_3995_; uint8_t v_libPrefixOnWindows_3996_; uint8_t v_allowImportAll_3997_; lean_object* v_builtinLint_x3f_3998_; lean_object* v_checks_3999_; uint8_t v_fixedToolchain_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
v_toLeanConfig_3967_ = lean_ctor_get(v_cfg_3966_, 1);
v_bootstrap_3968_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28);
v_extraDepTargets_3969_ = lean_ctor_get(v_cfg_3966_, 2);
v_precompileModules_3970_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_3971_ = lean_ctor_get(v_cfg_3966_, 3);
v_srcDir_3972_ = lean_ctor_get(v_cfg_3966_, 4);
v_buildDir_3973_ = lean_ctor_get(v_cfg_3966_, 5);
v_leanLibDir_3974_ = lean_ctor_get(v_cfg_3966_, 6);
v_nativeLibDir_3975_ = lean_ctor_get(v_cfg_3966_, 7);
v_binDir_3976_ = lean_ctor_get(v_cfg_3966_, 8);
v_irDir_3977_ = lean_ctor_get(v_cfg_3966_, 9);
v_releaseRepo_3978_ = lean_ctor_get(v_cfg_3966_, 10);
v_buildArchive_3979_ = lean_ctor_get(v_cfg_3966_, 11);
v_preferReleaseBuild_3980_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28 + 2);
v_testDriver_3981_ = lean_ctor_get(v_cfg_3966_, 12);
v_testDriverArgs_3982_ = lean_ctor_get(v_cfg_3966_, 13);
v_lintDriver_3983_ = lean_ctor_get(v_cfg_3966_, 14);
v_lintDriverArgs_3984_ = lean_ctor_get(v_cfg_3966_, 15);
v_version_3985_ = lean_ctor_get(v_cfg_3966_, 16);
v_versionTags_3986_ = lean_ctor_get(v_cfg_3966_, 17);
v_description_3987_ = lean_ctor_get(v_cfg_3966_, 18);
v_keywords_3988_ = lean_ctor_get(v_cfg_3966_, 19);
v_homepage_3989_ = lean_ctor_get(v_cfg_3966_, 20);
v_license_3990_ = lean_ctor_get(v_cfg_3966_, 21);
v_licenseFiles_3991_ = lean_ctor_get(v_cfg_3966_, 22);
v_readmeFile_3992_ = lean_ctor_get(v_cfg_3966_, 23);
v_reservoir_3993_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_3994_ = lean_ctor_get(v_cfg_3966_, 24);
v_restoreAllArtifacts_x3f_3995_ = lean_ctor_get(v_cfg_3966_, 25);
v_libPrefixOnWindows_3996_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28 + 4);
v_allowImportAll_3997_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_3998_ = lean_ctor_get(v_cfg_3966_, 26);
v_checks_3999_ = lean_ctor_get(v_cfg_3966_, 27);
v_fixedToolchain_4000_ = lean_ctor_get_uint8(v_cfg_3966_, sizeof(void*)*28 + 6);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_cfg_3966_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; 
v_unused_4008_ = lean_ctor_get(v_cfg_3966_, 0);
lean_dec(v_unused_4008_);
v___x_4002_ = v_cfg_3966_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_checks_3999_);
lean_inc(v_builtinLint_x3f_3998_);
lean_inc(v_restoreAllArtifacts_x3f_3995_);
lean_inc(v_enableArtifactCache_x3f_3994_);
lean_inc(v_readmeFile_3992_);
lean_inc(v_licenseFiles_3991_);
lean_inc(v_license_3990_);
lean_inc(v_homepage_3989_);
lean_inc(v_keywords_3988_);
lean_inc(v_description_3987_);
lean_inc(v_versionTags_3986_);
lean_inc(v_version_3985_);
lean_inc(v_lintDriverArgs_3984_);
lean_inc(v_lintDriver_3983_);
lean_inc(v_testDriverArgs_3982_);
lean_inc(v_testDriver_3981_);
lean_inc(v_buildArchive_3979_);
lean_inc(v_releaseRepo_3978_);
lean_inc(v_irDir_3977_);
lean_inc(v_binDir_3976_);
lean_inc(v_nativeLibDir_3975_);
lean_inc(v_leanLibDir_3974_);
lean_inc(v_buildDir_3973_);
lean_inc(v_srcDir_3972_);
lean_inc(v_moreGlobalServerArgs_3971_);
lean_inc(v_extraDepTargets_3969_);
lean_inc(v_toLeanConfig_3967_);
lean_dec(v_cfg_3966_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v_val_3965_);
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_val_3965_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_toLeanConfig_3967_);
lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_extraDepTargets_3969_);
lean_ctor_set(v_reuseFailAlloc_4006_, 3, v_moreGlobalServerArgs_3971_);
lean_ctor_set(v_reuseFailAlloc_4006_, 4, v_srcDir_3972_);
lean_ctor_set(v_reuseFailAlloc_4006_, 5, v_buildDir_3973_);
lean_ctor_set(v_reuseFailAlloc_4006_, 6, v_leanLibDir_3974_);
lean_ctor_set(v_reuseFailAlloc_4006_, 7, v_nativeLibDir_3975_);
lean_ctor_set(v_reuseFailAlloc_4006_, 8, v_binDir_3976_);
lean_ctor_set(v_reuseFailAlloc_4006_, 9, v_irDir_3977_);
lean_ctor_set(v_reuseFailAlloc_4006_, 10, v_releaseRepo_3978_);
lean_ctor_set(v_reuseFailAlloc_4006_, 11, v_buildArchive_3979_);
lean_ctor_set(v_reuseFailAlloc_4006_, 12, v_testDriver_3981_);
lean_ctor_set(v_reuseFailAlloc_4006_, 13, v_testDriverArgs_3982_);
lean_ctor_set(v_reuseFailAlloc_4006_, 14, v_lintDriver_3983_);
lean_ctor_set(v_reuseFailAlloc_4006_, 15, v_lintDriverArgs_3984_);
lean_ctor_set(v_reuseFailAlloc_4006_, 16, v_version_3985_);
lean_ctor_set(v_reuseFailAlloc_4006_, 17, v_versionTags_3986_);
lean_ctor_set(v_reuseFailAlloc_4006_, 18, v_description_3987_);
lean_ctor_set(v_reuseFailAlloc_4006_, 19, v_keywords_3988_);
lean_ctor_set(v_reuseFailAlloc_4006_, 20, v_homepage_3989_);
lean_ctor_set(v_reuseFailAlloc_4006_, 21, v_license_3990_);
lean_ctor_set(v_reuseFailAlloc_4006_, 22, v_licenseFiles_3991_);
lean_ctor_set(v_reuseFailAlloc_4006_, 23, v_readmeFile_3992_);
lean_ctor_set(v_reuseFailAlloc_4006_, 24, v_enableArtifactCache_x3f_3994_);
lean_ctor_set(v_reuseFailAlloc_4006_, 25, v_restoreAllArtifacts_x3f_3995_);
lean_ctor_set(v_reuseFailAlloc_4006_, 26, v_builtinLint_x3f_3998_);
lean_ctor_set(v_reuseFailAlloc_4006_, 27, v_checks_3999_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28, v_bootstrap_3968_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28 + 1, v_precompileModules_3970_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28 + 2, v_preferReleaseBuild_3980_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28 + 3, v_reservoir_3993_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_3996_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28 + 5, v_allowImportAll_3997_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*28 + 6, v_fixedToolchain_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__2(lean_object* v_f_4009_, lean_object* v_cfg_4010_){
_start:
{
lean_object* v_toWorkspaceConfig_4011_; lean_object* v_toLeanConfig_4012_; uint8_t v_bootstrap_4013_; lean_object* v_extraDepTargets_4014_; uint8_t v_precompileModules_4015_; lean_object* v_moreGlobalServerArgs_4016_; lean_object* v_srcDir_4017_; lean_object* v_buildDir_4018_; lean_object* v_leanLibDir_4019_; lean_object* v_nativeLibDir_4020_; lean_object* v_binDir_4021_; lean_object* v_irDir_4022_; lean_object* v_releaseRepo_4023_; lean_object* v_buildArchive_4024_; uint8_t v_preferReleaseBuild_4025_; lean_object* v_testDriver_4026_; lean_object* v_testDriverArgs_4027_; lean_object* v_lintDriver_4028_; lean_object* v_lintDriverArgs_4029_; lean_object* v_version_4030_; lean_object* v_versionTags_4031_; lean_object* v_description_4032_; lean_object* v_keywords_4033_; lean_object* v_homepage_4034_; lean_object* v_license_4035_; lean_object* v_licenseFiles_4036_; lean_object* v_readmeFile_4037_; uint8_t v_reservoir_4038_; lean_object* v_enableArtifactCache_x3f_4039_; lean_object* v_restoreAllArtifacts_x3f_4040_; uint8_t v_libPrefixOnWindows_4041_; uint8_t v_allowImportAll_4042_; lean_object* v_builtinLint_x3f_4043_; lean_object* v_checks_4044_; uint8_t v_fixedToolchain_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4053_; 
v_toWorkspaceConfig_4011_ = lean_ctor_get(v_cfg_4010_, 0);
v_toLeanConfig_4012_ = lean_ctor_get(v_cfg_4010_, 1);
v_bootstrap_4013_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28);
v_extraDepTargets_4014_ = lean_ctor_get(v_cfg_4010_, 2);
v_precompileModules_4015_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4016_ = lean_ctor_get(v_cfg_4010_, 3);
v_srcDir_4017_ = lean_ctor_get(v_cfg_4010_, 4);
v_buildDir_4018_ = lean_ctor_get(v_cfg_4010_, 5);
v_leanLibDir_4019_ = lean_ctor_get(v_cfg_4010_, 6);
v_nativeLibDir_4020_ = lean_ctor_get(v_cfg_4010_, 7);
v_binDir_4021_ = lean_ctor_get(v_cfg_4010_, 8);
v_irDir_4022_ = lean_ctor_get(v_cfg_4010_, 9);
v_releaseRepo_4023_ = lean_ctor_get(v_cfg_4010_, 10);
v_buildArchive_4024_ = lean_ctor_get(v_cfg_4010_, 11);
v_preferReleaseBuild_4025_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28 + 2);
v_testDriver_4026_ = lean_ctor_get(v_cfg_4010_, 12);
v_testDriverArgs_4027_ = lean_ctor_get(v_cfg_4010_, 13);
v_lintDriver_4028_ = lean_ctor_get(v_cfg_4010_, 14);
v_lintDriverArgs_4029_ = lean_ctor_get(v_cfg_4010_, 15);
v_version_4030_ = lean_ctor_get(v_cfg_4010_, 16);
v_versionTags_4031_ = lean_ctor_get(v_cfg_4010_, 17);
v_description_4032_ = lean_ctor_get(v_cfg_4010_, 18);
v_keywords_4033_ = lean_ctor_get(v_cfg_4010_, 19);
v_homepage_4034_ = lean_ctor_get(v_cfg_4010_, 20);
v_license_4035_ = lean_ctor_get(v_cfg_4010_, 21);
v_licenseFiles_4036_ = lean_ctor_get(v_cfg_4010_, 22);
v_readmeFile_4037_ = lean_ctor_get(v_cfg_4010_, 23);
v_reservoir_4038_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4039_ = lean_ctor_get(v_cfg_4010_, 24);
v_restoreAllArtifacts_x3f_4040_ = lean_ctor_get(v_cfg_4010_, 25);
v_libPrefixOnWindows_4041_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28 + 4);
v_allowImportAll_4042_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4043_ = lean_ctor_get(v_cfg_4010_, 26);
v_checks_4044_ = lean_ctor_get(v_cfg_4010_, 27);
v_fixedToolchain_4045_ = lean_ctor_get_uint8(v_cfg_4010_, sizeof(void*)*28 + 6);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_cfg_4010_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4047_ = v_cfg_4010_;
v_isShared_4048_ = v_isSharedCheck_4053_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_checks_4044_);
lean_inc(v_builtinLint_x3f_4043_);
lean_inc(v_restoreAllArtifacts_x3f_4040_);
lean_inc(v_enableArtifactCache_x3f_4039_);
lean_inc(v_readmeFile_4037_);
lean_inc(v_licenseFiles_4036_);
lean_inc(v_license_4035_);
lean_inc(v_homepage_4034_);
lean_inc(v_keywords_4033_);
lean_inc(v_description_4032_);
lean_inc(v_versionTags_4031_);
lean_inc(v_version_4030_);
lean_inc(v_lintDriverArgs_4029_);
lean_inc(v_lintDriver_4028_);
lean_inc(v_testDriverArgs_4027_);
lean_inc(v_testDriver_4026_);
lean_inc(v_buildArchive_4024_);
lean_inc(v_releaseRepo_4023_);
lean_inc(v_irDir_4022_);
lean_inc(v_binDir_4021_);
lean_inc(v_nativeLibDir_4020_);
lean_inc(v_leanLibDir_4019_);
lean_inc(v_buildDir_4018_);
lean_inc(v_srcDir_4017_);
lean_inc(v_moreGlobalServerArgs_4016_);
lean_inc(v_extraDepTargets_4014_);
lean_inc(v_toLeanConfig_4012_);
lean_inc(v_toWorkspaceConfig_4011_);
lean_dec(v_cfg_4010_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4053_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = lean_apply_1(v_f_4009_, v_toWorkspaceConfig_4011_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4049_);
v___x_4051_ = v___x_4047_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_toLeanConfig_4012_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_extraDepTargets_4014_);
lean_ctor_set(v_reuseFailAlloc_4052_, 3, v_moreGlobalServerArgs_4016_);
lean_ctor_set(v_reuseFailAlloc_4052_, 4, v_srcDir_4017_);
lean_ctor_set(v_reuseFailAlloc_4052_, 5, v_buildDir_4018_);
lean_ctor_set(v_reuseFailAlloc_4052_, 6, v_leanLibDir_4019_);
lean_ctor_set(v_reuseFailAlloc_4052_, 7, v_nativeLibDir_4020_);
lean_ctor_set(v_reuseFailAlloc_4052_, 8, v_binDir_4021_);
lean_ctor_set(v_reuseFailAlloc_4052_, 9, v_irDir_4022_);
lean_ctor_set(v_reuseFailAlloc_4052_, 10, v_releaseRepo_4023_);
lean_ctor_set(v_reuseFailAlloc_4052_, 11, v_buildArchive_4024_);
lean_ctor_set(v_reuseFailAlloc_4052_, 12, v_testDriver_4026_);
lean_ctor_set(v_reuseFailAlloc_4052_, 13, v_testDriverArgs_4027_);
lean_ctor_set(v_reuseFailAlloc_4052_, 14, v_lintDriver_4028_);
lean_ctor_set(v_reuseFailAlloc_4052_, 15, v_lintDriverArgs_4029_);
lean_ctor_set(v_reuseFailAlloc_4052_, 16, v_version_4030_);
lean_ctor_set(v_reuseFailAlloc_4052_, 17, v_versionTags_4031_);
lean_ctor_set(v_reuseFailAlloc_4052_, 18, v_description_4032_);
lean_ctor_set(v_reuseFailAlloc_4052_, 19, v_keywords_4033_);
lean_ctor_set(v_reuseFailAlloc_4052_, 20, v_homepage_4034_);
lean_ctor_set(v_reuseFailAlloc_4052_, 21, v_license_4035_);
lean_ctor_set(v_reuseFailAlloc_4052_, 22, v_licenseFiles_4036_);
lean_ctor_set(v_reuseFailAlloc_4052_, 23, v_readmeFile_4037_);
lean_ctor_set(v_reuseFailAlloc_4052_, 24, v_enableArtifactCache_x3f_4039_);
lean_ctor_set(v_reuseFailAlloc_4052_, 25, v_restoreAllArtifacts_x3f_4040_);
lean_ctor_set(v_reuseFailAlloc_4052_, 26, v_builtinLint_x3f_4043_);
lean_ctor_set(v_reuseFailAlloc_4052_, 27, v_checks_4044_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28, v_bootstrap_4013_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28 + 1, v_precompileModules_4015_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28 + 3, v_reservoir_4038_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4041_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28 + 5, v_allowImportAll_4042_);
lean_ctor_set_uint8(v_reuseFailAlloc_4052_, sizeof(void*)*28 + 6, v_fixedToolchain_4045_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(lean_object* v_x_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lake_defaultPackagesDir;
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3___boxed(lean_object* v_x_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___lam__3(v_x_4056_);
lean_dec_ref(v_x_4056_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_4067_, lean_object* v_n_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__4));
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_4070_, lean_object* v_n_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_4070_, v_n_4071_);
lean_dec(v_n_4071_);
lean_dec(v_p_4070_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_4073_, lean_object* v_n_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_4073_, v_n_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_4076_, lean_object* v_n_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_4076_, v_n_4077_);
lean_dec(v_n_4077_);
lean_dec(v_p_4076_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0(lean_object* v_cfg_4079_){
_start:
{
lean_object* v_toLeanConfig_4080_; 
v_toLeanConfig_4080_ = lean_ctor_get(v_cfg_4079_, 1);
lean_inc_ref(v_toLeanConfig_4080_);
return v_toLeanConfig_4080_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__0___boxed(lean_object* v_cfg_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__0(v_cfg_4081_);
lean_dec_ref(v_cfg_4081_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__1(lean_object* v_val_4083_, lean_object* v_cfg_4084_){
_start:
{
lean_object* v_toWorkspaceConfig_4085_; uint8_t v_bootstrap_4086_; lean_object* v_extraDepTargets_4087_; uint8_t v_precompileModules_4088_; lean_object* v_moreGlobalServerArgs_4089_; lean_object* v_srcDir_4090_; lean_object* v_buildDir_4091_; lean_object* v_leanLibDir_4092_; lean_object* v_nativeLibDir_4093_; lean_object* v_binDir_4094_; lean_object* v_irDir_4095_; lean_object* v_releaseRepo_4096_; lean_object* v_buildArchive_4097_; uint8_t v_preferReleaseBuild_4098_; lean_object* v_testDriver_4099_; lean_object* v_testDriverArgs_4100_; lean_object* v_lintDriver_4101_; lean_object* v_lintDriverArgs_4102_; lean_object* v_version_4103_; lean_object* v_versionTags_4104_; lean_object* v_description_4105_; lean_object* v_keywords_4106_; lean_object* v_homepage_4107_; lean_object* v_license_4108_; lean_object* v_licenseFiles_4109_; lean_object* v_readmeFile_4110_; uint8_t v_reservoir_4111_; lean_object* v_enableArtifactCache_x3f_4112_; lean_object* v_restoreAllArtifacts_x3f_4113_; uint8_t v_libPrefixOnWindows_4114_; uint8_t v_allowImportAll_4115_; lean_object* v_builtinLint_x3f_4116_; lean_object* v_checks_4117_; uint8_t v_fixedToolchain_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
v_toWorkspaceConfig_4085_ = lean_ctor_get(v_cfg_4084_, 0);
v_bootstrap_4086_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28);
v_extraDepTargets_4087_ = lean_ctor_get(v_cfg_4084_, 2);
v_precompileModules_4088_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4089_ = lean_ctor_get(v_cfg_4084_, 3);
v_srcDir_4090_ = lean_ctor_get(v_cfg_4084_, 4);
v_buildDir_4091_ = lean_ctor_get(v_cfg_4084_, 5);
v_leanLibDir_4092_ = lean_ctor_get(v_cfg_4084_, 6);
v_nativeLibDir_4093_ = lean_ctor_get(v_cfg_4084_, 7);
v_binDir_4094_ = lean_ctor_get(v_cfg_4084_, 8);
v_irDir_4095_ = lean_ctor_get(v_cfg_4084_, 9);
v_releaseRepo_4096_ = lean_ctor_get(v_cfg_4084_, 10);
v_buildArchive_4097_ = lean_ctor_get(v_cfg_4084_, 11);
v_preferReleaseBuild_4098_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28 + 2);
v_testDriver_4099_ = lean_ctor_get(v_cfg_4084_, 12);
v_testDriverArgs_4100_ = lean_ctor_get(v_cfg_4084_, 13);
v_lintDriver_4101_ = lean_ctor_get(v_cfg_4084_, 14);
v_lintDriverArgs_4102_ = lean_ctor_get(v_cfg_4084_, 15);
v_version_4103_ = lean_ctor_get(v_cfg_4084_, 16);
v_versionTags_4104_ = lean_ctor_get(v_cfg_4084_, 17);
v_description_4105_ = lean_ctor_get(v_cfg_4084_, 18);
v_keywords_4106_ = lean_ctor_get(v_cfg_4084_, 19);
v_homepage_4107_ = lean_ctor_get(v_cfg_4084_, 20);
v_license_4108_ = lean_ctor_get(v_cfg_4084_, 21);
v_licenseFiles_4109_ = lean_ctor_get(v_cfg_4084_, 22);
v_readmeFile_4110_ = lean_ctor_get(v_cfg_4084_, 23);
v_reservoir_4111_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4112_ = lean_ctor_get(v_cfg_4084_, 24);
v_restoreAllArtifacts_x3f_4113_ = lean_ctor_get(v_cfg_4084_, 25);
v_libPrefixOnWindows_4114_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28 + 4);
v_allowImportAll_4115_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4116_ = lean_ctor_get(v_cfg_4084_, 26);
v_checks_4117_ = lean_ctor_get(v_cfg_4084_, 27);
v_fixedToolchain_4118_ = lean_ctor_get_uint8(v_cfg_4084_, sizeof(void*)*28 + 6);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_cfg_4084_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; 
v_unused_4126_ = lean_ctor_get(v_cfg_4084_, 1);
lean_dec(v_unused_4126_);
v___x_4120_ = v_cfg_4084_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_checks_4117_);
lean_inc(v_builtinLint_x3f_4116_);
lean_inc(v_restoreAllArtifacts_x3f_4113_);
lean_inc(v_enableArtifactCache_x3f_4112_);
lean_inc(v_readmeFile_4110_);
lean_inc(v_licenseFiles_4109_);
lean_inc(v_license_4108_);
lean_inc(v_homepage_4107_);
lean_inc(v_keywords_4106_);
lean_inc(v_description_4105_);
lean_inc(v_versionTags_4104_);
lean_inc(v_version_4103_);
lean_inc(v_lintDriverArgs_4102_);
lean_inc(v_lintDriver_4101_);
lean_inc(v_testDriverArgs_4100_);
lean_inc(v_testDriver_4099_);
lean_inc(v_buildArchive_4097_);
lean_inc(v_releaseRepo_4096_);
lean_inc(v_irDir_4095_);
lean_inc(v_binDir_4094_);
lean_inc(v_nativeLibDir_4093_);
lean_inc(v_leanLibDir_4092_);
lean_inc(v_buildDir_4091_);
lean_inc(v_srcDir_4090_);
lean_inc(v_moreGlobalServerArgs_4089_);
lean_inc(v_extraDepTargets_4087_);
lean_inc(v_toWorkspaceConfig_4085_);
lean_dec(v_cfg_4084_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 1, v_val_4083_);
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_toWorkspaceConfig_4085_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v_val_4083_);
lean_ctor_set(v_reuseFailAlloc_4124_, 2, v_extraDepTargets_4087_);
lean_ctor_set(v_reuseFailAlloc_4124_, 3, v_moreGlobalServerArgs_4089_);
lean_ctor_set(v_reuseFailAlloc_4124_, 4, v_srcDir_4090_);
lean_ctor_set(v_reuseFailAlloc_4124_, 5, v_buildDir_4091_);
lean_ctor_set(v_reuseFailAlloc_4124_, 6, v_leanLibDir_4092_);
lean_ctor_set(v_reuseFailAlloc_4124_, 7, v_nativeLibDir_4093_);
lean_ctor_set(v_reuseFailAlloc_4124_, 8, v_binDir_4094_);
lean_ctor_set(v_reuseFailAlloc_4124_, 9, v_irDir_4095_);
lean_ctor_set(v_reuseFailAlloc_4124_, 10, v_releaseRepo_4096_);
lean_ctor_set(v_reuseFailAlloc_4124_, 11, v_buildArchive_4097_);
lean_ctor_set(v_reuseFailAlloc_4124_, 12, v_testDriver_4099_);
lean_ctor_set(v_reuseFailAlloc_4124_, 13, v_testDriverArgs_4100_);
lean_ctor_set(v_reuseFailAlloc_4124_, 14, v_lintDriver_4101_);
lean_ctor_set(v_reuseFailAlloc_4124_, 15, v_lintDriverArgs_4102_);
lean_ctor_set(v_reuseFailAlloc_4124_, 16, v_version_4103_);
lean_ctor_set(v_reuseFailAlloc_4124_, 17, v_versionTags_4104_);
lean_ctor_set(v_reuseFailAlloc_4124_, 18, v_description_4105_);
lean_ctor_set(v_reuseFailAlloc_4124_, 19, v_keywords_4106_);
lean_ctor_set(v_reuseFailAlloc_4124_, 20, v_homepage_4107_);
lean_ctor_set(v_reuseFailAlloc_4124_, 21, v_license_4108_);
lean_ctor_set(v_reuseFailAlloc_4124_, 22, v_licenseFiles_4109_);
lean_ctor_set(v_reuseFailAlloc_4124_, 23, v_readmeFile_4110_);
lean_ctor_set(v_reuseFailAlloc_4124_, 24, v_enableArtifactCache_x3f_4112_);
lean_ctor_set(v_reuseFailAlloc_4124_, 25, v_restoreAllArtifacts_x3f_4113_);
lean_ctor_set(v_reuseFailAlloc_4124_, 26, v_builtinLint_x3f_4116_);
lean_ctor_set(v_reuseFailAlloc_4124_, 27, v_checks_4117_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28, v_bootstrap_4086_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28 + 1, v_precompileModules_4088_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4098_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28 + 3, v_reservoir_4111_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4114_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28 + 5, v_allowImportAll_4115_);
lean_ctor_set_uint8(v_reuseFailAlloc_4124_, sizeof(void*)*28 + 6, v_fixedToolchain_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__2(lean_object* v_f_4127_, lean_object* v_cfg_4128_){
_start:
{
lean_object* v_toWorkspaceConfig_4129_; lean_object* v_toLeanConfig_4130_; uint8_t v_bootstrap_4131_; lean_object* v_extraDepTargets_4132_; uint8_t v_precompileModules_4133_; lean_object* v_moreGlobalServerArgs_4134_; lean_object* v_srcDir_4135_; lean_object* v_buildDir_4136_; lean_object* v_leanLibDir_4137_; lean_object* v_nativeLibDir_4138_; lean_object* v_binDir_4139_; lean_object* v_irDir_4140_; lean_object* v_releaseRepo_4141_; lean_object* v_buildArchive_4142_; uint8_t v_preferReleaseBuild_4143_; lean_object* v_testDriver_4144_; lean_object* v_testDriverArgs_4145_; lean_object* v_lintDriver_4146_; lean_object* v_lintDriverArgs_4147_; lean_object* v_version_4148_; lean_object* v_versionTags_4149_; lean_object* v_description_4150_; lean_object* v_keywords_4151_; lean_object* v_homepage_4152_; lean_object* v_license_4153_; lean_object* v_licenseFiles_4154_; lean_object* v_readmeFile_4155_; uint8_t v_reservoir_4156_; lean_object* v_enableArtifactCache_x3f_4157_; lean_object* v_restoreAllArtifacts_x3f_4158_; uint8_t v_libPrefixOnWindows_4159_; uint8_t v_allowImportAll_4160_; lean_object* v_builtinLint_x3f_4161_; lean_object* v_checks_4162_; uint8_t v_fixedToolchain_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4171_; 
v_toWorkspaceConfig_4129_ = lean_ctor_get(v_cfg_4128_, 0);
v_toLeanConfig_4130_ = lean_ctor_get(v_cfg_4128_, 1);
v_bootstrap_4131_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28);
v_extraDepTargets_4132_ = lean_ctor_get(v_cfg_4128_, 2);
v_precompileModules_4133_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28 + 1);
v_moreGlobalServerArgs_4134_ = lean_ctor_get(v_cfg_4128_, 3);
v_srcDir_4135_ = lean_ctor_get(v_cfg_4128_, 4);
v_buildDir_4136_ = lean_ctor_get(v_cfg_4128_, 5);
v_leanLibDir_4137_ = lean_ctor_get(v_cfg_4128_, 6);
v_nativeLibDir_4138_ = lean_ctor_get(v_cfg_4128_, 7);
v_binDir_4139_ = lean_ctor_get(v_cfg_4128_, 8);
v_irDir_4140_ = lean_ctor_get(v_cfg_4128_, 9);
v_releaseRepo_4141_ = lean_ctor_get(v_cfg_4128_, 10);
v_buildArchive_4142_ = lean_ctor_get(v_cfg_4128_, 11);
v_preferReleaseBuild_4143_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28 + 2);
v_testDriver_4144_ = lean_ctor_get(v_cfg_4128_, 12);
v_testDriverArgs_4145_ = lean_ctor_get(v_cfg_4128_, 13);
v_lintDriver_4146_ = lean_ctor_get(v_cfg_4128_, 14);
v_lintDriverArgs_4147_ = lean_ctor_get(v_cfg_4128_, 15);
v_version_4148_ = lean_ctor_get(v_cfg_4128_, 16);
v_versionTags_4149_ = lean_ctor_get(v_cfg_4128_, 17);
v_description_4150_ = lean_ctor_get(v_cfg_4128_, 18);
v_keywords_4151_ = lean_ctor_get(v_cfg_4128_, 19);
v_homepage_4152_ = lean_ctor_get(v_cfg_4128_, 20);
v_license_4153_ = lean_ctor_get(v_cfg_4128_, 21);
v_licenseFiles_4154_ = lean_ctor_get(v_cfg_4128_, 22);
v_readmeFile_4155_ = lean_ctor_get(v_cfg_4128_, 23);
v_reservoir_4156_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28 + 3);
v_enableArtifactCache_x3f_4157_ = lean_ctor_get(v_cfg_4128_, 24);
v_restoreAllArtifacts_x3f_4158_ = lean_ctor_get(v_cfg_4128_, 25);
v_libPrefixOnWindows_4159_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28 + 4);
v_allowImportAll_4160_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28 + 5);
v_builtinLint_x3f_4161_ = lean_ctor_get(v_cfg_4128_, 26);
v_checks_4162_ = lean_ctor_get(v_cfg_4128_, 27);
v_fixedToolchain_4163_ = lean_ctor_get_uint8(v_cfg_4128_, sizeof(void*)*28 + 6);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_cfg_4128_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4165_ = v_cfg_4128_;
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_checks_4162_);
lean_inc(v_builtinLint_x3f_4161_);
lean_inc(v_restoreAllArtifacts_x3f_4158_);
lean_inc(v_enableArtifactCache_x3f_4157_);
lean_inc(v_readmeFile_4155_);
lean_inc(v_licenseFiles_4154_);
lean_inc(v_license_4153_);
lean_inc(v_homepage_4152_);
lean_inc(v_keywords_4151_);
lean_inc(v_description_4150_);
lean_inc(v_versionTags_4149_);
lean_inc(v_version_4148_);
lean_inc(v_lintDriverArgs_4147_);
lean_inc(v_lintDriver_4146_);
lean_inc(v_testDriverArgs_4145_);
lean_inc(v_testDriver_4144_);
lean_inc(v_buildArchive_4142_);
lean_inc(v_releaseRepo_4141_);
lean_inc(v_irDir_4140_);
lean_inc(v_binDir_4139_);
lean_inc(v_nativeLibDir_4138_);
lean_inc(v_leanLibDir_4137_);
lean_inc(v_buildDir_4136_);
lean_inc(v_srcDir_4135_);
lean_inc(v_moreGlobalServerArgs_4134_);
lean_inc(v_extraDepTargets_4132_);
lean_inc(v_toLeanConfig_4130_);
lean_inc(v_toWorkspaceConfig_4129_);
lean_dec(v_cfg_4128_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4167_ = lean_apply_1(v_f_4127_, v_toLeanConfig_4130_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v___x_4167_);
v___x_4169_ = v___x_4165_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_toWorkspaceConfig_4129_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v___x_4167_);
lean_ctor_set(v_reuseFailAlloc_4170_, 2, v_extraDepTargets_4132_);
lean_ctor_set(v_reuseFailAlloc_4170_, 3, v_moreGlobalServerArgs_4134_);
lean_ctor_set(v_reuseFailAlloc_4170_, 4, v_srcDir_4135_);
lean_ctor_set(v_reuseFailAlloc_4170_, 5, v_buildDir_4136_);
lean_ctor_set(v_reuseFailAlloc_4170_, 6, v_leanLibDir_4137_);
lean_ctor_set(v_reuseFailAlloc_4170_, 7, v_nativeLibDir_4138_);
lean_ctor_set(v_reuseFailAlloc_4170_, 8, v_binDir_4139_);
lean_ctor_set(v_reuseFailAlloc_4170_, 9, v_irDir_4140_);
lean_ctor_set(v_reuseFailAlloc_4170_, 10, v_releaseRepo_4141_);
lean_ctor_set(v_reuseFailAlloc_4170_, 11, v_buildArchive_4142_);
lean_ctor_set(v_reuseFailAlloc_4170_, 12, v_testDriver_4144_);
lean_ctor_set(v_reuseFailAlloc_4170_, 13, v_testDriverArgs_4145_);
lean_ctor_set(v_reuseFailAlloc_4170_, 14, v_lintDriver_4146_);
lean_ctor_set(v_reuseFailAlloc_4170_, 15, v_lintDriverArgs_4147_);
lean_ctor_set(v_reuseFailAlloc_4170_, 16, v_version_4148_);
lean_ctor_set(v_reuseFailAlloc_4170_, 17, v_versionTags_4149_);
lean_ctor_set(v_reuseFailAlloc_4170_, 18, v_description_4150_);
lean_ctor_set(v_reuseFailAlloc_4170_, 19, v_keywords_4151_);
lean_ctor_set(v_reuseFailAlloc_4170_, 20, v_homepage_4152_);
lean_ctor_set(v_reuseFailAlloc_4170_, 21, v_license_4153_);
lean_ctor_set(v_reuseFailAlloc_4170_, 22, v_licenseFiles_4154_);
lean_ctor_set(v_reuseFailAlloc_4170_, 23, v_readmeFile_4155_);
lean_ctor_set(v_reuseFailAlloc_4170_, 24, v_enableArtifactCache_x3f_4157_);
lean_ctor_set(v_reuseFailAlloc_4170_, 25, v_restoreAllArtifacts_x3f_4158_);
lean_ctor_set(v_reuseFailAlloc_4170_, 26, v_builtinLint_x3f_4161_);
lean_ctor_set(v_reuseFailAlloc_4170_, 27, v_checks_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28, v_bootstrap_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28 + 1, v_precompileModules_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28 + 2, v_preferReleaseBuild_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28 + 3, v_reservoir_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28 + 4, v_libPrefixOnWindows_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28 + 5, v_allowImportAll_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*28 + 6, v_fixedToolchain_4163_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3(lean_object* v_x_4180_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___lam__3___boxed(lean_object* v_x_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lake_PackageConfig_toLeanConfig___proj___lam__3(v_x_4182_);
lean_dec_ref(v_x_4182_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_4193_, lean_object* v_n_4194_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___closed__4));
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_4196_, lean_object* v_n_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4196_, v_n_4197_);
lean_dec(v_n_4197_);
lean_dec(v_p_4196_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_4199_, lean_object* v_n_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4199_, v_n_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_4202_, lean_object* v_n_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_4202_, v_n_4203_);
lean_dec(v_n_4203_);
lean_dec(v_p_4202_);
return v_res_4204_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_4215_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_4216_ = lean_array_push(v___x_4215_, v___x_4214_);
return v___x_4216_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4224_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_4225_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_4226_ = lean_array_push(v___x_4225_, v___x_4224_);
return v___x_4226_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4234_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_4235_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_4236_ = lean_array_push(v___x_4235_, v___x_4234_);
return v___x_4236_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_4245_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_4246_ = lean_array_push(v___x_4245_, v___x_4244_);
return v___x_4246_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_4255_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_4256_ = lean_array_push(v___x_4255_, v___x_4254_);
return v___x_4256_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_4265_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_4266_ = lean_array_push(v___x_4265_, v___x_4264_);
return v___x_4266_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4274_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_4275_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_4276_ = lean_array_push(v___x_4275_, v___x_4274_);
return v___x_4276_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4284_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_4285_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_4286_ = lean_array_push(v___x_4285_, v___x_4284_);
return v___x_4286_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_4295_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_4296_ = lean_array_push(v___x_4295_, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4304_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_4305_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_4306_ = lean_array_push(v___x_4305_, v___x_4304_);
return v___x_4306_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4314_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_4315_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_4316_ = lean_array_push(v___x_4315_, v___x_4314_);
return v___x_4316_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4324_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_4325_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_4326_ = lean_array_push(v___x_4325_, v___x_4324_);
return v___x_4326_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_4335_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_4336_ = lean_array_push(v___x_4335_, v___x_4334_);
return v___x_4336_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4344_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_4345_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_4346_ = lean_array_push(v___x_4345_, v___x_4344_);
return v___x_4346_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4354_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_4355_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_4356_ = lean_array_push(v___x_4355_, v___x_4354_);
return v___x_4356_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4364_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_4365_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_4366_ = lean_array_push(v___x_4365_, v___x_4364_);
return v___x_4366_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__68(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__67));
v___x_4375_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4376_ = lean_array_push(v___x_4375_, v___x_4374_);
return v___x_4376_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4384_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4385_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__68, &l_Lake_PackageConfig___fields___closed__68_once, _init_l_Lake_PackageConfig___fields___closed__68);
v___x_4386_ = lean_array_push(v___x_4385_, v___x_4384_);
return v___x_4386_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4394_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4395_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4396_ = lean_array_push(v___x_4395_, v___x_4394_);
return v___x_4396_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4405_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4406_ = lean_array_push(v___x_4405_, v___x_4404_);
return v___x_4406_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4415_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4416_ = lean_array_push(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4424_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4425_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4426_ = lean_array_push(v___x_4425_, v___x_4424_);
return v___x_4426_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4435_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4436_ = lean_array_push(v___x_4435_, v___x_4434_);
return v___x_4436_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_4445_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_4446_ = lean_array_push(v___x_4445_, v___x_4444_);
return v___x_4446_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_4455_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_4456_ = lean_array_push(v___x_4455_, v___x_4454_);
return v___x_4456_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4464_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_4465_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_4466_ = lean_array_push(v___x_4465_, v___x_4464_);
return v___x_4466_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_4475_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_4476_ = lean_array_push(v___x_4475_, v___x_4474_);
return v___x_4476_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4484_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_4485_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_4486_ = lean_array_push(v___x_4485_, v___x_4484_);
return v___x_4486_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_4495_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_4496_ = lean_array_push(v___x_4495_, v___x_4494_);
return v___x_4496_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_4505_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_4506_ = lean_array_push(v___x_4505_, v___x_4504_);
return v___x_4506_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_4515_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_4516_ = lean_array_push(v___x_4515_, v___x_4514_);
return v___x_4516_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4524_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_4525_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_4526_ = lean_array_push(v___x_4525_, v___x_4524_);
return v___x_4526_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__132(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__131));
v___x_4535_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_4536_ = lean_array_push(v___x_4535_, v___x_4534_);
return v___x_4536_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_4545_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__132, &l_Lake_PackageConfig___fields___closed__132_once, _init_l_Lake_PackageConfig___fields___closed__132);
v___x_4546_ = lean_array_push(v___x_4545_, v___x_4544_);
return v___x_4546_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__140(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4554_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__139));
v___x_4555_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_4556_ = lean_array_push(v___x_4555_, v___x_4554_);
return v___x_4556_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_4565_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__140, &l_Lake_PackageConfig___fields___closed__140_once, _init_l_Lake_PackageConfig___fields___closed__140);
v___x_4566_ = lean_array_push(v___x_4565_, v___x_4564_);
return v___x_4566_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4574_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_4575_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_4576_ = lean_array_push(v___x_4575_, v___x_4574_);
return v___x_4576_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__152(void){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__151));
v___x_4585_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_4586_ = lean_array_push(v___x_4585_, v___x_4584_);
return v___x_4586_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__156(void){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__155));
v___x_4595_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__152, &l_Lake_PackageConfig___fields___closed__152_once, _init_l_Lake_PackageConfig___fields___closed__152);
v___x_4596_ = lean_array_push(v___x_4595_, v___x_4594_);
return v___x_4596_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__160(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__159));
v___x_4605_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__156, &l_Lake_PackageConfig___fields___closed__156_once, _init_l_Lake_PackageConfig___fields___closed__156);
v___x_4606_ = lean_array_push(v___x_4605_, v___x_4604_);
return v___x_4606_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__161(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = l_Lake_WorkspaceConfig___fields;
v___x_4608_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__160, &l_Lake_PackageConfig___fields___closed__160_once, _init_l_Lake_PackageConfig___fields___closed__160);
v___x_4609_ = l_Array_append___redArg(v___x_4608_, v___x_4607_);
return v___x_4609_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__165(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4617_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__164));
v___x_4618_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__161, &l_Lake_PackageConfig___fields___closed__161_once, _init_l_Lake_PackageConfig___fields___closed__161);
v___x_4619_ = lean_array_push(v___x_4618_, v___x_4617_);
return v___x_4619_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__166(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = l_Lake_LeanConfig___fields;
v___x_4621_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__165, &l_Lake_PackageConfig___fields___closed__165_once, _init_l_Lake_PackageConfig___fields___closed__165);
v___x_4622_ = l_Array_append___redArg(v___x_4621_, v___x_4620_);
return v___x_4622_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__170(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__169));
v___x_4631_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__166, &l_Lake_PackageConfig___fields___closed__166_once, _init_l_Lake_PackageConfig___fields___closed__166);
v___x_4632_ = lean_array_push(v___x_4631_, v___x_4630_);
return v___x_4632_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__170, &l_Lake_PackageConfig___fields___closed__170_once, _init_l_Lake_PackageConfig___fields___closed__170);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_4634_, lean_object* v_n_4635_){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Lake_PackageConfig___fields;
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_4637_, lean_object* v_n_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lake_PackageConfig_instConfigFields(v_p_4637_, v_n_4638_);
lean_dec(v_n_4638_);
lean_dec(v_p_4637_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_4640_, lean_object* v_x2_4641_){
_start:
{
lean_object* v_name_4642_; lean_object* v___x_4643_; 
v_name_4642_ = lean_ctor_get(v_x2_4641_, 0);
lean_inc(v_name_4642_);
v___x_4643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_4642_, v_x2_4641_, v_x1_4640_);
return v___x_4643_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = l_Lake_PackageConfig___fields;
v___x_4645_ = lean_array_get_size(v___x_4644_);
return v___x_4645_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___x_4665_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4666_ = lean_unsigned_to_nat(0u);
v___x_4667_ = lean_nat_dec_lt(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4669_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4670_ = lean_nat_dec_le(v___x_4669_, v___x_4669_);
return v___x_4670_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_4671_; size_t v___x_4672_; 
v___x_4671_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_4672_ = lean_usize_of_nat(v___x_4671_);
return v___x_4672_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_4673_; size_t v___x_4674_; size_t v___x_4675_; lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4673_ = lean_box(1);
v___x_4674_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___x_4675_ = ((size_t)0ULL);
v___x_4676_ = l_Lake_PackageConfig___fields;
v___f_4677_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_4678_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_4679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4678_, v___f_4677_, v___x_4676_, v___x_4675_, v___x_4674_, v___x_4673_);
return v___x_4679_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_4680_; lean_object* v___y_4682_; lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4680_ = l_Lake_PackageConfig___fields;
v___x_4685_ = lean_box(1);
v___x_4686_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_4686_ == 0)
{
v___y_4682_ = v___x_4685_;
goto v___jp_4681_;
}
else
{
uint8_t v___x_4687_; 
v___x_4687_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
if (v___x_4687_ == 0)
{
if (v___x_4686_ == 0)
{
v___y_4682_ = v___x_4685_;
goto v___jp_4681_;
}
else
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4682_ = v___x_4688_;
goto v___jp_4681_;
}
}
else
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__15, &l_Lake_PackageConfig_instConfigInfo___closed__15_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__15);
v___y_4682_ = v___x_4689_;
goto v___jp_4681_;
}
}
v___jp_4681_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_4682_);
v___x_4684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4680_);
lean_ctor_set(v___x_4684_, 1, v___y_4682_);
lean_ctor_set(v___x_4684_, 2, v___x_4683_);
return v___x_4684_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
uint8_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4690_ = 1;
v___x_4691_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__7));
v___x_4692_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__6));
v___x_4693_ = l_Lake_defaultVersionTags;
v___x_4694_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__4));
v___x_4695_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__2));
v___x_4696_ = lean_box(0);
v___x_4697_ = l_Lake_defaultIrDir;
v___x_4698_ = l_Lake_defaultBinDir;
v___x_4699_ = l_Lake_defaultNativeLibDir;
v___x_4700_ = l_Lake_defaultLeanLibDir;
v___x_4701_ = l_Lake_defaultBuildDir;
v___x_4702_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___closed__1));
v___x_4703_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__0));
v___x_4704_ = 0;
v___x_4705_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___lam__3___closed__1));
v___x_4706_ = l_Lake_defaultPackagesDir;
v___x_4707_ = lean_alloc_ctor(0, 28, 7);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
lean_ctor_set(v___x_4707_, 1, v___x_4705_);
lean_ctor_set(v___x_4707_, 2, v___x_4703_);
lean_ctor_set(v___x_4707_, 3, v___x_4703_);
lean_ctor_set(v___x_4707_, 4, v___x_4702_);
lean_ctor_set(v___x_4707_, 5, v___x_4701_);
lean_ctor_set(v___x_4707_, 6, v___x_4700_);
lean_ctor_set(v___x_4707_, 7, v___x_4699_);
lean_ctor_set(v___x_4707_, 8, v___x_4698_);
lean_ctor_set(v___x_4707_, 9, v___x_4697_);
lean_ctor_set(v___x_4707_, 10, v___x_4696_);
lean_ctor_set(v___x_4707_, 11, v___x_4696_);
lean_ctor_set(v___x_4707_, 12, v___x_4695_);
lean_ctor_set(v___x_4707_, 13, v___x_4703_);
lean_ctor_set(v___x_4707_, 14, v___x_4695_);
lean_ctor_set(v___x_4707_, 15, v___x_4703_);
lean_ctor_set(v___x_4707_, 16, v___x_4694_);
lean_ctor_set(v___x_4707_, 17, v___x_4693_);
lean_ctor_set(v___x_4707_, 18, v___x_4695_);
lean_ctor_set(v___x_4707_, 19, v___x_4703_);
lean_ctor_set(v___x_4707_, 20, v___x_4695_);
lean_ctor_set(v___x_4707_, 21, v___x_4695_);
lean_ctor_set(v___x_4707_, 22, v___x_4692_);
lean_ctor_set(v___x_4707_, 23, v___x_4691_);
lean_ctor_set(v___x_4707_, 24, v___x_4696_);
lean_ctor_set(v___x_4707_, 25, v___x_4696_);
lean_ctor_set(v___x_4707_, 26, v___x_4696_);
lean_ctor_set(v___x_4707_, 27, v___x_4703_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28, v___x_4704_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28 + 1, v___x_4704_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28 + 2, v___x_4704_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28 + 3, v___x_4690_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28 + 4, v___x_4704_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28 + 5, v___x_4704_);
lean_ctor_set_uint8(v___x_4707_, sizeof(void*)*28 + 6, v___x_4704_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_4708_, lean_object* v_n_4709_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_4711_, lean_object* v_n_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Lake_PackageConfig_instEmptyCollection(v_p_4711_, v_n_4712_);
lean_dec(v_n_4712_);
lean_dec(v_p_4711_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_4714_){
_start:
{
lean_inc(v_n_4714_);
return v_n_4714_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Lake_PackageConfig_origName___redArg(v_n_4715_);
lean_dec(v_n_4715_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_4717_, lean_object* v_n_4718_, lean_object* v_x_4719_){
_start:
{
lean_inc(v_n_4718_);
return v_n_4718_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_4720_, lean_object* v_n_4721_, lean_object* v_x_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_Lake_PackageConfig_origName(v_p_4720_, v_n_4721_, v_x_4722_);
lean_dec_ref(v_x_4722_);
lean_dec(v_n_4721_);
lean_dec(v_p_4720_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_4731_){
_start:
{
lean_object* v_keyName_4732_; 
v_keyName_4732_ = lean_ctor_get(v_self_4731_, 1);
lean_inc(v_keyName_4732_);
return v_keyName_4732_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lake_PackageDecl_name(v_self_4733_);
lean_dec_ref(v_self_4733_);
return v_res_4734_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_WorkspaceConfig(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_PackageConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
