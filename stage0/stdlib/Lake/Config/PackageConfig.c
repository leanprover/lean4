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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLeanLibDir;
extern lean_object* l_Lake_defaultNativeLibDir;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_defaultVersionTags;
extern lean_object* l_Lake_defaultIrDir;
extern lean_object* l_Lake_defaultBinDir;
extern lean_object* l_Lake_defaultBuildDir;
extern lean_object* l_Lake_defaultPackagesDir;
extern lean_object* l_Lake_instInhabitedLeanConfig_default;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanConfig___fields;
extern lean_object* l_Lake_WorkspaceConfig___fields;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
static const lean_array_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__0_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__1_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__2 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__3 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__3_value;
static const lean_ctor_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__3_value),((lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__2_value)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__4 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__4_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LICENSE"};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__5 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__5_value;
static const lean_array_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__5_value)}};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__6 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__6_value;
static const lean_string_object l_Lake_instInhabitedPackageConfig_default___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__7 = (const lean_object*)&l_Lake_instInhabitedPackageConfig_default___redArg___closed__7_value;
static lean_once_cell_t l_Lake_instInhabitedPackageConfig_default___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPackageConfig_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageConfig_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_bootstrap___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_bootstrap___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_bootstrap___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_extraDepTargets___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_precompileModules___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_precompileModules___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_precompileModules___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_precompileModules___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_precompileModules___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_precompileModules___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_precompileModules___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_precompileModules___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_srcDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_srcDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_srcDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_srcDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_srcDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_srcDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_buildDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_buildDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_buildDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_buildDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_buildDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_leanLibDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_leanLibDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_nativeLibDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_binDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_binDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_binDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_binDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_binDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_binDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_binDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_binDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_irDir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_irDir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_irDir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_irDir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_irDir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_irDir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_irDir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_irDir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_releaseRepo___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_releaseRepo___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_buildArchive___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_buildArchive___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildArchive___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_buildArchive___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_buildArchive___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_buildArchive___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_buildArchive___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_buildArchive___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_buildArchive___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriver___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_testDriver___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_testDriver___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_testDriver___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_testDriverArgs___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_lintDriver___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriver___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriver___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriver___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriver___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_lintDriver___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_lintDriver___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_lintDriver___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_lintDriver___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_version___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_version___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_version___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_version___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_version___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_version___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_version___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_version___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_version___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_version___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_version___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_versionTags___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_versionTags___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_versionTags___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_versionTags___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_versionTags___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_versionTags___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_description___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_description___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_description___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_description___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_description___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_description___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_description___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_description___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_description___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_description___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_description___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_description___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_description___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_description___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_keywords___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_keywords___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_keywords___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_keywords___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_keywords___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_keywords___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_keywords___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_keywords___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_keywords___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_keywords___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_keywords___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_keywords___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_keywords___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_keywords___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_homepage___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_homepage___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_homepage___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_homepage___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_homepage___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_homepage___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_homepage___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_homepage___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_homepage___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_homepage___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_homepage___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_homepage___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_homepage___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_homepage___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_license___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_license___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_license___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_license___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_license___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_license___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_license___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_license___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_license___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_license___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_testDriver___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_license___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_license___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_license___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_license___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_licenseFiles___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_licenseFiles___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_readmeFile___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_readmeFile___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_readmeFile___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_readmeFile___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_readmeFile___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_reservoir___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_reservoir___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_reservoir___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_reservoir___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_reservoir___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_reservoir___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_allowImportAll___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_allowImportAll___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_checks___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_checks___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_checks___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_checks___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_checks___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_checks___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_checks___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_checks___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_checks___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_checks___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_checks___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_checks___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_checks___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_checks___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__2_value;
static const lean_ctor_object l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_bootstrap___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_fixedToolchain___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__0 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__0_value;
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__1 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__1_value;
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__2 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__2_value;
static const lean_closure_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__3 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__3_value;
static const lean_ctor_object l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__0_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__1_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__2_value),((lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__3_value)}};
static const lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__4 = (const lean_object*)&l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_toLeanConfig___proj___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object*);
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
static const lean_string_object l_Lake_PackageConfig___fields___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "downloadCacheService"};
static const lean_object* l_Lake_PackageConfig___fields___closed__65 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__65_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__65_value),LEAN_SCALAR_PTR_LITERAL(209, 160, 111, 129, 135, 170, 59, 122)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__66 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__66_value;
static const lean_string_object l_Lake_PackageConfig___fields___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "downloadCacheService\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__67 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__67_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__67_value),LEAN_SCALAR_PTR_LITERAL(131, 34, 56, 246, 186, 170, 124, 46)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__68 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__68_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__66_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__68_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__69 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__69_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__70;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__68_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__68_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__71 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__71_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__72;
static const lean_string_object l_Lake_PackageConfig___fields___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__73 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__73_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__73_value),LEAN_SCALAR_PTR_LITERAL(187, 40, 173, 233, 223, 78, 220, 191)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__74 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__74_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__75 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__75_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__76;
static const lean_string_object l_Lake_PackageConfig___fields___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "testRunner"};
static const lean_object* l_Lake_PackageConfig___fields___closed__77 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__77_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__77_value),LEAN_SCALAR_PTR_LITERAL(58, 61, 59, 86, 150, 111, 127, 182)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__78 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__78_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__78_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__74_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__79 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__79_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__80;
static const lean_string_object l_Lake_PackageConfig___fields___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__81 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__81_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__81_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 168, 214, 71, 6, 72, 93)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__82 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__82_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__82_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__82_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__83 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__83_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__84;
static const lean_string_object l_Lake_PackageConfig___fields___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintDriver"};
static const lean_object* l_Lake_PackageConfig___fields___closed__85 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__85_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__85_value),LEAN_SCALAR_PTR_LITERAL(164, 80, 113, 139, 118, 238, 67, 240)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__86 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__86_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__86_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__86_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__87 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__87_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__88;
static const lean_string_object l_Lake_PackageConfig___fields___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverArgs"};
static const lean_object* l_Lake_PackageConfig___fields___closed__89 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__89_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__89_value),LEAN_SCALAR_PTR_LITERAL(102, 206, 227, 73, 236, 117, 156, 150)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__90 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__90_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__90_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__90_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__91 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__91_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__92;
static const lean_string_object l_Lake_PackageConfig___fields___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_PackageConfig___fields___closed__93 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__93_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__93_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__94 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__94_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__94_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__94_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__95 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__95_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__96;
static const lean_string_object l_Lake_PackageConfig___fields___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "versionTags"};
static const lean_object* l_Lake_PackageConfig___fields___closed__97 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__97_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__97_value),LEAN_SCALAR_PTR_LITERAL(76, 44, 235, 102, 59, 70, 79, 98)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__98 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__98_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__98_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__98_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__99 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__99_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__100;
static const lean_string_object l_Lake_PackageConfig___fields___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "description"};
static const lean_object* l_Lake_PackageConfig___fields___closed__101 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__101_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__101_value),LEAN_SCALAR_PTR_LITERAL(85, 116, 204, 74, 85, 134, 17, 161)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__102 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__102_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__102_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__102_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__103 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__103_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__104;
static const lean_string_object l_Lake_PackageConfig___fields___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "keywords"};
static const lean_object* l_Lake_PackageConfig___fields___closed__105 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__105_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__105_value),LEAN_SCALAR_PTR_LITERAL(84, 45, 198, 62, 56, 187, 72, 125)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__106 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__106_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__106_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__106_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__107 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__107_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__108;
static const lean_string_object l_Lake_PackageConfig___fields___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "homepage"};
static const lean_object* l_Lake_PackageConfig___fields___closed__109 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__109_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__109_value),LEAN_SCALAR_PTR_LITERAL(73, 148, 206, 183, 90, 222, 74, 16)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__110 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__110_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__110_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__110_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__111 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__111_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__112;
static const lean_string_object l_Lake_PackageConfig___fields___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "license"};
static const lean_object* l_Lake_PackageConfig___fields___closed__113 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__113_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__113_value),LEAN_SCALAR_PTR_LITERAL(149, 142, 81, 8, 241, 47, 83, 51)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__114 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__114_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__114_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__114_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__115 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__115_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__116_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__116;
static const lean_string_object l_Lake_PackageConfig___fields___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "licenseFiles"};
static const lean_object* l_Lake_PackageConfig___fields___closed__117 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__117_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__117_value),LEAN_SCALAR_PTR_LITERAL(115, 188, 70, 201, 62, 96, 76, 55)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__118 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__118_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__118_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__118_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__119 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__119_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__120;
static const lean_string_object l_Lake_PackageConfig___fields___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "readmeFile"};
static const lean_object* l_Lake_PackageConfig___fields___closed__121 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__121_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__121_value),LEAN_SCALAR_PTR_LITERAL(86, 68, 195, 254, 204, 64, 41, 249)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__122 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__122_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__122_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__122_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__123 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__123_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__124;
static const lean_string_object l_Lake_PackageConfig___fields___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_PackageConfig___fields___closed__125 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__125_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__125_value),LEAN_SCALAR_PTR_LITERAL(98, 62, 227, 196, 233, 158, 105, 168)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__126 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__126_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__126_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__126_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__127 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__127_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__128;
static const lean_string_object l_Lake_PackageConfig___fields___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "enableArtifactCache"};
static const lean_object* l_Lake_PackageConfig___fields___closed__129 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__129_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__129_value),LEAN_SCALAR_PTR_LITERAL(69, 183, 189, 255, 13, 235, 31, 38)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__130 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__130_value;
static const lean_string_object l_Lake_PackageConfig___fields___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "enableArtifactCache\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__131 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__131_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__131_value),LEAN_SCALAR_PTR_LITERAL(190, 150, 150, 100, 20, 242, 199, 174)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__132 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__132_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__130_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__132_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__133 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__133_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__134_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__134;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__132_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__132_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__135 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__135_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__136;
static const lean_string_object l_Lake_PackageConfig___fields___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "restoreAllArtifacts"};
static const lean_object* l_Lake_PackageConfig___fields___closed__137 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__137_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__137_value),LEAN_SCALAR_PTR_LITERAL(172, 122, 225, 122, 213, 189, 222, 165)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__138 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__138_value;
static const lean_string_object l_Lake_PackageConfig___fields___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "restoreAllArtifacts\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__139 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__139_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__139_value),LEAN_SCALAR_PTR_LITERAL(2, 1, 41, 192, 97, 8, 217, 82)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__140 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__140_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__138_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__140_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__141 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__141_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__142;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__140_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__140_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__143 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__143_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__144;
static const lean_string_object l_Lake_PackageConfig___fields___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libPrefixOnWindows"};
static const lean_object* l_Lake_PackageConfig___fields___closed__145 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__145_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__145_value),LEAN_SCALAR_PTR_LITERAL(26, 75, 58, 45, 181, 132, 175, 34)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__146 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__146_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__146_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__147 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__147_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__148;
static const lean_string_object l_Lake_PackageConfig___fields___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowImportAll"};
static const lean_object* l_Lake_PackageConfig___fields___closed__149 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__149_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__149_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 75, 91, 118, 43, 12, 210)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__150 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__150_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__150_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__150_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__151 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__151_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__152_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__152;
static const lean_string_object l_Lake_PackageConfig___fields___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "builtinLint"};
static const lean_object* l_Lake_PackageConfig___fields___closed__153 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__153_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__153_value),LEAN_SCALAR_PTR_LITERAL(188, 180, 184, 187, 78, 165, 206, 169)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__154 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__154_value;
static const lean_string_object l_Lake_PackageConfig___fields___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "builtinLint\?"};
static const lean_object* l_Lake_PackageConfig___fields___closed__155 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__155_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__155_value),LEAN_SCALAR_PTR_LITERAL(97, 5, 46, 89, 142, 210, 136, 240)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__156 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__156_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__154_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__156_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__157 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__157_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__158_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__158;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__156_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__156_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__159 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__159_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__160_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__160;
static const lean_string_object l_Lake_PackageConfig___fields___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "checks"};
static const lean_object* l_Lake_PackageConfig___fields___closed__161 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__161_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__161_value),LEAN_SCALAR_PTR_LITERAL(26, 43, 61, 84, 108, 97, 184, 96)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__162 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__162_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__162_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__162_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__163 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__163_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__164_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__164;
static const lean_string_object l_Lake_PackageConfig___fields___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fixedToolchain"};
static const lean_object* l_Lake_PackageConfig___fields___closed__165 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__165_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__165_value),LEAN_SCALAR_PTR_LITERAL(248, 4, 88, 39, 97, 195, 130, 156)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__166 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__166_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__166_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__166_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__167 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__167_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__168_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__168;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__169_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__169;
static const lean_string_object l_Lake_PackageConfig___fields___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toWorkspaceConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__170 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__170_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__170_value),LEAN_SCALAR_PTR_LITERAL(135, 228, 155, 156, 156, 252, 46, 118)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__171 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__171_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__171_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__171_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__172 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__172_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__173_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__173;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__174_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__174;
static const lean_string_object l_Lake_PackageConfig___fields___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toLeanConfig"};
static const lean_object* l_Lake_PackageConfig___fields___closed__175 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__175_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PackageConfig___fields___closed__175_value),LEAN_SCALAR_PTR_LITERAL(201, 26, 194, 50, 195, 212, 218, 10)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__176 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__176_value;
static const lean_ctor_object l_Lake_PackageConfig___fields___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageConfig___fields___closed__176_value),((lean_object*)&l_Lake_PackageConfig___fields___closed__176_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_PackageConfig___fields___closed__177 = (const lean_object*)&l_Lake_PackageConfig___fields___closed__177_value;
static lean_once_cell_t l_Lake_PackageConfig___fields___closed__178_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig___fields___closed__178;
LEAN_EXPORT lean_object* l_Lake_PackageConfig___fields;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg___boxed(lean_object*);
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
static size_t l_Lake_PackageConfig_instConfigInfo___closed__13;
static lean_once_cell_t l_Lake_PackageConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_instConfigInfo___closed__14;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo;
static lean_once_cell_t l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___redArg___closed__8(void){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_27_ = 1;
v___x_28_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
v___x_29_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
v___x_30_ = l_Lake_defaultVersionTags;
v___x_31_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
v___x_32_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
v___x_33_ = lean_box(0);
v___x_34_ = l_Lake_defaultIrDir;
v___x_35_ = l_Lake_defaultBinDir;
v___x_36_ = l_Lake_defaultNativeLibDir;
v___x_37_ = l_Lake_defaultLeanLibDir;
v___x_38_ = l_Lake_defaultBuildDir;
v___x_39_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
v___x_40_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__0));
v___x_41_ = 0;
v___x_42_ = l_Lake_instInhabitedLeanConfig_default;
v___x_43_ = l_Lake_defaultPackagesDir;
v___x_44_ = lean_alloc_ctor(0, 29, 7);
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
lean_ctor_set(v___x_44_, 12, v___x_33_);
lean_ctor_set(v___x_44_, 13, v___x_32_);
lean_ctor_set(v___x_44_, 14, v___x_40_);
lean_ctor_set(v___x_44_, 15, v___x_32_);
lean_ctor_set(v___x_44_, 16, v___x_40_);
lean_ctor_set(v___x_44_, 17, v___x_31_);
lean_ctor_set(v___x_44_, 18, v___x_30_);
lean_ctor_set(v___x_44_, 19, v___x_32_);
lean_ctor_set(v___x_44_, 20, v___x_40_);
lean_ctor_set(v___x_44_, 21, v___x_32_);
lean_ctor_set(v___x_44_, 22, v___x_32_);
lean_ctor_set(v___x_44_, 23, v___x_29_);
lean_ctor_set(v___x_44_, 24, v___x_28_);
lean_ctor_set(v___x_44_, 25, v___x_33_);
lean_ctor_set(v___x_44_, 26, v___x_33_);
lean_ctor_set(v___x_44_, 27, v___x_33_);
lean_ctor_set(v___x_44_, 28, v___x_40_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29 + 1, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29 + 2, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29 + 3, v___x_27_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29 + 4, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29 + 5, v___x_41_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*29 + 6, v___x_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___redArg(){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___redArg___closed__8, &l_Lake_instInhabitedPackageConfig_default___redArg___closed__8_once, _init_l_Lake_instInhabitedPackageConfig_default___redArg___closed__8);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_instInhabitedPackageConfig_default___redArg();
return v_res_48_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig_default___closed__0(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lake_instInhabitedPackageConfig_default___redArg();
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object* v_p_50_, lean_object* v_n_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__0, &l_Lake_instInhabitedPackageConfig_default___closed__0_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig_default___boxed(lean_object* v_p_53_, lean_object* v_n_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lake_instInhabitedPackageConfig_default(v_p_53_, v_n_54_);
lean_dec(v_n_54_);
lean_dec(v_p_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___redArg(){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__0, &l_Lake_instInhabitedPackageConfig_default___closed__0_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_instInhabitedPackageConfig___redArg();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig(lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Lake_instInhabitedPackageConfig_default___closed__0, &l_Lake_instInhabitedPackageConfig_default___closed__0_once, _init_l_Lake_instInhabitedPackageConfig_default___closed__0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig___boxed(lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_instInhabitedPackageConfig(v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0(lean_object* v_cfg_66_){
_start:
{
uint8_t v_bootstrap_67_; 
v_bootstrap_67_ = lean_ctor_get_uint8(v_cfg_66_, sizeof(void*)*29);
return v_bootstrap_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0___boxed(lean_object* v_cfg_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__0(v_cfg_68_);
lean_dec_ref(v_cfg_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(uint8_t v_val_71_, lean_object* v_cfg_72_){
_start:
{
lean_object* v_toWorkspaceConfig_73_; lean_object* v_toLeanConfig_74_; lean_object* v_extraDepTargets_75_; uint8_t v_precompileModules_76_; lean_object* v_moreGlobalServerArgs_77_; lean_object* v_srcDir_78_; lean_object* v_buildDir_79_; lean_object* v_leanLibDir_80_; lean_object* v_nativeLibDir_81_; lean_object* v_binDir_82_; lean_object* v_irDir_83_; lean_object* v_releaseRepo_84_; lean_object* v_buildArchive_85_; uint8_t v_preferReleaseBuild_86_; lean_object* v_downloadCacheService_x3f_87_; lean_object* v_testDriver_88_; lean_object* v_testDriverArgs_89_; lean_object* v_lintDriver_90_; lean_object* v_lintDriverArgs_91_; lean_object* v_version_92_; lean_object* v_versionTags_93_; lean_object* v_description_94_; lean_object* v_keywords_95_; lean_object* v_homepage_96_; lean_object* v_license_97_; lean_object* v_licenseFiles_98_; lean_object* v_readmeFile_99_; uint8_t v_reservoir_100_; lean_object* v_enableArtifactCache_x3f_101_; lean_object* v_restoreAllArtifacts_x3f_102_; uint8_t v_libPrefixOnWindows_103_; uint8_t v_allowImportAll_104_; lean_object* v_builtinLint_x3f_105_; lean_object* v_checks_106_; uint8_t v_fixedToolchain_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_toWorkspaceConfig_73_ = lean_ctor_get(v_cfg_72_, 0);
v_toLeanConfig_74_ = lean_ctor_get(v_cfg_72_, 1);
v_extraDepTargets_75_ = lean_ctor_get(v_cfg_72_, 2);
v_precompileModules_76_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_77_ = lean_ctor_get(v_cfg_72_, 3);
v_srcDir_78_ = lean_ctor_get(v_cfg_72_, 4);
v_buildDir_79_ = lean_ctor_get(v_cfg_72_, 5);
v_leanLibDir_80_ = lean_ctor_get(v_cfg_72_, 6);
v_nativeLibDir_81_ = lean_ctor_get(v_cfg_72_, 7);
v_binDir_82_ = lean_ctor_get(v_cfg_72_, 8);
v_irDir_83_ = lean_ctor_get(v_cfg_72_, 9);
v_releaseRepo_84_ = lean_ctor_get(v_cfg_72_, 10);
v_buildArchive_85_ = lean_ctor_get(v_cfg_72_, 11);
v_preferReleaseBuild_86_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_87_ = lean_ctor_get(v_cfg_72_, 12);
v_testDriver_88_ = lean_ctor_get(v_cfg_72_, 13);
v_testDriverArgs_89_ = lean_ctor_get(v_cfg_72_, 14);
v_lintDriver_90_ = lean_ctor_get(v_cfg_72_, 15);
v_lintDriverArgs_91_ = lean_ctor_get(v_cfg_72_, 16);
v_version_92_ = lean_ctor_get(v_cfg_72_, 17);
v_versionTags_93_ = lean_ctor_get(v_cfg_72_, 18);
v_description_94_ = lean_ctor_get(v_cfg_72_, 19);
v_keywords_95_ = lean_ctor_get(v_cfg_72_, 20);
v_homepage_96_ = lean_ctor_get(v_cfg_72_, 21);
v_license_97_ = lean_ctor_get(v_cfg_72_, 22);
v_licenseFiles_98_ = lean_ctor_get(v_cfg_72_, 23);
v_readmeFile_99_ = lean_ctor_get(v_cfg_72_, 24);
v_reservoir_100_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_101_ = lean_ctor_get(v_cfg_72_, 25);
v_restoreAllArtifacts_x3f_102_ = lean_ctor_get(v_cfg_72_, 26);
v_libPrefixOnWindows_103_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*29 + 4);
v_allowImportAll_104_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_105_ = lean_ctor_get(v_cfg_72_, 27);
v_checks_106_ = lean_ctor_get(v_cfg_72_, 28);
v_fixedToolchain_107_ = lean_ctor_get_uint8(v_cfg_72_, sizeof(void*)*29 + 6);
v_isSharedCheck_114_ = !lean_is_exclusive(v_cfg_72_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v_cfg_72_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_checks_106_);
lean_inc(v_builtinLint_x3f_105_);
lean_inc(v_restoreAllArtifacts_x3f_102_);
lean_inc(v_enableArtifactCache_x3f_101_);
lean_inc(v_readmeFile_99_);
lean_inc(v_licenseFiles_98_);
lean_inc(v_license_97_);
lean_inc(v_homepage_96_);
lean_inc(v_keywords_95_);
lean_inc(v_description_94_);
lean_inc(v_versionTags_93_);
lean_inc(v_version_92_);
lean_inc(v_lintDriverArgs_91_);
lean_inc(v_lintDriver_90_);
lean_inc(v_testDriverArgs_89_);
lean_inc(v_testDriver_88_);
lean_inc(v_downloadCacheService_x3f_87_);
lean_inc(v_buildArchive_85_);
lean_inc(v_releaseRepo_84_);
lean_inc(v_irDir_83_);
lean_inc(v_binDir_82_);
lean_inc(v_nativeLibDir_81_);
lean_inc(v_leanLibDir_80_);
lean_inc(v_buildDir_79_);
lean_inc(v_srcDir_78_);
lean_inc(v_moreGlobalServerArgs_77_);
lean_inc(v_extraDepTargets_75_);
lean_inc(v_toLeanConfig_74_);
lean_inc(v_toWorkspaceConfig_73_);
lean_dec(v_cfg_72_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_toWorkspaceConfig_73_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_toLeanConfig_74_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_extraDepTargets_75_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_moreGlobalServerArgs_77_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_srcDir_78_);
lean_ctor_set(v_reuseFailAlloc_113_, 5, v_buildDir_79_);
lean_ctor_set(v_reuseFailAlloc_113_, 6, v_leanLibDir_80_);
lean_ctor_set(v_reuseFailAlloc_113_, 7, v_nativeLibDir_81_);
lean_ctor_set(v_reuseFailAlloc_113_, 8, v_binDir_82_);
lean_ctor_set(v_reuseFailAlloc_113_, 9, v_irDir_83_);
lean_ctor_set(v_reuseFailAlloc_113_, 10, v_releaseRepo_84_);
lean_ctor_set(v_reuseFailAlloc_113_, 11, v_buildArchive_85_);
lean_ctor_set(v_reuseFailAlloc_113_, 12, v_downloadCacheService_x3f_87_);
lean_ctor_set(v_reuseFailAlloc_113_, 13, v_testDriver_88_);
lean_ctor_set(v_reuseFailAlloc_113_, 14, v_testDriverArgs_89_);
lean_ctor_set(v_reuseFailAlloc_113_, 15, v_lintDriver_90_);
lean_ctor_set(v_reuseFailAlloc_113_, 16, v_lintDriverArgs_91_);
lean_ctor_set(v_reuseFailAlloc_113_, 17, v_version_92_);
lean_ctor_set(v_reuseFailAlloc_113_, 18, v_versionTags_93_);
lean_ctor_set(v_reuseFailAlloc_113_, 19, v_description_94_);
lean_ctor_set(v_reuseFailAlloc_113_, 20, v_keywords_95_);
lean_ctor_set(v_reuseFailAlloc_113_, 21, v_homepage_96_);
lean_ctor_set(v_reuseFailAlloc_113_, 22, v_license_97_);
lean_ctor_set(v_reuseFailAlloc_113_, 23, v_licenseFiles_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 24, v_readmeFile_99_);
lean_ctor_set(v_reuseFailAlloc_113_, 25, v_enableArtifactCache_x3f_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 26, v_restoreAllArtifacts_x3f_102_);
lean_ctor_set(v_reuseFailAlloc_113_, 27, v_builtinLint_x3f_105_);
lean_ctor_set(v_reuseFailAlloc_113_, 28, v_checks_106_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*29 + 1, v_precompileModules_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*29 + 2, v_preferReleaseBuild_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*29 + 3, v_reservoir_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*29 + 5, v_allowImportAll_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*29 + 6, v_fixedToolchain_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*29, v_val_71_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1___boxed(lean_object* v_val_115_, lean_object* v_cfg_116_){
_start:
{
uint8_t v_val_144__boxed_117_; lean_object* v_res_118_; 
v_val_144__boxed_117_ = lean_unbox(v_val_115_);
v_res_118_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__1(v_val_144__boxed_117_, v_cfg_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__2(lean_object* v_f_119_, lean_object* v_cfg_120_){
_start:
{
lean_object* v_toWorkspaceConfig_121_; lean_object* v_toLeanConfig_122_; uint8_t v_bootstrap_123_; lean_object* v_extraDepTargets_124_; uint8_t v_precompileModules_125_; lean_object* v_moreGlobalServerArgs_126_; lean_object* v_srcDir_127_; lean_object* v_buildDir_128_; lean_object* v_leanLibDir_129_; lean_object* v_nativeLibDir_130_; lean_object* v_binDir_131_; lean_object* v_irDir_132_; lean_object* v_releaseRepo_133_; lean_object* v_buildArchive_134_; uint8_t v_preferReleaseBuild_135_; lean_object* v_downloadCacheService_x3f_136_; lean_object* v_testDriver_137_; lean_object* v_testDriverArgs_138_; lean_object* v_lintDriver_139_; lean_object* v_lintDriverArgs_140_; lean_object* v_version_141_; lean_object* v_versionTags_142_; lean_object* v_description_143_; lean_object* v_keywords_144_; lean_object* v_homepage_145_; lean_object* v_license_146_; lean_object* v_licenseFiles_147_; lean_object* v_readmeFile_148_; uint8_t v_reservoir_149_; lean_object* v_enableArtifactCache_x3f_150_; lean_object* v_restoreAllArtifacts_x3f_151_; uint8_t v_libPrefixOnWindows_152_; uint8_t v_allowImportAll_153_; lean_object* v_builtinLint_x3f_154_; lean_object* v_checks_155_; uint8_t v_fixedToolchain_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_166_; 
v_toWorkspaceConfig_121_ = lean_ctor_get(v_cfg_120_, 0);
v_toLeanConfig_122_ = lean_ctor_get(v_cfg_120_, 1);
v_bootstrap_123_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29);
v_extraDepTargets_124_ = lean_ctor_get(v_cfg_120_, 2);
v_precompileModules_125_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_126_ = lean_ctor_get(v_cfg_120_, 3);
v_srcDir_127_ = lean_ctor_get(v_cfg_120_, 4);
v_buildDir_128_ = lean_ctor_get(v_cfg_120_, 5);
v_leanLibDir_129_ = lean_ctor_get(v_cfg_120_, 6);
v_nativeLibDir_130_ = lean_ctor_get(v_cfg_120_, 7);
v_binDir_131_ = lean_ctor_get(v_cfg_120_, 8);
v_irDir_132_ = lean_ctor_get(v_cfg_120_, 9);
v_releaseRepo_133_ = lean_ctor_get(v_cfg_120_, 10);
v_buildArchive_134_ = lean_ctor_get(v_cfg_120_, 11);
v_preferReleaseBuild_135_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_136_ = lean_ctor_get(v_cfg_120_, 12);
v_testDriver_137_ = lean_ctor_get(v_cfg_120_, 13);
v_testDriverArgs_138_ = lean_ctor_get(v_cfg_120_, 14);
v_lintDriver_139_ = lean_ctor_get(v_cfg_120_, 15);
v_lintDriverArgs_140_ = lean_ctor_get(v_cfg_120_, 16);
v_version_141_ = lean_ctor_get(v_cfg_120_, 17);
v_versionTags_142_ = lean_ctor_get(v_cfg_120_, 18);
v_description_143_ = lean_ctor_get(v_cfg_120_, 19);
v_keywords_144_ = lean_ctor_get(v_cfg_120_, 20);
v_homepage_145_ = lean_ctor_get(v_cfg_120_, 21);
v_license_146_ = lean_ctor_get(v_cfg_120_, 22);
v_licenseFiles_147_ = lean_ctor_get(v_cfg_120_, 23);
v_readmeFile_148_ = lean_ctor_get(v_cfg_120_, 24);
v_reservoir_149_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_150_ = lean_ctor_get(v_cfg_120_, 25);
v_restoreAllArtifacts_x3f_151_ = lean_ctor_get(v_cfg_120_, 26);
v_libPrefixOnWindows_152_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29 + 4);
v_allowImportAll_153_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_154_ = lean_ctor_get(v_cfg_120_, 27);
v_checks_155_ = lean_ctor_get(v_cfg_120_, 28);
v_fixedToolchain_156_ = lean_ctor_get_uint8(v_cfg_120_, sizeof(void*)*29 + 6);
v_isSharedCheck_166_ = !lean_is_exclusive(v_cfg_120_);
if (v_isSharedCheck_166_ == 0)
{
v___x_158_ = v_cfg_120_;
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_checks_155_);
lean_inc(v_builtinLint_x3f_154_);
lean_inc(v_restoreAllArtifacts_x3f_151_);
lean_inc(v_enableArtifactCache_x3f_150_);
lean_inc(v_readmeFile_148_);
lean_inc(v_licenseFiles_147_);
lean_inc(v_license_146_);
lean_inc(v_homepage_145_);
lean_inc(v_keywords_144_);
lean_inc(v_description_143_);
lean_inc(v_versionTags_142_);
lean_inc(v_version_141_);
lean_inc(v_lintDriverArgs_140_);
lean_inc(v_lintDriver_139_);
lean_inc(v_testDriverArgs_138_);
lean_inc(v_testDriver_137_);
lean_inc(v_downloadCacheService_x3f_136_);
lean_inc(v_buildArchive_134_);
lean_inc(v_releaseRepo_133_);
lean_inc(v_irDir_132_);
lean_inc(v_binDir_131_);
lean_inc(v_nativeLibDir_130_);
lean_inc(v_leanLibDir_129_);
lean_inc(v_buildDir_128_);
lean_inc(v_srcDir_127_);
lean_inc(v_moreGlobalServerArgs_126_);
lean_inc(v_extraDepTargets_124_);
lean_inc(v_toLeanConfig_122_);
lean_inc(v_toWorkspaceConfig_121_);
lean_dec(v_cfg_120_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_box(v_bootstrap_123_);
v___x_161_ = lean_apply_1(v_f_119_, v___x_160_);
if (v_isShared_159_ == 0)
{
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_toWorkspaceConfig_121_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_toLeanConfig_122_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_extraDepTargets_124_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_moreGlobalServerArgs_126_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_srcDir_127_);
lean_ctor_set(v_reuseFailAlloc_165_, 5, v_buildDir_128_);
lean_ctor_set(v_reuseFailAlloc_165_, 6, v_leanLibDir_129_);
lean_ctor_set(v_reuseFailAlloc_165_, 7, v_nativeLibDir_130_);
lean_ctor_set(v_reuseFailAlloc_165_, 8, v_binDir_131_);
lean_ctor_set(v_reuseFailAlloc_165_, 9, v_irDir_132_);
lean_ctor_set(v_reuseFailAlloc_165_, 10, v_releaseRepo_133_);
lean_ctor_set(v_reuseFailAlloc_165_, 11, v_buildArchive_134_);
lean_ctor_set(v_reuseFailAlloc_165_, 12, v_downloadCacheService_x3f_136_);
lean_ctor_set(v_reuseFailAlloc_165_, 13, v_testDriver_137_);
lean_ctor_set(v_reuseFailAlloc_165_, 14, v_testDriverArgs_138_);
lean_ctor_set(v_reuseFailAlloc_165_, 15, v_lintDriver_139_);
lean_ctor_set(v_reuseFailAlloc_165_, 16, v_lintDriverArgs_140_);
lean_ctor_set(v_reuseFailAlloc_165_, 17, v_version_141_);
lean_ctor_set(v_reuseFailAlloc_165_, 18, v_versionTags_142_);
lean_ctor_set(v_reuseFailAlloc_165_, 19, v_description_143_);
lean_ctor_set(v_reuseFailAlloc_165_, 20, v_keywords_144_);
lean_ctor_set(v_reuseFailAlloc_165_, 21, v_homepage_145_);
lean_ctor_set(v_reuseFailAlloc_165_, 22, v_license_146_);
lean_ctor_set(v_reuseFailAlloc_165_, 23, v_licenseFiles_147_);
lean_ctor_set(v_reuseFailAlloc_165_, 24, v_readmeFile_148_);
lean_ctor_set(v_reuseFailAlloc_165_, 25, v_enableArtifactCache_x3f_150_);
lean_ctor_set(v_reuseFailAlloc_165_, 26, v_restoreAllArtifacts_x3f_151_);
lean_ctor_set(v_reuseFailAlloc_165_, 27, v_builtinLint_x3f_154_);
lean_ctor_set(v_reuseFailAlloc_165_, 28, v_checks_155_);
v___x_163_ = v_reuseFailAlloc_165_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
uint8_t v___x_164_; 
v___x_164_ = lean_unbox(v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29, v___x_164_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29 + 1, v_precompileModules_125_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29 + 2, v_preferReleaseBuild_135_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29 + 3, v_reservoir_149_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_152_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29 + 5, v_allowImportAll_153_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*29 + 6, v_fixedToolchain_156_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(lean_object* v_x_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3___boxed(lean_object* v_x_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Lake_PackageConfig_bootstrap___proj___redArg___lam__3(v_x_169_);
lean_dec_ref(v_x_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg(){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l_Lake_PackageConfig_bootstrap___proj___redArg___closed__4));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___redArg___boxed(lean_object* v___dummy_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
return v_res_184_;
}
}
static lean_object* _init_l_Lake_PackageConfig_bootstrap___proj___closed__0(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lake_PackageConfig_bootstrap___proj___redArg();
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj(lean_object* v_p_186_, lean_object* v_n_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap___proj___boxed(lean_object* v_p_189_, lean_object* v_n_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lake_PackageConfig_bootstrap___proj(v_p_189_, v_n_190_);
lean_dec(v_n_190_);
lean_dec(v_p_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg(){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___redArg___boxed(lean_object* v___dummy_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_PackageConfig_bootstrap_instConfigField___redArg();
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField(lean_object* v_p_196_, lean_object* v_n_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Lake_PackageConfig_bootstrap___proj___closed__0, &l_Lake_PackageConfig_bootstrap___proj___closed__0_once, _init_l_Lake_PackageConfig_bootstrap___proj___closed__0);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_bootstrap_instConfigField___boxed(lean_object* v_p_199_, lean_object* v_n_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_PackageConfig_bootstrap_instConfigField(v_p_199_, v_n_200_);
lean_dec(v_n_200_);
lean_dec(v_p_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(lean_object* v_cfg_202_){
_start:
{
lean_object* v_extraDepTargets_203_; 
v_extraDepTargets_203_ = lean_ctor_get(v_cfg_202_, 2);
lean_inc_ref(v_extraDepTargets_203_);
return v_extraDepTargets_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0___boxed(lean_object* v_cfg_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__0(v_cfg_204_);
lean_dec_ref(v_cfg_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__1(lean_object* v_val_206_, lean_object* v_cfg_207_){
_start:
{
lean_object* v_toWorkspaceConfig_208_; lean_object* v_toLeanConfig_209_; uint8_t v_bootstrap_210_; uint8_t v_precompileModules_211_; lean_object* v_moreGlobalServerArgs_212_; lean_object* v_srcDir_213_; lean_object* v_buildDir_214_; lean_object* v_leanLibDir_215_; lean_object* v_nativeLibDir_216_; lean_object* v_binDir_217_; lean_object* v_irDir_218_; lean_object* v_releaseRepo_219_; lean_object* v_buildArchive_220_; uint8_t v_preferReleaseBuild_221_; lean_object* v_downloadCacheService_x3f_222_; lean_object* v_testDriver_223_; lean_object* v_testDriverArgs_224_; lean_object* v_lintDriver_225_; lean_object* v_lintDriverArgs_226_; lean_object* v_version_227_; lean_object* v_versionTags_228_; lean_object* v_description_229_; lean_object* v_keywords_230_; lean_object* v_homepage_231_; lean_object* v_license_232_; lean_object* v_licenseFiles_233_; lean_object* v_readmeFile_234_; uint8_t v_reservoir_235_; lean_object* v_enableArtifactCache_x3f_236_; lean_object* v_restoreAllArtifacts_x3f_237_; uint8_t v_libPrefixOnWindows_238_; uint8_t v_allowImportAll_239_; lean_object* v_builtinLint_x3f_240_; lean_object* v_checks_241_; uint8_t v_fixedToolchain_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_toWorkspaceConfig_208_ = lean_ctor_get(v_cfg_207_, 0);
v_toLeanConfig_209_ = lean_ctor_get(v_cfg_207_, 1);
v_bootstrap_210_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29);
v_precompileModules_211_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_212_ = lean_ctor_get(v_cfg_207_, 3);
v_srcDir_213_ = lean_ctor_get(v_cfg_207_, 4);
v_buildDir_214_ = lean_ctor_get(v_cfg_207_, 5);
v_leanLibDir_215_ = lean_ctor_get(v_cfg_207_, 6);
v_nativeLibDir_216_ = lean_ctor_get(v_cfg_207_, 7);
v_binDir_217_ = lean_ctor_get(v_cfg_207_, 8);
v_irDir_218_ = lean_ctor_get(v_cfg_207_, 9);
v_releaseRepo_219_ = lean_ctor_get(v_cfg_207_, 10);
v_buildArchive_220_ = lean_ctor_get(v_cfg_207_, 11);
v_preferReleaseBuild_221_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_222_ = lean_ctor_get(v_cfg_207_, 12);
v_testDriver_223_ = lean_ctor_get(v_cfg_207_, 13);
v_testDriverArgs_224_ = lean_ctor_get(v_cfg_207_, 14);
v_lintDriver_225_ = lean_ctor_get(v_cfg_207_, 15);
v_lintDriverArgs_226_ = lean_ctor_get(v_cfg_207_, 16);
v_version_227_ = lean_ctor_get(v_cfg_207_, 17);
v_versionTags_228_ = lean_ctor_get(v_cfg_207_, 18);
v_description_229_ = lean_ctor_get(v_cfg_207_, 19);
v_keywords_230_ = lean_ctor_get(v_cfg_207_, 20);
v_homepage_231_ = lean_ctor_get(v_cfg_207_, 21);
v_license_232_ = lean_ctor_get(v_cfg_207_, 22);
v_licenseFiles_233_ = lean_ctor_get(v_cfg_207_, 23);
v_readmeFile_234_ = lean_ctor_get(v_cfg_207_, 24);
v_reservoir_235_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_236_ = lean_ctor_get(v_cfg_207_, 25);
v_restoreAllArtifacts_x3f_237_ = lean_ctor_get(v_cfg_207_, 26);
v_libPrefixOnWindows_238_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29 + 4);
v_allowImportAll_239_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_240_ = lean_ctor_get(v_cfg_207_, 27);
v_checks_241_ = lean_ctor_get(v_cfg_207_, 28);
v_fixedToolchain_242_ = lean_ctor_get_uint8(v_cfg_207_, sizeof(void*)*29 + 6);
v_isSharedCheck_249_ = !lean_is_exclusive(v_cfg_207_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v_cfg_207_, 2);
lean_dec(v_unused_250_);
v___x_244_ = v_cfg_207_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_checks_241_);
lean_inc(v_builtinLint_x3f_240_);
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
lean_inc(v_downloadCacheService_x3f_222_);
lean_inc(v_buildArchive_220_);
lean_inc(v_releaseRepo_219_);
lean_inc(v_irDir_218_);
lean_inc(v_binDir_217_);
lean_inc(v_nativeLibDir_216_);
lean_inc(v_leanLibDir_215_);
lean_inc(v_buildDir_214_);
lean_inc(v_srcDir_213_);
lean_inc(v_moreGlobalServerArgs_212_);
lean_inc(v_toLeanConfig_209_);
lean_inc(v_toWorkspaceConfig_208_);
lean_dec(v_cfg_207_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 2, v_val_206_);
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_toWorkspaceConfig_208_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_toLeanConfig_209_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_val_206_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_moreGlobalServerArgs_212_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_srcDir_213_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_buildDir_214_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_leanLibDir_215_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_nativeLibDir_216_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_binDir_217_);
lean_ctor_set(v_reuseFailAlloc_248_, 9, v_irDir_218_);
lean_ctor_set(v_reuseFailAlloc_248_, 10, v_releaseRepo_219_);
lean_ctor_set(v_reuseFailAlloc_248_, 11, v_buildArchive_220_);
lean_ctor_set(v_reuseFailAlloc_248_, 12, v_downloadCacheService_x3f_222_);
lean_ctor_set(v_reuseFailAlloc_248_, 13, v_testDriver_223_);
lean_ctor_set(v_reuseFailAlloc_248_, 14, v_testDriverArgs_224_);
lean_ctor_set(v_reuseFailAlloc_248_, 15, v_lintDriver_225_);
lean_ctor_set(v_reuseFailAlloc_248_, 16, v_lintDriverArgs_226_);
lean_ctor_set(v_reuseFailAlloc_248_, 17, v_version_227_);
lean_ctor_set(v_reuseFailAlloc_248_, 18, v_versionTags_228_);
lean_ctor_set(v_reuseFailAlloc_248_, 19, v_description_229_);
lean_ctor_set(v_reuseFailAlloc_248_, 20, v_keywords_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 21, v_homepage_231_);
lean_ctor_set(v_reuseFailAlloc_248_, 22, v_license_232_);
lean_ctor_set(v_reuseFailAlloc_248_, 23, v_licenseFiles_233_);
lean_ctor_set(v_reuseFailAlloc_248_, 24, v_readmeFile_234_);
lean_ctor_set(v_reuseFailAlloc_248_, 25, v_enableArtifactCache_x3f_236_);
lean_ctor_set(v_reuseFailAlloc_248_, 26, v_restoreAllArtifacts_x3f_237_);
lean_ctor_set(v_reuseFailAlloc_248_, 27, v_builtinLint_x3f_240_);
lean_ctor_set(v_reuseFailAlloc_248_, 28, v_checks_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29, v_bootstrap_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29 + 1, v_precompileModules_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29 + 2, v_preferReleaseBuild_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29 + 3, v_reservoir_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29 + 5, v_allowImportAll_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*29 + 6, v_fixedToolchain_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__2(lean_object* v_f_251_, lean_object* v_cfg_252_){
_start:
{
lean_object* v_toWorkspaceConfig_253_; lean_object* v_toLeanConfig_254_; uint8_t v_bootstrap_255_; lean_object* v_extraDepTargets_256_; uint8_t v_precompileModules_257_; lean_object* v_moreGlobalServerArgs_258_; lean_object* v_srcDir_259_; lean_object* v_buildDir_260_; lean_object* v_leanLibDir_261_; lean_object* v_nativeLibDir_262_; lean_object* v_binDir_263_; lean_object* v_irDir_264_; lean_object* v_releaseRepo_265_; lean_object* v_buildArchive_266_; uint8_t v_preferReleaseBuild_267_; lean_object* v_downloadCacheService_x3f_268_; lean_object* v_testDriver_269_; lean_object* v_testDriverArgs_270_; lean_object* v_lintDriver_271_; lean_object* v_lintDriverArgs_272_; lean_object* v_version_273_; lean_object* v_versionTags_274_; lean_object* v_description_275_; lean_object* v_keywords_276_; lean_object* v_homepage_277_; lean_object* v_license_278_; lean_object* v_licenseFiles_279_; lean_object* v_readmeFile_280_; uint8_t v_reservoir_281_; lean_object* v_enableArtifactCache_x3f_282_; lean_object* v_restoreAllArtifacts_x3f_283_; uint8_t v_libPrefixOnWindows_284_; uint8_t v_allowImportAll_285_; lean_object* v_builtinLint_x3f_286_; lean_object* v_checks_287_; uint8_t v_fixedToolchain_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_toWorkspaceConfig_253_ = lean_ctor_get(v_cfg_252_, 0);
v_toLeanConfig_254_ = lean_ctor_get(v_cfg_252_, 1);
v_bootstrap_255_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29);
v_extraDepTargets_256_ = lean_ctor_get(v_cfg_252_, 2);
v_precompileModules_257_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_258_ = lean_ctor_get(v_cfg_252_, 3);
v_srcDir_259_ = lean_ctor_get(v_cfg_252_, 4);
v_buildDir_260_ = lean_ctor_get(v_cfg_252_, 5);
v_leanLibDir_261_ = lean_ctor_get(v_cfg_252_, 6);
v_nativeLibDir_262_ = lean_ctor_get(v_cfg_252_, 7);
v_binDir_263_ = lean_ctor_get(v_cfg_252_, 8);
v_irDir_264_ = lean_ctor_get(v_cfg_252_, 9);
v_releaseRepo_265_ = lean_ctor_get(v_cfg_252_, 10);
v_buildArchive_266_ = lean_ctor_get(v_cfg_252_, 11);
v_preferReleaseBuild_267_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_268_ = lean_ctor_get(v_cfg_252_, 12);
v_testDriver_269_ = lean_ctor_get(v_cfg_252_, 13);
v_testDriverArgs_270_ = lean_ctor_get(v_cfg_252_, 14);
v_lintDriver_271_ = lean_ctor_get(v_cfg_252_, 15);
v_lintDriverArgs_272_ = lean_ctor_get(v_cfg_252_, 16);
v_version_273_ = lean_ctor_get(v_cfg_252_, 17);
v_versionTags_274_ = lean_ctor_get(v_cfg_252_, 18);
v_description_275_ = lean_ctor_get(v_cfg_252_, 19);
v_keywords_276_ = lean_ctor_get(v_cfg_252_, 20);
v_homepage_277_ = lean_ctor_get(v_cfg_252_, 21);
v_license_278_ = lean_ctor_get(v_cfg_252_, 22);
v_licenseFiles_279_ = lean_ctor_get(v_cfg_252_, 23);
v_readmeFile_280_ = lean_ctor_get(v_cfg_252_, 24);
v_reservoir_281_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_282_ = lean_ctor_get(v_cfg_252_, 25);
v_restoreAllArtifacts_x3f_283_ = lean_ctor_get(v_cfg_252_, 26);
v_libPrefixOnWindows_284_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29 + 4);
v_allowImportAll_285_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_286_ = lean_ctor_get(v_cfg_252_, 27);
v_checks_287_ = lean_ctor_get(v_cfg_252_, 28);
v_fixedToolchain_288_ = lean_ctor_get_uint8(v_cfg_252_, sizeof(void*)*29 + 6);
v_isSharedCheck_296_ = !lean_is_exclusive(v_cfg_252_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v_cfg_252_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_checks_287_);
lean_inc(v_builtinLint_x3f_286_);
lean_inc(v_restoreAllArtifacts_x3f_283_);
lean_inc(v_enableArtifactCache_x3f_282_);
lean_inc(v_readmeFile_280_);
lean_inc(v_licenseFiles_279_);
lean_inc(v_license_278_);
lean_inc(v_homepage_277_);
lean_inc(v_keywords_276_);
lean_inc(v_description_275_);
lean_inc(v_versionTags_274_);
lean_inc(v_version_273_);
lean_inc(v_lintDriverArgs_272_);
lean_inc(v_lintDriver_271_);
lean_inc(v_testDriverArgs_270_);
lean_inc(v_testDriver_269_);
lean_inc(v_downloadCacheService_x3f_268_);
lean_inc(v_buildArchive_266_);
lean_inc(v_releaseRepo_265_);
lean_inc(v_irDir_264_);
lean_inc(v_binDir_263_);
lean_inc(v_nativeLibDir_262_);
lean_inc(v_leanLibDir_261_);
lean_inc(v_buildDir_260_);
lean_inc(v_srcDir_259_);
lean_inc(v_moreGlobalServerArgs_258_);
lean_inc(v_extraDepTargets_256_);
lean_inc(v_toLeanConfig_254_);
lean_inc(v_toWorkspaceConfig_253_);
lean_dec(v_cfg_252_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_apply_1(v_f_251_, v_extraDepTargets_256_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 2, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_toWorkspaceConfig_253_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_toLeanConfig_254_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_moreGlobalServerArgs_258_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_srcDir_259_);
lean_ctor_set(v_reuseFailAlloc_295_, 5, v_buildDir_260_);
lean_ctor_set(v_reuseFailAlloc_295_, 6, v_leanLibDir_261_);
lean_ctor_set(v_reuseFailAlloc_295_, 7, v_nativeLibDir_262_);
lean_ctor_set(v_reuseFailAlloc_295_, 8, v_binDir_263_);
lean_ctor_set(v_reuseFailAlloc_295_, 9, v_irDir_264_);
lean_ctor_set(v_reuseFailAlloc_295_, 10, v_releaseRepo_265_);
lean_ctor_set(v_reuseFailAlloc_295_, 11, v_buildArchive_266_);
lean_ctor_set(v_reuseFailAlloc_295_, 12, v_downloadCacheService_x3f_268_);
lean_ctor_set(v_reuseFailAlloc_295_, 13, v_testDriver_269_);
lean_ctor_set(v_reuseFailAlloc_295_, 14, v_testDriverArgs_270_);
lean_ctor_set(v_reuseFailAlloc_295_, 15, v_lintDriver_271_);
lean_ctor_set(v_reuseFailAlloc_295_, 16, v_lintDriverArgs_272_);
lean_ctor_set(v_reuseFailAlloc_295_, 17, v_version_273_);
lean_ctor_set(v_reuseFailAlloc_295_, 18, v_versionTags_274_);
lean_ctor_set(v_reuseFailAlloc_295_, 19, v_description_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 20, v_keywords_276_);
lean_ctor_set(v_reuseFailAlloc_295_, 21, v_homepage_277_);
lean_ctor_set(v_reuseFailAlloc_295_, 22, v_license_278_);
lean_ctor_set(v_reuseFailAlloc_295_, 23, v_licenseFiles_279_);
lean_ctor_set(v_reuseFailAlloc_295_, 24, v_readmeFile_280_);
lean_ctor_set(v_reuseFailAlloc_295_, 25, v_enableArtifactCache_x3f_282_);
lean_ctor_set(v_reuseFailAlloc_295_, 26, v_restoreAllArtifacts_x3f_283_);
lean_ctor_set(v_reuseFailAlloc_295_, 27, v_builtinLint_x3f_286_);
lean_ctor_set(v_reuseFailAlloc_295_, 28, v_checks_287_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29, v_bootstrap_255_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29 + 1, v_precompileModules_257_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29 + 2, v_preferReleaseBuild_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29 + 3, v_reservoir_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29 + 5, v_allowImportAll_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_295_, sizeof(void*)*29 + 6, v_fixedToolchain_288_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(lean_object* v_x_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__0));
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3___boxed(lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg___lam__3(v_x_299_);
lean_dec_ref(v_x_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg(){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = ((lean_object*)(l_Lake_PackageConfig_extraDepTargets___proj___redArg___closed__4));
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___redArg___boxed(lean_object* v___dummy_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
return v_res_313_;
}
}
static lean_object* _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lake_PackageConfig_extraDepTargets___proj___redArg();
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj(lean_object* v_p_315_, lean_object* v_n_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___proj___boxed(lean_object* v_p_318_, lean_object* v_n_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lake_PackageConfig_extraDepTargets___proj(v_p_318_, v_n_319_);
lean_dec(v_n_319_);
lean_dec(v_p_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg(){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg___boxed(lean_object* v___dummy_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lake_PackageConfig_extraDepTargets_instConfigField___redArg();
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField(lean_object* v_p_325_, lean_object* v_n_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lake_PackageConfig_extraDepTargets___proj___closed__0, &l_Lake_PackageConfig_extraDepTargets___proj___closed__0_once, _init_l_Lake_PackageConfig_extraDepTargets___proj___closed__0);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets_instConfigField___boxed(lean_object* v_p_328_, lean_object* v_n_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lake_PackageConfig_extraDepTargets_instConfigField(v_p_328_, v_n_329_);
lean_dec(v_n_329_);
lean_dec(v_p_328_);
return v_res_330_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(lean_object* v_cfg_331_){
_start:
{
uint8_t v_precompileModules_332_; 
v_precompileModules_332_ = lean_ctor_get_uint8(v_cfg_331_, sizeof(void*)*29 + 1);
return v_precompileModules_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0___boxed(lean_object* v_cfg_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__0(v_cfg_333_);
lean_dec_ref(v_cfg_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(uint8_t v_val_336_, lean_object* v_cfg_337_){
_start:
{
lean_object* v_toWorkspaceConfig_338_; lean_object* v_toLeanConfig_339_; uint8_t v_bootstrap_340_; lean_object* v_extraDepTargets_341_; lean_object* v_moreGlobalServerArgs_342_; lean_object* v_srcDir_343_; lean_object* v_buildDir_344_; lean_object* v_leanLibDir_345_; lean_object* v_nativeLibDir_346_; lean_object* v_binDir_347_; lean_object* v_irDir_348_; lean_object* v_releaseRepo_349_; lean_object* v_buildArchive_350_; uint8_t v_preferReleaseBuild_351_; lean_object* v_downloadCacheService_x3f_352_; lean_object* v_testDriver_353_; lean_object* v_testDriverArgs_354_; lean_object* v_lintDriver_355_; lean_object* v_lintDriverArgs_356_; lean_object* v_version_357_; lean_object* v_versionTags_358_; lean_object* v_description_359_; lean_object* v_keywords_360_; lean_object* v_homepage_361_; lean_object* v_license_362_; lean_object* v_licenseFiles_363_; lean_object* v_readmeFile_364_; uint8_t v_reservoir_365_; lean_object* v_enableArtifactCache_x3f_366_; lean_object* v_restoreAllArtifacts_x3f_367_; uint8_t v_libPrefixOnWindows_368_; uint8_t v_allowImportAll_369_; lean_object* v_builtinLint_x3f_370_; lean_object* v_checks_371_; uint8_t v_fixedToolchain_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_toWorkspaceConfig_338_ = lean_ctor_get(v_cfg_337_, 0);
v_toLeanConfig_339_ = lean_ctor_get(v_cfg_337_, 1);
v_bootstrap_340_ = lean_ctor_get_uint8(v_cfg_337_, sizeof(void*)*29);
v_extraDepTargets_341_ = lean_ctor_get(v_cfg_337_, 2);
v_moreGlobalServerArgs_342_ = lean_ctor_get(v_cfg_337_, 3);
v_srcDir_343_ = lean_ctor_get(v_cfg_337_, 4);
v_buildDir_344_ = lean_ctor_get(v_cfg_337_, 5);
v_leanLibDir_345_ = lean_ctor_get(v_cfg_337_, 6);
v_nativeLibDir_346_ = lean_ctor_get(v_cfg_337_, 7);
v_binDir_347_ = lean_ctor_get(v_cfg_337_, 8);
v_irDir_348_ = lean_ctor_get(v_cfg_337_, 9);
v_releaseRepo_349_ = lean_ctor_get(v_cfg_337_, 10);
v_buildArchive_350_ = lean_ctor_get(v_cfg_337_, 11);
v_preferReleaseBuild_351_ = lean_ctor_get_uint8(v_cfg_337_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_352_ = lean_ctor_get(v_cfg_337_, 12);
v_testDriver_353_ = lean_ctor_get(v_cfg_337_, 13);
v_testDriverArgs_354_ = lean_ctor_get(v_cfg_337_, 14);
v_lintDriver_355_ = lean_ctor_get(v_cfg_337_, 15);
v_lintDriverArgs_356_ = lean_ctor_get(v_cfg_337_, 16);
v_version_357_ = lean_ctor_get(v_cfg_337_, 17);
v_versionTags_358_ = lean_ctor_get(v_cfg_337_, 18);
v_description_359_ = lean_ctor_get(v_cfg_337_, 19);
v_keywords_360_ = lean_ctor_get(v_cfg_337_, 20);
v_homepage_361_ = lean_ctor_get(v_cfg_337_, 21);
v_license_362_ = lean_ctor_get(v_cfg_337_, 22);
v_licenseFiles_363_ = lean_ctor_get(v_cfg_337_, 23);
v_readmeFile_364_ = lean_ctor_get(v_cfg_337_, 24);
v_reservoir_365_ = lean_ctor_get_uint8(v_cfg_337_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_366_ = lean_ctor_get(v_cfg_337_, 25);
v_restoreAllArtifacts_x3f_367_ = lean_ctor_get(v_cfg_337_, 26);
v_libPrefixOnWindows_368_ = lean_ctor_get_uint8(v_cfg_337_, sizeof(void*)*29 + 4);
v_allowImportAll_369_ = lean_ctor_get_uint8(v_cfg_337_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_370_ = lean_ctor_get(v_cfg_337_, 27);
v_checks_371_ = lean_ctor_get(v_cfg_337_, 28);
v_fixedToolchain_372_ = lean_ctor_get_uint8(v_cfg_337_, sizeof(void*)*29 + 6);
v_isSharedCheck_379_ = !lean_is_exclusive(v_cfg_337_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v_cfg_337_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_checks_371_);
lean_inc(v_builtinLint_x3f_370_);
lean_inc(v_restoreAllArtifacts_x3f_367_);
lean_inc(v_enableArtifactCache_x3f_366_);
lean_inc(v_readmeFile_364_);
lean_inc(v_licenseFiles_363_);
lean_inc(v_license_362_);
lean_inc(v_homepage_361_);
lean_inc(v_keywords_360_);
lean_inc(v_description_359_);
lean_inc(v_versionTags_358_);
lean_inc(v_version_357_);
lean_inc(v_lintDriverArgs_356_);
lean_inc(v_lintDriver_355_);
lean_inc(v_testDriverArgs_354_);
lean_inc(v_testDriver_353_);
lean_inc(v_downloadCacheService_x3f_352_);
lean_inc(v_buildArchive_350_);
lean_inc(v_releaseRepo_349_);
lean_inc(v_irDir_348_);
lean_inc(v_binDir_347_);
lean_inc(v_nativeLibDir_346_);
lean_inc(v_leanLibDir_345_);
lean_inc(v_buildDir_344_);
lean_inc(v_srcDir_343_);
lean_inc(v_moreGlobalServerArgs_342_);
lean_inc(v_extraDepTargets_341_);
lean_inc(v_toLeanConfig_339_);
lean_inc(v_toWorkspaceConfig_338_);
lean_dec(v_cfg_337_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_toWorkspaceConfig_338_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_toLeanConfig_339_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_extraDepTargets_341_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_moreGlobalServerArgs_342_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_srcDir_343_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_buildDir_344_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_leanLibDir_345_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v_nativeLibDir_346_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v_binDir_347_);
lean_ctor_set(v_reuseFailAlloc_378_, 9, v_irDir_348_);
lean_ctor_set(v_reuseFailAlloc_378_, 10, v_releaseRepo_349_);
lean_ctor_set(v_reuseFailAlloc_378_, 11, v_buildArchive_350_);
lean_ctor_set(v_reuseFailAlloc_378_, 12, v_downloadCacheService_x3f_352_);
lean_ctor_set(v_reuseFailAlloc_378_, 13, v_testDriver_353_);
lean_ctor_set(v_reuseFailAlloc_378_, 14, v_testDriverArgs_354_);
lean_ctor_set(v_reuseFailAlloc_378_, 15, v_lintDriver_355_);
lean_ctor_set(v_reuseFailAlloc_378_, 16, v_lintDriverArgs_356_);
lean_ctor_set(v_reuseFailAlloc_378_, 17, v_version_357_);
lean_ctor_set(v_reuseFailAlloc_378_, 18, v_versionTags_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 19, v_description_359_);
lean_ctor_set(v_reuseFailAlloc_378_, 20, v_keywords_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 21, v_homepage_361_);
lean_ctor_set(v_reuseFailAlloc_378_, 22, v_license_362_);
lean_ctor_set(v_reuseFailAlloc_378_, 23, v_licenseFiles_363_);
lean_ctor_set(v_reuseFailAlloc_378_, 24, v_readmeFile_364_);
lean_ctor_set(v_reuseFailAlloc_378_, 25, v_enableArtifactCache_x3f_366_);
lean_ctor_set(v_reuseFailAlloc_378_, 26, v_restoreAllArtifacts_x3f_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 27, v_builtinLint_x3f_370_);
lean_ctor_set(v_reuseFailAlloc_378_, 28, v_checks_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*29, v_bootstrap_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*29 + 2, v_preferReleaseBuild_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*29 + 3, v_reservoir_365_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_368_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*29 + 5, v_allowImportAll_369_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*29 + 6, v_fixedToolchain_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*29 + 1, v_val_336_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1___boxed(lean_object* v_val_380_, lean_object* v_cfg_381_){
_start:
{
uint8_t v_val_144__boxed_382_; lean_object* v_res_383_; 
v_val_144__boxed_382_ = lean_unbox(v_val_380_);
v_res_383_ = l_Lake_PackageConfig_precompileModules___proj___redArg___lam__1(v_val_144__boxed_382_, v_cfg_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___lam__2(lean_object* v_f_384_, lean_object* v_cfg_385_){
_start:
{
lean_object* v_toWorkspaceConfig_386_; lean_object* v_toLeanConfig_387_; uint8_t v_bootstrap_388_; lean_object* v_extraDepTargets_389_; uint8_t v_precompileModules_390_; lean_object* v_moreGlobalServerArgs_391_; lean_object* v_srcDir_392_; lean_object* v_buildDir_393_; lean_object* v_leanLibDir_394_; lean_object* v_nativeLibDir_395_; lean_object* v_binDir_396_; lean_object* v_irDir_397_; lean_object* v_releaseRepo_398_; lean_object* v_buildArchive_399_; uint8_t v_preferReleaseBuild_400_; lean_object* v_downloadCacheService_x3f_401_; lean_object* v_testDriver_402_; lean_object* v_testDriverArgs_403_; lean_object* v_lintDriver_404_; lean_object* v_lintDriverArgs_405_; lean_object* v_version_406_; lean_object* v_versionTags_407_; lean_object* v_description_408_; lean_object* v_keywords_409_; lean_object* v_homepage_410_; lean_object* v_license_411_; lean_object* v_licenseFiles_412_; lean_object* v_readmeFile_413_; uint8_t v_reservoir_414_; lean_object* v_enableArtifactCache_x3f_415_; lean_object* v_restoreAllArtifacts_x3f_416_; uint8_t v_libPrefixOnWindows_417_; uint8_t v_allowImportAll_418_; lean_object* v_builtinLint_x3f_419_; lean_object* v_checks_420_; uint8_t v_fixedToolchain_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_toWorkspaceConfig_386_ = lean_ctor_get(v_cfg_385_, 0);
v_toLeanConfig_387_ = lean_ctor_get(v_cfg_385_, 1);
v_bootstrap_388_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29);
v_extraDepTargets_389_ = lean_ctor_get(v_cfg_385_, 2);
v_precompileModules_390_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_391_ = lean_ctor_get(v_cfg_385_, 3);
v_srcDir_392_ = lean_ctor_get(v_cfg_385_, 4);
v_buildDir_393_ = lean_ctor_get(v_cfg_385_, 5);
v_leanLibDir_394_ = lean_ctor_get(v_cfg_385_, 6);
v_nativeLibDir_395_ = lean_ctor_get(v_cfg_385_, 7);
v_binDir_396_ = lean_ctor_get(v_cfg_385_, 8);
v_irDir_397_ = lean_ctor_get(v_cfg_385_, 9);
v_releaseRepo_398_ = lean_ctor_get(v_cfg_385_, 10);
v_buildArchive_399_ = lean_ctor_get(v_cfg_385_, 11);
v_preferReleaseBuild_400_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_401_ = lean_ctor_get(v_cfg_385_, 12);
v_testDriver_402_ = lean_ctor_get(v_cfg_385_, 13);
v_testDriverArgs_403_ = lean_ctor_get(v_cfg_385_, 14);
v_lintDriver_404_ = lean_ctor_get(v_cfg_385_, 15);
v_lintDriverArgs_405_ = lean_ctor_get(v_cfg_385_, 16);
v_version_406_ = lean_ctor_get(v_cfg_385_, 17);
v_versionTags_407_ = lean_ctor_get(v_cfg_385_, 18);
v_description_408_ = lean_ctor_get(v_cfg_385_, 19);
v_keywords_409_ = lean_ctor_get(v_cfg_385_, 20);
v_homepage_410_ = lean_ctor_get(v_cfg_385_, 21);
v_license_411_ = lean_ctor_get(v_cfg_385_, 22);
v_licenseFiles_412_ = lean_ctor_get(v_cfg_385_, 23);
v_readmeFile_413_ = lean_ctor_get(v_cfg_385_, 24);
v_reservoir_414_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_415_ = lean_ctor_get(v_cfg_385_, 25);
v_restoreAllArtifacts_x3f_416_ = lean_ctor_get(v_cfg_385_, 26);
v_libPrefixOnWindows_417_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29 + 4);
v_allowImportAll_418_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_419_ = lean_ctor_get(v_cfg_385_, 27);
v_checks_420_ = lean_ctor_get(v_cfg_385_, 28);
v_fixedToolchain_421_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*29 + 6);
v_isSharedCheck_431_ = !lean_is_exclusive(v_cfg_385_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v_cfg_385_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_checks_420_);
lean_inc(v_builtinLint_x3f_419_);
lean_inc(v_restoreAllArtifacts_x3f_416_);
lean_inc(v_enableArtifactCache_x3f_415_);
lean_inc(v_readmeFile_413_);
lean_inc(v_licenseFiles_412_);
lean_inc(v_license_411_);
lean_inc(v_homepage_410_);
lean_inc(v_keywords_409_);
lean_inc(v_description_408_);
lean_inc(v_versionTags_407_);
lean_inc(v_version_406_);
lean_inc(v_lintDriverArgs_405_);
lean_inc(v_lintDriver_404_);
lean_inc(v_testDriverArgs_403_);
lean_inc(v_testDriver_402_);
lean_inc(v_downloadCacheService_x3f_401_);
lean_inc(v_buildArchive_399_);
lean_inc(v_releaseRepo_398_);
lean_inc(v_irDir_397_);
lean_inc(v_binDir_396_);
lean_inc(v_nativeLibDir_395_);
lean_inc(v_leanLibDir_394_);
lean_inc(v_buildDir_393_);
lean_inc(v_srcDir_392_);
lean_inc(v_moreGlobalServerArgs_391_);
lean_inc(v_extraDepTargets_389_);
lean_inc(v_toLeanConfig_387_);
lean_inc(v_toWorkspaceConfig_386_);
lean_dec(v_cfg_385_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_425_ = lean_box(v_precompileModules_390_);
v___x_426_ = lean_apply_1(v_f_384_, v___x_425_);
if (v_isShared_424_ == 0)
{
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_toWorkspaceConfig_386_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_toLeanConfig_387_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_extraDepTargets_389_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_moreGlobalServerArgs_391_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_srcDir_392_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_buildDir_393_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v_leanLibDir_394_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_nativeLibDir_395_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_binDir_396_);
lean_ctor_set(v_reuseFailAlloc_430_, 9, v_irDir_397_);
lean_ctor_set(v_reuseFailAlloc_430_, 10, v_releaseRepo_398_);
lean_ctor_set(v_reuseFailAlloc_430_, 11, v_buildArchive_399_);
lean_ctor_set(v_reuseFailAlloc_430_, 12, v_downloadCacheService_x3f_401_);
lean_ctor_set(v_reuseFailAlloc_430_, 13, v_testDriver_402_);
lean_ctor_set(v_reuseFailAlloc_430_, 14, v_testDriverArgs_403_);
lean_ctor_set(v_reuseFailAlloc_430_, 15, v_lintDriver_404_);
lean_ctor_set(v_reuseFailAlloc_430_, 16, v_lintDriverArgs_405_);
lean_ctor_set(v_reuseFailAlloc_430_, 17, v_version_406_);
lean_ctor_set(v_reuseFailAlloc_430_, 18, v_versionTags_407_);
lean_ctor_set(v_reuseFailAlloc_430_, 19, v_description_408_);
lean_ctor_set(v_reuseFailAlloc_430_, 20, v_keywords_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 21, v_homepage_410_);
lean_ctor_set(v_reuseFailAlloc_430_, 22, v_license_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 23, v_licenseFiles_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 24, v_readmeFile_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 25, v_enableArtifactCache_x3f_415_);
lean_ctor_set(v_reuseFailAlloc_430_, 26, v_restoreAllArtifacts_x3f_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 27, v_builtinLint_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 28, v_checks_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_430_, sizeof(void*)*29, v_bootstrap_388_);
v___x_428_ = v_reuseFailAlloc_430_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
uint8_t v___x_429_; 
v___x_429_ = lean_unbox(v___x_426_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*29 + 1, v___x_429_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*29 + 2, v_preferReleaseBuild_400_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*29 + 3, v_reservoir_414_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_417_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*29 + 5, v_allowImportAll_418_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*29 + 6, v_fixedToolchain_421_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg(){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = ((lean_object*)(l_Lake_PackageConfig_precompileModules___proj___redArg___closed__3));
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___redArg___boxed(lean_object* v___dummy_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
return v_res_443_;
}
}
static lean_object* _init_l_Lake_PackageConfig_precompileModules___proj___closed__0(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lake_PackageConfig_precompileModules___proj___redArg();
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj(lean_object* v_p_445_, lean_object* v_n_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules___proj___boxed(lean_object* v_p_448_, lean_object* v_n_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lake_PackageConfig_precompileModules___proj(v_p_448_, v_n_449_);
lean_dec(v_n_449_);
lean_dec(v_p_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg(){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___redArg___boxed(lean_object* v___dummy_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lake_PackageConfig_precompileModules_instConfigField___redArg();
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField(lean_object* v_p_455_, lean_object* v_n_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Lake_PackageConfig_precompileModules___proj___closed__0, &l_Lake_PackageConfig_precompileModules___proj___closed__0_once, _init_l_Lake_PackageConfig_precompileModules___proj___closed__0);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_precompileModules_instConfigField___boxed(lean_object* v_p_458_, lean_object* v_n_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lake_PackageConfig_precompileModules_instConfigField(v_p_458_, v_n_459_);
lean_dec(v_n_459_);
lean_dec(v_p_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(lean_object* v_cfg_461_){
_start:
{
lean_object* v_moreGlobalServerArgs_462_; 
v_moreGlobalServerArgs_462_ = lean_ctor_get(v_cfg_461_, 3);
lean_inc_ref(v_moreGlobalServerArgs_462_);
return v_moreGlobalServerArgs_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__0(v_cfg_463_);
lean_dec_ref(v_cfg_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__1(lean_object* v_val_465_, lean_object* v_cfg_466_){
_start:
{
lean_object* v_toWorkspaceConfig_467_; lean_object* v_toLeanConfig_468_; uint8_t v_bootstrap_469_; lean_object* v_extraDepTargets_470_; uint8_t v_precompileModules_471_; lean_object* v_srcDir_472_; lean_object* v_buildDir_473_; lean_object* v_leanLibDir_474_; lean_object* v_nativeLibDir_475_; lean_object* v_binDir_476_; lean_object* v_irDir_477_; lean_object* v_releaseRepo_478_; lean_object* v_buildArchive_479_; uint8_t v_preferReleaseBuild_480_; lean_object* v_downloadCacheService_x3f_481_; lean_object* v_testDriver_482_; lean_object* v_testDriverArgs_483_; lean_object* v_lintDriver_484_; lean_object* v_lintDriverArgs_485_; lean_object* v_version_486_; lean_object* v_versionTags_487_; lean_object* v_description_488_; lean_object* v_keywords_489_; lean_object* v_homepage_490_; lean_object* v_license_491_; lean_object* v_licenseFiles_492_; lean_object* v_readmeFile_493_; uint8_t v_reservoir_494_; lean_object* v_enableArtifactCache_x3f_495_; lean_object* v_restoreAllArtifacts_x3f_496_; uint8_t v_libPrefixOnWindows_497_; uint8_t v_allowImportAll_498_; lean_object* v_builtinLint_x3f_499_; lean_object* v_checks_500_; uint8_t v_fixedToolchain_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_toWorkspaceConfig_467_ = lean_ctor_get(v_cfg_466_, 0);
v_toLeanConfig_468_ = lean_ctor_get(v_cfg_466_, 1);
v_bootstrap_469_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29);
v_extraDepTargets_470_ = lean_ctor_get(v_cfg_466_, 2);
v_precompileModules_471_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29 + 1);
v_srcDir_472_ = lean_ctor_get(v_cfg_466_, 4);
v_buildDir_473_ = lean_ctor_get(v_cfg_466_, 5);
v_leanLibDir_474_ = lean_ctor_get(v_cfg_466_, 6);
v_nativeLibDir_475_ = lean_ctor_get(v_cfg_466_, 7);
v_binDir_476_ = lean_ctor_get(v_cfg_466_, 8);
v_irDir_477_ = lean_ctor_get(v_cfg_466_, 9);
v_releaseRepo_478_ = lean_ctor_get(v_cfg_466_, 10);
v_buildArchive_479_ = lean_ctor_get(v_cfg_466_, 11);
v_preferReleaseBuild_480_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_481_ = lean_ctor_get(v_cfg_466_, 12);
v_testDriver_482_ = lean_ctor_get(v_cfg_466_, 13);
v_testDriverArgs_483_ = lean_ctor_get(v_cfg_466_, 14);
v_lintDriver_484_ = lean_ctor_get(v_cfg_466_, 15);
v_lintDriverArgs_485_ = lean_ctor_get(v_cfg_466_, 16);
v_version_486_ = lean_ctor_get(v_cfg_466_, 17);
v_versionTags_487_ = lean_ctor_get(v_cfg_466_, 18);
v_description_488_ = lean_ctor_get(v_cfg_466_, 19);
v_keywords_489_ = lean_ctor_get(v_cfg_466_, 20);
v_homepage_490_ = lean_ctor_get(v_cfg_466_, 21);
v_license_491_ = lean_ctor_get(v_cfg_466_, 22);
v_licenseFiles_492_ = lean_ctor_get(v_cfg_466_, 23);
v_readmeFile_493_ = lean_ctor_get(v_cfg_466_, 24);
v_reservoir_494_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_495_ = lean_ctor_get(v_cfg_466_, 25);
v_restoreAllArtifacts_x3f_496_ = lean_ctor_get(v_cfg_466_, 26);
v_libPrefixOnWindows_497_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29 + 4);
v_allowImportAll_498_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_499_ = lean_ctor_get(v_cfg_466_, 27);
v_checks_500_ = lean_ctor_get(v_cfg_466_, 28);
v_fixedToolchain_501_ = lean_ctor_get_uint8(v_cfg_466_, sizeof(void*)*29 + 6);
v_isSharedCheck_508_ = !lean_is_exclusive(v_cfg_466_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_cfg_466_, 3);
lean_dec(v_unused_509_);
v___x_503_ = v_cfg_466_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_checks_500_);
lean_inc(v_builtinLint_x3f_499_);
lean_inc(v_restoreAllArtifacts_x3f_496_);
lean_inc(v_enableArtifactCache_x3f_495_);
lean_inc(v_readmeFile_493_);
lean_inc(v_licenseFiles_492_);
lean_inc(v_license_491_);
lean_inc(v_homepage_490_);
lean_inc(v_keywords_489_);
lean_inc(v_description_488_);
lean_inc(v_versionTags_487_);
lean_inc(v_version_486_);
lean_inc(v_lintDriverArgs_485_);
lean_inc(v_lintDriver_484_);
lean_inc(v_testDriverArgs_483_);
lean_inc(v_testDriver_482_);
lean_inc(v_downloadCacheService_x3f_481_);
lean_inc(v_buildArchive_479_);
lean_inc(v_releaseRepo_478_);
lean_inc(v_irDir_477_);
lean_inc(v_binDir_476_);
lean_inc(v_nativeLibDir_475_);
lean_inc(v_leanLibDir_474_);
lean_inc(v_buildDir_473_);
lean_inc(v_srcDir_472_);
lean_inc(v_extraDepTargets_470_);
lean_inc(v_toLeanConfig_468_);
lean_inc(v_toWorkspaceConfig_467_);
lean_dec(v_cfg_466_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_val_465_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_toWorkspaceConfig_467_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_toLeanConfig_468_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_extraDepTargets_470_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_val_465_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_srcDir_472_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v_buildDir_473_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_leanLibDir_474_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v_nativeLibDir_475_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v_binDir_476_);
lean_ctor_set(v_reuseFailAlloc_507_, 9, v_irDir_477_);
lean_ctor_set(v_reuseFailAlloc_507_, 10, v_releaseRepo_478_);
lean_ctor_set(v_reuseFailAlloc_507_, 11, v_buildArchive_479_);
lean_ctor_set(v_reuseFailAlloc_507_, 12, v_downloadCacheService_x3f_481_);
lean_ctor_set(v_reuseFailAlloc_507_, 13, v_testDriver_482_);
lean_ctor_set(v_reuseFailAlloc_507_, 14, v_testDriverArgs_483_);
lean_ctor_set(v_reuseFailAlloc_507_, 15, v_lintDriver_484_);
lean_ctor_set(v_reuseFailAlloc_507_, 16, v_lintDriverArgs_485_);
lean_ctor_set(v_reuseFailAlloc_507_, 17, v_version_486_);
lean_ctor_set(v_reuseFailAlloc_507_, 18, v_versionTags_487_);
lean_ctor_set(v_reuseFailAlloc_507_, 19, v_description_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 20, v_keywords_489_);
lean_ctor_set(v_reuseFailAlloc_507_, 21, v_homepage_490_);
lean_ctor_set(v_reuseFailAlloc_507_, 22, v_license_491_);
lean_ctor_set(v_reuseFailAlloc_507_, 23, v_licenseFiles_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 24, v_readmeFile_493_);
lean_ctor_set(v_reuseFailAlloc_507_, 25, v_enableArtifactCache_x3f_495_);
lean_ctor_set(v_reuseFailAlloc_507_, 26, v_restoreAllArtifacts_x3f_496_);
lean_ctor_set(v_reuseFailAlloc_507_, 27, v_builtinLint_x3f_499_);
lean_ctor_set(v_reuseFailAlloc_507_, 28, v_checks_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29, v_bootstrap_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29 + 1, v_precompileModules_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29 + 2, v_preferReleaseBuild_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29 + 3, v_reservoir_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29 + 5, v_allowImportAll_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*29 + 6, v_fixedToolchain_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__2(lean_object* v_f_510_, lean_object* v_cfg_511_){
_start:
{
lean_object* v_toWorkspaceConfig_512_; lean_object* v_toLeanConfig_513_; uint8_t v_bootstrap_514_; lean_object* v_extraDepTargets_515_; uint8_t v_precompileModules_516_; lean_object* v_moreGlobalServerArgs_517_; lean_object* v_srcDir_518_; lean_object* v_buildDir_519_; lean_object* v_leanLibDir_520_; lean_object* v_nativeLibDir_521_; lean_object* v_binDir_522_; lean_object* v_irDir_523_; lean_object* v_releaseRepo_524_; lean_object* v_buildArchive_525_; uint8_t v_preferReleaseBuild_526_; lean_object* v_downloadCacheService_x3f_527_; lean_object* v_testDriver_528_; lean_object* v_testDriverArgs_529_; lean_object* v_lintDriver_530_; lean_object* v_lintDriverArgs_531_; lean_object* v_version_532_; lean_object* v_versionTags_533_; lean_object* v_description_534_; lean_object* v_keywords_535_; lean_object* v_homepage_536_; lean_object* v_license_537_; lean_object* v_licenseFiles_538_; lean_object* v_readmeFile_539_; uint8_t v_reservoir_540_; lean_object* v_enableArtifactCache_x3f_541_; lean_object* v_restoreAllArtifacts_x3f_542_; uint8_t v_libPrefixOnWindows_543_; uint8_t v_allowImportAll_544_; lean_object* v_builtinLint_x3f_545_; lean_object* v_checks_546_; uint8_t v_fixedToolchain_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_toWorkspaceConfig_512_ = lean_ctor_get(v_cfg_511_, 0);
v_toLeanConfig_513_ = lean_ctor_get(v_cfg_511_, 1);
v_bootstrap_514_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29);
v_extraDepTargets_515_ = lean_ctor_get(v_cfg_511_, 2);
v_precompileModules_516_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_517_ = lean_ctor_get(v_cfg_511_, 3);
v_srcDir_518_ = lean_ctor_get(v_cfg_511_, 4);
v_buildDir_519_ = lean_ctor_get(v_cfg_511_, 5);
v_leanLibDir_520_ = lean_ctor_get(v_cfg_511_, 6);
v_nativeLibDir_521_ = lean_ctor_get(v_cfg_511_, 7);
v_binDir_522_ = lean_ctor_get(v_cfg_511_, 8);
v_irDir_523_ = lean_ctor_get(v_cfg_511_, 9);
v_releaseRepo_524_ = lean_ctor_get(v_cfg_511_, 10);
v_buildArchive_525_ = lean_ctor_get(v_cfg_511_, 11);
v_preferReleaseBuild_526_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_527_ = lean_ctor_get(v_cfg_511_, 12);
v_testDriver_528_ = lean_ctor_get(v_cfg_511_, 13);
v_testDriverArgs_529_ = lean_ctor_get(v_cfg_511_, 14);
v_lintDriver_530_ = lean_ctor_get(v_cfg_511_, 15);
v_lintDriverArgs_531_ = lean_ctor_get(v_cfg_511_, 16);
v_version_532_ = lean_ctor_get(v_cfg_511_, 17);
v_versionTags_533_ = lean_ctor_get(v_cfg_511_, 18);
v_description_534_ = lean_ctor_get(v_cfg_511_, 19);
v_keywords_535_ = lean_ctor_get(v_cfg_511_, 20);
v_homepage_536_ = lean_ctor_get(v_cfg_511_, 21);
v_license_537_ = lean_ctor_get(v_cfg_511_, 22);
v_licenseFiles_538_ = lean_ctor_get(v_cfg_511_, 23);
v_readmeFile_539_ = lean_ctor_get(v_cfg_511_, 24);
v_reservoir_540_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_541_ = lean_ctor_get(v_cfg_511_, 25);
v_restoreAllArtifacts_x3f_542_ = lean_ctor_get(v_cfg_511_, 26);
v_libPrefixOnWindows_543_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29 + 4);
v_allowImportAll_544_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_545_ = lean_ctor_get(v_cfg_511_, 27);
v_checks_546_ = lean_ctor_get(v_cfg_511_, 28);
v_fixedToolchain_547_ = lean_ctor_get_uint8(v_cfg_511_, sizeof(void*)*29 + 6);
v_isSharedCheck_555_ = !lean_is_exclusive(v_cfg_511_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v_cfg_511_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_checks_546_);
lean_inc(v_builtinLint_x3f_545_);
lean_inc(v_restoreAllArtifacts_x3f_542_);
lean_inc(v_enableArtifactCache_x3f_541_);
lean_inc(v_readmeFile_539_);
lean_inc(v_licenseFiles_538_);
lean_inc(v_license_537_);
lean_inc(v_homepage_536_);
lean_inc(v_keywords_535_);
lean_inc(v_description_534_);
lean_inc(v_versionTags_533_);
lean_inc(v_version_532_);
lean_inc(v_lintDriverArgs_531_);
lean_inc(v_lintDriver_530_);
lean_inc(v_testDriverArgs_529_);
lean_inc(v_testDriver_528_);
lean_inc(v_downloadCacheService_x3f_527_);
lean_inc(v_buildArchive_525_);
lean_inc(v_releaseRepo_524_);
lean_inc(v_irDir_523_);
lean_inc(v_binDir_522_);
lean_inc(v_nativeLibDir_521_);
lean_inc(v_leanLibDir_520_);
lean_inc(v_buildDir_519_);
lean_inc(v_srcDir_518_);
lean_inc(v_moreGlobalServerArgs_517_);
lean_inc(v_extraDepTargets_515_);
lean_inc(v_toLeanConfig_513_);
lean_inc(v_toWorkspaceConfig_512_);
lean_dec(v_cfg_511_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_apply_1(v_f_510_, v_moreGlobalServerArgs_517_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 3, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_toWorkspaceConfig_512_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_toLeanConfig_513_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_extraDepTargets_515_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_srcDir_518_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_buildDir_519_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_leanLibDir_520_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v_nativeLibDir_521_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_binDir_522_);
lean_ctor_set(v_reuseFailAlloc_554_, 9, v_irDir_523_);
lean_ctor_set(v_reuseFailAlloc_554_, 10, v_releaseRepo_524_);
lean_ctor_set(v_reuseFailAlloc_554_, 11, v_buildArchive_525_);
lean_ctor_set(v_reuseFailAlloc_554_, 12, v_downloadCacheService_x3f_527_);
lean_ctor_set(v_reuseFailAlloc_554_, 13, v_testDriver_528_);
lean_ctor_set(v_reuseFailAlloc_554_, 14, v_testDriverArgs_529_);
lean_ctor_set(v_reuseFailAlloc_554_, 15, v_lintDriver_530_);
lean_ctor_set(v_reuseFailAlloc_554_, 16, v_lintDriverArgs_531_);
lean_ctor_set(v_reuseFailAlloc_554_, 17, v_version_532_);
lean_ctor_set(v_reuseFailAlloc_554_, 18, v_versionTags_533_);
lean_ctor_set(v_reuseFailAlloc_554_, 19, v_description_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 20, v_keywords_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 21, v_homepage_536_);
lean_ctor_set(v_reuseFailAlloc_554_, 22, v_license_537_);
lean_ctor_set(v_reuseFailAlloc_554_, 23, v_licenseFiles_538_);
lean_ctor_set(v_reuseFailAlloc_554_, 24, v_readmeFile_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 25, v_enableArtifactCache_x3f_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 26, v_restoreAllArtifacts_x3f_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 27, v_builtinLint_x3f_545_);
lean_ctor_set(v_reuseFailAlloc_554_, 28, v_checks_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29, v_bootstrap_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29 + 1, v_precompileModules_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29 + 2, v_preferReleaseBuild_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29 + 3, v_reservoir_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29 + 5, v_allowImportAll_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*29 + 6, v_fixedToolchain_547_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___closed__0));
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3___boxed(lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___lam__3(v_x_560_);
lean_dec_ref(v_x_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg(){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___closed__4));
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg___boxed(lean_object* v___dummy_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
return v_res_574_;
}
}
static lean_object* _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj___redArg();
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj(lean_object* v_p_576_, lean_object* v_n_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___proj___boxed(lean_object* v_p_579_, lean_object* v_n_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lake_PackageConfig_moreGlobalServerArgs___proj(v_p_579_, v_n_580_);
lean_dec(v_n_580_);
lean_dec(v_p_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg___boxed(lean_object* v___dummy_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___redArg();
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(lean_object* v_p_586_, lean_object* v_n_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField___boxed(lean_object* v_p_589_, lean_object* v_n_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lake_PackageConfig_moreGlobalServerArgs_instConfigField(v_p_589_, v_n_590_);
lean_dec(v_n_590_);
lean_dec(v_p_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg___boxed(lean_object* v___dummy_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lake_PackageConfig_moreServerArgs_instConfigField___redArg();
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField(lean_object* v_p_596_, lean_object* v_n_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0, &l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_moreGlobalServerArgs___proj___closed__0);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs_instConfigField___boxed(lean_object* v_p_599_, lean_object* v_n_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lake_PackageConfig_moreServerArgs_instConfigField(v_p_599_, v_n_600_);
lean_dec(v_n_600_);
lean_dec(v_p_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(lean_object* v_cfg_602_){
_start:
{
lean_object* v_srcDir_603_; 
v_srcDir_603_ = lean_ctor_get(v_cfg_602_, 4);
lean_inc_ref(v_srcDir_603_);
return v_srcDir_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lake_PackageConfig_srcDir___proj___redArg___lam__0(v_cfg_604_);
lean_dec_ref(v_cfg_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__1(lean_object* v_val_606_, lean_object* v_cfg_607_){
_start:
{
lean_object* v_toWorkspaceConfig_608_; lean_object* v_toLeanConfig_609_; uint8_t v_bootstrap_610_; lean_object* v_extraDepTargets_611_; uint8_t v_precompileModules_612_; lean_object* v_moreGlobalServerArgs_613_; lean_object* v_buildDir_614_; lean_object* v_leanLibDir_615_; lean_object* v_nativeLibDir_616_; lean_object* v_binDir_617_; lean_object* v_irDir_618_; lean_object* v_releaseRepo_619_; lean_object* v_buildArchive_620_; uint8_t v_preferReleaseBuild_621_; lean_object* v_downloadCacheService_x3f_622_; lean_object* v_testDriver_623_; lean_object* v_testDriverArgs_624_; lean_object* v_lintDriver_625_; lean_object* v_lintDriverArgs_626_; lean_object* v_version_627_; lean_object* v_versionTags_628_; lean_object* v_description_629_; lean_object* v_keywords_630_; lean_object* v_homepage_631_; lean_object* v_license_632_; lean_object* v_licenseFiles_633_; lean_object* v_readmeFile_634_; uint8_t v_reservoir_635_; lean_object* v_enableArtifactCache_x3f_636_; lean_object* v_restoreAllArtifacts_x3f_637_; uint8_t v_libPrefixOnWindows_638_; uint8_t v_allowImportAll_639_; lean_object* v_builtinLint_x3f_640_; lean_object* v_checks_641_; uint8_t v_fixedToolchain_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_toWorkspaceConfig_608_ = lean_ctor_get(v_cfg_607_, 0);
v_toLeanConfig_609_ = lean_ctor_get(v_cfg_607_, 1);
v_bootstrap_610_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29);
v_extraDepTargets_611_ = lean_ctor_get(v_cfg_607_, 2);
v_precompileModules_612_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_613_ = lean_ctor_get(v_cfg_607_, 3);
v_buildDir_614_ = lean_ctor_get(v_cfg_607_, 5);
v_leanLibDir_615_ = lean_ctor_get(v_cfg_607_, 6);
v_nativeLibDir_616_ = lean_ctor_get(v_cfg_607_, 7);
v_binDir_617_ = lean_ctor_get(v_cfg_607_, 8);
v_irDir_618_ = lean_ctor_get(v_cfg_607_, 9);
v_releaseRepo_619_ = lean_ctor_get(v_cfg_607_, 10);
v_buildArchive_620_ = lean_ctor_get(v_cfg_607_, 11);
v_preferReleaseBuild_621_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_622_ = lean_ctor_get(v_cfg_607_, 12);
v_testDriver_623_ = lean_ctor_get(v_cfg_607_, 13);
v_testDriverArgs_624_ = lean_ctor_get(v_cfg_607_, 14);
v_lintDriver_625_ = lean_ctor_get(v_cfg_607_, 15);
v_lintDriverArgs_626_ = lean_ctor_get(v_cfg_607_, 16);
v_version_627_ = lean_ctor_get(v_cfg_607_, 17);
v_versionTags_628_ = lean_ctor_get(v_cfg_607_, 18);
v_description_629_ = lean_ctor_get(v_cfg_607_, 19);
v_keywords_630_ = lean_ctor_get(v_cfg_607_, 20);
v_homepage_631_ = lean_ctor_get(v_cfg_607_, 21);
v_license_632_ = lean_ctor_get(v_cfg_607_, 22);
v_licenseFiles_633_ = lean_ctor_get(v_cfg_607_, 23);
v_readmeFile_634_ = lean_ctor_get(v_cfg_607_, 24);
v_reservoir_635_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_636_ = lean_ctor_get(v_cfg_607_, 25);
v_restoreAllArtifacts_x3f_637_ = lean_ctor_get(v_cfg_607_, 26);
v_libPrefixOnWindows_638_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29 + 4);
v_allowImportAll_639_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_640_ = lean_ctor_get(v_cfg_607_, 27);
v_checks_641_ = lean_ctor_get(v_cfg_607_, 28);
v_fixedToolchain_642_ = lean_ctor_get_uint8(v_cfg_607_, sizeof(void*)*29 + 6);
v_isSharedCheck_649_ = !lean_is_exclusive(v_cfg_607_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_cfg_607_, 4);
lean_dec(v_unused_650_);
v___x_644_ = v_cfg_607_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_checks_641_);
lean_inc(v_builtinLint_x3f_640_);
lean_inc(v_restoreAllArtifacts_x3f_637_);
lean_inc(v_enableArtifactCache_x3f_636_);
lean_inc(v_readmeFile_634_);
lean_inc(v_licenseFiles_633_);
lean_inc(v_license_632_);
lean_inc(v_homepage_631_);
lean_inc(v_keywords_630_);
lean_inc(v_description_629_);
lean_inc(v_versionTags_628_);
lean_inc(v_version_627_);
lean_inc(v_lintDriverArgs_626_);
lean_inc(v_lintDriver_625_);
lean_inc(v_testDriverArgs_624_);
lean_inc(v_testDriver_623_);
lean_inc(v_downloadCacheService_x3f_622_);
lean_inc(v_buildArchive_620_);
lean_inc(v_releaseRepo_619_);
lean_inc(v_irDir_618_);
lean_inc(v_binDir_617_);
lean_inc(v_nativeLibDir_616_);
lean_inc(v_leanLibDir_615_);
lean_inc(v_buildDir_614_);
lean_inc(v_moreGlobalServerArgs_613_);
lean_inc(v_extraDepTargets_611_);
lean_inc(v_toLeanConfig_609_);
lean_inc(v_toWorkspaceConfig_608_);
lean_dec(v_cfg_607_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 4, v_val_606_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_toWorkspaceConfig_608_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_toLeanConfig_609_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_extraDepTargets_611_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_moreGlobalServerArgs_613_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_val_606_);
lean_ctor_set(v_reuseFailAlloc_648_, 5, v_buildDir_614_);
lean_ctor_set(v_reuseFailAlloc_648_, 6, v_leanLibDir_615_);
lean_ctor_set(v_reuseFailAlloc_648_, 7, v_nativeLibDir_616_);
lean_ctor_set(v_reuseFailAlloc_648_, 8, v_binDir_617_);
lean_ctor_set(v_reuseFailAlloc_648_, 9, v_irDir_618_);
lean_ctor_set(v_reuseFailAlloc_648_, 10, v_releaseRepo_619_);
lean_ctor_set(v_reuseFailAlloc_648_, 11, v_buildArchive_620_);
lean_ctor_set(v_reuseFailAlloc_648_, 12, v_downloadCacheService_x3f_622_);
lean_ctor_set(v_reuseFailAlloc_648_, 13, v_testDriver_623_);
lean_ctor_set(v_reuseFailAlloc_648_, 14, v_testDriverArgs_624_);
lean_ctor_set(v_reuseFailAlloc_648_, 15, v_lintDriver_625_);
lean_ctor_set(v_reuseFailAlloc_648_, 16, v_lintDriverArgs_626_);
lean_ctor_set(v_reuseFailAlloc_648_, 17, v_version_627_);
lean_ctor_set(v_reuseFailAlloc_648_, 18, v_versionTags_628_);
lean_ctor_set(v_reuseFailAlloc_648_, 19, v_description_629_);
lean_ctor_set(v_reuseFailAlloc_648_, 20, v_keywords_630_);
lean_ctor_set(v_reuseFailAlloc_648_, 21, v_homepage_631_);
lean_ctor_set(v_reuseFailAlloc_648_, 22, v_license_632_);
lean_ctor_set(v_reuseFailAlloc_648_, 23, v_licenseFiles_633_);
lean_ctor_set(v_reuseFailAlloc_648_, 24, v_readmeFile_634_);
lean_ctor_set(v_reuseFailAlloc_648_, 25, v_enableArtifactCache_x3f_636_);
lean_ctor_set(v_reuseFailAlloc_648_, 26, v_restoreAllArtifacts_x3f_637_);
lean_ctor_set(v_reuseFailAlloc_648_, 27, v_builtinLint_x3f_640_);
lean_ctor_set(v_reuseFailAlloc_648_, 28, v_checks_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29, v_bootstrap_610_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29 + 1, v_precompileModules_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29 + 2, v_preferReleaseBuild_621_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29 + 3, v_reservoir_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29 + 5, v_allowImportAll_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_648_, sizeof(void*)*29 + 6, v_fixedToolchain_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__2(lean_object* v_f_651_, lean_object* v_cfg_652_){
_start:
{
lean_object* v_toWorkspaceConfig_653_; lean_object* v_toLeanConfig_654_; uint8_t v_bootstrap_655_; lean_object* v_extraDepTargets_656_; uint8_t v_precompileModules_657_; lean_object* v_moreGlobalServerArgs_658_; lean_object* v_srcDir_659_; lean_object* v_buildDir_660_; lean_object* v_leanLibDir_661_; lean_object* v_nativeLibDir_662_; lean_object* v_binDir_663_; lean_object* v_irDir_664_; lean_object* v_releaseRepo_665_; lean_object* v_buildArchive_666_; uint8_t v_preferReleaseBuild_667_; lean_object* v_downloadCacheService_x3f_668_; lean_object* v_testDriver_669_; lean_object* v_testDriverArgs_670_; lean_object* v_lintDriver_671_; lean_object* v_lintDriverArgs_672_; lean_object* v_version_673_; lean_object* v_versionTags_674_; lean_object* v_description_675_; lean_object* v_keywords_676_; lean_object* v_homepage_677_; lean_object* v_license_678_; lean_object* v_licenseFiles_679_; lean_object* v_readmeFile_680_; uint8_t v_reservoir_681_; lean_object* v_enableArtifactCache_x3f_682_; lean_object* v_restoreAllArtifacts_x3f_683_; uint8_t v_libPrefixOnWindows_684_; uint8_t v_allowImportAll_685_; lean_object* v_builtinLint_x3f_686_; lean_object* v_checks_687_; uint8_t v_fixedToolchain_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_toWorkspaceConfig_653_ = lean_ctor_get(v_cfg_652_, 0);
v_toLeanConfig_654_ = lean_ctor_get(v_cfg_652_, 1);
v_bootstrap_655_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29);
v_extraDepTargets_656_ = lean_ctor_get(v_cfg_652_, 2);
v_precompileModules_657_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_658_ = lean_ctor_get(v_cfg_652_, 3);
v_srcDir_659_ = lean_ctor_get(v_cfg_652_, 4);
v_buildDir_660_ = lean_ctor_get(v_cfg_652_, 5);
v_leanLibDir_661_ = lean_ctor_get(v_cfg_652_, 6);
v_nativeLibDir_662_ = lean_ctor_get(v_cfg_652_, 7);
v_binDir_663_ = lean_ctor_get(v_cfg_652_, 8);
v_irDir_664_ = lean_ctor_get(v_cfg_652_, 9);
v_releaseRepo_665_ = lean_ctor_get(v_cfg_652_, 10);
v_buildArchive_666_ = lean_ctor_get(v_cfg_652_, 11);
v_preferReleaseBuild_667_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_668_ = lean_ctor_get(v_cfg_652_, 12);
v_testDriver_669_ = lean_ctor_get(v_cfg_652_, 13);
v_testDriverArgs_670_ = lean_ctor_get(v_cfg_652_, 14);
v_lintDriver_671_ = lean_ctor_get(v_cfg_652_, 15);
v_lintDriverArgs_672_ = lean_ctor_get(v_cfg_652_, 16);
v_version_673_ = lean_ctor_get(v_cfg_652_, 17);
v_versionTags_674_ = lean_ctor_get(v_cfg_652_, 18);
v_description_675_ = lean_ctor_get(v_cfg_652_, 19);
v_keywords_676_ = lean_ctor_get(v_cfg_652_, 20);
v_homepage_677_ = lean_ctor_get(v_cfg_652_, 21);
v_license_678_ = lean_ctor_get(v_cfg_652_, 22);
v_licenseFiles_679_ = lean_ctor_get(v_cfg_652_, 23);
v_readmeFile_680_ = lean_ctor_get(v_cfg_652_, 24);
v_reservoir_681_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_682_ = lean_ctor_get(v_cfg_652_, 25);
v_restoreAllArtifacts_x3f_683_ = lean_ctor_get(v_cfg_652_, 26);
v_libPrefixOnWindows_684_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29 + 4);
v_allowImportAll_685_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_686_ = lean_ctor_get(v_cfg_652_, 27);
v_checks_687_ = lean_ctor_get(v_cfg_652_, 28);
v_fixedToolchain_688_ = lean_ctor_get_uint8(v_cfg_652_, sizeof(void*)*29 + 6);
v_isSharedCheck_696_ = !lean_is_exclusive(v_cfg_652_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v_cfg_652_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_checks_687_);
lean_inc(v_builtinLint_x3f_686_);
lean_inc(v_restoreAllArtifacts_x3f_683_);
lean_inc(v_enableArtifactCache_x3f_682_);
lean_inc(v_readmeFile_680_);
lean_inc(v_licenseFiles_679_);
lean_inc(v_license_678_);
lean_inc(v_homepage_677_);
lean_inc(v_keywords_676_);
lean_inc(v_description_675_);
lean_inc(v_versionTags_674_);
lean_inc(v_version_673_);
lean_inc(v_lintDriverArgs_672_);
lean_inc(v_lintDriver_671_);
lean_inc(v_testDriverArgs_670_);
lean_inc(v_testDriver_669_);
lean_inc(v_downloadCacheService_x3f_668_);
lean_inc(v_buildArchive_666_);
lean_inc(v_releaseRepo_665_);
lean_inc(v_irDir_664_);
lean_inc(v_binDir_663_);
lean_inc(v_nativeLibDir_662_);
lean_inc(v_leanLibDir_661_);
lean_inc(v_buildDir_660_);
lean_inc(v_srcDir_659_);
lean_inc(v_moreGlobalServerArgs_658_);
lean_inc(v_extraDepTargets_656_);
lean_inc(v_toLeanConfig_654_);
lean_inc(v_toWorkspaceConfig_653_);
lean_dec(v_cfg_652_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_apply_1(v_f_651_, v_srcDir_659_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_toWorkspaceConfig_653_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_toLeanConfig_654_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_extraDepTargets_656_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_moreGlobalServerArgs_658_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v_buildDir_660_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_leanLibDir_661_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_nativeLibDir_662_);
lean_ctor_set(v_reuseFailAlloc_695_, 8, v_binDir_663_);
lean_ctor_set(v_reuseFailAlloc_695_, 9, v_irDir_664_);
lean_ctor_set(v_reuseFailAlloc_695_, 10, v_releaseRepo_665_);
lean_ctor_set(v_reuseFailAlloc_695_, 11, v_buildArchive_666_);
lean_ctor_set(v_reuseFailAlloc_695_, 12, v_downloadCacheService_x3f_668_);
lean_ctor_set(v_reuseFailAlloc_695_, 13, v_testDriver_669_);
lean_ctor_set(v_reuseFailAlloc_695_, 14, v_testDriverArgs_670_);
lean_ctor_set(v_reuseFailAlloc_695_, 15, v_lintDriver_671_);
lean_ctor_set(v_reuseFailAlloc_695_, 16, v_lintDriverArgs_672_);
lean_ctor_set(v_reuseFailAlloc_695_, 17, v_version_673_);
lean_ctor_set(v_reuseFailAlloc_695_, 18, v_versionTags_674_);
lean_ctor_set(v_reuseFailAlloc_695_, 19, v_description_675_);
lean_ctor_set(v_reuseFailAlloc_695_, 20, v_keywords_676_);
lean_ctor_set(v_reuseFailAlloc_695_, 21, v_homepage_677_);
lean_ctor_set(v_reuseFailAlloc_695_, 22, v_license_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 23, v_licenseFiles_679_);
lean_ctor_set(v_reuseFailAlloc_695_, 24, v_readmeFile_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 25, v_enableArtifactCache_x3f_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 26, v_restoreAllArtifacts_x3f_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 27, v_builtinLint_x3f_686_);
lean_ctor_set(v_reuseFailAlloc_695_, 28, v_checks_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29, v_bootstrap_655_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29 + 1, v_precompileModules_657_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29 + 2, v_preferReleaseBuild_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29 + 3, v_reservoir_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29 + 5, v_allowImportAll_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*29 + 6, v_fixedToolchain_688_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___lam__3___boxed(lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_PackageConfig_srcDir___proj___redArg___lam__3(v_x_699_);
lean_dec_ref(v_x_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg(){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = ((lean_object*)(l_Lake_PackageConfig_srcDir___proj___redArg___closed__4));
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___redArg___boxed(lean_object* v___dummy_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lake_PackageConfig_srcDir___proj___redArg();
return v_res_713_;
}
}
static lean_object* _init_l_Lake_PackageConfig_srcDir___proj___closed__0(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lake_PackageConfig_srcDir___proj___redArg();
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj(lean_object* v_p_715_, lean_object* v_n_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___proj___boxed(lean_object* v_p_718_, lean_object* v_n_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lake_PackageConfig_srcDir___proj(v_p_718_, v_n_719_);
lean_dec(v_n_719_);
lean_dec(v_p_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___redArg___boxed(lean_object* v___dummy_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lake_PackageConfig_srcDir_instConfigField___redArg();
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField(lean_object* v_p_725_, lean_object* v_n_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Lake_PackageConfig_srcDir___proj___closed__0, &l_Lake_PackageConfig_srcDir___proj___closed__0_once, _init_l_Lake_PackageConfig_srcDir___proj___closed__0);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir_instConfigField___boxed(lean_object* v_p_728_, lean_object* v_n_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lake_PackageConfig_srcDir_instConfigField(v_p_728_, v_n_729_);
lean_dec(v_n_729_);
lean_dec(v_p_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(lean_object* v_cfg_731_){
_start:
{
lean_object* v_buildDir_732_; 
v_buildDir_732_ = lean_ctor_get(v_cfg_731_, 5);
lean_inc_ref(v_buildDir_732_);
return v_buildDir_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lake_PackageConfig_buildDir___proj___redArg___lam__0(v_cfg_733_);
lean_dec_ref(v_cfg_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__1(lean_object* v_val_735_, lean_object* v_cfg_736_){
_start:
{
lean_object* v_toWorkspaceConfig_737_; lean_object* v_toLeanConfig_738_; uint8_t v_bootstrap_739_; lean_object* v_extraDepTargets_740_; uint8_t v_precompileModules_741_; lean_object* v_moreGlobalServerArgs_742_; lean_object* v_srcDir_743_; lean_object* v_leanLibDir_744_; lean_object* v_nativeLibDir_745_; lean_object* v_binDir_746_; lean_object* v_irDir_747_; lean_object* v_releaseRepo_748_; lean_object* v_buildArchive_749_; uint8_t v_preferReleaseBuild_750_; lean_object* v_downloadCacheService_x3f_751_; lean_object* v_testDriver_752_; lean_object* v_testDriverArgs_753_; lean_object* v_lintDriver_754_; lean_object* v_lintDriverArgs_755_; lean_object* v_version_756_; lean_object* v_versionTags_757_; lean_object* v_description_758_; lean_object* v_keywords_759_; lean_object* v_homepage_760_; lean_object* v_license_761_; lean_object* v_licenseFiles_762_; lean_object* v_readmeFile_763_; uint8_t v_reservoir_764_; lean_object* v_enableArtifactCache_x3f_765_; lean_object* v_restoreAllArtifacts_x3f_766_; uint8_t v_libPrefixOnWindows_767_; uint8_t v_allowImportAll_768_; lean_object* v_builtinLint_x3f_769_; lean_object* v_checks_770_; uint8_t v_fixedToolchain_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_toWorkspaceConfig_737_ = lean_ctor_get(v_cfg_736_, 0);
v_toLeanConfig_738_ = lean_ctor_get(v_cfg_736_, 1);
v_bootstrap_739_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29);
v_extraDepTargets_740_ = lean_ctor_get(v_cfg_736_, 2);
v_precompileModules_741_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_742_ = lean_ctor_get(v_cfg_736_, 3);
v_srcDir_743_ = lean_ctor_get(v_cfg_736_, 4);
v_leanLibDir_744_ = lean_ctor_get(v_cfg_736_, 6);
v_nativeLibDir_745_ = lean_ctor_get(v_cfg_736_, 7);
v_binDir_746_ = lean_ctor_get(v_cfg_736_, 8);
v_irDir_747_ = lean_ctor_get(v_cfg_736_, 9);
v_releaseRepo_748_ = lean_ctor_get(v_cfg_736_, 10);
v_buildArchive_749_ = lean_ctor_get(v_cfg_736_, 11);
v_preferReleaseBuild_750_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_751_ = lean_ctor_get(v_cfg_736_, 12);
v_testDriver_752_ = lean_ctor_get(v_cfg_736_, 13);
v_testDriverArgs_753_ = lean_ctor_get(v_cfg_736_, 14);
v_lintDriver_754_ = lean_ctor_get(v_cfg_736_, 15);
v_lintDriverArgs_755_ = lean_ctor_get(v_cfg_736_, 16);
v_version_756_ = lean_ctor_get(v_cfg_736_, 17);
v_versionTags_757_ = lean_ctor_get(v_cfg_736_, 18);
v_description_758_ = lean_ctor_get(v_cfg_736_, 19);
v_keywords_759_ = lean_ctor_get(v_cfg_736_, 20);
v_homepage_760_ = lean_ctor_get(v_cfg_736_, 21);
v_license_761_ = lean_ctor_get(v_cfg_736_, 22);
v_licenseFiles_762_ = lean_ctor_get(v_cfg_736_, 23);
v_readmeFile_763_ = lean_ctor_get(v_cfg_736_, 24);
v_reservoir_764_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_765_ = lean_ctor_get(v_cfg_736_, 25);
v_restoreAllArtifacts_x3f_766_ = lean_ctor_get(v_cfg_736_, 26);
v_libPrefixOnWindows_767_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29 + 4);
v_allowImportAll_768_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_769_ = lean_ctor_get(v_cfg_736_, 27);
v_checks_770_ = lean_ctor_get(v_cfg_736_, 28);
v_fixedToolchain_771_ = lean_ctor_get_uint8(v_cfg_736_, sizeof(void*)*29 + 6);
v_isSharedCheck_778_ = !lean_is_exclusive(v_cfg_736_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_cfg_736_, 5);
lean_dec(v_unused_779_);
v___x_773_ = v_cfg_736_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_checks_770_);
lean_inc(v_builtinLint_x3f_769_);
lean_inc(v_restoreAllArtifacts_x3f_766_);
lean_inc(v_enableArtifactCache_x3f_765_);
lean_inc(v_readmeFile_763_);
lean_inc(v_licenseFiles_762_);
lean_inc(v_license_761_);
lean_inc(v_homepage_760_);
lean_inc(v_keywords_759_);
lean_inc(v_description_758_);
lean_inc(v_versionTags_757_);
lean_inc(v_version_756_);
lean_inc(v_lintDriverArgs_755_);
lean_inc(v_lintDriver_754_);
lean_inc(v_testDriverArgs_753_);
lean_inc(v_testDriver_752_);
lean_inc(v_downloadCacheService_x3f_751_);
lean_inc(v_buildArchive_749_);
lean_inc(v_releaseRepo_748_);
lean_inc(v_irDir_747_);
lean_inc(v_binDir_746_);
lean_inc(v_nativeLibDir_745_);
lean_inc(v_leanLibDir_744_);
lean_inc(v_srcDir_743_);
lean_inc(v_moreGlobalServerArgs_742_);
lean_inc(v_extraDepTargets_740_);
lean_inc(v_toLeanConfig_738_);
lean_inc(v_toWorkspaceConfig_737_);
lean_dec(v_cfg_736_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 5, v_val_735_);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_toWorkspaceConfig_737_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_toLeanConfig_738_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_extraDepTargets_740_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_moreGlobalServerArgs_742_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_srcDir_743_);
lean_ctor_set(v_reuseFailAlloc_777_, 5, v_val_735_);
lean_ctor_set(v_reuseFailAlloc_777_, 6, v_leanLibDir_744_);
lean_ctor_set(v_reuseFailAlloc_777_, 7, v_nativeLibDir_745_);
lean_ctor_set(v_reuseFailAlloc_777_, 8, v_binDir_746_);
lean_ctor_set(v_reuseFailAlloc_777_, 9, v_irDir_747_);
lean_ctor_set(v_reuseFailAlloc_777_, 10, v_releaseRepo_748_);
lean_ctor_set(v_reuseFailAlloc_777_, 11, v_buildArchive_749_);
lean_ctor_set(v_reuseFailAlloc_777_, 12, v_downloadCacheService_x3f_751_);
lean_ctor_set(v_reuseFailAlloc_777_, 13, v_testDriver_752_);
lean_ctor_set(v_reuseFailAlloc_777_, 14, v_testDriverArgs_753_);
lean_ctor_set(v_reuseFailAlloc_777_, 15, v_lintDriver_754_);
lean_ctor_set(v_reuseFailAlloc_777_, 16, v_lintDriverArgs_755_);
lean_ctor_set(v_reuseFailAlloc_777_, 17, v_version_756_);
lean_ctor_set(v_reuseFailAlloc_777_, 18, v_versionTags_757_);
lean_ctor_set(v_reuseFailAlloc_777_, 19, v_description_758_);
lean_ctor_set(v_reuseFailAlloc_777_, 20, v_keywords_759_);
lean_ctor_set(v_reuseFailAlloc_777_, 21, v_homepage_760_);
lean_ctor_set(v_reuseFailAlloc_777_, 22, v_license_761_);
lean_ctor_set(v_reuseFailAlloc_777_, 23, v_licenseFiles_762_);
lean_ctor_set(v_reuseFailAlloc_777_, 24, v_readmeFile_763_);
lean_ctor_set(v_reuseFailAlloc_777_, 25, v_enableArtifactCache_x3f_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 26, v_restoreAllArtifacts_x3f_766_);
lean_ctor_set(v_reuseFailAlloc_777_, 27, v_builtinLint_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_777_, 28, v_checks_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29, v_bootstrap_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29 + 1, v_precompileModules_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29 + 2, v_preferReleaseBuild_750_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29 + 3, v_reservoir_764_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29 + 5, v_allowImportAll_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*29 + 6, v_fixedToolchain_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__2(lean_object* v_f_780_, lean_object* v_cfg_781_){
_start:
{
lean_object* v_toWorkspaceConfig_782_; lean_object* v_toLeanConfig_783_; uint8_t v_bootstrap_784_; lean_object* v_extraDepTargets_785_; uint8_t v_precompileModules_786_; lean_object* v_moreGlobalServerArgs_787_; lean_object* v_srcDir_788_; lean_object* v_buildDir_789_; lean_object* v_leanLibDir_790_; lean_object* v_nativeLibDir_791_; lean_object* v_binDir_792_; lean_object* v_irDir_793_; lean_object* v_releaseRepo_794_; lean_object* v_buildArchive_795_; uint8_t v_preferReleaseBuild_796_; lean_object* v_downloadCacheService_x3f_797_; lean_object* v_testDriver_798_; lean_object* v_testDriverArgs_799_; lean_object* v_lintDriver_800_; lean_object* v_lintDriverArgs_801_; lean_object* v_version_802_; lean_object* v_versionTags_803_; lean_object* v_description_804_; lean_object* v_keywords_805_; lean_object* v_homepage_806_; lean_object* v_license_807_; lean_object* v_licenseFiles_808_; lean_object* v_readmeFile_809_; uint8_t v_reservoir_810_; lean_object* v_enableArtifactCache_x3f_811_; lean_object* v_restoreAllArtifacts_x3f_812_; uint8_t v_libPrefixOnWindows_813_; uint8_t v_allowImportAll_814_; lean_object* v_builtinLint_x3f_815_; lean_object* v_checks_816_; uint8_t v_fixedToolchain_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_toWorkspaceConfig_782_ = lean_ctor_get(v_cfg_781_, 0);
v_toLeanConfig_783_ = lean_ctor_get(v_cfg_781_, 1);
v_bootstrap_784_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29);
v_extraDepTargets_785_ = lean_ctor_get(v_cfg_781_, 2);
v_precompileModules_786_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_787_ = lean_ctor_get(v_cfg_781_, 3);
v_srcDir_788_ = lean_ctor_get(v_cfg_781_, 4);
v_buildDir_789_ = lean_ctor_get(v_cfg_781_, 5);
v_leanLibDir_790_ = lean_ctor_get(v_cfg_781_, 6);
v_nativeLibDir_791_ = lean_ctor_get(v_cfg_781_, 7);
v_binDir_792_ = lean_ctor_get(v_cfg_781_, 8);
v_irDir_793_ = lean_ctor_get(v_cfg_781_, 9);
v_releaseRepo_794_ = lean_ctor_get(v_cfg_781_, 10);
v_buildArchive_795_ = lean_ctor_get(v_cfg_781_, 11);
v_preferReleaseBuild_796_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_797_ = lean_ctor_get(v_cfg_781_, 12);
v_testDriver_798_ = lean_ctor_get(v_cfg_781_, 13);
v_testDriverArgs_799_ = lean_ctor_get(v_cfg_781_, 14);
v_lintDriver_800_ = lean_ctor_get(v_cfg_781_, 15);
v_lintDriverArgs_801_ = lean_ctor_get(v_cfg_781_, 16);
v_version_802_ = lean_ctor_get(v_cfg_781_, 17);
v_versionTags_803_ = lean_ctor_get(v_cfg_781_, 18);
v_description_804_ = lean_ctor_get(v_cfg_781_, 19);
v_keywords_805_ = lean_ctor_get(v_cfg_781_, 20);
v_homepage_806_ = lean_ctor_get(v_cfg_781_, 21);
v_license_807_ = lean_ctor_get(v_cfg_781_, 22);
v_licenseFiles_808_ = lean_ctor_get(v_cfg_781_, 23);
v_readmeFile_809_ = lean_ctor_get(v_cfg_781_, 24);
v_reservoir_810_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_811_ = lean_ctor_get(v_cfg_781_, 25);
v_restoreAllArtifacts_x3f_812_ = lean_ctor_get(v_cfg_781_, 26);
v_libPrefixOnWindows_813_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29 + 4);
v_allowImportAll_814_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_815_ = lean_ctor_get(v_cfg_781_, 27);
v_checks_816_ = lean_ctor_get(v_cfg_781_, 28);
v_fixedToolchain_817_ = lean_ctor_get_uint8(v_cfg_781_, sizeof(void*)*29 + 6);
v_isSharedCheck_825_ = !lean_is_exclusive(v_cfg_781_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v_cfg_781_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_checks_816_);
lean_inc(v_builtinLint_x3f_815_);
lean_inc(v_restoreAllArtifacts_x3f_812_);
lean_inc(v_enableArtifactCache_x3f_811_);
lean_inc(v_readmeFile_809_);
lean_inc(v_licenseFiles_808_);
lean_inc(v_license_807_);
lean_inc(v_homepage_806_);
lean_inc(v_keywords_805_);
lean_inc(v_description_804_);
lean_inc(v_versionTags_803_);
lean_inc(v_version_802_);
lean_inc(v_lintDriverArgs_801_);
lean_inc(v_lintDriver_800_);
lean_inc(v_testDriverArgs_799_);
lean_inc(v_testDriver_798_);
lean_inc(v_downloadCacheService_x3f_797_);
lean_inc(v_buildArchive_795_);
lean_inc(v_releaseRepo_794_);
lean_inc(v_irDir_793_);
lean_inc(v_binDir_792_);
lean_inc(v_nativeLibDir_791_);
lean_inc(v_leanLibDir_790_);
lean_inc(v_buildDir_789_);
lean_inc(v_srcDir_788_);
lean_inc(v_moreGlobalServerArgs_787_);
lean_inc(v_extraDepTargets_785_);
lean_inc(v_toLeanConfig_783_);
lean_inc(v_toWorkspaceConfig_782_);
lean_dec(v_cfg_781_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_apply_1(v_f_780_, v_buildDir_789_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 5, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_toWorkspaceConfig_782_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_toLeanConfig_783_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_extraDepTargets_785_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_moreGlobalServerArgs_787_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_srcDir_788_);
lean_ctor_set(v_reuseFailAlloc_824_, 5, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_824_, 6, v_leanLibDir_790_);
lean_ctor_set(v_reuseFailAlloc_824_, 7, v_nativeLibDir_791_);
lean_ctor_set(v_reuseFailAlloc_824_, 8, v_binDir_792_);
lean_ctor_set(v_reuseFailAlloc_824_, 9, v_irDir_793_);
lean_ctor_set(v_reuseFailAlloc_824_, 10, v_releaseRepo_794_);
lean_ctor_set(v_reuseFailAlloc_824_, 11, v_buildArchive_795_);
lean_ctor_set(v_reuseFailAlloc_824_, 12, v_downloadCacheService_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_824_, 13, v_testDriver_798_);
lean_ctor_set(v_reuseFailAlloc_824_, 14, v_testDriverArgs_799_);
lean_ctor_set(v_reuseFailAlloc_824_, 15, v_lintDriver_800_);
lean_ctor_set(v_reuseFailAlloc_824_, 16, v_lintDriverArgs_801_);
lean_ctor_set(v_reuseFailAlloc_824_, 17, v_version_802_);
lean_ctor_set(v_reuseFailAlloc_824_, 18, v_versionTags_803_);
lean_ctor_set(v_reuseFailAlloc_824_, 19, v_description_804_);
lean_ctor_set(v_reuseFailAlloc_824_, 20, v_keywords_805_);
lean_ctor_set(v_reuseFailAlloc_824_, 21, v_homepage_806_);
lean_ctor_set(v_reuseFailAlloc_824_, 22, v_license_807_);
lean_ctor_set(v_reuseFailAlloc_824_, 23, v_licenseFiles_808_);
lean_ctor_set(v_reuseFailAlloc_824_, 24, v_readmeFile_809_);
lean_ctor_set(v_reuseFailAlloc_824_, 25, v_enableArtifactCache_x3f_811_);
lean_ctor_set(v_reuseFailAlloc_824_, 26, v_restoreAllArtifacts_x3f_812_);
lean_ctor_set(v_reuseFailAlloc_824_, 27, v_builtinLint_x3f_815_);
lean_ctor_set(v_reuseFailAlloc_824_, 28, v_checks_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29, v_bootstrap_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29 + 1, v_precompileModules_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29 + 2, v_preferReleaseBuild_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29 + 3, v_reservoir_810_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29 + 5, v_allowImportAll_814_);
lean_ctor_set_uint8(v_reuseFailAlloc_824_, sizeof(void*)*29 + 6, v_fixedToolchain_817_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(lean_object* v_x_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lake_defaultBuildDir;
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___lam__3___boxed(lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lake_PackageConfig_buildDir___proj___redArg___lam__3(v_x_828_);
lean_dec_ref(v_x_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg(){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = ((lean_object*)(l_Lake_PackageConfig_buildDir___proj___redArg___closed__4));
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___redArg___boxed(lean_object* v___dummy_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_PackageConfig_buildDir___proj___redArg();
return v_res_842_;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildDir___proj___closed__0(void){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lake_PackageConfig_buildDir___proj___redArg();
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj(lean_object* v_p_844_, lean_object* v_n_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___proj___boxed(lean_object* v_p_847_, lean_object* v_n_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lake_PackageConfig_buildDir___proj(v_p_847_, v_n_848_);
lean_dec(v_n_848_);
lean_dec(v_p_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___redArg___boxed(lean_object* v___dummy_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lake_PackageConfig_buildDir_instConfigField___redArg();
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField(lean_object* v_p_854_, lean_object* v_n_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_obj_once(&l_Lake_PackageConfig_buildDir___proj___closed__0, &l_Lake_PackageConfig_buildDir___proj___closed__0_once, _init_l_Lake_PackageConfig_buildDir___proj___closed__0);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir_instConfigField___boxed(lean_object* v_p_857_, lean_object* v_n_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lake_PackageConfig_buildDir_instConfigField(v_p_857_, v_n_858_);
lean_dec(v_n_858_);
lean_dec(v_p_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(lean_object* v_cfg_860_){
_start:
{
lean_object* v_leanLibDir_861_; 
v_leanLibDir_861_ = lean_ctor_get(v_cfg_860_, 6);
lean_inc_ref(v_leanLibDir_861_);
return v_leanLibDir_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__0(v_cfg_862_);
lean_dec_ref(v_cfg_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__1(lean_object* v_val_864_, lean_object* v_cfg_865_){
_start:
{
lean_object* v_toWorkspaceConfig_866_; lean_object* v_toLeanConfig_867_; uint8_t v_bootstrap_868_; lean_object* v_extraDepTargets_869_; uint8_t v_precompileModules_870_; lean_object* v_moreGlobalServerArgs_871_; lean_object* v_srcDir_872_; lean_object* v_buildDir_873_; lean_object* v_nativeLibDir_874_; lean_object* v_binDir_875_; lean_object* v_irDir_876_; lean_object* v_releaseRepo_877_; lean_object* v_buildArchive_878_; uint8_t v_preferReleaseBuild_879_; lean_object* v_downloadCacheService_x3f_880_; lean_object* v_testDriver_881_; lean_object* v_testDriverArgs_882_; lean_object* v_lintDriver_883_; lean_object* v_lintDriverArgs_884_; lean_object* v_version_885_; lean_object* v_versionTags_886_; lean_object* v_description_887_; lean_object* v_keywords_888_; lean_object* v_homepage_889_; lean_object* v_license_890_; lean_object* v_licenseFiles_891_; lean_object* v_readmeFile_892_; uint8_t v_reservoir_893_; lean_object* v_enableArtifactCache_x3f_894_; lean_object* v_restoreAllArtifacts_x3f_895_; uint8_t v_libPrefixOnWindows_896_; uint8_t v_allowImportAll_897_; lean_object* v_builtinLint_x3f_898_; lean_object* v_checks_899_; uint8_t v_fixedToolchain_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_toWorkspaceConfig_866_ = lean_ctor_get(v_cfg_865_, 0);
v_toLeanConfig_867_ = lean_ctor_get(v_cfg_865_, 1);
v_bootstrap_868_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29);
v_extraDepTargets_869_ = lean_ctor_get(v_cfg_865_, 2);
v_precompileModules_870_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_871_ = lean_ctor_get(v_cfg_865_, 3);
v_srcDir_872_ = lean_ctor_get(v_cfg_865_, 4);
v_buildDir_873_ = lean_ctor_get(v_cfg_865_, 5);
v_nativeLibDir_874_ = lean_ctor_get(v_cfg_865_, 7);
v_binDir_875_ = lean_ctor_get(v_cfg_865_, 8);
v_irDir_876_ = lean_ctor_get(v_cfg_865_, 9);
v_releaseRepo_877_ = lean_ctor_get(v_cfg_865_, 10);
v_buildArchive_878_ = lean_ctor_get(v_cfg_865_, 11);
v_preferReleaseBuild_879_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_880_ = lean_ctor_get(v_cfg_865_, 12);
v_testDriver_881_ = lean_ctor_get(v_cfg_865_, 13);
v_testDriverArgs_882_ = lean_ctor_get(v_cfg_865_, 14);
v_lintDriver_883_ = lean_ctor_get(v_cfg_865_, 15);
v_lintDriverArgs_884_ = lean_ctor_get(v_cfg_865_, 16);
v_version_885_ = lean_ctor_get(v_cfg_865_, 17);
v_versionTags_886_ = lean_ctor_get(v_cfg_865_, 18);
v_description_887_ = lean_ctor_get(v_cfg_865_, 19);
v_keywords_888_ = lean_ctor_get(v_cfg_865_, 20);
v_homepage_889_ = lean_ctor_get(v_cfg_865_, 21);
v_license_890_ = lean_ctor_get(v_cfg_865_, 22);
v_licenseFiles_891_ = lean_ctor_get(v_cfg_865_, 23);
v_readmeFile_892_ = lean_ctor_get(v_cfg_865_, 24);
v_reservoir_893_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_894_ = lean_ctor_get(v_cfg_865_, 25);
v_restoreAllArtifacts_x3f_895_ = lean_ctor_get(v_cfg_865_, 26);
v_libPrefixOnWindows_896_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29 + 4);
v_allowImportAll_897_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_898_ = lean_ctor_get(v_cfg_865_, 27);
v_checks_899_ = lean_ctor_get(v_cfg_865_, 28);
v_fixedToolchain_900_ = lean_ctor_get_uint8(v_cfg_865_, sizeof(void*)*29 + 6);
v_isSharedCheck_907_ = !lean_is_exclusive(v_cfg_865_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_cfg_865_, 6);
lean_dec(v_unused_908_);
v___x_902_ = v_cfg_865_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_checks_899_);
lean_inc(v_builtinLint_x3f_898_);
lean_inc(v_restoreAllArtifacts_x3f_895_);
lean_inc(v_enableArtifactCache_x3f_894_);
lean_inc(v_readmeFile_892_);
lean_inc(v_licenseFiles_891_);
lean_inc(v_license_890_);
lean_inc(v_homepage_889_);
lean_inc(v_keywords_888_);
lean_inc(v_description_887_);
lean_inc(v_versionTags_886_);
lean_inc(v_version_885_);
lean_inc(v_lintDriverArgs_884_);
lean_inc(v_lintDriver_883_);
lean_inc(v_testDriverArgs_882_);
lean_inc(v_testDriver_881_);
lean_inc(v_downloadCacheService_x3f_880_);
lean_inc(v_buildArchive_878_);
lean_inc(v_releaseRepo_877_);
lean_inc(v_irDir_876_);
lean_inc(v_binDir_875_);
lean_inc(v_nativeLibDir_874_);
lean_inc(v_buildDir_873_);
lean_inc(v_srcDir_872_);
lean_inc(v_moreGlobalServerArgs_871_);
lean_inc(v_extraDepTargets_869_);
lean_inc(v_toLeanConfig_867_);
lean_inc(v_toWorkspaceConfig_866_);
lean_dec(v_cfg_865_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 6, v_val_864_);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_toWorkspaceConfig_866_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_toLeanConfig_867_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_extraDepTargets_869_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_moreGlobalServerArgs_871_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_srcDir_872_);
lean_ctor_set(v_reuseFailAlloc_906_, 5, v_buildDir_873_);
lean_ctor_set(v_reuseFailAlloc_906_, 6, v_val_864_);
lean_ctor_set(v_reuseFailAlloc_906_, 7, v_nativeLibDir_874_);
lean_ctor_set(v_reuseFailAlloc_906_, 8, v_binDir_875_);
lean_ctor_set(v_reuseFailAlloc_906_, 9, v_irDir_876_);
lean_ctor_set(v_reuseFailAlloc_906_, 10, v_releaseRepo_877_);
lean_ctor_set(v_reuseFailAlloc_906_, 11, v_buildArchive_878_);
lean_ctor_set(v_reuseFailAlloc_906_, 12, v_downloadCacheService_x3f_880_);
lean_ctor_set(v_reuseFailAlloc_906_, 13, v_testDriver_881_);
lean_ctor_set(v_reuseFailAlloc_906_, 14, v_testDriverArgs_882_);
lean_ctor_set(v_reuseFailAlloc_906_, 15, v_lintDriver_883_);
lean_ctor_set(v_reuseFailAlloc_906_, 16, v_lintDriverArgs_884_);
lean_ctor_set(v_reuseFailAlloc_906_, 17, v_version_885_);
lean_ctor_set(v_reuseFailAlloc_906_, 18, v_versionTags_886_);
lean_ctor_set(v_reuseFailAlloc_906_, 19, v_description_887_);
lean_ctor_set(v_reuseFailAlloc_906_, 20, v_keywords_888_);
lean_ctor_set(v_reuseFailAlloc_906_, 21, v_homepage_889_);
lean_ctor_set(v_reuseFailAlloc_906_, 22, v_license_890_);
lean_ctor_set(v_reuseFailAlloc_906_, 23, v_licenseFiles_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 24, v_readmeFile_892_);
lean_ctor_set(v_reuseFailAlloc_906_, 25, v_enableArtifactCache_x3f_894_);
lean_ctor_set(v_reuseFailAlloc_906_, 26, v_restoreAllArtifacts_x3f_895_);
lean_ctor_set(v_reuseFailAlloc_906_, 27, v_builtinLint_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_906_, 28, v_checks_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29, v_bootstrap_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29 + 1, v_precompileModules_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29 + 2, v_preferReleaseBuild_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29 + 3, v_reservoir_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29 + 5, v_allowImportAll_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*29 + 6, v_fixedToolchain_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__2(lean_object* v_f_909_, lean_object* v_cfg_910_){
_start:
{
lean_object* v_toWorkspaceConfig_911_; lean_object* v_toLeanConfig_912_; uint8_t v_bootstrap_913_; lean_object* v_extraDepTargets_914_; uint8_t v_precompileModules_915_; lean_object* v_moreGlobalServerArgs_916_; lean_object* v_srcDir_917_; lean_object* v_buildDir_918_; lean_object* v_leanLibDir_919_; lean_object* v_nativeLibDir_920_; lean_object* v_binDir_921_; lean_object* v_irDir_922_; lean_object* v_releaseRepo_923_; lean_object* v_buildArchive_924_; uint8_t v_preferReleaseBuild_925_; lean_object* v_downloadCacheService_x3f_926_; lean_object* v_testDriver_927_; lean_object* v_testDriverArgs_928_; lean_object* v_lintDriver_929_; lean_object* v_lintDriverArgs_930_; lean_object* v_version_931_; lean_object* v_versionTags_932_; lean_object* v_description_933_; lean_object* v_keywords_934_; lean_object* v_homepage_935_; lean_object* v_license_936_; lean_object* v_licenseFiles_937_; lean_object* v_readmeFile_938_; uint8_t v_reservoir_939_; lean_object* v_enableArtifactCache_x3f_940_; lean_object* v_restoreAllArtifacts_x3f_941_; uint8_t v_libPrefixOnWindows_942_; uint8_t v_allowImportAll_943_; lean_object* v_builtinLint_x3f_944_; lean_object* v_checks_945_; uint8_t v_fixedToolchain_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
v_toWorkspaceConfig_911_ = lean_ctor_get(v_cfg_910_, 0);
v_toLeanConfig_912_ = lean_ctor_get(v_cfg_910_, 1);
v_bootstrap_913_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29);
v_extraDepTargets_914_ = lean_ctor_get(v_cfg_910_, 2);
v_precompileModules_915_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_916_ = lean_ctor_get(v_cfg_910_, 3);
v_srcDir_917_ = lean_ctor_get(v_cfg_910_, 4);
v_buildDir_918_ = lean_ctor_get(v_cfg_910_, 5);
v_leanLibDir_919_ = lean_ctor_get(v_cfg_910_, 6);
v_nativeLibDir_920_ = lean_ctor_get(v_cfg_910_, 7);
v_binDir_921_ = lean_ctor_get(v_cfg_910_, 8);
v_irDir_922_ = lean_ctor_get(v_cfg_910_, 9);
v_releaseRepo_923_ = lean_ctor_get(v_cfg_910_, 10);
v_buildArchive_924_ = lean_ctor_get(v_cfg_910_, 11);
v_preferReleaseBuild_925_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_926_ = lean_ctor_get(v_cfg_910_, 12);
v_testDriver_927_ = lean_ctor_get(v_cfg_910_, 13);
v_testDriverArgs_928_ = lean_ctor_get(v_cfg_910_, 14);
v_lintDriver_929_ = lean_ctor_get(v_cfg_910_, 15);
v_lintDriverArgs_930_ = lean_ctor_get(v_cfg_910_, 16);
v_version_931_ = lean_ctor_get(v_cfg_910_, 17);
v_versionTags_932_ = lean_ctor_get(v_cfg_910_, 18);
v_description_933_ = lean_ctor_get(v_cfg_910_, 19);
v_keywords_934_ = lean_ctor_get(v_cfg_910_, 20);
v_homepage_935_ = lean_ctor_get(v_cfg_910_, 21);
v_license_936_ = lean_ctor_get(v_cfg_910_, 22);
v_licenseFiles_937_ = lean_ctor_get(v_cfg_910_, 23);
v_readmeFile_938_ = lean_ctor_get(v_cfg_910_, 24);
v_reservoir_939_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_940_ = lean_ctor_get(v_cfg_910_, 25);
v_restoreAllArtifacts_x3f_941_ = lean_ctor_get(v_cfg_910_, 26);
v_libPrefixOnWindows_942_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29 + 4);
v_allowImportAll_943_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_944_ = lean_ctor_get(v_cfg_910_, 27);
v_checks_945_ = lean_ctor_get(v_cfg_910_, 28);
v_fixedToolchain_946_ = lean_ctor_get_uint8(v_cfg_910_, sizeof(void*)*29 + 6);
v_isSharedCheck_954_ = !lean_is_exclusive(v_cfg_910_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v_cfg_910_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_checks_945_);
lean_inc(v_builtinLint_x3f_944_);
lean_inc(v_restoreAllArtifacts_x3f_941_);
lean_inc(v_enableArtifactCache_x3f_940_);
lean_inc(v_readmeFile_938_);
lean_inc(v_licenseFiles_937_);
lean_inc(v_license_936_);
lean_inc(v_homepage_935_);
lean_inc(v_keywords_934_);
lean_inc(v_description_933_);
lean_inc(v_versionTags_932_);
lean_inc(v_version_931_);
lean_inc(v_lintDriverArgs_930_);
lean_inc(v_lintDriver_929_);
lean_inc(v_testDriverArgs_928_);
lean_inc(v_testDriver_927_);
lean_inc(v_downloadCacheService_x3f_926_);
lean_inc(v_buildArchive_924_);
lean_inc(v_releaseRepo_923_);
lean_inc(v_irDir_922_);
lean_inc(v_binDir_921_);
lean_inc(v_nativeLibDir_920_);
lean_inc(v_leanLibDir_919_);
lean_inc(v_buildDir_918_);
lean_inc(v_srcDir_917_);
lean_inc(v_moreGlobalServerArgs_916_);
lean_inc(v_extraDepTargets_914_);
lean_inc(v_toLeanConfig_912_);
lean_inc(v_toWorkspaceConfig_911_);
lean_dec(v_cfg_910_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_apply_1(v_f_909_, v_leanLibDir_919_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 6, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_toWorkspaceConfig_911_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_toLeanConfig_912_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_extraDepTargets_914_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_moreGlobalServerArgs_916_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_srcDir_917_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_buildDir_918_);
lean_ctor_set(v_reuseFailAlloc_953_, 6, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_953_, 7, v_nativeLibDir_920_);
lean_ctor_set(v_reuseFailAlloc_953_, 8, v_binDir_921_);
lean_ctor_set(v_reuseFailAlloc_953_, 9, v_irDir_922_);
lean_ctor_set(v_reuseFailAlloc_953_, 10, v_releaseRepo_923_);
lean_ctor_set(v_reuseFailAlloc_953_, 11, v_buildArchive_924_);
lean_ctor_set(v_reuseFailAlloc_953_, 12, v_downloadCacheService_x3f_926_);
lean_ctor_set(v_reuseFailAlloc_953_, 13, v_testDriver_927_);
lean_ctor_set(v_reuseFailAlloc_953_, 14, v_testDriverArgs_928_);
lean_ctor_set(v_reuseFailAlloc_953_, 15, v_lintDriver_929_);
lean_ctor_set(v_reuseFailAlloc_953_, 16, v_lintDriverArgs_930_);
lean_ctor_set(v_reuseFailAlloc_953_, 17, v_version_931_);
lean_ctor_set(v_reuseFailAlloc_953_, 18, v_versionTags_932_);
lean_ctor_set(v_reuseFailAlloc_953_, 19, v_description_933_);
lean_ctor_set(v_reuseFailAlloc_953_, 20, v_keywords_934_);
lean_ctor_set(v_reuseFailAlloc_953_, 21, v_homepage_935_);
lean_ctor_set(v_reuseFailAlloc_953_, 22, v_license_936_);
lean_ctor_set(v_reuseFailAlloc_953_, 23, v_licenseFiles_937_);
lean_ctor_set(v_reuseFailAlloc_953_, 24, v_readmeFile_938_);
lean_ctor_set(v_reuseFailAlloc_953_, 25, v_enableArtifactCache_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_953_, 26, v_restoreAllArtifacts_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 27, v_builtinLint_x3f_944_);
lean_ctor_set(v_reuseFailAlloc_953_, 28, v_checks_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29, v_bootstrap_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29 + 1, v_precompileModules_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29 + 2, v_preferReleaseBuild_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29 + 3, v_reservoir_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29 + 5, v_allowImportAll_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_953_, sizeof(void*)*29 + 6, v_fixedToolchain_946_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lake_defaultLeanLibDir;
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3___boxed(lean_object* v_x_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lake_PackageConfig_leanLibDir___proj___redArg___lam__3(v_x_957_);
lean_dec_ref(v_x_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg(){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Lake_PackageConfig_leanLibDir___proj___redArg___closed__4));
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___redArg___boxed(lean_object* v___dummy_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
return v_res_971_;
}
}
static lean_object* _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lake_PackageConfig_leanLibDir___proj___redArg();
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj(lean_object* v_p_973_, lean_object* v_n_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___proj___boxed(lean_object* v_p_976_, lean_object* v_n_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lake_PackageConfig_leanLibDir___proj(v_p_976_, v_n_977_);
lean_dec(v_n_977_);
lean_dec(v_p_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___redArg___boxed(lean_object* v___dummy_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lake_PackageConfig_leanLibDir_instConfigField___redArg();
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField(lean_object* v_p_983_, lean_object* v_n_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_obj_once(&l_Lake_PackageConfig_leanLibDir___proj___closed__0, &l_Lake_PackageConfig_leanLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_leanLibDir___proj___closed__0);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir_instConfigField___boxed(lean_object* v_p_986_, lean_object* v_n_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lake_PackageConfig_leanLibDir_instConfigField(v_p_986_, v_n_987_);
lean_dec(v_n_987_);
lean_dec(v_p_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(lean_object* v_cfg_989_){
_start:
{
lean_object* v_nativeLibDir_990_; 
v_nativeLibDir_990_ = lean_ctor_get(v_cfg_989_, 7);
lean_inc_ref(v_nativeLibDir_990_);
return v_nativeLibDir_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__0(v_cfg_991_);
lean_dec_ref(v_cfg_991_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__1(lean_object* v_val_993_, lean_object* v_cfg_994_){
_start:
{
lean_object* v_toWorkspaceConfig_995_; lean_object* v_toLeanConfig_996_; uint8_t v_bootstrap_997_; lean_object* v_extraDepTargets_998_; uint8_t v_precompileModules_999_; lean_object* v_moreGlobalServerArgs_1000_; lean_object* v_srcDir_1001_; lean_object* v_buildDir_1002_; lean_object* v_leanLibDir_1003_; lean_object* v_binDir_1004_; lean_object* v_irDir_1005_; lean_object* v_releaseRepo_1006_; lean_object* v_buildArchive_1007_; uint8_t v_preferReleaseBuild_1008_; lean_object* v_downloadCacheService_x3f_1009_; lean_object* v_testDriver_1010_; lean_object* v_testDriverArgs_1011_; lean_object* v_lintDriver_1012_; lean_object* v_lintDriverArgs_1013_; lean_object* v_version_1014_; lean_object* v_versionTags_1015_; lean_object* v_description_1016_; lean_object* v_keywords_1017_; lean_object* v_homepage_1018_; lean_object* v_license_1019_; lean_object* v_licenseFiles_1020_; lean_object* v_readmeFile_1021_; uint8_t v_reservoir_1022_; lean_object* v_enableArtifactCache_x3f_1023_; lean_object* v_restoreAllArtifacts_x3f_1024_; uint8_t v_libPrefixOnWindows_1025_; uint8_t v_allowImportAll_1026_; lean_object* v_builtinLint_x3f_1027_; lean_object* v_checks_1028_; uint8_t v_fixedToolchain_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_toWorkspaceConfig_995_ = lean_ctor_get(v_cfg_994_, 0);
v_toLeanConfig_996_ = lean_ctor_get(v_cfg_994_, 1);
v_bootstrap_997_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29);
v_extraDepTargets_998_ = lean_ctor_get(v_cfg_994_, 2);
v_precompileModules_999_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1000_ = lean_ctor_get(v_cfg_994_, 3);
v_srcDir_1001_ = lean_ctor_get(v_cfg_994_, 4);
v_buildDir_1002_ = lean_ctor_get(v_cfg_994_, 5);
v_leanLibDir_1003_ = lean_ctor_get(v_cfg_994_, 6);
v_binDir_1004_ = lean_ctor_get(v_cfg_994_, 8);
v_irDir_1005_ = lean_ctor_get(v_cfg_994_, 9);
v_releaseRepo_1006_ = lean_ctor_get(v_cfg_994_, 10);
v_buildArchive_1007_ = lean_ctor_get(v_cfg_994_, 11);
v_preferReleaseBuild_1008_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1009_ = lean_ctor_get(v_cfg_994_, 12);
v_testDriver_1010_ = lean_ctor_get(v_cfg_994_, 13);
v_testDriverArgs_1011_ = lean_ctor_get(v_cfg_994_, 14);
v_lintDriver_1012_ = lean_ctor_get(v_cfg_994_, 15);
v_lintDriverArgs_1013_ = lean_ctor_get(v_cfg_994_, 16);
v_version_1014_ = lean_ctor_get(v_cfg_994_, 17);
v_versionTags_1015_ = lean_ctor_get(v_cfg_994_, 18);
v_description_1016_ = lean_ctor_get(v_cfg_994_, 19);
v_keywords_1017_ = lean_ctor_get(v_cfg_994_, 20);
v_homepage_1018_ = lean_ctor_get(v_cfg_994_, 21);
v_license_1019_ = lean_ctor_get(v_cfg_994_, 22);
v_licenseFiles_1020_ = lean_ctor_get(v_cfg_994_, 23);
v_readmeFile_1021_ = lean_ctor_get(v_cfg_994_, 24);
v_reservoir_1022_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1023_ = lean_ctor_get(v_cfg_994_, 25);
v_restoreAllArtifacts_x3f_1024_ = lean_ctor_get(v_cfg_994_, 26);
v_libPrefixOnWindows_1025_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29 + 4);
v_allowImportAll_1026_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1027_ = lean_ctor_get(v_cfg_994_, 27);
v_checks_1028_ = lean_ctor_get(v_cfg_994_, 28);
v_fixedToolchain_1029_ = lean_ctor_get_uint8(v_cfg_994_, sizeof(void*)*29 + 6);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_cfg_994_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_cfg_994_, 7);
lean_dec(v_unused_1037_);
v___x_1031_ = v_cfg_994_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_checks_1028_);
lean_inc(v_builtinLint_x3f_1027_);
lean_inc(v_restoreAllArtifacts_x3f_1024_);
lean_inc(v_enableArtifactCache_x3f_1023_);
lean_inc(v_readmeFile_1021_);
lean_inc(v_licenseFiles_1020_);
lean_inc(v_license_1019_);
lean_inc(v_homepage_1018_);
lean_inc(v_keywords_1017_);
lean_inc(v_description_1016_);
lean_inc(v_versionTags_1015_);
lean_inc(v_version_1014_);
lean_inc(v_lintDriverArgs_1013_);
lean_inc(v_lintDriver_1012_);
lean_inc(v_testDriverArgs_1011_);
lean_inc(v_testDriver_1010_);
lean_inc(v_downloadCacheService_x3f_1009_);
lean_inc(v_buildArchive_1007_);
lean_inc(v_releaseRepo_1006_);
lean_inc(v_irDir_1005_);
lean_inc(v_binDir_1004_);
lean_inc(v_leanLibDir_1003_);
lean_inc(v_buildDir_1002_);
lean_inc(v_srcDir_1001_);
lean_inc(v_moreGlobalServerArgs_1000_);
lean_inc(v_extraDepTargets_998_);
lean_inc(v_toLeanConfig_996_);
lean_inc(v_toWorkspaceConfig_995_);
lean_dec(v_cfg_994_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 7, v_val_993_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_toWorkspaceConfig_995_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_toLeanConfig_996_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_extraDepTargets_998_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_moreGlobalServerArgs_1000_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_srcDir_1001_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v_buildDir_1002_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_leanLibDir_1003_);
lean_ctor_set(v_reuseFailAlloc_1035_, 7, v_val_993_);
lean_ctor_set(v_reuseFailAlloc_1035_, 8, v_binDir_1004_);
lean_ctor_set(v_reuseFailAlloc_1035_, 9, v_irDir_1005_);
lean_ctor_set(v_reuseFailAlloc_1035_, 10, v_releaseRepo_1006_);
lean_ctor_set(v_reuseFailAlloc_1035_, 11, v_buildArchive_1007_);
lean_ctor_set(v_reuseFailAlloc_1035_, 12, v_downloadCacheService_x3f_1009_);
lean_ctor_set(v_reuseFailAlloc_1035_, 13, v_testDriver_1010_);
lean_ctor_set(v_reuseFailAlloc_1035_, 14, v_testDriverArgs_1011_);
lean_ctor_set(v_reuseFailAlloc_1035_, 15, v_lintDriver_1012_);
lean_ctor_set(v_reuseFailAlloc_1035_, 16, v_lintDriverArgs_1013_);
lean_ctor_set(v_reuseFailAlloc_1035_, 17, v_version_1014_);
lean_ctor_set(v_reuseFailAlloc_1035_, 18, v_versionTags_1015_);
lean_ctor_set(v_reuseFailAlloc_1035_, 19, v_description_1016_);
lean_ctor_set(v_reuseFailAlloc_1035_, 20, v_keywords_1017_);
lean_ctor_set(v_reuseFailAlloc_1035_, 21, v_homepage_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 22, v_license_1019_);
lean_ctor_set(v_reuseFailAlloc_1035_, 23, v_licenseFiles_1020_);
lean_ctor_set(v_reuseFailAlloc_1035_, 24, v_readmeFile_1021_);
lean_ctor_set(v_reuseFailAlloc_1035_, 25, v_enableArtifactCache_x3f_1023_);
lean_ctor_set(v_reuseFailAlloc_1035_, 26, v_restoreAllArtifacts_x3f_1024_);
lean_ctor_set(v_reuseFailAlloc_1035_, 27, v_builtinLint_x3f_1027_);
lean_ctor_set(v_reuseFailAlloc_1035_, 28, v_checks_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29, v_bootstrap_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29 + 1, v_precompileModules_999_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29 + 3, v_reservoir_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29 + 5, v_allowImportAll_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*29 + 6, v_fixedToolchain_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__2(lean_object* v_f_1038_, lean_object* v_cfg_1039_){
_start:
{
lean_object* v_toWorkspaceConfig_1040_; lean_object* v_toLeanConfig_1041_; uint8_t v_bootstrap_1042_; lean_object* v_extraDepTargets_1043_; uint8_t v_precompileModules_1044_; lean_object* v_moreGlobalServerArgs_1045_; lean_object* v_srcDir_1046_; lean_object* v_buildDir_1047_; lean_object* v_leanLibDir_1048_; lean_object* v_nativeLibDir_1049_; lean_object* v_binDir_1050_; lean_object* v_irDir_1051_; lean_object* v_releaseRepo_1052_; lean_object* v_buildArchive_1053_; uint8_t v_preferReleaseBuild_1054_; lean_object* v_downloadCacheService_x3f_1055_; lean_object* v_testDriver_1056_; lean_object* v_testDriverArgs_1057_; lean_object* v_lintDriver_1058_; lean_object* v_lintDriverArgs_1059_; lean_object* v_version_1060_; lean_object* v_versionTags_1061_; lean_object* v_description_1062_; lean_object* v_keywords_1063_; lean_object* v_homepage_1064_; lean_object* v_license_1065_; lean_object* v_licenseFiles_1066_; lean_object* v_readmeFile_1067_; uint8_t v_reservoir_1068_; lean_object* v_enableArtifactCache_x3f_1069_; lean_object* v_restoreAllArtifacts_x3f_1070_; uint8_t v_libPrefixOnWindows_1071_; uint8_t v_allowImportAll_1072_; lean_object* v_builtinLint_x3f_1073_; lean_object* v_checks_1074_; uint8_t v_fixedToolchain_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_toWorkspaceConfig_1040_ = lean_ctor_get(v_cfg_1039_, 0);
v_toLeanConfig_1041_ = lean_ctor_get(v_cfg_1039_, 1);
v_bootstrap_1042_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29);
v_extraDepTargets_1043_ = lean_ctor_get(v_cfg_1039_, 2);
v_precompileModules_1044_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1045_ = lean_ctor_get(v_cfg_1039_, 3);
v_srcDir_1046_ = lean_ctor_get(v_cfg_1039_, 4);
v_buildDir_1047_ = lean_ctor_get(v_cfg_1039_, 5);
v_leanLibDir_1048_ = lean_ctor_get(v_cfg_1039_, 6);
v_nativeLibDir_1049_ = lean_ctor_get(v_cfg_1039_, 7);
v_binDir_1050_ = lean_ctor_get(v_cfg_1039_, 8);
v_irDir_1051_ = lean_ctor_get(v_cfg_1039_, 9);
v_releaseRepo_1052_ = lean_ctor_get(v_cfg_1039_, 10);
v_buildArchive_1053_ = lean_ctor_get(v_cfg_1039_, 11);
v_preferReleaseBuild_1054_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1055_ = lean_ctor_get(v_cfg_1039_, 12);
v_testDriver_1056_ = lean_ctor_get(v_cfg_1039_, 13);
v_testDriverArgs_1057_ = lean_ctor_get(v_cfg_1039_, 14);
v_lintDriver_1058_ = lean_ctor_get(v_cfg_1039_, 15);
v_lintDriverArgs_1059_ = lean_ctor_get(v_cfg_1039_, 16);
v_version_1060_ = lean_ctor_get(v_cfg_1039_, 17);
v_versionTags_1061_ = lean_ctor_get(v_cfg_1039_, 18);
v_description_1062_ = lean_ctor_get(v_cfg_1039_, 19);
v_keywords_1063_ = lean_ctor_get(v_cfg_1039_, 20);
v_homepage_1064_ = lean_ctor_get(v_cfg_1039_, 21);
v_license_1065_ = lean_ctor_get(v_cfg_1039_, 22);
v_licenseFiles_1066_ = lean_ctor_get(v_cfg_1039_, 23);
v_readmeFile_1067_ = lean_ctor_get(v_cfg_1039_, 24);
v_reservoir_1068_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1069_ = lean_ctor_get(v_cfg_1039_, 25);
v_restoreAllArtifacts_x3f_1070_ = lean_ctor_get(v_cfg_1039_, 26);
v_libPrefixOnWindows_1071_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29 + 4);
v_allowImportAll_1072_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1073_ = lean_ctor_get(v_cfg_1039_, 27);
v_checks_1074_ = lean_ctor_get(v_cfg_1039_, 28);
v_fixedToolchain_1075_ = lean_ctor_get_uint8(v_cfg_1039_, sizeof(void*)*29 + 6);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_cfg_1039_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_cfg_1039_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_checks_1074_);
lean_inc(v_builtinLint_x3f_1073_);
lean_inc(v_restoreAllArtifacts_x3f_1070_);
lean_inc(v_enableArtifactCache_x3f_1069_);
lean_inc(v_readmeFile_1067_);
lean_inc(v_licenseFiles_1066_);
lean_inc(v_license_1065_);
lean_inc(v_homepage_1064_);
lean_inc(v_keywords_1063_);
lean_inc(v_description_1062_);
lean_inc(v_versionTags_1061_);
lean_inc(v_version_1060_);
lean_inc(v_lintDriverArgs_1059_);
lean_inc(v_lintDriver_1058_);
lean_inc(v_testDriverArgs_1057_);
lean_inc(v_testDriver_1056_);
lean_inc(v_downloadCacheService_x3f_1055_);
lean_inc(v_buildArchive_1053_);
lean_inc(v_releaseRepo_1052_);
lean_inc(v_irDir_1051_);
lean_inc(v_binDir_1050_);
lean_inc(v_nativeLibDir_1049_);
lean_inc(v_leanLibDir_1048_);
lean_inc(v_buildDir_1047_);
lean_inc(v_srcDir_1046_);
lean_inc(v_moreGlobalServerArgs_1045_);
lean_inc(v_extraDepTargets_1043_);
lean_inc(v_toLeanConfig_1041_);
lean_inc(v_toWorkspaceConfig_1040_);
lean_dec(v_cfg_1039_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_apply_1(v_f_1038_, v_nativeLibDir_1049_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 7, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_toWorkspaceConfig_1040_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_toLeanConfig_1041_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_extraDepTargets_1043_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_moreGlobalServerArgs_1045_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_srcDir_1046_);
lean_ctor_set(v_reuseFailAlloc_1082_, 5, v_buildDir_1047_);
lean_ctor_set(v_reuseFailAlloc_1082_, 6, v_leanLibDir_1048_);
lean_ctor_set(v_reuseFailAlloc_1082_, 7, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 8, v_binDir_1050_);
lean_ctor_set(v_reuseFailAlloc_1082_, 9, v_irDir_1051_);
lean_ctor_set(v_reuseFailAlloc_1082_, 10, v_releaseRepo_1052_);
lean_ctor_set(v_reuseFailAlloc_1082_, 11, v_buildArchive_1053_);
lean_ctor_set(v_reuseFailAlloc_1082_, 12, v_downloadCacheService_x3f_1055_);
lean_ctor_set(v_reuseFailAlloc_1082_, 13, v_testDriver_1056_);
lean_ctor_set(v_reuseFailAlloc_1082_, 14, v_testDriverArgs_1057_);
lean_ctor_set(v_reuseFailAlloc_1082_, 15, v_lintDriver_1058_);
lean_ctor_set(v_reuseFailAlloc_1082_, 16, v_lintDriverArgs_1059_);
lean_ctor_set(v_reuseFailAlloc_1082_, 17, v_version_1060_);
lean_ctor_set(v_reuseFailAlloc_1082_, 18, v_versionTags_1061_);
lean_ctor_set(v_reuseFailAlloc_1082_, 19, v_description_1062_);
lean_ctor_set(v_reuseFailAlloc_1082_, 20, v_keywords_1063_);
lean_ctor_set(v_reuseFailAlloc_1082_, 21, v_homepage_1064_);
lean_ctor_set(v_reuseFailAlloc_1082_, 22, v_license_1065_);
lean_ctor_set(v_reuseFailAlloc_1082_, 23, v_licenseFiles_1066_);
lean_ctor_set(v_reuseFailAlloc_1082_, 24, v_readmeFile_1067_);
lean_ctor_set(v_reuseFailAlloc_1082_, 25, v_enableArtifactCache_x3f_1069_);
lean_ctor_set(v_reuseFailAlloc_1082_, 26, v_restoreAllArtifacts_x3f_1070_);
lean_ctor_set(v_reuseFailAlloc_1082_, 27, v_builtinLint_x3f_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 28, v_checks_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29, v_bootstrap_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29 + 1, v_precompileModules_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29 + 3, v_reservoir_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29 + 5, v_allowImportAll_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*29 + 6, v_fixedToolchain_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lake_defaultNativeLibDir;
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3___boxed(lean_object* v_x_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg___lam__3(v_x_1086_);
lean_dec_ref(v_x_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg(){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l_Lake_PackageConfig_nativeLibDir___proj___redArg___closed__4));
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___redArg___boxed(lean_object* v___dummy_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
return v_res_1100_;
}
}
static lean_object* _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lake_PackageConfig_nativeLibDir___proj___redArg();
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj(lean_object* v_p_1102_, lean_object* v_n_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___proj___boxed(lean_object* v_p_1105_, lean_object* v_n_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lake_PackageConfig_nativeLibDir___proj(v_p_1105_, v_n_1106_);
lean_dec(v_n_1106_);
lean_dec(v_p_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg___boxed(lean_object* v___dummy_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lake_PackageConfig_nativeLibDir_instConfigField___redArg();
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField(lean_object* v_p_1112_, lean_object* v_n_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_obj_once(&l_Lake_PackageConfig_nativeLibDir___proj___closed__0, &l_Lake_PackageConfig_nativeLibDir___proj___closed__0_once, _init_l_Lake_PackageConfig_nativeLibDir___proj___closed__0);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir_instConfigField___boxed(lean_object* v_p_1115_, lean_object* v_n_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lake_PackageConfig_nativeLibDir_instConfigField(v_p_1115_, v_n_1116_);
lean_dec(v_n_1116_);
lean_dec(v_p_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0(lean_object* v_cfg_1118_){
_start:
{
lean_object* v_binDir_1119_; 
v_binDir_1119_ = lean_ctor_get(v_cfg_1118_, 8);
lean_inc_ref(v_binDir_1119_);
return v_binDir_1119_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lake_PackageConfig_binDir___proj___redArg___lam__0(v_cfg_1120_);
lean_dec_ref(v_cfg_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__1(lean_object* v_val_1122_, lean_object* v_cfg_1123_){
_start:
{
lean_object* v_toWorkspaceConfig_1124_; lean_object* v_toLeanConfig_1125_; uint8_t v_bootstrap_1126_; lean_object* v_extraDepTargets_1127_; uint8_t v_precompileModules_1128_; lean_object* v_moreGlobalServerArgs_1129_; lean_object* v_srcDir_1130_; lean_object* v_buildDir_1131_; lean_object* v_leanLibDir_1132_; lean_object* v_nativeLibDir_1133_; lean_object* v_irDir_1134_; lean_object* v_releaseRepo_1135_; lean_object* v_buildArchive_1136_; uint8_t v_preferReleaseBuild_1137_; lean_object* v_downloadCacheService_x3f_1138_; lean_object* v_testDriver_1139_; lean_object* v_testDriverArgs_1140_; lean_object* v_lintDriver_1141_; lean_object* v_lintDriverArgs_1142_; lean_object* v_version_1143_; lean_object* v_versionTags_1144_; lean_object* v_description_1145_; lean_object* v_keywords_1146_; lean_object* v_homepage_1147_; lean_object* v_license_1148_; lean_object* v_licenseFiles_1149_; lean_object* v_readmeFile_1150_; uint8_t v_reservoir_1151_; lean_object* v_enableArtifactCache_x3f_1152_; lean_object* v_restoreAllArtifacts_x3f_1153_; uint8_t v_libPrefixOnWindows_1154_; uint8_t v_allowImportAll_1155_; lean_object* v_builtinLint_x3f_1156_; lean_object* v_checks_1157_; uint8_t v_fixedToolchain_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_toWorkspaceConfig_1124_ = lean_ctor_get(v_cfg_1123_, 0);
v_toLeanConfig_1125_ = lean_ctor_get(v_cfg_1123_, 1);
v_bootstrap_1126_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29);
v_extraDepTargets_1127_ = lean_ctor_get(v_cfg_1123_, 2);
v_precompileModules_1128_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1129_ = lean_ctor_get(v_cfg_1123_, 3);
v_srcDir_1130_ = lean_ctor_get(v_cfg_1123_, 4);
v_buildDir_1131_ = lean_ctor_get(v_cfg_1123_, 5);
v_leanLibDir_1132_ = lean_ctor_get(v_cfg_1123_, 6);
v_nativeLibDir_1133_ = lean_ctor_get(v_cfg_1123_, 7);
v_irDir_1134_ = lean_ctor_get(v_cfg_1123_, 9);
v_releaseRepo_1135_ = lean_ctor_get(v_cfg_1123_, 10);
v_buildArchive_1136_ = lean_ctor_get(v_cfg_1123_, 11);
v_preferReleaseBuild_1137_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1138_ = lean_ctor_get(v_cfg_1123_, 12);
v_testDriver_1139_ = lean_ctor_get(v_cfg_1123_, 13);
v_testDriverArgs_1140_ = lean_ctor_get(v_cfg_1123_, 14);
v_lintDriver_1141_ = lean_ctor_get(v_cfg_1123_, 15);
v_lintDriverArgs_1142_ = lean_ctor_get(v_cfg_1123_, 16);
v_version_1143_ = lean_ctor_get(v_cfg_1123_, 17);
v_versionTags_1144_ = lean_ctor_get(v_cfg_1123_, 18);
v_description_1145_ = lean_ctor_get(v_cfg_1123_, 19);
v_keywords_1146_ = lean_ctor_get(v_cfg_1123_, 20);
v_homepage_1147_ = lean_ctor_get(v_cfg_1123_, 21);
v_license_1148_ = lean_ctor_get(v_cfg_1123_, 22);
v_licenseFiles_1149_ = lean_ctor_get(v_cfg_1123_, 23);
v_readmeFile_1150_ = lean_ctor_get(v_cfg_1123_, 24);
v_reservoir_1151_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1152_ = lean_ctor_get(v_cfg_1123_, 25);
v_restoreAllArtifacts_x3f_1153_ = lean_ctor_get(v_cfg_1123_, 26);
v_libPrefixOnWindows_1154_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29 + 4);
v_allowImportAll_1155_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1156_ = lean_ctor_get(v_cfg_1123_, 27);
v_checks_1157_ = lean_ctor_get(v_cfg_1123_, 28);
v_fixedToolchain_1158_ = lean_ctor_get_uint8(v_cfg_1123_, sizeof(void*)*29 + 6);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_cfg_1123_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_cfg_1123_, 8);
lean_dec(v_unused_1166_);
v___x_1160_ = v_cfg_1123_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_checks_1157_);
lean_inc(v_builtinLint_x3f_1156_);
lean_inc(v_restoreAllArtifacts_x3f_1153_);
lean_inc(v_enableArtifactCache_x3f_1152_);
lean_inc(v_readmeFile_1150_);
lean_inc(v_licenseFiles_1149_);
lean_inc(v_license_1148_);
lean_inc(v_homepage_1147_);
lean_inc(v_keywords_1146_);
lean_inc(v_description_1145_);
lean_inc(v_versionTags_1144_);
lean_inc(v_version_1143_);
lean_inc(v_lintDriverArgs_1142_);
lean_inc(v_lintDriver_1141_);
lean_inc(v_testDriverArgs_1140_);
lean_inc(v_testDriver_1139_);
lean_inc(v_downloadCacheService_x3f_1138_);
lean_inc(v_buildArchive_1136_);
lean_inc(v_releaseRepo_1135_);
lean_inc(v_irDir_1134_);
lean_inc(v_nativeLibDir_1133_);
lean_inc(v_leanLibDir_1132_);
lean_inc(v_buildDir_1131_);
lean_inc(v_srcDir_1130_);
lean_inc(v_moreGlobalServerArgs_1129_);
lean_inc(v_extraDepTargets_1127_);
lean_inc(v_toLeanConfig_1125_);
lean_inc(v_toWorkspaceConfig_1124_);
lean_dec(v_cfg_1123_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 8, v_val_1122_);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_toWorkspaceConfig_1124_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_toLeanConfig_1125_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_extraDepTargets_1127_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_moreGlobalServerArgs_1129_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_srcDir_1130_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_buildDir_1131_);
lean_ctor_set(v_reuseFailAlloc_1164_, 6, v_leanLibDir_1132_);
lean_ctor_set(v_reuseFailAlloc_1164_, 7, v_nativeLibDir_1133_);
lean_ctor_set(v_reuseFailAlloc_1164_, 8, v_val_1122_);
lean_ctor_set(v_reuseFailAlloc_1164_, 9, v_irDir_1134_);
lean_ctor_set(v_reuseFailAlloc_1164_, 10, v_releaseRepo_1135_);
lean_ctor_set(v_reuseFailAlloc_1164_, 11, v_buildArchive_1136_);
lean_ctor_set(v_reuseFailAlloc_1164_, 12, v_downloadCacheService_x3f_1138_);
lean_ctor_set(v_reuseFailAlloc_1164_, 13, v_testDriver_1139_);
lean_ctor_set(v_reuseFailAlloc_1164_, 14, v_testDriverArgs_1140_);
lean_ctor_set(v_reuseFailAlloc_1164_, 15, v_lintDriver_1141_);
lean_ctor_set(v_reuseFailAlloc_1164_, 16, v_lintDriverArgs_1142_);
lean_ctor_set(v_reuseFailAlloc_1164_, 17, v_version_1143_);
lean_ctor_set(v_reuseFailAlloc_1164_, 18, v_versionTags_1144_);
lean_ctor_set(v_reuseFailAlloc_1164_, 19, v_description_1145_);
lean_ctor_set(v_reuseFailAlloc_1164_, 20, v_keywords_1146_);
lean_ctor_set(v_reuseFailAlloc_1164_, 21, v_homepage_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 22, v_license_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 23, v_licenseFiles_1149_);
lean_ctor_set(v_reuseFailAlloc_1164_, 24, v_readmeFile_1150_);
lean_ctor_set(v_reuseFailAlloc_1164_, 25, v_enableArtifactCache_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 26, v_restoreAllArtifacts_x3f_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 27, v_builtinLint_x3f_1156_);
lean_ctor_set(v_reuseFailAlloc_1164_, 28, v_checks_1157_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29, v_bootstrap_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29 + 1, v_precompileModules_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29 + 3, v_reservoir_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29 + 5, v_allowImportAll_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1164_, sizeof(void*)*29 + 6, v_fixedToolchain_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__2(lean_object* v_f_1167_, lean_object* v_cfg_1168_){
_start:
{
lean_object* v_toWorkspaceConfig_1169_; lean_object* v_toLeanConfig_1170_; uint8_t v_bootstrap_1171_; lean_object* v_extraDepTargets_1172_; uint8_t v_precompileModules_1173_; lean_object* v_moreGlobalServerArgs_1174_; lean_object* v_srcDir_1175_; lean_object* v_buildDir_1176_; lean_object* v_leanLibDir_1177_; lean_object* v_nativeLibDir_1178_; lean_object* v_binDir_1179_; lean_object* v_irDir_1180_; lean_object* v_releaseRepo_1181_; lean_object* v_buildArchive_1182_; uint8_t v_preferReleaseBuild_1183_; lean_object* v_downloadCacheService_x3f_1184_; lean_object* v_testDriver_1185_; lean_object* v_testDriverArgs_1186_; lean_object* v_lintDriver_1187_; lean_object* v_lintDriverArgs_1188_; lean_object* v_version_1189_; lean_object* v_versionTags_1190_; lean_object* v_description_1191_; lean_object* v_keywords_1192_; lean_object* v_homepage_1193_; lean_object* v_license_1194_; lean_object* v_licenseFiles_1195_; lean_object* v_readmeFile_1196_; uint8_t v_reservoir_1197_; lean_object* v_enableArtifactCache_x3f_1198_; lean_object* v_restoreAllArtifacts_x3f_1199_; uint8_t v_libPrefixOnWindows_1200_; uint8_t v_allowImportAll_1201_; lean_object* v_builtinLint_x3f_1202_; lean_object* v_checks_1203_; uint8_t v_fixedToolchain_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
v_toWorkspaceConfig_1169_ = lean_ctor_get(v_cfg_1168_, 0);
v_toLeanConfig_1170_ = lean_ctor_get(v_cfg_1168_, 1);
v_bootstrap_1171_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29);
v_extraDepTargets_1172_ = lean_ctor_get(v_cfg_1168_, 2);
v_precompileModules_1173_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1174_ = lean_ctor_get(v_cfg_1168_, 3);
v_srcDir_1175_ = lean_ctor_get(v_cfg_1168_, 4);
v_buildDir_1176_ = lean_ctor_get(v_cfg_1168_, 5);
v_leanLibDir_1177_ = lean_ctor_get(v_cfg_1168_, 6);
v_nativeLibDir_1178_ = lean_ctor_get(v_cfg_1168_, 7);
v_binDir_1179_ = lean_ctor_get(v_cfg_1168_, 8);
v_irDir_1180_ = lean_ctor_get(v_cfg_1168_, 9);
v_releaseRepo_1181_ = lean_ctor_get(v_cfg_1168_, 10);
v_buildArchive_1182_ = lean_ctor_get(v_cfg_1168_, 11);
v_preferReleaseBuild_1183_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1184_ = lean_ctor_get(v_cfg_1168_, 12);
v_testDriver_1185_ = lean_ctor_get(v_cfg_1168_, 13);
v_testDriverArgs_1186_ = lean_ctor_get(v_cfg_1168_, 14);
v_lintDriver_1187_ = lean_ctor_get(v_cfg_1168_, 15);
v_lintDriverArgs_1188_ = lean_ctor_get(v_cfg_1168_, 16);
v_version_1189_ = lean_ctor_get(v_cfg_1168_, 17);
v_versionTags_1190_ = lean_ctor_get(v_cfg_1168_, 18);
v_description_1191_ = lean_ctor_get(v_cfg_1168_, 19);
v_keywords_1192_ = lean_ctor_get(v_cfg_1168_, 20);
v_homepage_1193_ = lean_ctor_get(v_cfg_1168_, 21);
v_license_1194_ = lean_ctor_get(v_cfg_1168_, 22);
v_licenseFiles_1195_ = lean_ctor_get(v_cfg_1168_, 23);
v_readmeFile_1196_ = lean_ctor_get(v_cfg_1168_, 24);
v_reservoir_1197_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1198_ = lean_ctor_get(v_cfg_1168_, 25);
v_restoreAllArtifacts_x3f_1199_ = lean_ctor_get(v_cfg_1168_, 26);
v_libPrefixOnWindows_1200_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29 + 4);
v_allowImportAll_1201_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1202_ = lean_ctor_get(v_cfg_1168_, 27);
v_checks_1203_ = lean_ctor_get(v_cfg_1168_, 28);
v_fixedToolchain_1204_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*29 + 6);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_cfg_1168_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1206_ = v_cfg_1168_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_checks_1203_);
lean_inc(v_builtinLint_x3f_1202_);
lean_inc(v_restoreAllArtifacts_x3f_1199_);
lean_inc(v_enableArtifactCache_x3f_1198_);
lean_inc(v_readmeFile_1196_);
lean_inc(v_licenseFiles_1195_);
lean_inc(v_license_1194_);
lean_inc(v_homepage_1193_);
lean_inc(v_keywords_1192_);
lean_inc(v_description_1191_);
lean_inc(v_versionTags_1190_);
lean_inc(v_version_1189_);
lean_inc(v_lintDriverArgs_1188_);
lean_inc(v_lintDriver_1187_);
lean_inc(v_testDriverArgs_1186_);
lean_inc(v_testDriver_1185_);
lean_inc(v_downloadCacheService_x3f_1184_);
lean_inc(v_buildArchive_1182_);
lean_inc(v_releaseRepo_1181_);
lean_inc(v_irDir_1180_);
lean_inc(v_binDir_1179_);
lean_inc(v_nativeLibDir_1178_);
lean_inc(v_leanLibDir_1177_);
lean_inc(v_buildDir_1176_);
lean_inc(v_srcDir_1175_);
lean_inc(v_moreGlobalServerArgs_1174_);
lean_inc(v_extraDepTargets_1172_);
lean_inc(v_toLeanConfig_1170_);
lean_inc(v_toWorkspaceConfig_1169_);
lean_dec(v_cfg_1168_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_apply_1(v_f_1167_, v_binDir_1179_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 8, v___x_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_toWorkspaceConfig_1169_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_toLeanConfig_1170_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_extraDepTargets_1172_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_moreGlobalServerArgs_1174_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_srcDir_1175_);
lean_ctor_set(v_reuseFailAlloc_1211_, 5, v_buildDir_1176_);
lean_ctor_set(v_reuseFailAlloc_1211_, 6, v_leanLibDir_1177_);
lean_ctor_set(v_reuseFailAlloc_1211_, 7, v_nativeLibDir_1178_);
lean_ctor_set(v_reuseFailAlloc_1211_, 8, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 9, v_irDir_1180_);
lean_ctor_set(v_reuseFailAlloc_1211_, 10, v_releaseRepo_1181_);
lean_ctor_set(v_reuseFailAlloc_1211_, 11, v_buildArchive_1182_);
lean_ctor_set(v_reuseFailAlloc_1211_, 12, v_downloadCacheService_x3f_1184_);
lean_ctor_set(v_reuseFailAlloc_1211_, 13, v_testDriver_1185_);
lean_ctor_set(v_reuseFailAlloc_1211_, 14, v_testDriverArgs_1186_);
lean_ctor_set(v_reuseFailAlloc_1211_, 15, v_lintDriver_1187_);
lean_ctor_set(v_reuseFailAlloc_1211_, 16, v_lintDriverArgs_1188_);
lean_ctor_set(v_reuseFailAlloc_1211_, 17, v_version_1189_);
lean_ctor_set(v_reuseFailAlloc_1211_, 18, v_versionTags_1190_);
lean_ctor_set(v_reuseFailAlloc_1211_, 19, v_description_1191_);
lean_ctor_set(v_reuseFailAlloc_1211_, 20, v_keywords_1192_);
lean_ctor_set(v_reuseFailAlloc_1211_, 21, v_homepage_1193_);
lean_ctor_set(v_reuseFailAlloc_1211_, 22, v_license_1194_);
lean_ctor_set(v_reuseFailAlloc_1211_, 23, v_licenseFiles_1195_);
lean_ctor_set(v_reuseFailAlloc_1211_, 24, v_readmeFile_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 25, v_enableArtifactCache_x3f_1198_);
lean_ctor_set(v_reuseFailAlloc_1211_, 26, v_restoreAllArtifacts_x3f_1199_);
lean_ctor_set(v_reuseFailAlloc_1211_, 27, v_builtinLint_x3f_1202_);
lean_ctor_set(v_reuseFailAlloc_1211_, 28, v_checks_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29, v_bootstrap_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29 + 1, v_precompileModules_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29 + 3, v_reservoir_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29 + 5, v_allowImportAll_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*29 + 6, v_fixedToolchain_1204_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3(lean_object* v_x_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lake_defaultBinDir;
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___lam__3___boxed(lean_object* v_x_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lake_PackageConfig_binDir___proj___redArg___lam__3(v_x_1215_);
lean_dec_ref(v_x_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg(){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = ((lean_object*)(l_Lake_PackageConfig_binDir___proj___redArg___closed__4));
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___redArg___boxed(lean_object* v___dummy_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lake_PackageConfig_binDir___proj___redArg();
return v_res_1229_;
}
}
static lean_object* _init_l_Lake_PackageConfig_binDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lake_PackageConfig_binDir___proj___redArg();
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj(lean_object* v_p_1231_, lean_object* v_n_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___proj___boxed(lean_object* v_p_1234_, lean_object* v_n_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lake_PackageConfig_binDir___proj(v_p_1234_, v_n_1235_);
lean_dec(v_n_1235_);
lean_dec(v_p_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___redArg___boxed(lean_object* v___dummy_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lake_PackageConfig_binDir_instConfigField___redArg();
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField(lean_object* v_p_1241_, lean_object* v_n_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_obj_once(&l_Lake_PackageConfig_binDir___proj___closed__0, &l_Lake_PackageConfig_binDir___proj___closed__0_once, _init_l_Lake_PackageConfig_binDir___proj___closed__0);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir_instConfigField___boxed(lean_object* v_p_1244_, lean_object* v_n_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lake_PackageConfig_binDir_instConfigField(v_p_1244_, v_n_1245_);
lean_dec(v_n_1245_);
lean_dec(v_p_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0(lean_object* v_cfg_1247_){
_start:
{
lean_object* v_irDir_1248_; 
v_irDir_1248_ = lean_ctor_get(v_cfg_1247_, 9);
lean_inc_ref(v_irDir_1248_);
return v_irDir_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__0___boxed(lean_object* v_cfg_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lake_PackageConfig_irDir___proj___redArg___lam__0(v_cfg_1249_);
lean_dec_ref(v_cfg_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__1(lean_object* v_val_1251_, lean_object* v_cfg_1252_){
_start:
{
lean_object* v_toWorkspaceConfig_1253_; lean_object* v_toLeanConfig_1254_; uint8_t v_bootstrap_1255_; lean_object* v_extraDepTargets_1256_; uint8_t v_precompileModules_1257_; lean_object* v_moreGlobalServerArgs_1258_; lean_object* v_srcDir_1259_; lean_object* v_buildDir_1260_; lean_object* v_leanLibDir_1261_; lean_object* v_nativeLibDir_1262_; lean_object* v_binDir_1263_; lean_object* v_releaseRepo_1264_; lean_object* v_buildArchive_1265_; uint8_t v_preferReleaseBuild_1266_; lean_object* v_downloadCacheService_x3f_1267_; lean_object* v_testDriver_1268_; lean_object* v_testDriverArgs_1269_; lean_object* v_lintDriver_1270_; lean_object* v_lintDriverArgs_1271_; lean_object* v_version_1272_; lean_object* v_versionTags_1273_; lean_object* v_description_1274_; lean_object* v_keywords_1275_; lean_object* v_homepage_1276_; lean_object* v_license_1277_; lean_object* v_licenseFiles_1278_; lean_object* v_readmeFile_1279_; uint8_t v_reservoir_1280_; lean_object* v_enableArtifactCache_x3f_1281_; lean_object* v_restoreAllArtifacts_x3f_1282_; uint8_t v_libPrefixOnWindows_1283_; uint8_t v_allowImportAll_1284_; lean_object* v_builtinLint_x3f_1285_; lean_object* v_checks_1286_; uint8_t v_fixedToolchain_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_toWorkspaceConfig_1253_ = lean_ctor_get(v_cfg_1252_, 0);
v_toLeanConfig_1254_ = lean_ctor_get(v_cfg_1252_, 1);
v_bootstrap_1255_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29);
v_extraDepTargets_1256_ = lean_ctor_get(v_cfg_1252_, 2);
v_precompileModules_1257_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1258_ = lean_ctor_get(v_cfg_1252_, 3);
v_srcDir_1259_ = lean_ctor_get(v_cfg_1252_, 4);
v_buildDir_1260_ = lean_ctor_get(v_cfg_1252_, 5);
v_leanLibDir_1261_ = lean_ctor_get(v_cfg_1252_, 6);
v_nativeLibDir_1262_ = lean_ctor_get(v_cfg_1252_, 7);
v_binDir_1263_ = lean_ctor_get(v_cfg_1252_, 8);
v_releaseRepo_1264_ = lean_ctor_get(v_cfg_1252_, 10);
v_buildArchive_1265_ = lean_ctor_get(v_cfg_1252_, 11);
v_preferReleaseBuild_1266_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1267_ = lean_ctor_get(v_cfg_1252_, 12);
v_testDriver_1268_ = lean_ctor_get(v_cfg_1252_, 13);
v_testDriverArgs_1269_ = lean_ctor_get(v_cfg_1252_, 14);
v_lintDriver_1270_ = lean_ctor_get(v_cfg_1252_, 15);
v_lintDriverArgs_1271_ = lean_ctor_get(v_cfg_1252_, 16);
v_version_1272_ = lean_ctor_get(v_cfg_1252_, 17);
v_versionTags_1273_ = lean_ctor_get(v_cfg_1252_, 18);
v_description_1274_ = lean_ctor_get(v_cfg_1252_, 19);
v_keywords_1275_ = lean_ctor_get(v_cfg_1252_, 20);
v_homepage_1276_ = lean_ctor_get(v_cfg_1252_, 21);
v_license_1277_ = lean_ctor_get(v_cfg_1252_, 22);
v_licenseFiles_1278_ = lean_ctor_get(v_cfg_1252_, 23);
v_readmeFile_1279_ = lean_ctor_get(v_cfg_1252_, 24);
v_reservoir_1280_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1281_ = lean_ctor_get(v_cfg_1252_, 25);
v_restoreAllArtifacts_x3f_1282_ = lean_ctor_get(v_cfg_1252_, 26);
v_libPrefixOnWindows_1283_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29 + 4);
v_allowImportAll_1284_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1285_ = lean_ctor_get(v_cfg_1252_, 27);
v_checks_1286_ = lean_ctor_get(v_cfg_1252_, 28);
v_fixedToolchain_1287_ = lean_ctor_get_uint8(v_cfg_1252_, sizeof(void*)*29 + 6);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_cfg_1252_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_cfg_1252_, 9);
lean_dec(v_unused_1295_);
v___x_1289_ = v_cfg_1252_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_checks_1286_);
lean_inc(v_builtinLint_x3f_1285_);
lean_inc(v_restoreAllArtifacts_x3f_1282_);
lean_inc(v_enableArtifactCache_x3f_1281_);
lean_inc(v_readmeFile_1279_);
lean_inc(v_licenseFiles_1278_);
lean_inc(v_license_1277_);
lean_inc(v_homepage_1276_);
lean_inc(v_keywords_1275_);
lean_inc(v_description_1274_);
lean_inc(v_versionTags_1273_);
lean_inc(v_version_1272_);
lean_inc(v_lintDriverArgs_1271_);
lean_inc(v_lintDriver_1270_);
lean_inc(v_testDriverArgs_1269_);
lean_inc(v_testDriver_1268_);
lean_inc(v_downloadCacheService_x3f_1267_);
lean_inc(v_buildArchive_1265_);
lean_inc(v_releaseRepo_1264_);
lean_inc(v_binDir_1263_);
lean_inc(v_nativeLibDir_1262_);
lean_inc(v_leanLibDir_1261_);
lean_inc(v_buildDir_1260_);
lean_inc(v_srcDir_1259_);
lean_inc(v_moreGlobalServerArgs_1258_);
lean_inc(v_extraDepTargets_1256_);
lean_inc(v_toLeanConfig_1254_);
lean_inc(v_toWorkspaceConfig_1253_);
lean_dec(v_cfg_1252_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 9, v_val_1251_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_toWorkspaceConfig_1253_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_toLeanConfig_1254_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_extraDepTargets_1256_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_moreGlobalServerArgs_1258_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_srcDir_1259_);
lean_ctor_set(v_reuseFailAlloc_1293_, 5, v_buildDir_1260_);
lean_ctor_set(v_reuseFailAlloc_1293_, 6, v_leanLibDir_1261_);
lean_ctor_set(v_reuseFailAlloc_1293_, 7, v_nativeLibDir_1262_);
lean_ctor_set(v_reuseFailAlloc_1293_, 8, v_binDir_1263_);
lean_ctor_set(v_reuseFailAlloc_1293_, 9, v_val_1251_);
lean_ctor_set(v_reuseFailAlloc_1293_, 10, v_releaseRepo_1264_);
lean_ctor_set(v_reuseFailAlloc_1293_, 11, v_buildArchive_1265_);
lean_ctor_set(v_reuseFailAlloc_1293_, 12, v_downloadCacheService_x3f_1267_);
lean_ctor_set(v_reuseFailAlloc_1293_, 13, v_testDriver_1268_);
lean_ctor_set(v_reuseFailAlloc_1293_, 14, v_testDriverArgs_1269_);
lean_ctor_set(v_reuseFailAlloc_1293_, 15, v_lintDriver_1270_);
lean_ctor_set(v_reuseFailAlloc_1293_, 16, v_lintDriverArgs_1271_);
lean_ctor_set(v_reuseFailAlloc_1293_, 17, v_version_1272_);
lean_ctor_set(v_reuseFailAlloc_1293_, 18, v_versionTags_1273_);
lean_ctor_set(v_reuseFailAlloc_1293_, 19, v_description_1274_);
lean_ctor_set(v_reuseFailAlloc_1293_, 20, v_keywords_1275_);
lean_ctor_set(v_reuseFailAlloc_1293_, 21, v_homepage_1276_);
lean_ctor_set(v_reuseFailAlloc_1293_, 22, v_license_1277_);
lean_ctor_set(v_reuseFailAlloc_1293_, 23, v_licenseFiles_1278_);
lean_ctor_set(v_reuseFailAlloc_1293_, 24, v_readmeFile_1279_);
lean_ctor_set(v_reuseFailAlloc_1293_, 25, v_enableArtifactCache_x3f_1281_);
lean_ctor_set(v_reuseFailAlloc_1293_, 26, v_restoreAllArtifacts_x3f_1282_);
lean_ctor_set(v_reuseFailAlloc_1293_, 27, v_builtinLint_x3f_1285_);
lean_ctor_set(v_reuseFailAlloc_1293_, 28, v_checks_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29, v_bootstrap_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29 + 1, v_precompileModules_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29 + 3, v_reservoir_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29 + 5, v_allowImportAll_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1293_, sizeof(void*)*29 + 6, v_fixedToolchain_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__2(lean_object* v_f_1296_, lean_object* v_cfg_1297_){
_start:
{
lean_object* v_toWorkspaceConfig_1298_; lean_object* v_toLeanConfig_1299_; uint8_t v_bootstrap_1300_; lean_object* v_extraDepTargets_1301_; uint8_t v_precompileModules_1302_; lean_object* v_moreGlobalServerArgs_1303_; lean_object* v_srcDir_1304_; lean_object* v_buildDir_1305_; lean_object* v_leanLibDir_1306_; lean_object* v_nativeLibDir_1307_; lean_object* v_binDir_1308_; lean_object* v_irDir_1309_; lean_object* v_releaseRepo_1310_; lean_object* v_buildArchive_1311_; uint8_t v_preferReleaseBuild_1312_; lean_object* v_downloadCacheService_x3f_1313_; lean_object* v_testDriver_1314_; lean_object* v_testDriverArgs_1315_; lean_object* v_lintDriver_1316_; lean_object* v_lintDriverArgs_1317_; lean_object* v_version_1318_; lean_object* v_versionTags_1319_; lean_object* v_description_1320_; lean_object* v_keywords_1321_; lean_object* v_homepage_1322_; lean_object* v_license_1323_; lean_object* v_licenseFiles_1324_; lean_object* v_readmeFile_1325_; uint8_t v_reservoir_1326_; lean_object* v_enableArtifactCache_x3f_1327_; lean_object* v_restoreAllArtifacts_x3f_1328_; uint8_t v_libPrefixOnWindows_1329_; uint8_t v_allowImportAll_1330_; lean_object* v_builtinLint_x3f_1331_; lean_object* v_checks_1332_; uint8_t v_fixedToolchain_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_toWorkspaceConfig_1298_ = lean_ctor_get(v_cfg_1297_, 0);
v_toLeanConfig_1299_ = lean_ctor_get(v_cfg_1297_, 1);
v_bootstrap_1300_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29);
v_extraDepTargets_1301_ = lean_ctor_get(v_cfg_1297_, 2);
v_precompileModules_1302_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1303_ = lean_ctor_get(v_cfg_1297_, 3);
v_srcDir_1304_ = lean_ctor_get(v_cfg_1297_, 4);
v_buildDir_1305_ = lean_ctor_get(v_cfg_1297_, 5);
v_leanLibDir_1306_ = lean_ctor_get(v_cfg_1297_, 6);
v_nativeLibDir_1307_ = lean_ctor_get(v_cfg_1297_, 7);
v_binDir_1308_ = lean_ctor_get(v_cfg_1297_, 8);
v_irDir_1309_ = lean_ctor_get(v_cfg_1297_, 9);
v_releaseRepo_1310_ = lean_ctor_get(v_cfg_1297_, 10);
v_buildArchive_1311_ = lean_ctor_get(v_cfg_1297_, 11);
v_preferReleaseBuild_1312_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1313_ = lean_ctor_get(v_cfg_1297_, 12);
v_testDriver_1314_ = lean_ctor_get(v_cfg_1297_, 13);
v_testDriverArgs_1315_ = lean_ctor_get(v_cfg_1297_, 14);
v_lintDriver_1316_ = lean_ctor_get(v_cfg_1297_, 15);
v_lintDriverArgs_1317_ = lean_ctor_get(v_cfg_1297_, 16);
v_version_1318_ = lean_ctor_get(v_cfg_1297_, 17);
v_versionTags_1319_ = lean_ctor_get(v_cfg_1297_, 18);
v_description_1320_ = lean_ctor_get(v_cfg_1297_, 19);
v_keywords_1321_ = lean_ctor_get(v_cfg_1297_, 20);
v_homepage_1322_ = lean_ctor_get(v_cfg_1297_, 21);
v_license_1323_ = lean_ctor_get(v_cfg_1297_, 22);
v_licenseFiles_1324_ = lean_ctor_get(v_cfg_1297_, 23);
v_readmeFile_1325_ = lean_ctor_get(v_cfg_1297_, 24);
v_reservoir_1326_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1327_ = lean_ctor_get(v_cfg_1297_, 25);
v_restoreAllArtifacts_x3f_1328_ = lean_ctor_get(v_cfg_1297_, 26);
v_libPrefixOnWindows_1329_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29 + 4);
v_allowImportAll_1330_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1331_ = lean_ctor_get(v_cfg_1297_, 27);
v_checks_1332_ = lean_ctor_get(v_cfg_1297_, 28);
v_fixedToolchain_1333_ = lean_ctor_get_uint8(v_cfg_1297_, sizeof(void*)*29 + 6);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_cfg_1297_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v_cfg_1297_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_checks_1332_);
lean_inc(v_builtinLint_x3f_1331_);
lean_inc(v_restoreAllArtifacts_x3f_1328_);
lean_inc(v_enableArtifactCache_x3f_1327_);
lean_inc(v_readmeFile_1325_);
lean_inc(v_licenseFiles_1324_);
lean_inc(v_license_1323_);
lean_inc(v_homepage_1322_);
lean_inc(v_keywords_1321_);
lean_inc(v_description_1320_);
lean_inc(v_versionTags_1319_);
lean_inc(v_version_1318_);
lean_inc(v_lintDriverArgs_1317_);
lean_inc(v_lintDriver_1316_);
lean_inc(v_testDriverArgs_1315_);
lean_inc(v_testDriver_1314_);
lean_inc(v_downloadCacheService_x3f_1313_);
lean_inc(v_buildArchive_1311_);
lean_inc(v_releaseRepo_1310_);
lean_inc(v_irDir_1309_);
lean_inc(v_binDir_1308_);
lean_inc(v_nativeLibDir_1307_);
lean_inc(v_leanLibDir_1306_);
lean_inc(v_buildDir_1305_);
lean_inc(v_srcDir_1304_);
lean_inc(v_moreGlobalServerArgs_1303_);
lean_inc(v_extraDepTargets_1301_);
lean_inc(v_toLeanConfig_1299_);
lean_inc(v_toWorkspaceConfig_1298_);
lean_dec(v_cfg_1297_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_apply_1(v_f_1296_, v_irDir_1309_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 9, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_toWorkspaceConfig_1298_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_toLeanConfig_1299_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_extraDepTargets_1301_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_moreGlobalServerArgs_1303_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_srcDir_1304_);
lean_ctor_set(v_reuseFailAlloc_1340_, 5, v_buildDir_1305_);
lean_ctor_set(v_reuseFailAlloc_1340_, 6, v_leanLibDir_1306_);
lean_ctor_set(v_reuseFailAlloc_1340_, 7, v_nativeLibDir_1307_);
lean_ctor_set(v_reuseFailAlloc_1340_, 8, v_binDir_1308_);
lean_ctor_set(v_reuseFailAlloc_1340_, 9, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1340_, 10, v_releaseRepo_1310_);
lean_ctor_set(v_reuseFailAlloc_1340_, 11, v_buildArchive_1311_);
lean_ctor_set(v_reuseFailAlloc_1340_, 12, v_downloadCacheService_x3f_1313_);
lean_ctor_set(v_reuseFailAlloc_1340_, 13, v_testDriver_1314_);
lean_ctor_set(v_reuseFailAlloc_1340_, 14, v_testDriverArgs_1315_);
lean_ctor_set(v_reuseFailAlloc_1340_, 15, v_lintDriver_1316_);
lean_ctor_set(v_reuseFailAlloc_1340_, 16, v_lintDriverArgs_1317_);
lean_ctor_set(v_reuseFailAlloc_1340_, 17, v_version_1318_);
lean_ctor_set(v_reuseFailAlloc_1340_, 18, v_versionTags_1319_);
lean_ctor_set(v_reuseFailAlloc_1340_, 19, v_description_1320_);
lean_ctor_set(v_reuseFailAlloc_1340_, 20, v_keywords_1321_);
lean_ctor_set(v_reuseFailAlloc_1340_, 21, v_homepage_1322_);
lean_ctor_set(v_reuseFailAlloc_1340_, 22, v_license_1323_);
lean_ctor_set(v_reuseFailAlloc_1340_, 23, v_licenseFiles_1324_);
lean_ctor_set(v_reuseFailAlloc_1340_, 24, v_readmeFile_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 25, v_enableArtifactCache_x3f_1327_);
lean_ctor_set(v_reuseFailAlloc_1340_, 26, v_restoreAllArtifacts_x3f_1328_);
lean_ctor_set(v_reuseFailAlloc_1340_, 27, v_builtinLint_x3f_1331_);
lean_ctor_set(v_reuseFailAlloc_1340_, 28, v_checks_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29, v_bootstrap_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29 + 1, v_precompileModules_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29 + 3, v_reservoir_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29 + 5, v_allowImportAll_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*29 + 6, v_fixedToolchain_1333_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3(lean_object* v_x_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lake_defaultIrDir;
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___lam__3___boxed(lean_object* v_x_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lake_PackageConfig_irDir___proj___redArg___lam__3(v_x_1344_);
lean_dec_ref(v_x_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg(){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = ((lean_object*)(l_Lake_PackageConfig_irDir___proj___redArg___closed__4));
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___redArg___boxed(lean_object* v___dummy_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lake_PackageConfig_irDir___proj___redArg();
return v_res_1358_;
}
}
static lean_object* _init_l_Lake_PackageConfig_irDir___proj___closed__0(void){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lake_PackageConfig_irDir___proj___redArg();
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj(lean_object* v_p_1360_, lean_object* v_n_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___proj___boxed(lean_object* v_p_1363_, lean_object* v_n_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lake_PackageConfig_irDir___proj(v_p_1363_, v_n_1364_);
lean_dec(v_n_1364_);
lean_dec(v_p_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg(){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___redArg___boxed(lean_object* v___dummy_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lake_PackageConfig_irDir_instConfigField___redArg();
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField(lean_object* v_p_1370_, lean_object* v_n_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_obj_once(&l_Lake_PackageConfig_irDir___proj___closed__0, &l_Lake_PackageConfig_irDir___proj___closed__0_once, _init_l_Lake_PackageConfig_irDir___proj___closed__0);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir_instConfigField___boxed(lean_object* v_p_1373_, lean_object* v_n_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lake_PackageConfig_irDir_instConfigField(v_p_1373_, v_n_1374_);
lean_dec(v_n_1374_);
lean_dec(v_p_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(lean_object* v_cfg_1376_){
_start:
{
lean_object* v_releaseRepo_1377_; 
v_releaseRepo_1377_ = lean_ctor_get(v_cfg_1376_, 10);
lean_inc(v_releaseRepo_1377_);
return v_releaseRepo_1377_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0___boxed(lean_object* v_cfg_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__0(v_cfg_1378_);
lean_dec_ref(v_cfg_1378_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__1(lean_object* v_val_1380_, lean_object* v_cfg_1381_){
_start:
{
lean_object* v_toWorkspaceConfig_1382_; lean_object* v_toLeanConfig_1383_; uint8_t v_bootstrap_1384_; lean_object* v_extraDepTargets_1385_; uint8_t v_precompileModules_1386_; lean_object* v_moreGlobalServerArgs_1387_; lean_object* v_srcDir_1388_; lean_object* v_buildDir_1389_; lean_object* v_leanLibDir_1390_; lean_object* v_nativeLibDir_1391_; lean_object* v_binDir_1392_; lean_object* v_irDir_1393_; lean_object* v_buildArchive_1394_; uint8_t v_preferReleaseBuild_1395_; lean_object* v_downloadCacheService_x3f_1396_; lean_object* v_testDriver_1397_; lean_object* v_testDriverArgs_1398_; lean_object* v_lintDriver_1399_; lean_object* v_lintDriverArgs_1400_; lean_object* v_version_1401_; lean_object* v_versionTags_1402_; lean_object* v_description_1403_; lean_object* v_keywords_1404_; lean_object* v_homepage_1405_; lean_object* v_license_1406_; lean_object* v_licenseFiles_1407_; lean_object* v_readmeFile_1408_; uint8_t v_reservoir_1409_; lean_object* v_enableArtifactCache_x3f_1410_; lean_object* v_restoreAllArtifacts_x3f_1411_; uint8_t v_libPrefixOnWindows_1412_; uint8_t v_allowImportAll_1413_; lean_object* v_builtinLint_x3f_1414_; lean_object* v_checks_1415_; uint8_t v_fixedToolchain_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_toWorkspaceConfig_1382_ = lean_ctor_get(v_cfg_1381_, 0);
v_toLeanConfig_1383_ = lean_ctor_get(v_cfg_1381_, 1);
v_bootstrap_1384_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29);
v_extraDepTargets_1385_ = lean_ctor_get(v_cfg_1381_, 2);
v_precompileModules_1386_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1387_ = lean_ctor_get(v_cfg_1381_, 3);
v_srcDir_1388_ = lean_ctor_get(v_cfg_1381_, 4);
v_buildDir_1389_ = lean_ctor_get(v_cfg_1381_, 5);
v_leanLibDir_1390_ = lean_ctor_get(v_cfg_1381_, 6);
v_nativeLibDir_1391_ = lean_ctor_get(v_cfg_1381_, 7);
v_binDir_1392_ = lean_ctor_get(v_cfg_1381_, 8);
v_irDir_1393_ = lean_ctor_get(v_cfg_1381_, 9);
v_buildArchive_1394_ = lean_ctor_get(v_cfg_1381_, 11);
v_preferReleaseBuild_1395_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1396_ = lean_ctor_get(v_cfg_1381_, 12);
v_testDriver_1397_ = lean_ctor_get(v_cfg_1381_, 13);
v_testDriverArgs_1398_ = lean_ctor_get(v_cfg_1381_, 14);
v_lintDriver_1399_ = lean_ctor_get(v_cfg_1381_, 15);
v_lintDriverArgs_1400_ = lean_ctor_get(v_cfg_1381_, 16);
v_version_1401_ = lean_ctor_get(v_cfg_1381_, 17);
v_versionTags_1402_ = lean_ctor_get(v_cfg_1381_, 18);
v_description_1403_ = lean_ctor_get(v_cfg_1381_, 19);
v_keywords_1404_ = lean_ctor_get(v_cfg_1381_, 20);
v_homepage_1405_ = lean_ctor_get(v_cfg_1381_, 21);
v_license_1406_ = lean_ctor_get(v_cfg_1381_, 22);
v_licenseFiles_1407_ = lean_ctor_get(v_cfg_1381_, 23);
v_readmeFile_1408_ = lean_ctor_get(v_cfg_1381_, 24);
v_reservoir_1409_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1410_ = lean_ctor_get(v_cfg_1381_, 25);
v_restoreAllArtifacts_x3f_1411_ = lean_ctor_get(v_cfg_1381_, 26);
v_libPrefixOnWindows_1412_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29 + 4);
v_allowImportAll_1413_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1414_ = lean_ctor_get(v_cfg_1381_, 27);
v_checks_1415_ = lean_ctor_get(v_cfg_1381_, 28);
v_fixedToolchain_1416_ = lean_ctor_get_uint8(v_cfg_1381_, sizeof(void*)*29 + 6);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_cfg_1381_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_cfg_1381_, 10);
lean_dec(v_unused_1424_);
v___x_1418_ = v_cfg_1381_;
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
lean_inc(v_downloadCacheService_x3f_1396_);
lean_inc(v_buildArchive_1394_);
lean_inc(v_irDir_1393_);
lean_inc(v_binDir_1392_);
lean_inc(v_nativeLibDir_1391_);
lean_inc(v_leanLibDir_1390_);
lean_inc(v_buildDir_1389_);
lean_inc(v_srcDir_1388_);
lean_inc(v_moreGlobalServerArgs_1387_);
lean_inc(v_extraDepTargets_1385_);
lean_inc(v_toLeanConfig_1383_);
lean_inc(v_toWorkspaceConfig_1382_);
lean_dec(v_cfg_1381_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 10, v_val_1380_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_toWorkspaceConfig_1382_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_toLeanConfig_1383_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_extraDepTargets_1385_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_moreGlobalServerArgs_1387_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_srcDir_1388_);
lean_ctor_set(v_reuseFailAlloc_1422_, 5, v_buildDir_1389_);
lean_ctor_set(v_reuseFailAlloc_1422_, 6, v_leanLibDir_1390_);
lean_ctor_set(v_reuseFailAlloc_1422_, 7, v_nativeLibDir_1391_);
lean_ctor_set(v_reuseFailAlloc_1422_, 8, v_binDir_1392_);
lean_ctor_set(v_reuseFailAlloc_1422_, 9, v_irDir_1393_);
lean_ctor_set(v_reuseFailAlloc_1422_, 10, v_val_1380_);
lean_ctor_set(v_reuseFailAlloc_1422_, 11, v_buildArchive_1394_);
lean_ctor_set(v_reuseFailAlloc_1422_, 12, v_downloadCacheService_x3f_1396_);
lean_ctor_set(v_reuseFailAlloc_1422_, 13, v_testDriver_1397_);
lean_ctor_set(v_reuseFailAlloc_1422_, 14, v_testDriverArgs_1398_);
lean_ctor_set(v_reuseFailAlloc_1422_, 15, v_lintDriver_1399_);
lean_ctor_set(v_reuseFailAlloc_1422_, 16, v_lintDriverArgs_1400_);
lean_ctor_set(v_reuseFailAlloc_1422_, 17, v_version_1401_);
lean_ctor_set(v_reuseFailAlloc_1422_, 18, v_versionTags_1402_);
lean_ctor_set(v_reuseFailAlloc_1422_, 19, v_description_1403_);
lean_ctor_set(v_reuseFailAlloc_1422_, 20, v_keywords_1404_);
lean_ctor_set(v_reuseFailAlloc_1422_, 21, v_homepage_1405_);
lean_ctor_set(v_reuseFailAlloc_1422_, 22, v_license_1406_);
lean_ctor_set(v_reuseFailAlloc_1422_, 23, v_licenseFiles_1407_);
lean_ctor_set(v_reuseFailAlloc_1422_, 24, v_readmeFile_1408_);
lean_ctor_set(v_reuseFailAlloc_1422_, 25, v_enableArtifactCache_x3f_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 26, v_restoreAllArtifacts_x3f_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 27, v_builtinLint_x3f_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 28, v_checks_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29, v_bootstrap_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29 + 1, v_precompileModules_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29 + 3, v_reservoir_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29 + 5, v_allowImportAll_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*29 + 6, v_fixedToolchain_1416_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__2(lean_object* v_f_1425_, lean_object* v_cfg_1426_){
_start:
{
lean_object* v_toWorkspaceConfig_1427_; lean_object* v_toLeanConfig_1428_; uint8_t v_bootstrap_1429_; lean_object* v_extraDepTargets_1430_; uint8_t v_precompileModules_1431_; lean_object* v_moreGlobalServerArgs_1432_; lean_object* v_srcDir_1433_; lean_object* v_buildDir_1434_; lean_object* v_leanLibDir_1435_; lean_object* v_nativeLibDir_1436_; lean_object* v_binDir_1437_; lean_object* v_irDir_1438_; lean_object* v_releaseRepo_1439_; lean_object* v_buildArchive_1440_; uint8_t v_preferReleaseBuild_1441_; lean_object* v_downloadCacheService_x3f_1442_; lean_object* v_testDriver_1443_; lean_object* v_testDriverArgs_1444_; lean_object* v_lintDriver_1445_; lean_object* v_lintDriverArgs_1446_; lean_object* v_version_1447_; lean_object* v_versionTags_1448_; lean_object* v_description_1449_; lean_object* v_keywords_1450_; lean_object* v_homepage_1451_; lean_object* v_license_1452_; lean_object* v_licenseFiles_1453_; lean_object* v_readmeFile_1454_; uint8_t v_reservoir_1455_; lean_object* v_enableArtifactCache_x3f_1456_; lean_object* v_restoreAllArtifacts_x3f_1457_; uint8_t v_libPrefixOnWindows_1458_; uint8_t v_allowImportAll_1459_; lean_object* v_builtinLint_x3f_1460_; lean_object* v_checks_1461_; uint8_t v_fixedToolchain_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_toWorkspaceConfig_1427_ = lean_ctor_get(v_cfg_1426_, 0);
v_toLeanConfig_1428_ = lean_ctor_get(v_cfg_1426_, 1);
v_bootstrap_1429_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29);
v_extraDepTargets_1430_ = lean_ctor_get(v_cfg_1426_, 2);
v_precompileModules_1431_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1432_ = lean_ctor_get(v_cfg_1426_, 3);
v_srcDir_1433_ = lean_ctor_get(v_cfg_1426_, 4);
v_buildDir_1434_ = lean_ctor_get(v_cfg_1426_, 5);
v_leanLibDir_1435_ = lean_ctor_get(v_cfg_1426_, 6);
v_nativeLibDir_1436_ = lean_ctor_get(v_cfg_1426_, 7);
v_binDir_1437_ = lean_ctor_get(v_cfg_1426_, 8);
v_irDir_1438_ = lean_ctor_get(v_cfg_1426_, 9);
v_releaseRepo_1439_ = lean_ctor_get(v_cfg_1426_, 10);
v_buildArchive_1440_ = lean_ctor_get(v_cfg_1426_, 11);
v_preferReleaseBuild_1441_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1442_ = lean_ctor_get(v_cfg_1426_, 12);
v_testDriver_1443_ = lean_ctor_get(v_cfg_1426_, 13);
v_testDriverArgs_1444_ = lean_ctor_get(v_cfg_1426_, 14);
v_lintDriver_1445_ = lean_ctor_get(v_cfg_1426_, 15);
v_lintDriverArgs_1446_ = lean_ctor_get(v_cfg_1426_, 16);
v_version_1447_ = lean_ctor_get(v_cfg_1426_, 17);
v_versionTags_1448_ = lean_ctor_get(v_cfg_1426_, 18);
v_description_1449_ = lean_ctor_get(v_cfg_1426_, 19);
v_keywords_1450_ = lean_ctor_get(v_cfg_1426_, 20);
v_homepage_1451_ = lean_ctor_get(v_cfg_1426_, 21);
v_license_1452_ = lean_ctor_get(v_cfg_1426_, 22);
v_licenseFiles_1453_ = lean_ctor_get(v_cfg_1426_, 23);
v_readmeFile_1454_ = lean_ctor_get(v_cfg_1426_, 24);
v_reservoir_1455_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1456_ = lean_ctor_get(v_cfg_1426_, 25);
v_restoreAllArtifacts_x3f_1457_ = lean_ctor_get(v_cfg_1426_, 26);
v_libPrefixOnWindows_1458_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29 + 4);
v_allowImportAll_1459_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1460_ = lean_ctor_get(v_cfg_1426_, 27);
v_checks_1461_ = lean_ctor_get(v_cfg_1426_, 28);
v_fixedToolchain_1462_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*29 + 6);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_cfg_1426_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_cfg_1426_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_checks_1461_);
lean_inc(v_builtinLint_x3f_1460_);
lean_inc(v_restoreAllArtifacts_x3f_1457_);
lean_inc(v_enableArtifactCache_x3f_1456_);
lean_inc(v_readmeFile_1454_);
lean_inc(v_licenseFiles_1453_);
lean_inc(v_license_1452_);
lean_inc(v_homepage_1451_);
lean_inc(v_keywords_1450_);
lean_inc(v_description_1449_);
lean_inc(v_versionTags_1448_);
lean_inc(v_version_1447_);
lean_inc(v_lintDriverArgs_1446_);
lean_inc(v_lintDriver_1445_);
lean_inc(v_testDriverArgs_1444_);
lean_inc(v_testDriver_1443_);
lean_inc(v_downloadCacheService_x3f_1442_);
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
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_apply_1(v_f_1425_, v_releaseRepo_1439_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 10, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_toWorkspaceConfig_1427_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_toLeanConfig_1428_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_extraDepTargets_1430_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_moreGlobalServerArgs_1432_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_srcDir_1433_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v_buildDir_1434_);
lean_ctor_set(v_reuseFailAlloc_1469_, 6, v_leanLibDir_1435_);
lean_ctor_set(v_reuseFailAlloc_1469_, 7, v_nativeLibDir_1436_);
lean_ctor_set(v_reuseFailAlloc_1469_, 8, v_binDir_1437_);
lean_ctor_set(v_reuseFailAlloc_1469_, 9, v_irDir_1438_);
lean_ctor_set(v_reuseFailAlloc_1469_, 10, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1469_, 11, v_buildArchive_1440_);
lean_ctor_set(v_reuseFailAlloc_1469_, 12, v_downloadCacheService_x3f_1442_);
lean_ctor_set(v_reuseFailAlloc_1469_, 13, v_testDriver_1443_);
lean_ctor_set(v_reuseFailAlloc_1469_, 14, v_testDriverArgs_1444_);
lean_ctor_set(v_reuseFailAlloc_1469_, 15, v_lintDriver_1445_);
lean_ctor_set(v_reuseFailAlloc_1469_, 16, v_lintDriverArgs_1446_);
lean_ctor_set(v_reuseFailAlloc_1469_, 17, v_version_1447_);
lean_ctor_set(v_reuseFailAlloc_1469_, 18, v_versionTags_1448_);
lean_ctor_set(v_reuseFailAlloc_1469_, 19, v_description_1449_);
lean_ctor_set(v_reuseFailAlloc_1469_, 20, v_keywords_1450_);
lean_ctor_set(v_reuseFailAlloc_1469_, 21, v_homepage_1451_);
lean_ctor_set(v_reuseFailAlloc_1469_, 22, v_license_1452_);
lean_ctor_set(v_reuseFailAlloc_1469_, 23, v_licenseFiles_1453_);
lean_ctor_set(v_reuseFailAlloc_1469_, 24, v_readmeFile_1454_);
lean_ctor_set(v_reuseFailAlloc_1469_, 25, v_enableArtifactCache_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1469_, 26, v_restoreAllArtifacts_x3f_1457_);
lean_ctor_set(v_reuseFailAlloc_1469_, 27, v_builtinLint_x3f_1460_);
lean_ctor_set(v_reuseFailAlloc_1469_, 28, v_checks_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29, v_bootstrap_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29 + 1, v_precompileModules_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29 + 3, v_reservoir_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29 + 5, v_allowImportAll_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*29 + 6, v_fixedToolchain_1462_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3___boxed(lean_object* v_x_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lake_PackageConfig_releaseRepo___proj___redArg___lam__3(v_x_1473_);
lean_dec_ref(v_x_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg(){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = ((lean_object*)(l_Lake_PackageConfig_releaseRepo___proj___redArg___closed__4));
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___redArg___boxed(lean_object* v___dummy_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
return v_res_1487_;
}
}
static lean_object* _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0(void){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lake_PackageConfig_releaseRepo___proj___redArg();
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj(lean_object* v_p_1489_, lean_object* v_n_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___proj___boxed(lean_object* v_p_1492_, lean_object* v_n_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lake_PackageConfig_releaseRepo___proj(v_p_1492_, v_n_1493_);
lean_dec(v_n_1493_);
lean_dec(v_p_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg(){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___redArg___boxed(lean_object* v___dummy_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lake_PackageConfig_releaseRepo_instConfigField___redArg();
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField(lean_object* v_p_1499_, lean_object* v_n_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_instConfigField___boxed(lean_object* v_p_1502_, lean_object* v_n_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lake_PackageConfig_releaseRepo_instConfigField(v_p_1502_, v_n_1503_);
lean_dec(v_n_1503_);
lean_dec(v_p_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___redArg();
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(lean_object* v_p_1509_, lean_object* v_n_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_obj_once(&l_Lake_PackageConfig_releaseRepo___proj___closed__0, &l_Lake_PackageConfig_releaseRepo___proj___closed__0_once, _init_l_Lake_PackageConfig_releaseRepo___proj___closed__0);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f_instConfigField___boxed(lean_object* v_p_1512_, lean_object* v_n_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lake_PackageConfig_releaseRepo_x3f_instConfigField(v_p_1512_, v_n_1513_);
lean_dec(v_n_1513_);
lean_dec(v_p_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(lean_object* v_cfg_1515_){
_start:
{
lean_object* v_buildArchive_1516_; 
v_buildArchive_1516_ = lean_ctor_get(v_cfg_1515_, 11);
lean_inc(v_buildArchive_1516_);
return v_buildArchive_1516_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0___boxed(lean_object* v_cfg_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lake_PackageConfig_buildArchive___proj___redArg___lam__0(v_cfg_1517_);
lean_dec_ref(v_cfg_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__1(lean_object* v_val_1519_, lean_object* v_cfg_1520_){
_start:
{
lean_object* v_toWorkspaceConfig_1521_; lean_object* v_toLeanConfig_1522_; uint8_t v_bootstrap_1523_; lean_object* v_extraDepTargets_1524_; uint8_t v_precompileModules_1525_; lean_object* v_moreGlobalServerArgs_1526_; lean_object* v_srcDir_1527_; lean_object* v_buildDir_1528_; lean_object* v_leanLibDir_1529_; lean_object* v_nativeLibDir_1530_; lean_object* v_binDir_1531_; lean_object* v_irDir_1532_; lean_object* v_releaseRepo_1533_; uint8_t v_preferReleaseBuild_1534_; lean_object* v_downloadCacheService_x3f_1535_; lean_object* v_testDriver_1536_; lean_object* v_testDriverArgs_1537_; lean_object* v_lintDriver_1538_; lean_object* v_lintDriverArgs_1539_; lean_object* v_version_1540_; lean_object* v_versionTags_1541_; lean_object* v_description_1542_; lean_object* v_keywords_1543_; lean_object* v_homepage_1544_; lean_object* v_license_1545_; lean_object* v_licenseFiles_1546_; lean_object* v_readmeFile_1547_; uint8_t v_reservoir_1548_; lean_object* v_enableArtifactCache_x3f_1549_; lean_object* v_restoreAllArtifacts_x3f_1550_; uint8_t v_libPrefixOnWindows_1551_; uint8_t v_allowImportAll_1552_; lean_object* v_builtinLint_x3f_1553_; lean_object* v_checks_1554_; uint8_t v_fixedToolchain_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_toWorkspaceConfig_1521_ = lean_ctor_get(v_cfg_1520_, 0);
v_toLeanConfig_1522_ = lean_ctor_get(v_cfg_1520_, 1);
v_bootstrap_1523_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29);
v_extraDepTargets_1524_ = lean_ctor_get(v_cfg_1520_, 2);
v_precompileModules_1525_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1526_ = lean_ctor_get(v_cfg_1520_, 3);
v_srcDir_1527_ = lean_ctor_get(v_cfg_1520_, 4);
v_buildDir_1528_ = lean_ctor_get(v_cfg_1520_, 5);
v_leanLibDir_1529_ = lean_ctor_get(v_cfg_1520_, 6);
v_nativeLibDir_1530_ = lean_ctor_get(v_cfg_1520_, 7);
v_binDir_1531_ = lean_ctor_get(v_cfg_1520_, 8);
v_irDir_1532_ = lean_ctor_get(v_cfg_1520_, 9);
v_releaseRepo_1533_ = lean_ctor_get(v_cfg_1520_, 10);
v_preferReleaseBuild_1534_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1535_ = lean_ctor_get(v_cfg_1520_, 12);
v_testDriver_1536_ = lean_ctor_get(v_cfg_1520_, 13);
v_testDriverArgs_1537_ = lean_ctor_get(v_cfg_1520_, 14);
v_lintDriver_1538_ = lean_ctor_get(v_cfg_1520_, 15);
v_lintDriverArgs_1539_ = lean_ctor_get(v_cfg_1520_, 16);
v_version_1540_ = lean_ctor_get(v_cfg_1520_, 17);
v_versionTags_1541_ = lean_ctor_get(v_cfg_1520_, 18);
v_description_1542_ = lean_ctor_get(v_cfg_1520_, 19);
v_keywords_1543_ = lean_ctor_get(v_cfg_1520_, 20);
v_homepage_1544_ = lean_ctor_get(v_cfg_1520_, 21);
v_license_1545_ = lean_ctor_get(v_cfg_1520_, 22);
v_licenseFiles_1546_ = lean_ctor_get(v_cfg_1520_, 23);
v_readmeFile_1547_ = lean_ctor_get(v_cfg_1520_, 24);
v_reservoir_1548_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1549_ = lean_ctor_get(v_cfg_1520_, 25);
v_restoreAllArtifacts_x3f_1550_ = lean_ctor_get(v_cfg_1520_, 26);
v_libPrefixOnWindows_1551_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29 + 4);
v_allowImportAll_1552_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1553_ = lean_ctor_get(v_cfg_1520_, 27);
v_checks_1554_ = lean_ctor_get(v_cfg_1520_, 28);
v_fixedToolchain_1555_ = lean_ctor_get_uint8(v_cfg_1520_, sizeof(void*)*29 + 6);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_cfg_1520_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_cfg_1520_, 11);
lean_dec(v_unused_1563_);
v___x_1557_ = v_cfg_1520_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_checks_1554_);
lean_inc(v_builtinLint_x3f_1553_);
lean_inc(v_restoreAllArtifacts_x3f_1550_);
lean_inc(v_enableArtifactCache_x3f_1549_);
lean_inc(v_readmeFile_1547_);
lean_inc(v_licenseFiles_1546_);
lean_inc(v_license_1545_);
lean_inc(v_homepage_1544_);
lean_inc(v_keywords_1543_);
lean_inc(v_description_1542_);
lean_inc(v_versionTags_1541_);
lean_inc(v_version_1540_);
lean_inc(v_lintDriverArgs_1539_);
lean_inc(v_lintDriver_1538_);
lean_inc(v_testDriverArgs_1537_);
lean_inc(v_testDriver_1536_);
lean_inc(v_downloadCacheService_x3f_1535_);
lean_inc(v_releaseRepo_1533_);
lean_inc(v_irDir_1532_);
lean_inc(v_binDir_1531_);
lean_inc(v_nativeLibDir_1530_);
lean_inc(v_leanLibDir_1529_);
lean_inc(v_buildDir_1528_);
lean_inc(v_srcDir_1527_);
lean_inc(v_moreGlobalServerArgs_1526_);
lean_inc(v_extraDepTargets_1524_);
lean_inc(v_toLeanConfig_1522_);
lean_inc(v_toWorkspaceConfig_1521_);
lean_dec(v_cfg_1520_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 11, v_val_1519_);
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_toWorkspaceConfig_1521_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_toLeanConfig_1522_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_extraDepTargets_1524_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_moreGlobalServerArgs_1526_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_srcDir_1527_);
lean_ctor_set(v_reuseFailAlloc_1561_, 5, v_buildDir_1528_);
lean_ctor_set(v_reuseFailAlloc_1561_, 6, v_leanLibDir_1529_);
lean_ctor_set(v_reuseFailAlloc_1561_, 7, v_nativeLibDir_1530_);
lean_ctor_set(v_reuseFailAlloc_1561_, 8, v_binDir_1531_);
lean_ctor_set(v_reuseFailAlloc_1561_, 9, v_irDir_1532_);
lean_ctor_set(v_reuseFailAlloc_1561_, 10, v_releaseRepo_1533_);
lean_ctor_set(v_reuseFailAlloc_1561_, 11, v_val_1519_);
lean_ctor_set(v_reuseFailAlloc_1561_, 12, v_downloadCacheService_x3f_1535_);
lean_ctor_set(v_reuseFailAlloc_1561_, 13, v_testDriver_1536_);
lean_ctor_set(v_reuseFailAlloc_1561_, 14, v_testDriverArgs_1537_);
lean_ctor_set(v_reuseFailAlloc_1561_, 15, v_lintDriver_1538_);
lean_ctor_set(v_reuseFailAlloc_1561_, 16, v_lintDriverArgs_1539_);
lean_ctor_set(v_reuseFailAlloc_1561_, 17, v_version_1540_);
lean_ctor_set(v_reuseFailAlloc_1561_, 18, v_versionTags_1541_);
lean_ctor_set(v_reuseFailAlloc_1561_, 19, v_description_1542_);
lean_ctor_set(v_reuseFailAlloc_1561_, 20, v_keywords_1543_);
lean_ctor_set(v_reuseFailAlloc_1561_, 21, v_homepage_1544_);
lean_ctor_set(v_reuseFailAlloc_1561_, 22, v_license_1545_);
lean_ctor_set(v_reuseFailAlloc_1561_, 23, v_licenseFiles_1546_);
lean_ctor_set(v_reuseFailAlloc_1561_, 24, v_readmeFile_1547_);
lean_ctor_set(v_reuseFailAlloc_1561_, 25, v_enableArtifactCache_x3f_1549_);
lean_ctor_set(v_reuseFailAlloc_1561_, 26, v_restoreAllArtifacts_x3f_1550_);
lean_ctor_set(v_reuseFailAlloc_1561_, 27, v_builtinLint_x3f_1553_);
lean_ctor_set(v_reuseFailAlloc_1561_, 28, v_checks_1554_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29, v_bootstrap_1523_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29 + 1, v_precompileModules_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29 + 3, v_reservoir_1548_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29 + 5, v_allowImportAll_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1561_, sizeof(void*)*29 + 6, v_fixedToolchain_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___lam__2(lean_object* v_f_1564_, lean_object* v_cfg_1565_){
_start:
{
lean_object* v_toWorkspaceConfig_1566_; lean_object* v_toLeanConfig_1567_; uint8_t v_bootstrap_1568_; lean_object* v_extraDepTargets_1569_; uint8_t v_precompileModules_1570_; lean_object* v_moreGlobalServerArgs_1571_; lean_object* v_srcDir_1572_; lean_object* v_buildDir_1573_; lean_object* v_leanLibDir_1574_; lean_object* v_nativeLibDir_1575_; lean_object* v_binDir_1576_; lean_object* v_irDir_1577_; lean_object* v_releaseRepo_1578_; lean_object* v_buildArchive_1579_; uint8_t v_preferReleaseBuild_1580_; lean_object* v_downloadCacheService_x3f_1581_; lean_object* v_testDriver_1582_; lean_object* v_testDriverArgs_1583_; lean_object* v_lintDriver_1584_; lean_object* v_lintDriverArgs_1585_; lean_object* v_version_1586_; lean_object* v_versionTags_1587_; lean_object* v_description_1588_; lean_object* v_keywords_1589_; lean_object* v_homepage_1590_; lean_object* v_license_1591_; lean_object* v_licenseFiles_1592_; lean_object* v_readmeFile_1593_; uint8_t v_reservoir_1594_; lean_object* v_enableArtifactCache_x3f_1595_; lean_object* v_restoreAllArtifacts_x3f_1596_; uint8_t v_libPrefixOnWindows_1597_; uint8_t v_allowImportAll_1598_; lean_object* v_builtinLint_x3f_1599_; lean_object* v_checks_1600_; uint8_t v_fixedToolchain_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_toWorkspaceConfig_1566_ = lean_ctor_get(v_cfg_1565_, 0);
v_toLeanConfig_1567_ = lean_ctor_get(v_cfg_1565_, 1);
v_bootstrap_1568_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29);
v_extraDepTargets_1569_ = lean_ctor_get(v_cfg_1565_, 2);
v_precompileModules_1570_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1571_ = lean_ctor_get(v_cfg_1565_, 3);
v_srcDir_1572_ = lean_ctor_get(v_cfg_1565_, 4);
v_buildDir_1573_ = lean_ctor_get(v_cfg_1565_, 5);
v_leanLibDir_1574_ = lean_ctor_get(v_cfg_1565_, 6);
v_nativeLibDir_1575_ = lean_ctor_get(v_cfg_1565_, 7);
v_binDir_1576_ = lean_ctor_get(v_cfg_1565_, 8);
v_irDir_1577_ = lean_ctor_get(v_cfg_1565_, 9);
v_releaseRepo_1578_ = lean_ctor_get(v_cfg_1565_, 10);
v_buildArchive_1579_ = lean_ctor_get(v_cfg_1565_, 11);
v_preferReleaseBuild_1580_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1581_ = lean_ctor_get(v_cfg_1565_, 12);
v_testDriver_1582_ = lean_ctor_get(v_cfg_1565_, 13);
v_testDriverArgs_1583_ = lean_ctor_get(v_cfg_1565_, 14);
v_lintDriver_1584_ = lean_ctor_get(v_cfg_1565_, 15);
v_lintDriverArgs_1585_ = lean_ctor_get(v_cfg_1565_, 16);
v_version_1586_ = lean_ctor_get(v_cfg_1565_, 17);
v_versionTags_1587_ = lean_ctor_get(v_cfg_1565_, 18);
v_description_1588_ = lean_ctor_get(v_cfg_1565_, 19);
v_keywords_1589_ = lean_ctor_get(v_cfg_1565_, 20);
v_homepage_1590_ = lean_ctor_get(v_cfg_1565_, 21);
v_license_1591_ = lean_ctor_get(v_cfg_1565_, 22);
v_licenseFiles_1592_ = lean_ctor_get(v_cfg_1565_, 23);
v_readmeFile_1593_ = lean_ctor_get(v_cfg_1565_, 24);
v_reservoir_1594_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1595_ = lean_ctor_get(v_cfg_1565_, 25);
v_restoreAllArtifacts_x3f_1596_ = lean_ctor_get(v_cfg_1565_, 26);
v_libPrefixOnWindows_1597_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29 + 4);
v_allowImportAll_1598_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1599_ = lean_ctor_get(v_cfg_1565_, 27);
v_checks_1600_ = lean_ctor_get(v_cfg_1565_, 28);
v_fixedToolchain_1601_ = lean_ctor_get_uint8(v_cfg_1565_, sizeof(void*)*29 + 6);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_cfg_1565_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1603_ = v_cfg_1565_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_checks_1600_);
lean_inc(v_builtinLint_x3f_1599_);
lean_inc(v_restoreAllArtifacts_x3f_1596_);
lean_inc(v_enableArtifactCache_x3f_1595_);
lean_inc(v_readmeFile_1593_);
lean_inc(v_licenseFiles_1592_);
lean_inc(v_license_1591_);
lean_inc(v_homepage_1590_);
lean_inc(v_keywords_1589_);
lean_inc(v_description_1588_);
lean_inc(v_versionTags_1587_);
lean_inc(v_version_1586_);
lean_inc(v_lintDriverArgs_1585_);
lean_inc(v_lintDriver_1584_);
lean_inc(v_testDriverArgs_1583_);
lean_inc(v_testDriver_1582_);
lean_inc(v_downloadCacheService_x3f_1581_);
lean_inc(v_buildArchive_1579_);
lean_inc(v_releaseRepo_1578_);
lean_inc(v_irDir_1577_);
lean_inc(v_binDir_1576_);
lean_inc(v_nativeLibDir_1575_);
lean_inc(v_leanLibDir_1574_);
lean_inc(v_buildDir_1573_);
lean_inc(v_srcDir_1572_);
lean_inc(v_moreGlobalServerArgs_1571_);
lean_inc(v_extraDepTargets_1569_);
lean_inc(v_toLeanConfig_1567_);
lean_inc(v_toWorkspaceConfig_1566_);
lean_dec(v_cfg_1565_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_apply_1(v_f_1564_, v_buildArchive_1579_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 11, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_toWorkspaceConfig_1566_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_toLeanConfig_1567_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_extraDepTargets_1569_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_moreGlobalServerArgs_1571_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_srcDir_1572_);
lean_ctor_set(v_reuseFailAlloc_1608_, 5, v_buildDir_1573_);
lean_ctor_set(v_reuseFailAlloc_1608_, 6, v_leanLibDir_1574_);
lean_ctor_set(v_reuseFailAlloc_1608_, 7, v_nativeLibDir_1575_);
lean_ctor_set(v_reuseFailAlloc_1608_, 8, v_binDir_1576_);
lean_ctor_set(v_reuseFailAlloc_1608_, 9, v_irDir_1577_);
lean_ctor_set(v_reuseFailAlloc_1608_, 10, v_releaseRepo_1578_);
lean_ctor_set(v_reuseFailAlloc_1608_, 11, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 12, v_downloadCacheService_x3f_1581_);
lean_ctor_set(v_reuseFailAlloc_1608_, 13, v_testDriver_1582_);
lean_ctor_set(v_reuseFailAlloc_1608_, 14, v_testDriverArgs_1583_);
lean_ctor_set(v_reuseFailAlloc_1608_, 15, v_lintDriver_1584_);
lean_ctor_set(v_reuseFailAlloc_1608_, 16, v_lintDriverArgs_1585_);
lean_ctor_set(v_reuseFailAlloc_1608_, 17, v_version_1586_);
lean_ctor_set(v_reuseFailAlloc_1608_, 18, v_versionTags_1587_);
lean_ctor_set(v_reuseFailAlloc_1608_, 19, v_description_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 20, v_keywords_1589_);
lean_ctor_set(v_reuseFailAlloc_1608_, 21, v_homepage_1590_);
lean_ctor_set(v_reuseFailAlloc_1608_, 22, v_license_1591_);
lean_ctor_set(v_reuseFailAlloc_1608_, 23, v_licenseFiles_1592_);
lean_ctor_set(v_reuseFailAlloc_1608_, 24, v_readmeFile_1593_);
lean_ctor_set(v_reuseFailAlloc_1608_, 25, v_enableArtifactCache_x3f_1595_);
lean_ctor_set(v_reuseFailAlloc_1608_, 26, v_restoreAllArtifacts_x3f_1596_);
lean_ctor_set(v_reuseFailAlloc_1608_, 27, v_builtinLint_x3f_1599_);
lean_ctor_set(v_reuseFailAlloc_1608_, 28, v_checks_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29, v_bootstrap_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29 + 1, v_precompileModules_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1580_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29 + 3, v_reservoir_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29 + 5, v_allowImportAll_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1608_, sizeof(void*)*29 + 6, v_fixedToolchain_1601_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg(){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = ((lean_object*)(l_Lake_PackageConfig_buildArchive___proj___redArg___closed__3));
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___redArg___boxed(lean_object* v___dummy_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
return v_res_1621_;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildArchive___proj___closed__0(void){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lake_PackageConfig_buildArchive___proj___redArg();
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj(lean_object* v_p_1623_, lean_object* v_n_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___proj___boxed(lean_object* v_p_1626_, lean_object* v_n_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lake_PackageConfig_buildArchive___proj(v_p_1626_, v_n_1627_);
lean_dec(v_n_1627_);
lean_dec(v_p_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg(){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___redArg___boxed(lean_object* v___dummy_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lake_PackageConfig_buildArchive_instConfigField___redArg();
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField(lean_object* v_p_1633_, lean_object* v_n_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_instConfigField___boxed(lean_object* v_p_1636_, lean_object* v_n_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lake_PackageConfig_buildArchive_instConfigField(v_p_1636_, v_n_1637_);
lean_dec(v_n_1637_);
lean_dec(v_p_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField___redArg();
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField(lean_object* v_p_1643_, lean_object* v_n_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_obj_once(&l_Lake_PackageConfig_buildArchive___proj___closed__0, &l_Lake_PackageConfig_buildArchive___proj___closed__0_once, _init_l_Lake_PackageConfig_buildArchive___proj___closed__0);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f_instConfigField___boxed(lean_object* v_p_1646_, lean_object* v_n_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lake_PackageConfig_buildArchive_x3f_instConfigField(v_p_1646_, v_n_1647_);
lean_dec(v_n_1647_);
lean_dec(v_p_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(lean_object* v_cfg_1649_){
_start:
{
uint8_t v_preferReleaseBuild_1650_; 
v_preferReleaseBuild_1650_ = lean_ctor_get_uint8(v_cfg_1649_, sizeof(void*)*29 + 2);
return v_preferReleaseBuild_1650_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0___boxed(lean_object* v_cfg_1651_){
_start:
{
uint8_t v_res_1652_; lean_object* v_r_1653_; 
v_res_1652_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__0(v_cfg_1651_);
lean_dec_ref(v_cfg_1651_);
v_r_1653_ = lean_box(v_res_1652_);
return v_r_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(uint8_t v_val_1654_, lean_object* v_cfg_1655_){
_start:
{
lean_object* v_toWorkspaceConfig_1656_; lean_object* v_toLeanConfig_1657_; uint8_t v_bootstrap_1658_; lean_object* v_extraDepTargets_1659_; uint8_t v_precompileModules_1660_; lean_object* v_moreGlobalServerArgs_1661_; lean_object* v_srcDir_1662_; lean_object* v_buildDir_1663_; lean_object* v_leanLibDir_1664_; lean_object* v_nativeLibDir_1665_; lean_object* v_binDir_1666_; lean_object* v_irDir_1667_; lean_object* v_releaseRepo_1668_; lean_object* v_buildArchive_1669_; lean_object* v_downloadCacheService_x3f_1670_; lean_object* v_testDriver_1671_; lean_object* v_testDriverArgs_1672_; lean_object* v_lintDriver_1673_; lean_object* v_lintDriverArgs_1674_; lean_object* v_version_1675_; lean_object* v_versionTags_1676_; lean_object* v_description_1677_; lean_object* v_keywords_1678_; lean_object* v_homepage_1679_; lean_object* v_license_1680_; lean_object* v_licenseFiles_1681_; lean_object* v_readmeFile_1682_; uint8_t v_reservoir_1683_; lean_object* v_enableArtifactCache_x3f_1684_; lean_object* v_restoreAllArtifacts_x3f_1685_; uint8_t v_libPrefixOnWindows_1686_; uint8_t v_allowImportAll_1687_; lean_object* v_builtinLint_x3f_1688_; lean_object* v_checks_1689_; uint8_t v_fixedToolchain_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_toWorkspaceConfig_1656_ = lean_ctor_get(v_cfg_1655_, 0);
v_toLeanConfig_1657_ = lean_ctor_get(v_cfg_1655_, 1);
v_bootstrap_1658_ = lean_ctor_get_uint8(v_cfg_1655_, sizeof(void*)*29);
v_extraDepTargets_1659_ = lean_ctor_get(v_cfg_1655_, 2);
v_precompileModules_1660_ = lean_ctor_get_uint8(v_cfg_1655_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1661_ = lean_ctor_get(v_cfg_1655_, 3);
v_srcDir_1662_ = lean_ctor_get(v_cfg_1655_, 4);
v_buildDir_1663_ = lean_ctor_get(v_cfg_1655_, 5);
v_leanLibDir_1664_ = lean_ctor_get(v_cfg_1655_, 6);
v_nativeLibDir_1665_ = lean_ctor_get(v_cfg_1655_, 7);
v_binDir_1666_ = lean_ctor_get(v_cfg_1655_, 8);
v_irDir_1667_ = lean_ctor_get(v_cfg_1655_, 9);
v_releaseRepo_1668_ = lean_ctor_get(v_cfg_1655_, 10);
v_buildArchive_1669_ = lean_ctor_get(v_cfg_1655_, 11);
v_downloadCacheService_x3f_1670_ = lean_ctor_get(v_cfg_1655_, 12);
v_testDriver_1671_ = lean_ctor_get(v_cfg_1655_, 13);
v_testDriverArgs_1672_ = lean_ctor_get(v_cfg_1655_, 14);
v_lintDriver_1673_ = lean_ctor_get(v_cfg_1655_, 15);
v_lintDriverArgs_1674_ = lean_ctor_get(v_cfg_1655_, 16);
v_version_1675_ = lean_ctor_get(v_cfg_1655_, 17);
v_versionTags_1676_ = lean_ctor_get(v_cfg_1655_, 18);
v_description_1677_ = lean_ctor_get(v_cfg_1655_, 19);
v_keywords_1678_ = lean_ctor_get(v_cfg_1655_, 20);
v_homepage_1679_ = lean_ctor_get(v_cfg_1655_, 21);
v_license_1680_ = lean_ctor_get(v_cfg_1655_, 22);
v_licenseFiles_1681_ = lean_ctor_get(v_cfg_1655_, 23);
v_readmeFile_1682_ = lean_ctor_get(v_cfg_1655_, 24);
v_reservoir_1683_ = lean_ctor_get_uint8(v_cfg_1655_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1684_ = lean_ctor_get(v_cfg_1655_, 25);
v_restoreAllArtifacts_x3f_1685_ = lean_ctor_get(v_cfg_1655_, 26);
v_libPrefixOnWindows_1686_ = lean_ctor_get_uint8(v_cfg_1655_, sizeof(void*)*29 + 4);
v_allowImportAll_1687_ = lean_ctor_get_uint8(v_cfg_1655_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1688_ = lean_ctor_get(v_cfg_1655_, 27);
v_checks_1689_ = lean_ctor_get(v_cfg_1655_, 28);
v_fixedToolchain_1690_ = lean_ctor_get_uint8(v_cfg_1655_, sizeof(void*)*29 + 6);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_cfg_1655_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v_cfg_1655_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_checks_1689_);
lean_inc(v_builtinLint_x3f_1688_);
lean_inc(v_restoreAllArtifacts_x3f_1685_);
lean_inc(v_enableArtifactCache_x3f_1684_);
lean_inc(v_readmeFile_1682_);
lean_inc(v_licenseFiles_1681_);
lean_inc(v_license_1680_);
lean_inc(v_homepage_1679_);
lean_inc(v_keywords_1678_);
lean_inc(v_description_1677_);
lean_inc(v_versionTags_1676_);
lean_inc(v_version_1675_);
lean_inc(v_lintDriverArgs_1674_);
lean_inc(v_lintDriver_1673_);
lean_inc(v_testDriverArgs_1672_);
lean_inc(v_testDriver_1671_);
lean_inc(v_downloadCacheService_x3f_1670_);
lean_inc(v_buildArchive_1669_);
lean_inc(v_releaseRepo_1668_);
lean_inc(v_irDir_1667_);
lean_inc(v_binDir_1666_);
lean_inc(v_nativeLibDir_1665_);
lean_inc(v_leanLibDir_1664_);
lean_inc(v_buildDir_1663_);
lean_inc(v_srcDir_1662_);
lean_inc(v_moreGlobalServerArgs_1661_);
lean_inc(v_extraDepTargets_1659_);
lean_inc(v_toLeanConfig_1657_);
lean_inc(v_toWorkspaceConfig_1656_);
lean_dec(v_cfg_1655_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_toWorkspaceConfig_1656_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_toLeanConfig_1657_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_extraDepTargets_1659_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_moreGlobalServerArgs_1661_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v_srcDir_1662_);
lean_ctor_set(v_reuseFailAlloc_1696_, 5, v_buildDir_1663_);
lean_ctor_set(v_reuseFailAlloc_1696_, 6, v_leanLibDir_1664_);
lean_ctor_set(v_reuseFailAlloc_1696_, 7, v_nativeLibDir_1665_);
lean_ctor_set(v_reuseFailAlloc_1696_, 8, v_binDir_1666_);
lean_ctor_set(v_reuseFailAlloc_1696_, 9, v_irDir_1667_);
lean_ctor_set(v_reuseFailAlloc_1696_, 10, v_releaseRepo_1668_);
lean_ctor_set(v_reuseFailAlloc_1696_, 11, v_buildArchive_1669_);
lean_ctor_set(v_reuseFailAlloc_1696_, 12, v_downloadCacheService_x3f_1670_);
lean_ctor_set(v_reuseFailAlloc_1696_, 13, v_testDriver_1671_);
lean_ctor_set(v_reuseFailAlloc_1696_, 14, v_testDriverArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1696_, 15, v_lintDriver_1673_);
lean_ctor_set(v_reuseFailAlloc_1696_, 16, v_lintDriverArgs_1674_);
lean_ctor_set(v_reuseFailAlloc_1696_, 17, v_version_1675_);
lean_ctor_set(v_reuseFailAlloc_1696_, 18, v_versionTags_1676_);
lean_ctor_set(v_reuseFailAlloc_1696_, 19, v_description_1677_);
lean_ctor_set(v_reuseFailAlloc_1696_, 20, v_keywords_1678_);
lean_ctor_set(v_reuseFailAlloc_1696_, 21, v_homepage_1679_);
lean_ctor_set(v_reuseFailAlloc_1696_, 22, v_license_1680_);
lean_ctor_set(v_reuseFailAlloc_1696_, 23, v_licenseFiles_1681_);
lean_ctor_set(v_reuseFailAlloc_1696_, 24, v_readmeFile_1682_);
lean_ctor_set(v_reuseFailAlloc_1696_, 25, v_enableArtifactCache_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 26, v_restoreAllArtifacts_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1696_, 27, v_builtinLint_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1696_, 28, v_checks_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*29, v_bootstrap_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*29 + 1, v_precompileModules_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*29 + 3, v_reservoir_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*29 + 5, v_allowImportAll_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*29 + 6, v_fixedToolchain_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*29 + 2, v_val_1654_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1___boxed(lean_object* v_val_1698_, lean_object* v_cfg_1699_){
_start:
{
uint8_t v_val_144__boxed_1700_; lean_object* v_res_1701_; 
v_val_144__boxed_1700_ = lean_unbox(v_val_1698_);
v_res_1701_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__1(v_val_144__boxed_1700_, v_cfg_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___lam__2(lean_object* v_f_1702_, lean_object* v_cfg_1703_){
_start:
{
lean_object* v_toWorkspaceConfig_1704_; lean_object* v_toLeanConfig_1705_; uint8_t v_bootstrap_1706_; lean_object* v_extraDepTargets_1707_; uint8_t v_precompileModules_1708_; lean_object* v_moreGlobalServerArgs_1709_; lean_object* v_srcDir_1710_; lean_object* v_buildDir_1711_; lean_object* v_leanLibDir_1712_; lean_object* v_nativeLibDir_1713_; lean_object* v_binDir_1714_; lean_object* v_irDir_1715_; lean_object* v_releaseRepo_1716_; lean_object* v_buildArchive_1717_; uint8_t v_preferReleaseBuild_1718_; lean_object* v_downloadCacheService_x3f_1719_; lean_object* v_testDriver_1720_; lean_object* v_testDriverArgs_1721_; lean_object* v_lintDriver_1722_; lean_object* v_lintDriverArgs_1723_; lean_object* v_version_1724_; lean_object* v_versionTags_1725_; lean_object* v_description_1726_; lean_object* v_keywords_1727_; lean_object* v_homepage_1728_; lean_object* v_license_1729_; lean_object* v_licenseFiles_1730_; lean_object* v_readmeFile_1731_; uint8_t v_reservoir_1732_; lean_object* v_enableArtifactCache_x3f_1733_; lean_object* v_restoreAllArtifacts_x3f_1734_; uint8_t v_libPrefixOnWindows_1735_; uint8_t v_allowImportAll_1736_; lean_object* v_builtinLint_x3f_1737_; lean_object* v_checks_1738_; uint8_t v_fixedToolchain_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1749_; 
v_toWorkspaceConfig_1704_ = lean_ctor_get(v_cfg_1703_, 0);
v_toLeanConfig_1705_ = lean_ctor_get(v_cfg_1703_, 1);
v_bootstrap_1706_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29);
v_extraDepTargets_1707_ = lean_ctor_get(v_cfg_1703_, 2);
v_precompileModules_1708_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1709_ = lean_ctor_get(v_cfg_1703_, 3);
v_srcDir_1710_ = lean_ctor_get(v_cfg_1703_, 4);
v_buildDir_1711_ = lean_ctor_get(v_cfg_1703_, 5);
v_leanLibDir_1712_ = lean_ctor_get(v_cfg_1703_, 6);
v_nativeLibDir_1713_ = lean_ctor_get(v_cfg_1703_, 7);
v_binDir_1714_ = lean_ctor_get(v_cfg_1703_, 8);
v_irDir_1715_ = lean_ctor_get(v_cfg_1703_, 9);
v_releaseRepo_1716_ = lean_ctor_get(v_cfg_1703_, 10);
v_buildArchive_1717_ = lean_ctor_get(v_cfg_1703_, 11);
v_preferReleaseBuild_1718_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1719_ = lean_ctor_get(v_cfg_1703_, 12);
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
v_reservoir_1732_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1733_ = lean_ctor_get(v_cfg_1703_, 25);
v_restoreAllArtifacts_x3f_1734_ = lean_ctor_get(v_cfg_1703_, 26);
v_libPrefixOnWindows_1735_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29 + 4);
v_allowImportAll_1736_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1737_ = lean_ctor_get(v_cfg_1703_, 27);
v_checks_1738_ = lean_ctor_get(v_cfg_1703_, 28);
v_fixedToolchain_1739_ = lean_ctor_get_uint8(v_cfg_1703_, sizeof(void*)*29 + 6);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_cfg_1703_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1741_ = v_cfg_1703_;
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_checks_1738_);
lean_inc(v_builtinLint_x3f_1737_);
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
lean_inc(v_downloadCacheService_x3f_1719_);
lean_inc(v_buildArchive_1717_);
lean_inc(v_releaseRepo_1716_);
lean_inc(v_irDir_1715_);
lean_inc(v_binDir_1714_);
lean_inc(v_nativeLibDir_1713_);
lean_inc(v_leanLibDir_1712_);
lean_inc(v_buildDir_1711_);
lean_inc(v_srcDir_1710_);
lean_inc(v_moreGlobalServerArgs_1709_);
lean_inc(v_extraDepTargets_1707_);
lean_inc(v_toLeanConfig_1705_);
lean_inc(v_toWorkspaceConfig_1704_);
lean_dec(v_cfg_1703_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1743_ = lean_box(v_preferReleaseBuild_1718_);
v___x_1744_ = lean_apply_1(v_f_1702_, v___x_1743_);
if (v_isShared_1742_ == 0)
{
v___x_1746_ = v___x_1741_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_toWorkspaceConfig_1704_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_toLeanConfig_1705_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_extraDepTargets_1707_);
lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_moreGlobalServerArgs_1709_);
lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_srcDir_1710_);
lean_ctor_set(v_reuseFailAlloc_1748_, 5, v_buildDir_1711_);
lean_ctor_set(v_reuseFailAlloc_1748_, 6, v_leanLibDir_1712_);
lean_ctor_set(v_reuseFailAlloc_1748_, 7, v_nativeLibDir_1713_);
lean_ctor_set(v_reuseFailAlloc_1748_, 8, v_binDir_1714_);
lean_ctor_set(v_reuseFailAlloc_1748_, 9, v_irDir_1715_);
lean_ctor_set(v_reuseFailAlloc_1748_, 10, v_releaseRepo_1716_);
lean_ctor_set(v_reuseFailAlloc_1748_, 11, v_buildArchive_1717_);
lean_ctor_set(v_reuseFailAlloc_1748_, 12, v_downloadCacheService_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1748_, 13, v_testDriver_1720_);
lean_ctor_set(v_reuseFailAlloc_1748_, 14, v_testDriverArgs_1721_);
lean_ctor_set(v_reuseFailAlloc_1748_, 15, v_lintDriver_1722_);
lean_ctor_set(v_reuseFailAlloc_1748_, 16, v_lintDriverArgs_1723_);
lean_ctor_set(v_reuseFailAlloc_1748_, 17, v_version_1724_);
lean_ctor_set(v_reuseFailAlloc_1748_, 18, v_versionTags_1725_);
lean_ctor_set(v_reuseFailAlloc_1748_, 19, v_description_1726_);
lean_ctor_set(v_reuseFailAlloc_1748_, 20, v_keywords_1727_);
lean_ctor_set(v_reuseFailAlloc_1748_, 21, v_homepage_1728_);
lean_ctor_set(v_reuseFailAlloc_1748_, 22, v_license_1729_);
lean_ctor_set(v_reuseFailAlloc_1748_, 23, v_licenseFiles_1730_);
lean_ctor_set(v_reuseFailAlloc_1748_, 24, v_readmeFile_1731_);
lean_ctor_set(v_reuseFailAlloc_1748_, 25, v_enableArtifactCache_x3f_1733_);
lean_ctor_set(v_reuseFailAlloc_1748_, 26, v_restoreAllArtifacts_x3f_1734_);
lean_ctor_set(v_reuseFailAlloc_1748_, 27, v_builtinLint_x3f_1737_);
lean_ctor_set(v_reuseFailAlloc_1748_, 28, v_checks_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, sizeof(void*)*29, v_bootstrap_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, sizeof(void*)*29 + 1, v_precompileModules_1708_);
v___x_1746_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_unbox(v___x_1744_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*29 + 2, v___x_1747_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*29 + 3, v_reservoir_1732_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1735_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*29 + 5, v_allowImportAll_1736_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*29 + 6, v_fixedToolchain_1739_);
return v___x_1746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg(){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = ((lean_object*)(l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___closed__3));
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___redArg___boxed(lean_object* v___dummy_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
return v_res_1761_;
}
}
static lean_object* _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0(void){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lake_PackageConfig_preferReleaseBuild___proj___redArg();
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj(lean_object* v_p_1763_, lean_object* v_n_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild___proj___boxed(lean_object* v_p_1766_, lean_object* v_n_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lake_PackageConfig_preferReleaseBuild___proj(v_p_1766_, v_n_1767_);
lean_dec(v_n_1767_);
lean_dec(v_p_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg(){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg___boxed(lean_object* v___dummy_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField___redArg();
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField(lean_object* v_p_1773_, lean_object* v_n_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_obj_once(&l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0, &l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0_once, _init_l_Lake_PackageConfig_preferReleaseBuild___proj___closed__0);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_preferReleaseBuild_instConfigField___boxed(lean_object* v_p_1776_, lean_object* v_n_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lake_PackageConfig_preferReleaseBuild_instConfigField(v_p_1776_, v_n_1777_);
lean_dec(v_n_1777_);
lean_dec(v_p_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__0(lean_object* v_cfg_1779_){
_start:
{
lean_object* v_downloadCacheService_x3f_1780_; 
v_downloadCacheService_x3f_1780_ = lean_ctor_get(v_cfg_1779_, 12);
lean_inc(v_downloadCacheService_x3f_1780_);
return v_downloadCacheService_x3f_1780_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__0(v_cfg_1781_);
lean_dec_ref(v_cfg_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__1(lean_object* v_val_1783_, lean_object* v_cfg_1784_){
_start:
{
lean_object* v_toWorkspaceConfig_1785_; lean_object* v_toLeanConfig_1786_; uint8_t v_bootstrap_1787_; lean_object* v_extraDepTargets_1788_; uint8_t v_precompileModules_1789_; lean_object* v_moreGlobalServerArgs_1790_; lean_object* v_srcDir_1791_; lean_object* v_buildDir_1792_; lean_object* v_leanLibDir_1793_; lean_object* v_nativeLibDir_1794_; lean_object* v_binDir_1795_; lean_object* v_irDir_1796_; lean_object* v_releaseRepo_1797_; lean_object* v_buildArchive_1798_; uint8_t v_preferReleaseBuild_1799_; lean_object* v_testDriver_1800_; lean_object* v_testDriverArgs_1801_; lean_object* v_lintDriver_1802_; lean_object* v_lintDriverArgs_1803_; lean_object* v_version_1804_; lean_object* v_versionTags_1805_; lean_object* v_description_1806_; lean_object* v_keywords_1807_; lean_object* v_homepage_1808_; lean_object* v_license_1809_; lean_object* v_licenseFiles_1810_; lean_object* v_readmeFile_1811_; uint8_t v_reservoir_1812_; lean_object* v_enableArtifactCache_x3f_1813_; lean_object* v_restoreAllArtifacts_x3f_1814_; uint8_t v_libPrefixOnWindows_1815_; uint8_t v_allowImportAll_1816_; lean_object* v_builtinLint_x3f_1817_; lean_object* v_checks_1818_; uint8_t v_fixedToolchain_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
v_toWorkspaceConfig_1785_ = lean_ctor_get(v_cfg_1784_, 0);
v_toLeanConfig_1786_ = lean_ctor_get(v_cfg_1784_, 1);
v_bootstrap_1787_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29);
v_extraDepTargets_1788_ = lean_ctor_get(v_cfg_1784_, 2);
v_precompileModules_1789_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1790_ = lean_ctor_get(v_cfg_1784_, 3);
v_srcDir_1791_ = lean_ctor_get(v_cfg_1784_, 4);
v_buildDir_1792_ = lean_ctor_get(v_cfg_1784_, 5);
v_leanLibDir_1793_ = lean_ctor_get(v_cfg_1784_, 6);
v_nativeLibDir_1794_ = lean_ctor_get(v_cfg_1784_, 7);
v_binDir_1795_ = lean_ctor_get(v_cfg_1784_, 8);
v_irDir_1796_ = lean_ctor_get(v_cfg_1784_, 9);
v_releaseRepo_1797_ = lean_ctor_get(v_cfg_1784_, 10);
v_buildArchive_1798_ = lean_ctor_get(v_cfg_1784_, 11);
v_preferReleaseBuild_1799_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29 + 2);
v_testDriver_1800_ = lean_ctor_get(v_cfg_1784_, 13);
v_testDriverArgs_1801_ = lean_ctor_get(v_cfg_1784_, 14);
v_lintDriver_1802_ = lean_ctor_get(v_cfg_1784_, 15);
v_lintDriverArgs_1803_ = lean_ctor_get(v_cfg_1784_, 16);
v_version_1804_ = lean_ctor_get(v_cfg_1784_, 17);
v_versionTags_1805_ = lean_ctor_get(v_cfg_1784_, 18);
v_description_1806_ = lean_ctor_get(v_cfg_1784_, 19);
v_keywords_1807_ = lean_ctor_get(v_cfg_1784_, 20);
v_homepage_1808_ = lean_ctor_get(v_cfg_1784_, 21);
v_license_1809_ = lean_ctor_get(v_cfg_1784_, 22);
v_licenseFiles_1810_ = lean_ctor_get(v_cfg_1784_, 23);
v_readmeFile_1811_ = lean_ctor_get(v_cfg_1784_, 24);
v_reservoir_1812_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1813_ = lean_ctor_get(v_cfg_1784_, 25);
v_restoreAllArtifacts_x3f_1814_ = lean_ctor_get(v_cfg_1784_, 26);
v_libPrefixOnWindows_1815_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29 + 4);
v_allowImportAll_1816_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1817_ = lean_ctor_get(v_cfg_1784_, 27);
v_checks_1818_ = lean_ctor_get(v_cfg_1784_, 28);
v_fixedToolchain_1819_ = lean_ctor_get_uint8(v_cfg_1784_, sizeof(void*)*29 + 6);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_cfg_1784_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v_cfg_1784_, 12);
lean_dec(v_unused_1827_);
v___x_1821_ = v_cfg_1784_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_checks_1818_);
lean_inc(v_builtinLint_x3f_1817_);
lean_inc(v_restoreAllArtifacts_x3f_1814_);
lean_inc(v_enableArtifactCache_x3f_1813_);
lean_inc(v_readmeFile_1811_);
lean_inc(v_licenseFiles_1810_);
lean_inc(v_license_1809_);
lean_inc(v_homepage_1808_);
lean_inc(v_keywords_1807_);
lean_inc(v_description_1806_);
lean_inc(v_versionTags_1805_);
lean_inc(v_version_1804_);
lean_inc(v_lintDriverArgs_1803_);
lean_inc(v_lintDriver_1802_);
lean_inc(v_testDriverArgs_1801_);
lean_inc(v_testDriver_1800_);
lean_inc(v_buildArchive_1798_);
lean_inc(v_releaseRepo_1797_);
lean_inc(v_irDir_1796_);
lean_inc(v_binDir_1795_);
lean_inc(v_nativeLibDir_1794_);
lean_inc(v_leanLibDir_1793_);
lean_inc(v_buildDir_1792_);
lean_inc(v_srcDir_1791_);
lean_inc(v_moreGlobalServerArgs_1790_);
lean_inc(v_extraDepTargets_1788_);
lean_inc(v_toLeanConfig_1786_);
lean_inc(v_toWorkspaceConfig_1785_);
lean_dec(v_cfg_1784_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 12, v_val_1783_);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_toWorkspaceConfig_1785_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_toLeanConfig_1786_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_extraDepTargets_1788_);
lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_moreGlobalServerArgs_1790_);
lean_ctor_set(v_reuseFailAlloc_1825_, 4, v_srcDir_1791_);
lean_ctor_set(v_reuseFailAlloc_1825_, 5, v_buildDir_1792_);
lean_ctor_set(v_reuseFailAlloc_1825_, 6, v_leanLibDir_1793_);
lean_ctor_set(v_reuseFailAlloc_1825_, 7, v_nativeLibDir_1794_);
lean_ctor_set(v_reuseFailAlloc_1825_, 8, v_binDir_1795_);
lean_ctor_set(v_reuseFailAlloc_1825_, 9, v_irDir_1796_);
lean_ctor_set(v_reuseFailAlloc_1825_, 10, v_releaseRepo_1797_);
lean_ctor_set(v_reuseFailAlloc_1825_, 11, v_buildArchive_1798_);
lean_ctor_set(v_reuseFailAlloc_1825_, 12, v_val_1783_);
lean_ctor_set(v_reuseFailAlloc_1825_, 13, v_testDriver_1800_);
lean_ctor_set(v_reuseFailAlloc_1825_, 14, v_testDriverArgs_1801_);
lean_ctor_set(v_reuseFailAlloc_1825_, 15, v_lintDriver_1802_);
lean_ctor_set(v_reuseFailAlloc_1825_, 16, v_lintDriverArgs_1803_);
lean_ctor_set(v_reuseFailAlloc_1825_, 17, v_version_1804_);
lean_ctor_set(v_reuseFailAlloc_1825_, 18, v_versionTags_1805_);
lean_ctor_set(v_reuseFailAlloc_1825_, 19, v_description_1806_);
lean_ctor_set(v_reuseFailAlloc_1825_, 20, v_keywords_1807_);
lean_ctor_set(v_reuseFailAlloc_1825_, 21, v_homepage_1808_);
lean_ctor_set(v_reuseFailAlloc_1825_, 22, v_license_1809_);
lean_ctor_set(v_reuseFailAlloc_1825_, 23, v_licenseFiles_1810_);
lean_ctor_set(v_reuseFailAlloc_1825_, 24, v_readmeFile_1811_);
lean_ctor_set(v_reuseFailAlloc_1825_, 25, v_enableArtifactCache_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1825_, 26, v_restoreAllArtifacts_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1825_, 27, v_builtinLint_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1825_, 28, v_checks_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29, v_bootstrap_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29 + 1, v_precompileModules_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29 + 3, v_reservoir_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29 + 5, v_allowImportAll_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1825_, sizeof(void*)*29 + 6, v_fixedToolchain_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___lam__2(lean_object* v_f_1828_, lean_object* v_cfg_1829_){
_start:
{
lean_object* v_toWorkspaceConfig_1830_; lean_object* v_toLeanConfig_1831_; uint8_t v_bootstrap_1832_; lean_object* v_extraDepTargets_1833_; uint8_t v_precompileModules_1834_; lean_object* v_moreGlobalServerArgs_1835_; lean_object* v_srcDir_1836_; lean_object* v_buildDir_1837_; lean_object* v_leanLibDir_1838_; lean_object* v_nativeLibDir_1839_; lean_object* v_binDir_1840_; lean_object* v_irDir_1841_; lean_object* v_releaseRepo_1842_; lean_object* v_buildArchive_1843_; uint8_t v_preferReleaseBuild_1844_; lean_object* v_downloadCacheService_x3f_1845_; lean_object* v_testDriver_1846_; lean_object* v_testDriverArgs_1847_; lean_object* v_lintDriver_1848_; lean_object* v_lintDriverArgs_1849_; lean_object* v_version_1850_; lean_object* v_versionTags_1851_; lean_object* v_description_1852_; lean_object* v_keywords_1853_; lean_object* v_homepage_1854_; lean_object* v_license_1855_; lean_object* v_licenseFiles_1856_; lean_object* v_readmeFile_1857_; uint8_t v_reservoir_1858_; lean_object* v_enableArtifactCache_x3f_1859_; lean_object* v_restoreAllArtifacts_x3f_1860_; uint8_t v_libPrefixOnWindows_1861_; uint8_t v_allowImportAll_1862_; lean_object* v_builtinLint_x3f_1863_; lean_object* v_checks_1864_; uint8_t v_fixedToolchain_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_toWorkspaceConfig_1830_ = lean_ctor_get(v_cfg_1829_, 0);
v_toLeanConfig_1831_ = lean_ctor_get(v_cfg_1829_, 1);
v_bootstrap_1832_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29);
v_extraDepTargets_1833_ = lean_ctor_get(v_cfg_1829_, 2);
v_precompileModules_1834_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1835_ = lean_ctor_get(v_cfg_1829_, 3);
v_srcDir_1836_ = lean_ctor_get(v_cfg_1829_, 4);
v_buildDir_1837_ = lean_ctor_get(v_cfg_1829_, 5);
v_leanLibDir_1838_ = lean_ctor_get(v_cfg_1829_, 6);
v_nativeLibDir_1839_ = lean_ctor_get(v_cfg_1829_, 7);
v_binDir_1840_ = lean_ctor_get(v_cfg_1829_, 8);
v_irDir_1841_ = lean_ctor_get(v_cfg_1829_, 9);
v_releaseRepo_1842_ = lean_ctor_get(v_cfg_1829_, 10);
v_buildArchive_1843_ = lean_ctor_get(v_cfg_1829_, 11);
v_preferReleaseBuild_1844_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1845_ = lean_ctor_get(v_cfg_1829_, 12);
v_testDriver_1846_ = lean_ctor_get(v_cfg_1829_, 13);
v_testDriverArgs_1847_ = lean_ctor_get(v_cfg_1829_, 14);
v_lintDriver_1848_ = lean_ctor_get(v_cfg_1829_, 15);
v_lintDriverArgs_1849_ = lean_ctor_get(v_cfg_1829_, 16);
v_version_1850_ = lean_ctor_get(v_cfg_1829_, 17);
v_versionTags_1851_ = lean_ctor_get(v_cfg_1829_, 18);
v_description_1852_ = lean_ctor_get(v_cfg_1829_, 19);
v_keywords_1853_ = lean_ctor_get(v_cfg_1829_, 20);
v_homepage_1854_ = lean_ctor_get(v_cfg_1829_, 21);
v_license_1855_ = lean_ctor_get(v_cfg_1829_, 22);
v_licenseFiles_1856_ = lean_ctor_get(v_cfg_1829_, 23);
v_readmeFile_1857_ = lean_ctor_get(v_cfg_1829_, 24);
v_reservoir_1858_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1859_ = lean_ctor_get(v_cfg_1829_, 25);
v_restoreAllArtifacts_x3f_1860_ = lean_ctor_get(v_cfg_1829_, 26);
v_libPrefixOnWindows_1861_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29 + 4);
v_allowImportAll_1862_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1863_ = lean_ctor_get(v_cfg_1829_, 27);
v_checks_1864_ = lean_ctor_get(v_cfg_1829_, 28);
v_fixedToolchain_1865_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*29 + 6);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_cfg_1829_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v_cfg_1829_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_checks_1864_);
lean_inc(v_builtinLint_x3f_1863_);
lean_inc(v_restoreAllArtifacts_x3f_1860_);
lean_inc(v_enableArtifactCache_x3f_1859_);
lean_inc(v_readmeFile_1857_);
lean_inc(v_licenseFiles_1856_);
lean_inc(v_license_1855_);
lean_inc(v_homepage_1854_);
lean_inc(v_keywords_1853_);
lean_inc(v_description_1852_);
lean_inc(v_versionTags_1851_);
lean_inc(v_version_1850_);
lean_inc(v_lintDriverArgs_1849_);
lean_inc(v_lintDriver_1848_);
lean_inc(v_testDriverArgs_1847_);
lean_inc(v_testDriver_1846_);
lean_inc(v_downloadCacheService_x3f_1845_);
lean_inc(v_buildArchive_1843_);
lean_inc(v_releaseRepo_1842_);
lean_inc(v_irDir_1841_);
lean_inc(v_binDir_1840_);
lean_inc(v_nativeLibDir_1839_);
lean_inc(v_leanLibDir_1838_);
lean_inc(v_buildDir_1837_);
lean_inc(v_srcDir_1836_);
lean_inc(v_moreGlobalServerArgs_1835_);
lean_inc(v_extraDepTargets_1833_);
lean_inc(v_toLeanConfig_1831_);
lean_inc(v_toWorkspaceConfig_1830_);
lean_dec(v_cfg_1829_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_apply_1(v_f_1828_, v_downloadCacheService_x3f_1845_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 12, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_toWorkspaceConfig_1830_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_toLeanConfig_1831_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_extraDepTargets_1833_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_moreGlobalServerArgs_1835_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_srcDir_1836_);
lean_ctor_set(v_reuseFailAlloc_1872_, 5, v_buildDir_1837_);
lean_ctor_set(v_reuseFailAlloc_1872_, 6, v_leanLibDir_1838_);
lean_ctor_set(v_reuseFailAlloc_1872_, 7, v_nativeLibDir_1839_);
lean_ctor_set(v_reuseFailAlloc_1872_, 8, v_binDir_1840_);
lean_ctor_set(v_reuseFailAlloc_1872_, 9, v_irDir_1841_);
lean_ctor_set(v_reuseFailAlloc_1872_, 10, v_releaseRepo_1842_);
lean_ctor_set(v_reuseFailAlloc_1872_, 11, v_buildArchive_1843_);
lean_ctor_set(v_reuseFailAlloc_1872_, 12, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1872_, 13, v_testDriver_1846_);
lean_ctor_set(v_reuseFailAlloc_1872_, 14, v_testDriverArgs_1847_);
lean_ctor_set(v_reuseFailAlloc_1872_, 15, v_lintDriver_1848_);
lean_ctor_set(v_reuseFailAlloc_1872_, 16, v_lintDriverArgs_1849_);
lean_ctor_set(v_reuseFailAlloc_1872_, 17, v_version_1850_);
lean_ctor_set(v_reuseFailAlloc_1872_, 18, v_versionTags_1851_);
lean_ctor_set(v_reuseFailAlloc_1872_, 19, v_description_1852_);
lean_ctor_set(v_reuseFailAlloc_1872_, 20, v_keywords_1853_);
lean_ctor_set(v_reuseFailAlloc_1872_, 21, v_homepage_1854_);
lean_ctor_set(v_reuseFailAlloc_1872_, 22, v_license_1855_);
lean_ctor_set(v_reuseFailAlloc_1872_, 23, v_licenseFiles_1856_);
lean_ctor_set(v_reuseFailAlloc_1872_, 24, v_readmeFile_1857_);
lean_ctor_set(v_reuseFailAlloc_1872_, 25, v_enableArtifactCache_x3f_1859_);
lean_ctor_set(v_reuseFailAlloc_1872_, 26, v_restoreAllArtifacts_x3f_1860_);
lean_ctor_set(v_reuseFailAlloc_1872_, 27, v_builtinLint_x3f_1863_);
lean_ctor_set(v_reuseFailAlloc_1872_, 28, v_checks_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29, v_bootstrap_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29 + 1, v_precompileModules_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29 + 3, v_reservoir_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29 + 5, v_allowImportAll_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*29 + 6, v_fixedToolchain_1865_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg(){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = ((lean_object*)(l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___closed__3));
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg___boxed(lean_object* v___dummy_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg();
return v_res_1885_;
}
}
static lean_object* _init_l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lake_PackageConfig_downloadCacheService_x3f___proj___redArg();
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj(lean_object* v_p_1887_, lean_object* v_n_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_obj_once(&l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0, &l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f___proj___boxed(lean_object* v_p_1890_, lean_object* v_n_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lake_PackageConfig_downloadCacheService_x3f___proj(v_p_1890_, v_n_1891_);
lean_dec(v_n_1891_);
lean_dec(v_p_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField___redArg(){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_obj_once(&l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0, &l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField___redArg___boxed(lean_object* v___dummy_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lake_PackageConfig_downloadCacheService_instConfigField___redArg();
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField(lean_object* v_p_1897_, lean_object* v_n_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_obj_once(&l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0, &l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_instConfigField___boxed(lean_object* v_p_1900_, lean_object* v_n_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lake_PackageConfig_downloadCacheService_instConfigField(v_p_1900_, v_n_1901_);
lean_dec(v_n_1901_);
lean_dec(v_p_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_obj_once(&l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0, &l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___redArg();
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField(lean_object* v_p_1907_, lean_object* v_n_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_obj_once(&l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0, &l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_downloadCacheService_x3f___proj___closed__0);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField___boxed(lean_object* v_p_1910_, lean_object* v_n_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lake_PackageConfig_downloadCacheService_x3f_instConfigField(v_p_1910_, v_n_1911_);
lean_dec(v_n_1911_);
lean_dec(v_p_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(lean_object* v_cfg_1913_){
_start:
{
lean_object* v_testDriver_1914_; 
v_testDriver_1914_ = lean_ctor_get(v_cfg_1913_, 13);
lean_inc_ref(v_testDriver_1914_);
return v_testDriver_1914_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__0___boxed(lean_object* v_cfg_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lake_PackageConfig_testDriver___proj___redArg___lam__0(v_cfg_1915_);
lean_dec_ref(v_cfg_1915_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__1(lean_object* v_val_1917_, lean_object* v_cfg_1918_){
_start:
{
lean_object* v_toWorkspaceConfig_1919_; lean_object* v_toLeanConfig_1920_; uint8_t v_bootstrap_1921_; lean_object* v_extraDepTargets_1922_; uint8_t v_precompileModules_1923_; lean_object* v_moreGlobalServerArgs_1924_; lean_object* v_srcDir_1925_; lean_object* v_buildDir_1926_; lean_object* v_leanLibDir_1927_; lean_object* v_nativeLibDir_1928_; lean_object* v_binDir_1929_; lean_object* v_irDir_1930_; lean_object* v_releaseRepo_1931_; lean_object* v_buildArchive_1932_; uint8_t v_preferReleaseBuild_1933_; lean_object* v_downloadCacheService_x3f_1934_; lean_object* v_testDriverArgs_1935_; lean_object* v_lintDriver_1936_; lean_object* v_lintDriverArgs_1937_; lean_object* v_version_1938_; lean_object* v_versionTags_1939_; lean_object* v_description_1940_; lean_object* v_keywords_1941_; lean_object* v_homepage_1942_; lean_object* v_license_1943_; lean_object* v_licenseFiles_1944_; lean_object* v_readmeFile_1945_; uint8_t v_reservoir_1946_; lean_object* v_enableArtifactCache_x3f_1947_; lean_object* v_restoreAllArtifacts_x3f_1948_; uint8_t v_libPrefixOnWindows_1949_; uint8_t v_allowImportAll_1950_; lean_object* v_builtinLint_x3f_1951_; lean_object* v_checks_1952_; uint8_t v_fixedToolchain_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_toWorkspaceConfig_1919_ = lean_ctor_get(v_cfg_1918_, 0);
v_toLeanConfig_1920_ = lean_ctor_get(v_cfg_1918_, 1);
v_bootstrap_1921_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29);
v_extraDepTargets_1922_ = lean_ctor_get(v_cfg_1918_, 2);
v_precompileModules_1923_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1924_ = lean_ctor_get(v_cfg_1918_, 3);
v_srcDir_1925_ = lean_ctor_get(v_cfg_1918_, 4);
v_buildDir_1926_ = lean_ctor_get(v_cfg_1918_, 5);
v_leanLibDir_1927_ = lean_ctor_get(v_cfg_1918_, 6);
v_nativeLibDir_1928_ = lean_ctor_get(v_cfg_1918_, 7);
v_binDir_1929_ = lean_ctor_get(v_cfg_1918_, 8);
v_irDir_1930_ = lean_ctor_get(v_cfg_1918_, 9);
v_releaseRepo_1931_ = lean_ctor_get(v_cfg_1918_, 10);
v_buildArchive_1932_ = lean_ctor_get(v_cfg_1918_, 11);
v_preferReleaseBuild_1933_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1934_ = lean_ctor_get(v_cfg_1918_, 12);
v_testDriverArgs_1935_ = lean_ctor_get(v_cfg_1918_, 14);
v_lintDriver_1936_ = lean_ctor_get(v_cfg_1918_, 15);
v_lintDriverArgs_1937_ = lean_ctor_get(v_cfg_1918_, 16);
v_version_1938_ = lean_ctor_get(v_cfg_1918_, 17);
v_versionTags_1939_ = lean_ctor_get(v_cfg_1918_, 18);
v_description_1940_ = lean_ctor_get(v_cfg_1918_, 19);
v_keywords_1941_ = lean_ctor_get(v_cfg_1918_, 20);
v_homepage_1942_ = lean_ctor_get(v_cfg_1918_, 21);
v_license_1943_ = lean_ctor_get(v_cfg_1918_, 22);
v_licenseFiles_1944_ = lean_ctor_get(v_cfg_1918_, 23);
v_readmeFile_1945_ = lean_ctor_get(v_cfg_1918_, 24);
v_reservoir_1946_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1947_ = lean_ctor_get(v_cfg_1918_, 25);
v_restoreAllArtifacts_x3f_1948_ = lean_ctor_get(v_cfg_1918_, 26);
v_libPrefixOnWindows_1949_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29 + 4);
v_allowImportAll_1950_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1951_ = lean_ctor_get(v_cfg_1918_, 27);
v_checks_1952_ = lean_ctor_get(v_cfg_1918_, 28);
v_fixedToolchain_1953_ = lean_ctor_get_uint8(v_cfg_1918_, sizeof(void*)*29 + 6);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_cfg_1918_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v_cfg_1918_, 13);
lean_dec(v_unused_1961_);
v___x_1955_ = v_cfg_1918_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_checks_1952_);
lean_inc(v_builtinLint_x3f_1951_);
lean_inc(v_restoreAllArtifacts_x3f_1948_);
lean_inc(v_enableArtifactCache_x3f_1947_);
lean_inc(v_readmeFile_1945_);
lean_inc(v_licenseFiles_1944_);
lean_inc(v_license_1943_);
lean_inc(v_homepage_1942_);
lean_inc(v_keywords_1941_);
lean_inc(v_description_1940_);
lean_inc(v_versionTags_1939_);
lean_inc(v_version_1938_);
lean_inc(v_lintDriverArgs_1937_);
lean_inc(v_lintDriver_1936_);
lean_inc(v_testDriverArgs_1935_);
lean_inc(v_downloadCacheService_x3f_1934_);
lean_inc(v_buildArchive_1932_);
lean_inc(v_releaseRepo_1931_);
lean_inc(v_irDir_1930_);
lean_inc(v_binDir_1929_);
lean_inc(v_nativeLibDir_1928_);
lean_inc(v_leanLibDir_1927_);
lean_inc(v_buildDir_1926_);
lean_inc(v_srcDir_1925_);
lean_inc(v_moreGlobalServerArgs_1924_);
lean_inc(v_extraDepTargets_1922_);
lean_inc(v_toLeanConfig_1920_);
lean_inc(v_toWorkspaceConfig_1919_);
lean_dec(v_cfg_1918_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 13, v_val_1917_);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_toWorkspaceConfig_1919_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_toLeanConfig_1920_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_extraDepTargets_1922_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_moreGlobalServerArgs_1924_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v_srcDir_1925_);
lean_ctor_set(v_reuseFailAlloc_1959_, 5, v_buildDir_1926_);
lean_ctor_set(v_reuseFailAlloc_1959_, 6, v_leanLibDir_1927_);
lean_ctor_set(v_reuseFailAlloc_1959_, 7, v_nativeLibDir_1928_);
lean_ctor_set(v_reuseFailAlloc_1959_, 8, v_binDir_1929_);
lean_ctor_set(v_reuseFailAlloc_1959_, 9, v_irDir_1930_);
lean_ctor_set(v_reuseFailAlloc_1959_, 10, v_releaseRepo_1931_);
lean_ctor_set(v_reuseFailAlloc_1959_, 11, v_buildArchive_1932_);
lean_ctor_set(v_reuseFailAlloc_1959_, 12, v_downloadCacheService_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1959_, 13, v_val_1917_);
lean_ctor_set(v_reuseFailAlloc_1959_, 14, v_testDriverArgs_1935_);
lean_ctor_set(v_reuseFailAlloc_1959_, 15, v_lintDriver_1936_);
lean_ctor_set(v_reuseFailAlloc_1959_, 16, v_lintDriverArgs_1937_);
lean_ctor_set(v_reuseFailAlloc_1959_, 17, v_version_1938_);
lean_ctor_set(v_reuseFailAlloc_1959_, 18, v_versionTags_1939_);
lean_ctor_set(v_reuseFailAlloc_1959_, 19, v_description_1940_);
lean_ctor_set(v_reuseFailAlloc_1959_, 20, v_keywords_1941_);
lean_ctor_set(v_reuseFailAlloc_1959_, 21, v_homepage_1942_);
lean_ctor_set(v_reuseFailAlloc_1959_, 22, v_license_1943_);
lean_ctor_set(v_reuseFailAlloc_1959_, 23, v_licenseFiles_1944_);
lean_ctor_set(v_reuseFailAlloc_1959_, 24, v_readmeFile_1945_);
lean_ctor_set(v_reuseFailAlloc_1959_, 25, v_enableArtifactCache_x3f_1947_);
lean_ctor_set(v_reuseFailAlloc_1959_, 26, v_restoreAllArtifacts_x3f_1948_);
lean_ctor_set(v_reuseFailAlloc_1959_, 27, v_builtinLint_x3f_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 28, v_checks_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29, v_bootstrap_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29 + 1, v_precompileModules_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29 + 3, v_reservoir_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29 + 5, v_allowImportAll_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*29 + 6, v_fixedToolchain_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__2(lean_object* v_f_1962_, lean_object* v_cfg_1963_){
_start:
{
lean_object* v_toWorkspaceConfig_1964_; lean_object* v_toLeanConfig_1965_; uint8_t v_bootstrap_1966_; lean_object* v_extraDepTargets_1967_; uint8_t v_precompileModules_1968_; lean_object* v_moreGlobalServerArgs_1969_; lean_object* v_srcDir_1970_; lean_object* v_buildDir_1971_; lean_object* v_leanLibDir_1972_; lean_object* v_nativeLibDir_1973_; lean_object* v_binDir_1974_; lean_object* v_irDir_1975_; lean_object* v_releaseRepo_1976_; lean_object* v_buildArchive_1977_; uint8_t v_preferReleaseBuild_1978_; lean_object* v_downloadCacheService_x3f_1979_; lean_object* v_testDriver_1980_; lean_object* v_testDriverArgs_1981_; lean_object* v_lintDriver_1982_; lean_object* v_lintDriverArgs_1983_; lean_object* v_version_1984_; lean_object* v_versionTags_1985_; lean_object* v_description_1986_; lean_object* v_keywords_1987_; lean_object* v_homepage_1988_; lean_object* v_license_1989_; lean_object* v_licenseFiles_1990_; lean_object* v_readmeFile_1991_; uint8_t v_reservoir_1992_; lean_object* v_enableArtifactCache_x3f_1993_; lean_object* v_restoreAllArtifacts_x3f_1994_; uint8_t v_libPrefixOnWindows_1995_; uint8_t v_allowImportAll_1996_; lean_object* v_builtinLint_x3f_1997_; lean_object* v_checks_1998_; uint8_t v_fixedToolchain_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_toWorkspaceConfig_1964_ = lean_ctor_get(v_cfg_1963_, 0);
v_toLeanConfig_1965_ = lean_ctor_get(v_cfg_1963_, 1);
v_bootstrap_1966_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29);
v_extraDepTargets_1967_ = lean_ctor_get(v_cfg_1963_, 2);
v_precompileModules_1968_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_1969_ = lean_ctor_get(v_cfg_1963_, 3);
v_srcDir_1970_ = lean_ctor_get(v_cfg_1963_, 4);
v_buildDir_1971_ = lean_ctor_get(v_cfg_1963_, 5);
v_leanLibDir_1972_ = lean_ctor_get(v_cfg_1963_, 6);
v_nativeLibDir_1973_ = lean_ctor_get(v_cfg_1963_, 7);
v_binDir_1974_ = lean_ctor_get(v_cfg_1963_, 8);
v_irDir_1975_ = lean_ctor_get(v_cfg_1963_, 9);
v_releaseRepo_1976_ = lean_ctor_get(v_cfg_1963_, 10);
v_buildArchive_1977_ = lean_ctor_get(v_cfg_1963_, 11);
v_preferReleaseBuild_1978_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1979_ = lean_ctor_get(v_cfg_1963_, 12);
v_testDriver_1980_ = lean_ctor_get(v_cfg_1963_, 13);
v_testDriverArgs_1981_ = lean_ctor_get(v_cfg_1963_, 14);
v_lintDriver_1982_ = lean_ctor_get(v_cfg_1963_, 15);
v_lintDriverArgs_1983_ = lean_ctor_get(v_cfg_1963_, 16);
v_version_1984_ = lean_ctor_get(v_cfg_1963_, 17);
v_versionTags_1985_ = lean_ctor_get(v_cfg_1963_, 18);
v_description_1986_ = lean_ctor_get(v_cfg_1963_, 19);
v_keywords_1987_ = lean_ctor_get(v_cfg_1963_, 20);
v_homepage_1988_ = lean_ctor_get(v_cfg_1963_, 21);
v_license_1989_ = lean_ctor_get(v_cfg_1963_, 22);
v_licenseFiles_1990_ = lean_ctor_get(v_cfg_1963_, 23);
v_readmeFile_1991_ = lean_ctor_get(v_cfg_1963_, 24);
v_reservoir_1992_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_1993_ = lean_ctor_get(v_cfg_1963_, 25);
v_restoreAllArtifacts_x3f_1994_ = lean_ctor_get(v_cfg_1963_, 26);
v_libPrefixOnWindows_1995_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29 + 4);
v_allowImportAll_1996_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_1997_ = lean_ctor_get(v_cfg_1963_, 27);
v_checks_1998_ = lean_ctor_get(v_cfg_1963_, 28);
v_fixedToolchain_1999_ = lean_ctor_get_uint8(v_cfg_1963_, sizeof(void*)*29 + 6);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_cfg_1963_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2001_ = v_cfg_1963_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_checks_1998_);
lean_inc(v_builtinLint_x3f_1997_);
lean_inc(v_restoreAllArtifacts_x3f_1994_);
lean_inc(v_enableArtifactCache_x3f_1993_);
lean_inc(v_readmeFile_1991_);
lean_inc(v_licenseFiles_1990_);
lean_inc(v_license_1989_);
lean_inc(v_homepage_1988_);
lean_inc(v_keywords_1987_);
lean_inc(v_description_1986_);
lean_inc(v_versionTags_1985_);
lean_inc(v_version_1984_);
lean_inc(v_lintDriverArgs_1983_);
lean_inc(v_lintDriver_1982_);
lean_inc(v_testDriverArgs_1981_);
lean_inc(v_testDriver_1980_);
lean_inc(v_downloadCacheService_x3f_1979_);
lean_inc(v_buildArchive_1977_);
lean_inc(v_releaseRepo_1976_);
lean_inc(v_irDir_1975_);
lean_inc(v_binDir_1974_);
lean_inc(v_nativeLibDir_1973_);
lean_inc(v_leanLibDir_1972_);
lean_inc(v_buildDir_1971_);
lean_inc(v_srcDir_1970_);
lean_inc(v_moreGlobalServerArgs_1969_);
lean_inc(v_extraDepTargets_1967_);
lean_inc(v_toLeanConfig_1965_);
lean_inc(v_toWorkspaceConfig_1964_);
lean_dec(v_cfg_1963_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_apply_1(v_f_1962_, v_testDriver_1980_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 13, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_toWorkspaceConfig_1964_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_toLeanConfig_1965_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_extraDepTargets_1967_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_moreGlobalServerArgs_1969_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_srcDir_1970_);
lean_ctor_set(v_reuseFailAlloc_2006_, 5, v_buildDir_1971_);
lean_ctor_set(v_reuseFailAlloc_2006_, 6, v_leanLibDir_1972_);
lean_ctor_set(v_reuseFailAlloc_2006_, 7, v_nativeLibDir_1973_);
lean_ctor_set(v_reuseFailAlloc_2006_, 8, v_binDir_1974_);
lean_ctor_set(v_reuseFailAlloc_2006_, 9, v_irDir_1975_);
lean_ctor_set(v_reuseFailAlloc_2006_, 10, v_releaseRepo_1976_);
lean_ctor_set(v_reuseFailAlloc_2006_, 11, v_buildArchive_1977_);
lean_ctor_set(v_reuseFailAlloc_2006_, 12, v_downloadCacheService_x3f_1979_);
lean_ctor_set(v_reuseFailAlloc_2006_, 13, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 14, v_testDriverArgs_1981_);
lean_ctor_set(v_reuseFailAlloc_2006_, 15, v_lintDriver_1982_);
lean_ctor_set(v_reuseFailAlloc_2006_, 16, v_lintDriverArgs_1983_);
lean_ctor_set(v_reuseFailAlloc_2006_, 17, v_version_1984_);
lean_ctor_set(v_reuseFailAlloc_2006_, 18, v_versionTags_1985_);
lean_ctor_set(v_reuseFailAlloc_2006_, 19, v_description_1986_);
lean_ctor_set(v_reuseFailAlloc_2006_, 20, v_keywords_1987_);
lean_ctor_set(v_reuseFailAlloc_2006_, 21, v_homepage_1988_);
lean_ctor_set(v_reuseFailAlloc_2006_, 22, v_license_1989_);
lean_ctor_set(v_reuseFailAlloc_2006_, 23, v_licenseFiles_1990_);
lean_ctor_set(v_reuseFailAlloc_2006_, 24, v_readmeFile_1991_);
lean_ctor_set(v_reuseFailAlloc_2006_, 25, v_enableArtifactCache_x3f_1993_);
lean_ctor_set(v_reuseFailAlloc_2006_, 26, v_restoreAllArtifacts_x3f_1994_);
lean_ctor_set(v_reuseFailAlloc_2006_, 27, v_builtinLint_x3f_1997_);
lean_ctor_set(v_reuseFailAlloc_2006_, 28, v_checks_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29, v_bootstrap_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29 + 1, v_precompileModules_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29 + 2, v_preferReleaseBuild_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29 + 3, v_reservoir_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29 + 5, v_allowImportAll_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*29 + 6, v_fixedToolchain_1999_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(lean_object* v_x_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___lam__3___boxed(lean_object* v_x_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lake_PackageConfig_testDriver___proj___redArg___lam__3(v_x_2010_);
lean_dec_ref(v_x_2010_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg(){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = ((lean_object*)(l_Lake_PackageConfig_testDriver___proj___redArg___closed__4));
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___redArg___boxed(lean_object* v___dummy_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lake_PackageConfig_testDriver___proj___redArg();
return v_res_2024_;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriver___proj___closed__0(void){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lake_PackageConfig_testDriver___proj___redArg();
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj(lean_object* v_p_2026_, lean_object* v_n_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___proj___boxed(lean_object* v_p_2029_, lean_object* v_n_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lake_PackageConfig_testDriver___proj(v_p_2029_, v_n_2030_);
lean_dec(v_n_2030_);
lean_dec(v_p_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg(){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___redArg___boxed(lean_object* v___dummy_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lake_PackageConfig_testDriver_instConfigField___redArg();
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField(lean_object* v_p_2036_, lean_object* v_n_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver_instConfigField___boxed(lean_object* v_p_2039_, lean_object* v_n_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lake_PackageConfig_testDriver_instConfigField(v_p_2039_, v_n_2040_);
lean_dec(v_n_2040_);
lean_dec(v_p_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg(){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___redArg___boxed(lean_object* v___dummy_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lake_PackageConfig_testRunner_instConfigField___redArg();
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField(lean_object* v_p_2046_, lean_object* v_n_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_obj_once(&l_Lake_PackageConfig_testDriver___proj___closed__0, &l_Lake_PackageConfig_testDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriver___proj___closed__0);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testRunner_instConfigField___boxed(lean_object* v_p_2049_, lean_object* v_n_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lake_PackageConfig_testRunner_instConfigField(v_p_2049_, v_n_2050_);
lean_dec(v_n_2050_);
lean_dec(v_p_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(lean_object* v_cfg_2052_){
_start:
{
lean_object* v_testDriverArgs_2053_; 
v_testDriverArgs_2053_ = lean_ctor_get(v_cfg_2052_, 14);
lean_inc_ref(v_testDriverArgs_2053_);
return v_testDriverArgs_2053_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__0(v_cfg_2054_);
lean_dec_ref(v_cfg_2054_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__1(lean_object* v_val_2056_, lean_object* v_cfg_2057_){
_start:
{
lean_object* v_toWorkspaceConfig_2058_; lean_object* v_toLeanConfig_2059_; uint8_t v_bootstrap_2060_; lean_object* v_extraDepTargets_2061_; uint8_t v_precompileModules_2062_; lean_object* v_moreGlobalServerArgs_2063_; lean_object* v_srcDir_2064_; lean_object* v_buildDir_2065_; lean_object* v_leanLibDir_2066_; lean_object* v_nativeLibDir_2067_; lean_object* v_binDir_2068_; lean_object* v_irDir_2069_; lean_object* v_releaseRepo_2070_; lean_object* v_buildArchive_2071_; uint8_t v_preferReleaseBuild_2072_; lean_object* v_downloadCacheService_x3f_2073_; lean_object* v_testDriver_2074_; lean_object* v_lintDriver_2075_; lean_object* v_lintDriverArgs_2076_; lean_object* v_version_2077_; lean_object* v_versionTags_2078_; lean_object* v_description_2079_; lean_object* v_keywords_2080_; lean_object* v_homepage_2081_; lean_object* v_license_2082_; lean_object* v_licenseFiles_2083_; lean_object* v_readmeFile_2084_; uint8_t v_reservoir_2085_; lean_object* v_enableArtifactCache_x3f_2086_; lean_object* v_restoreAllArtifacts_x3f_2087_; uint8_t v_libPrefixOnWindows_2088_; uint8_t v_allowImportAll_2089_; lean_object* v_builtinLint_x3f_2090_; lean_object* v_checks_2091_; uint8_t v_fixedToolchain_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
v_toWorkspaceConfig_2058_ = lean_ctor_get(v_cfg_2057_, 0);
v_toLeanConfig_2059_ = lean_ctor_get(v_cfg_2057_, 1);
v_bootstrap_2060_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29);
v_extraDepTargets_2061_ = lean_ctor_get(v_cfg_2057_, 2);
v_precompileModules_2062_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2063_ = lean_ctor_get(v_cfg_2057_, 3);
v_srcDir_2064_ = lean_ctor_get(v_cfg_2057_, 4);
v_buildDir_2065_ = lean_ctor_get(v_cfg_2057_, 5);
v_leanLibDir_2066_ = lean_ctor_get(v_cfg_2057_, 6);
v_nativeLibDir_2067_ = lean_ctor_get(v_cfg_2057_, 7);
v_binDir_2068_ = lean_ctor_get(v_cfg_2057_, 8);
v_irDir_2069_ = lean_ctor_get(v_cfg_2057_, 9);
v_releaseRepo_2070_ = lean_ctor_get(v_cfg_2057_, 10);
v_buildArchive_2071_ = lean_ctor_get(v_cfg_2057_, 11);
v_preferReleaseBuild_2072_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2073_ = lean_ctor_get(v_cfg_2057_, 12);
v_testDriver_2074_ = lean_ctor_get(v_cfg_2057_, 13);
v_lintDriver_2075_ = lean_ctor_get(v_cfg_2057_, 15);
v_lintDriverArgs_2076_ = lean_ctor_get(v_cfg_2057_, 16);
v_version_2077_ = lean_ctor_get(v_cfg_2057_, 17);
v_versionTags_2078_ = lean_ctor_get(v_cfg_2057_, 18);
v_description_2079_ = lean_ctor_get(v_cfg_2057_, 19);
v_keywords_2080_ = lean_ctor_get(v_cfg_2057_, 20);
v_homepage_2081_ = lean_ctor_get(v_cfg_2057_, 21);
v_license_2082_ = lean_ctor_get(v_cfg_2057_, 22);
v_licenseFiles_2083_ = lean_ctor_get(v_cfg_2057_, 23);
v_readmeFile_2084_ = lean_ctor_get(v_cfg_2057_, 24);
v_reservoir_2085_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2086_ = lean_ctor_get(v_cfg_2057_, 25);
v_restoreAllArtifacts_x3f_2087_ = lean_ctor_get(v_cfg_2057_, 26);
v_libPrefixOnWindows_2088_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29 + 4);
v_allowImportAll_2089_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2090_ = lean_ctor_get(v_cfg_2057_, 27);
v_checks_2091_ = lean_ctor_get(v_cfg_2057_, 28);
v_fixedToolchain_2092_ = lean_ctor_get_uint8(v_cfg_2057_, sizeof(void*)*29 + 6);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_cfg_2057_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_cfg_2057_, 14);
lean_dec(v_unused_2100_);
v___x_2094_ = v_cfg_2057_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_checks_2091_);
lean_inc(v_builtinLint_x3f_2090_);
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
lean_inc(v_testDriver_2074_);
lean_inc(v_downloadCacheService_x3f_2073_);
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
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 14, v_val_2056_);
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_toWorkspaceConfig_2058_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_toLeanConfig_2059_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_extraDepTargets_2061_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_moreGlobalServerArgs_2063_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_srcDir_2064_);
lean_ctor_set(v_reuseFailAlloc_2098_, 5, v_buildDir_2065_);
lean_ctor_set(v_reuseFailAlloc_2098_, 6, v_leanLibDir_2066_);
lean_ctor_set(v_reuseFailAlloc_2098_, 7, v_nativeLibDir_2067_);
lean_ctor_set(v_reuseFailAlloc_2098_, 8, v_binDir_2068_);
lean_ctor_set(v_reuseFailAlloc_2098_, 9, v_irDir_2069_);
lean_ctor_set(v_reuseFailAlloc_2098_, 10, v_releaseRepo_2070_);
lean_ctor_set(v_reuseFailAlloc_2098_, 11, v_buildArchive_2071_);
lean_ctor_set(v_reuseFailAlloc_2098_, 12, v_downloadCacheService_x3f_2073_);
lean_ctor_set(v_reuseFailAlloc_2098_, 13, v_testDriver_2074_);
lean_ctor_set(v_reuseFailAlloc_2098_, 14, v_val_2056_);
lean_ctor_set(v_reuseFailAlloc_2098_, 15, v_lintDriver_2075_);
lean_ctor_set(v_reuseFailAlloc_2098_, 16, v_lintDriverArgs_2076_);
lean_ctor_set(v_reuseFailAlloc_2098_, 17, v_version_2077_);
lean_ctor_set(v_reuseFailAlloc_2098_, 18, v_versionTags_2078_);
lean_ctor_set(v_reuseFailAlloc_2098_, 19, v_description_2079_);
lean_ctor_set(v_reuseFailAlloc_2098_, 20, v_keywords_2080_);
lean_ctor_set(v_reuseFailAlloc_2098_, 21, v_homepage_2081_);
lean_ctor_set(v_reuseFailAlloc_2098_, 22, v_license_2082_);
lean_ctor_set(v_reuseFailAlloc_2098_, 23, v_licenseFiles_2083_);
lean_ctor_set(v_reuseFailAlloc_2098_, 24, v_readmeFile_2084_);
lean_ctor_set(v_reuseFailAlloc_2098_, 25, v_enableArtifactCache_x3f_2086_);
lean_ctor_set(v_reuseFailAlloc_2098_, 26, v_restoreAllArtifacts_x3f_2087_);
lean_ctor_set(v_reuseFailAlloc_2098_, 27, v_builtinLint_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2098_, 28, v_checks_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29, v_bootstrap_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29 + 1, v_precompileModules_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29 + 3, v_reservoir_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29 + 5, v_allowImportAll_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2098_, sizeof(void*)*29 + 6, v_fixedToolchain_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___lam__2(lean_object* v_f_2101_, lean_object* v_cfg_2102_){
_start:
{
lean_object* v_toWorkspaceConfig_2103_; lean_object* v_toLeanConfig_2104_; uint8_t v_bootstrap_2105_; lean_object* v_extraDepTargets_2106_; uint8_t v_precompileModules_2107_; lean_object* v_moreGlobalServerArgs_2108_; lean_object* v_srcDir_2109_; lean_object* v_buildDir_2110_; lean_object* v_leanLibDir_2111_; lean_object* v_nativeLibDir_2112_; lean_object* v_binDir_2113_; lean_object* v_irDir_2114_; lean_object* v_releaseRepo_2115_; lean_object* v_buildArchive_2116_; uint8_t v_preferReleaseBuild_2117_; lean_object* v_downloadCacheService_x3f_2118_; lean_object* v_testDriver_2119_; lean_object* v_testDriverArgs_2120_; lean_object* v_lintDriver_2121_; lean_object* v_lintDriverArgs_2122_; lean_object* v_version_2123_; lean_object* v_versionTags_2124_; lean_object* v_description_2125_; lean_object* v_keywords_2126_; lean_object* v_homepage_2127_; lean_object* v_license_2128_; lean_object* v_licenseFiles_2129_; lean_object* v_readmeFile_2130_; uint8_t v_reservoir_2131_; lean_object* v_enableArtifactCache_x3f_2132_; lean_object* v_restoreAllArtifacts_x3f_2133_; uint8_t v_libPrefixOnWindows_2134_; uint8_t v_allowImportAll_2135_; lean_object* v_builtinLint_x3f_2136_; lean_object* v_checks_2137_; uint8_t v_fixedToolchain_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
v_toWorkspaceConfig_2103_ = lean_ctor_get(v_cfg_2102_, 0);
v_toLeanConfig_2104_ = lean_ctor_get(v_cfg_2102_, 1);
v_bootstrap_2105_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29);
v_extraDepTargets_2106_ = lean_ctor_get(v_cfg_2102_, 2);
v_precompileModules_2107_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2108_ = lean_ctor_get(v_cfg_2102_, 3);
v_srcDir_2109_ = lean_ctor_get(v_cfg_2102_, 4);
v_buildDir_2110_ = lean_ctor_get(v_cfg_2102_, 5);
v_leanLibDir_2111_ = lean_ctor_get(v_cfg_2102_, 6);
v_nativeLibDir_2112_ = lean_ctor_get(v_cfg_2102_, 7);
v_binDir_2113_ = lean_ctor_get(v_cfg_2102_, 8);
v_irDir_2114_ = lean_ctor_get(v_cfg_2102_, 9);
v_releaseRepo_2115_ = lean_ctor_get(v_cfg_2102_, 10);
v_buildArchive_2116_ = lean_ctor_get(v_cfg_2102_, 11);
v_preferReleaseBuild_2117_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2118_ = lean_ctor_get(v_cfg_2102_, 12);
v_testDriver_2119_ = lean_ctor_get(v_cfg_2102_, 13);
v_testDriverArgs_2120_ = lean_ctor_get(v_cfg_2102_, 14);
v_lintDriver_2121_ = lean_ctor_get(v_cfg_2102_, 15);
v_lintDriverArgs_2122_ = lean_ctor_get(v_cfg_2102_, 16);
v_version_2123_ = lean_ctor_get(v_cfg_2102_, 17);
v_versionTags_2124_ = lean_ctor_get(v_cfg_2102_, 18);
v_description_2125_ = lean_ctor_get(v_cfg_2102_, 19);
v_keywords_2126_ = lean_ctor_get(v_cfg_2102_, 20);
v_homepage_2127_ = lean_ctor_get(v_cfg_2102_, 21);
v_license_2128_ = lean_ctor_get(v_cfg_2102_, 22);
v_licenseFiles_2129_ = lean_ctor_get(v_cfg_2102_, 23);
v_readmeFile_2130_ = lean_ctor_get(v_cfg_2102_, 24);
v_reservoir_2131_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2132_ = lean_ctor_get(v_cfg_2102_, 25);
v_restoreAllArtifacts_x3f_2133_ = lean_ctor_get(v_cfg_2102_, 26);
v_libPrefixOnWindows_2134_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29 + 4);
v_allowImportAll_2135_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2136_ = lean_ctor_get(v_cfg_2102_, 27);
v_checks_2137_ = lean_ctor_get(v_cfg_2102_, 28);
v_fixedToolchain_2138_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*29 + 6);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_cfg_2102_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v_cfg_2102_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_checks_2137_);
lean_inc(v_builtinLint_x3f_2136_);
lean_inc(v_restoreAllArtifacts_x3f_2133_);
lean_inc(v_enableArtifactCache_x3f_2132_);
lean_inc(v_readmeFile_2130_);
lean_inc(v_licenseFiles_2129_);
lean_inc(v_license_2128_);
lean_inc(v_homepage_2127_);
lean_inc(v_keywords_2126_);
lean_inc(v_description_2125_);
lean_inc(v_versionTags_2124_);
lean_inc(v_version_2123_);
lean_inc(v_lintDriverArgs_2122_);
lean_inc(v_lintDriver_2121_);
lean_inc(v_testDriverArgs_2120_);
lean_inc(v_testDriver_2119_);
lean_inc(v_downloadCacheService_x3f_2118_);
lean_inc(v_buildArchive_2116_);
lean_inc(v_releaseRepo_2115_);
lean_inc(v_irDir_2114_);
lean_inc(v_binDir_2113_);
lean_inc(v_nativeLibDir_2112_);
lean_inc(v_leanLibDir_2111_);
lean_inc(v_buildDir_2110_);
lean_inc(v_srcDir_2109_);
lean_inc(v_moreGlobalServerArgs_2108_);
lean_inc(v_extraDepTargets_2106_);
lean_inc(v_toLeanConfig_2104_);
lean_inc(v_toWorkspaceConfig_2103_);
lean_dec(v_cfg_2102_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_apply_1(v_f_2101_, v_testDriverArgs_2120_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 14, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_toWorkspaceConfig_2103_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_toLeanConfig_2104_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_extraDepTargets_2106_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_moreGlobalServerArgs_2108_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_srcDir_2109_);
lean_ctor_set(v_reuseFailAlloc_2145_, 5, v_buildDir_2110_);
lean_ctor_set(v_reuseFailAlloc_2145_, 6, v_leanLibDir_2111_);
lean_ctor_set(v_reuseFailAlloc_2145_, 7, v_nativeLibDir_2112_);
lean_ctor_set(v_reuseFailAlloc_2145_, 8, v_binDir_2113_);
lean_ctor_set(v_reuseFailAlloc_2145_, 9, v_irDir_2114_);
lean_ctor_set(v_reuseFailAlloc_2145_, 10, v_releaseRepo_2115_);
lean_ctor_set(v_reuseFailAlloc_2145_, 11, v_buildArchive_2116_);
lean_ctor_set(v_reuseFailAlloc_2145_, 12, v_downloadCacheService_x3f_2118_);
lean_ctor_set(v_reuseFailAlloc_2145_, 13, v_testDriver_2119_);
lean_ctor_set(v_reuseFailAlloc_2145_, 14, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2145_, 15, v_lintDriver_2121_);
lean_ctor_set(v_reuseFailAlloc_2145_, 16, v_lintDriverArgs_2122_);
lean_ctor_set(v_reuseFailAlloc_2145_, 17, v_version_2123_);
lean_ctor_set(v_reuseFailAlloc_2145_, 18, v_versionTags_2124_);
lean_ctor_set(v_reuseFailAlloc_2145_, 19, v_description_2125_);
lean_ctor_set(v_reuseFailAlloc_2145_, 20, v_keywords_2126_);
lean_ctor_set(v_reuseFailAlloc_2145_, 21, v_homepage_2127_);
lean_ctor_set(v_reuseFailAlloc_2145_, 22, v_license_2128_);
lean_ctor_set(v_reuseFailAlloc_2145_, 23, v_licenseFiles_2129_);
lean_ctor_set(v_reuseFailAlloc_2145_, 24, v_readmeFile_2130_);
lean_ctor_set(v_reuseFailAlloc_2145_, 25, v_enableArtifactCache_x3f_2132_);
lean_ctor_set(v_reuseFailAlloc_2145_, 26, v_restoreAllArtifacts_x3f_2133_);
lean_ctor_set(v_reuseFailAlloc_2145_, 27, v_builtinLint_x3f_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 28, v_checks_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29, v_bootstrap_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29 + 1, v_precompileModules_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2117_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29 + 3, v_reservoir_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29 + 5, v_allowImportAll_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*29 + 6, v_fixedToolchain_2138_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg(){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = ((lean_object*)(l_Lake_PackageConfig_testDriverArgs___proj___redArg___closed__3));
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___redArg___boxed(lean_object* v___dummy_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
return v_res_2158_;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lake_PackageConfig_testDriverArgs___proj___redArg();
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj(lean_object* v_p_2160_, lean_object* v_n_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___proj___boxed(lean_object* v_p_2163_, lean_object* v_n_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lake_PackageConfig_testDriverArgs___proj(v_p_2163_, v_n_2164_);
lean_dec(v_n_2164_);
lean_dec(v_p_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg___boxed(lean_object* v___dummy_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lake_PackageConfig_testDriverArgs_instConfigField___redArg();
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField(lean_object* v_p_2170_, lean_object* v_n_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_obj_once(&l_Lake_PackageConfig_testDriverArgs___proj___closed__0, &l_Lake_PackageConfig_testDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_testDriverArgs___proj___closed__0);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs_instConfigField___boxed(lean_object* v_p_2173_, lean_object* v_n_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lake_PackageConfig_testDriverArgs_instConfigField(v_p_2173_, v_n_2174_);
lean_dec(v_n_2174_);
lean_dec(v_p_2173_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(lean_object* v_cfg_2176_){
_start:
{
lean_object* v_lintDriver_2177_; 
v_lintDriver_2177_ = lean_ctor_get(v_cfg_2176_, 15);
lean_inc_ref(v_lintDriver_2177_);
return v_lintDriver_2177_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0___boxed(lean_object* v_cfg_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lake_PackageConfig_lintDriver___proj___redArg___lam__0(v_cfg_2178_);
lean_dec_ref(v_cfg_2178_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__1(lean_object* v_val_2180_, lean_object* v_cfg_2181_){
_start:
{
lean_object* v_toWorkspaceConfig_2182_; lean_object* v_toLeanConfig_2183_; uint8_t v_bootstrap_2184_; lean_object* v_extraDepTargets_2185_; uint8_t v_precompileModules_2186_; lean_object* v_moreGlobalServerArgs_2187_; lean_object* v_srcDir_2188_; lean_object* v_buildDir_2189_; lean_object* v_leanLibDir_2190_; lean_object* v_nativeLibDir_2191_; lean_object* v_binDir_2192_; lean_object* v_irDir_2193_; lean_object* v_releaseRepo_2194_; lean_object* v_buildArchive_2195_; uint8_t v_preferReleaseBuild_2196_; lean_object* v_downloadCacheService_x3f_2197_; lean_object* v_testDriver_2198_; lean_object* v_testDriverArgs_2199_; lean_object* v_lintDriverArgs_2200_; lean_object* v_version_2201_; lean_object* v_versionTags_2202_; lean_object* v_description_2203_; lean_object* v_keywords_2204_; lean_object* v_homepage_2205_; lean_object* v_license_2206_; lean_object* v_licenseFiles_2207_; lean_object* v_readmeFile_2208_; uint8_t v_reservoir_2209_; lean_object* v_enableArtifactCache_x3f_2210_; lean_object* v_restoreAllArtifacts_x3f_2211_; uint8_t v_libPrefixOnWindows_2212_; uint8_t v_allowImportAll_2213_; lean_object* v_builtinLint_x3f_2214_; lean_object* v_checks_2215_; uint8_t v_fixedToolchain_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v_toWorkspaceConfig_2182_ = lean_ctor_get(v_cfg_2181_, 0);
v_toLeanConfig_2183_ = lean_ctor_get(v_cfg_2181_, 1);
v_bootstrap_2184_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29);
v_extraDepTargets_2185_ = lean_ctor_get(v_cfg_2181_, 2);
v_precompileModules_2186_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2187_ = lean_ctor_get(v_cfg_2181_, 3);
v_srcDir_2188_ = lean_ctor_get(v_cfg_2181_, 4);
v_buildDir_2189_ = lean_ctor_get(v_cfg_2181_, 5);
v_leanLibDir_2190_ = lean_ctor_get(v_cfg_2181_, 6);
v_nativeLibDir_2191_ = lean_ctor_get(v_cfg_2181_, 7);
v_binDir_2192_ = lean_ctor_get(v_cfg_2181_, 8);
v_irDir_2193_ = lean_ctor_get(v_cfg_2181_, 9);
v_releaseRepo_2194_ = lean_ctor_get(v_cfg_2181_, 10);
v_buildArchive_2195_ = lean_ctor_get(v_cfg_2181_, 11);
v_preferReleaseBuild_2196_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2197_ = lean_ctor_get(v_cfg_2181_, 12);
v_testDriver_2198_ = lean_ctor_get(v_cfg_2181_, 13);
v_testDriverArgs_2199_ = lean_ctor_get(v_cfg_2181_, 14);
v_lintDriverArgs_2200_ = lean_ctor_get(v_cfg_2181_, 16);
v_version_2201_ = lean_ctor_get(v_cfg_2181_, 17);
v_versionTags_2202_ = lean_ctor_get(v_cfg_2181_, 18);
v_description_2203_ = lean_ctor_get(v_cfg_2181_, 19);
v_keywords_2204_ = lean_ctor_get(v_cfg_2181_, 20);
v_homepage_2205_ = lean_ctor_get(v_cfg_2181_, 21);
v_license_2206_ = lean_ctor_get(v_cfg_2181_, 22);
v_licenseFiles_2207_ = lean_ctor_get(v_cfg_2181_, 23);
v_readmeFile_2208_ = lean_ctor_get(v_cfg_2181_, 24);
v_reservoir_2209_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2210_ = lean_ctor_get(v_cfg_2181_, 25);
v_restoreAllArtifacts_x3f_2211_ = lean_ctor_get(v_cfg_2181_, 26);
v_libPrefixOnWindows_2212_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29 + 4);
v_allowImportAll_2213_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2214_ = lean_ctor_get(v_cfg_2181_, 27);
v_checks_2215_ = lean_ctor_get(v_cfg_2181_, 28);
v_fixedToolchain_2216_ = lean_ctor_get_uint8(v_cfg_2181_, sizeof(void*)*29 + 6);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_cfg_2181_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v_cfg_2181_, 15);
lean_dec(v_unused_2224_);
v___x_2218_ = v_cfg_2181_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_checks_2215_);
lean_inc(v_builtinLint_x3f_2214_);
lean_inc(v_restoreAllArtifacts_x3f_2211_);
lean_inc(v_enableArtifactCache_x3f_2210_);
lean_inc(v_readmeFile_2208_);
lean_inc(v_licenseFiles_2207_);
lean_inc(v_license_2206_);
lean_inc(v_homepage_2205_);
lean_inc(v_keywords_2204_);
lean_inc(v_description_2203_);
lean_inc(v_versionTags_2202_);
lean_inc(v_version_2201_);
lean_inc(v_lintDriverArgs_2200_);
lean_inc(v_testDriverArgs_2199_);
lean_inc(v_testDriver_2198_);
lean_inc(v_downloadCacheService_x3f_2197_);
lean_inc(v_buildArchive_2195_);
lean_inc(v_releaseRepo_2194_);
lean_inc(v_irDir_2193_);
lean_inc(v_binDir_2192_);
lean_inc(v_nativeLibDir_2191_);
lean_inc(v_leanLibDir_2190_);
lean_inc(v_buildDir_2189_);
lean_inc(v_srcDir_2188_);
lean_inc(v_moreGlobalServerArgs_2187_);
lean_inc(v_extraDepTargets_2185_);
lean_inc(v_toLeanConfig_2183_);
lean_inc(v_toWorkspaceConfig_2182_);
lean_dec(v_cfg_2181_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 15, v_val_2180_);
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_toWorkspaceConfig_2182_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_toLeanConfig_2183_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_extraDepTargets_2185_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_moreGlobalServerArgs_2187_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_srcDir_2188_);
lean_ctor_set(v_reuseFailAlloc_2222_, 5, v_buildDir_2189_);
lean_ctor_set(v_reuseFailAlloc_2222_, 6, v_leanLibDir_2190_);
lean_ctor_set(v_reuseFailAlloc_2222_, 7, v_nativeLibDir_2191_);
lean_ctor_set(v_reuseFailAlloc_2222_, 8, v_binDir_2192_);
lean_ctor_set(v_reuseFailAlloc_2222_, 9, v_irDir_2193_);
lean_ctor_set(v_reuseFailAlloc_2222_, 10, v_releaseRepo_2194_);
lean_ctor_set(v_reuseFailAlloc_2222_, 11, v_buildArchive_2195_);
lean_ctor_set(v_reuseFailAlloc_2222_, 12, v_downloadCacheService_x3f_2197_);
lean_ctor_set(v_reuseFailAlloc_2222_, 13, v_testDriver_2198_);
lean_ctor_set(v_reuseFailAlloc_2222_, 14, v_testDriverArgs_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 15, v_val_2180_);
lean_ctor_set(v_reuseFailAlloc_2222_, 16, v_lintDriverArgs_2200_);
lean_ctor_set(v_reuseFailAlloc_2222_, 17, v_version_2201_);
lean_ctor_set(v_reuseFailAlloc_2222_, 18, v_versionTags_2202_);
lean_ctor_set(v_reuseFailAlloc_2222_, 19, v_description_2203_);
lean_ctor_set(v_reuseFailAlloc_2222_, 20, v_keywords_2204_);
lean_ctor_set(v_reuseFailAlloc_2222_, 21, v_homepage_2205_);
lean_ctor_set(v_reuseFailAlloc_2222_, 22, v_license_2206_);
lean_ctor_set(v_reuseFailAlloc_2222_, 23, v_licenseFiles_2207_);
lean_ctor_set(v_reuseFailAlloc_2222_, 24, v_readmeFile_2208_);
lean_ctor_set(v_reuseFailAlloc_2222_, 25, v_enableArtifactCache_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2222_, 26, v_restoreAllArtifacts_x3f_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 27, v_builtinLint_x3f_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 28, v_checks_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29, v_bootstrap_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29 + 1, v_precompileModules_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29 + 3, v_reservoir_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29 + 5, v_allowImportAll_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*29 + 6, v_fixedToolchain_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___lam__2(lean_object* v_f_2225_, lean_object* v_cfg_2226_){
_start:
{
lean_object* v_toWorkspaceConfig_2227_; lean_object* v_toLeanConfig_2228_; uint8_t v_bootstrap_2229_; lean_object* v_extraDepTargets_2230_; uint8_t v_precompileModules_2231_; lean_object* v_moreGlobalServerArgs_2232_; lean_object* v_srcDir_2233_; lean_object* v_buildDir_2234_; lean_object* v_leanLibDir_2235_; lean_object* v_nativeLibDir_2236_; lean_object* v_binDir_2237_; lean_object* v_irDir_2238_; lean_object* v_releaseRepo_2239_; lean_object* v_buildArchive_2240_; uint8_t v_preferReleaseBuild_2241_; lean_object* v_downloadCacheService_x3f_2242_; lean_object* v_testDriver_2243_; lean_object* v_testDriverArgs_2244_; lean_object* v_lintDriver_2245_; lean_object* v_lintDriverArgs_2246_; lean_object* v_version_2247_; lean_object* v_versionTags_2248_; lean_object* v_description_2249_; lean_object* v_keywords_2250_; lean_object* v_homepage_2251_; lean_object* v_license_2252_; lean_object* v_licenseFiles_2253_; lean_object* v_readmeFile_2254_; uint8_t v_reservoir_2255_; lean_object* v_enableArtifactCache_x3f_2256_; lean_object* v_restoreAllArtifacts_x3f_2257_; uint8_t v_libPrefixOnWindows_2258_; uint8_t v_allowImportAll_2259_; lean_object* v_builtinLint_x3f_2260_; lean_object* v_checks_2261_; uint8_t v_fixedToolchain_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2270_; 
v_toWorkspaceConfig_2227_ = lean_ctor_get(v_cfg_2226_, 0);
v_toLeanConfig_2228_ = lean_ctor_get(v_cfg_2226_, 1);
v_bootstrap_2229_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29);
v_extraDepTargets_2230_ = lean_ctor_get(v_cfg_2226_, 2);
v_precompileModules_2231_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2232_ = lean_ctor_get(v_cfg_2226_, 3);
v_srcDir_2233_ = lean_ctor_get(v_cfg_2226_, 4);
v_buildDir_2234_ = lean_ctor_get(v_cfg_2226_, 5);
v_leanLibDir_2235_ = lean_ctor_get(v_cfg_2226_, 6);
v_nativeLibDir_2236_ = lean_ctor_get(v_cfg_2226_, 7);
v_binDir_2237_ = lean_ctor_get(v_cfg_2226_, 8);
v_irDir_2238_ = lean_ctor_get(v_cfg_2226_, 9);
v_releaseRepo_2239_ = lean_ctor_get(v_cfg_2226_, 10);
v_buildArchive_2240_ = lean_ctor_get(v_cfg_2226_, 11);
v_preferReleaseBuild_2241_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2242_ = lean_ctor_get(v_cfg_2226_, 12);
v_testDriver_2243_ = lean_ctor_get(v_cfg_2226_, 13);
v_testDriverArgs_2244_ = lean_ctor_get(v_cfg_2226_, 14);
v_lintDriver_2245_ = lean_ctor_get(v_cfg_2226_, 15);
v_lintDriverArgs_2246_ = lean_ctor_get(v_cfg_2226_, 16);
v_version_2247_ = lean_ctor_get(v_cfg_2226_, 17);
v_versionTags_2248_ = lean_ctor_get(v_cfg_2226_, 18);
v_description_2249_ = lean_ctor_get(v_cfg_2226_, 19);
v_keywords_2250_ = lean_ctor_get(v_cfg_2226_, 20);
v_homepage_2251_ = lean_ctor_get(v_cfg_2226_, 21);
v_license_2252_ = lean_ctor_get(v_cfg_2226_, 22);
v_licenseFiles_2253_ = lean_ctor_get(v_cfg_2226_, 23);
v_readmeFile_2254_ = lean_ctor_get(v_cfg_2226_, 24);
v_reservoir_2255_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2256_ = lean_ctor_get(v_cfg_2226_, 25);
v_restoreAllArtifacts_x3f_2257_ = lean_ctor_get(v_cfg_2226_, 26);
v_libPrefixOnWindows_2258_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29 + 4);
v_allowImportAll_2259_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2260_ = lean_ctor_get(v_cfg_2226_, 27);
v_checks_2261_ = lean_ctor_get(v_cfg_2226_, 28);
v_fixedToolchain_2262_ = lean_ctor_get_uint8(v_cfg_2226_, sizeof(void*)*29 + 6);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_cfg_2226_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2264_ = v_cfg_2226_;
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_checks_2261_);
lean_inc(v_builtinLint_x3f_2260_);
lean_inc(v_restoreAllArtifacts_x3f_2257_);
lean_inc(v_enableArtifactCache_x3f_2256_);
lean_inc(v_readmeFile_2254_);
lean_inc(v_licenseFiles_2253_);
lean_inc(v_license_2252_);
lean_inc(v_homepage_2251_);
lean_inc(v_keywords_2250_);
lean_inc(v_description_2249_);
lean_inc(v_versionTags_2248_);
lean_inc(v_version_2247_);
lean_inc(v_lintDriverArgs_2246_);
lean_inc(v_lintDriver_2245_);
lean_inc(v_testDriverArgs_2244_);
lean_inc(v_testDriver_2243_);
lean_inc(v_downloadCacheService_x3f_2242_);
lean_inc(v_buildArchive_2240_);
lean_inc(v_releaseRepo_2239_);
lean_inc(v_irDir_2238_);
lean_inc(v_binDir_2237_);
lean_inc(v_nativeLibDir_2236_);
lean_inc(v_leanLibDir_2235_);
lean_inc(v_buildDir_2234_);
lean_inc(v_srcDir_2233_);
lean_inc(v_moreGlobalServerArgs_2232_);
lean_inc(v_extraDepTargets_2230_);
lean_inc(v_toLeanConfig_2228_);
lean_inc(v_toWorkspaceConfig_2227_);
lean_dec(v_cfg_2226_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = lean_apply_1(v_f_2225_, v_lintDriver_2245_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 15, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_toWorkspaceConfig_2227_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_toLeanConfig_2228_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_extraDepTargets_2230_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_moreGlobalServerArgs_2232_);
lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_srcDir_2233_);
lean_ctor_set(v_reuseFailAlloc_2269_, 5, v_buildDir_2234_);
lean_ctor_set(v_reuseFailAlloc_2269_, 6, v_leanLibDir_2235_);
lean_ctor_set(v_reuseFailAlloc_2269_, 7, v_nativeLibDir_2236_);
lean_ctor_set(v_reuseFailAlloc_2269_, 8, v_binDir_2237_);
lean_ctor_set(v_reuseFailAlloc_2269_, 9, v_irDir_2238_);
lean_ctor_set(v_reuseFailAlloc_2269_, 10, v_releaseRepo_2239_);
lean_ctor_set(v_reuseFailAlloc_2269_, 11, v_buildArchive_2240_);
lean_ctor_set(v_reuseFailAlloc_2269_, 12, v_downloadCacheService_x3f_2242_);
lean_ctor_set(v_reuseFailAlloc_2269_, 13, v_testDriver_2243_);
lean_ctor_set(v_reuseFailAlloc_2269_, 14, v_testDriverArgs_2244_);
lean_ctor_set(v_reuseFailAlloc_2269_, 15, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2269_, 16, v_lintDriverArgs_2246_);
lean_ctor_set(v_reuseFailAlloc_2269_, 17, v_version_2247_);
lean_ctor_set(v_reuseFailAlloc_2269_, 18, v_versionTags_2248_);
lean_ctor_set(v_reuseFailAlloc_2269_, 19, v_description_2249_);
lean_ctor_set(v_reuseFailAlloc_2269_, 20, v_keywords_2250_);
lean_ctor_set(v_reuseFailAlloc_2269_, 21, v_homepage_2251_);
lean_ctor_set(v_reuseFailAlloc_2269_, 22, v_license_2252_);
lean_ctor_set(v_reuseFailAlloc_2269_, 23, v_licenseFiles_2253_);
lean_ctor_set(v_reuseFailAlloc_2269_, 24, v_readmeFile_2254_);
lean_ctor_set(v_reuseFailAlloc_2269_, 25, v_enableArtifactCache_x3f_2256_);
lean_ctor_set(v_reuseFailAlloc_2269_, 26, v_restoreAllArtifacts_x3f_2257_);
lean_ctor_set(v_reuseFailAlloc_2269_, 27, v_builtinLint_x3f_2260_);
lean_ctor_set(v_reuseFailAlloc_2269_, 28, v_checks_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29, v_bootstrap_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29 + 1, v_precompileModules_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2241_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29 + 3, v_reservoir_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29 + 5, v_allowImportAll_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2269_, sizeof(void*)*29 + 6, v_fixedToolchain_2262_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg(){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = ((lean_object*)(l_Lake_PackageConfig_lintDriver___proj___redArg___closed__3));
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___redArg___boxed(lean_object* v___dummy_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
return v_res_2282_;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriver___proj___closed__0(void){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lake_PackageConfig_lintDriver___proj___redArg();
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj(lean_object* v_p_2284_, lean_object* v_n_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___proj___boxed(lean_object* v_p_2287_, lean_object* v_n_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lake_PackageConfig_lintDriver___proj(v_p_2287_, v_n_2288_);
lean_dec(v_n_2288_);
lean_dec(v_p_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg(){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___redArg___boxed(lean_object* v___dummy_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lake_PackageConfig_lintDriver_instConfigField___redArg();
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField(lean_object* v_p_2294_, lean_object* v_n_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_obj_once(&l_Lake_PackageConfig_lintDriver___proj___closed__0, &l_Lake_PackageConfig_lintDriver___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriver___proj___closed__0);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver_instConfigField___boxed(lean_object* v_p_2297_, lean_object* v_n_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lake_PackageConfig_lintDriver_instConfigField(v_p_2297_, v_n_2298_);
lean_dec(v_n_2298_);
lean_dec(v_p_2297_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(lean_object* v_cfg_2300_){
_start:
{
lean_object* v_lintDriverArgs_2301_; 
v_lintDriverArgs_2301_ = lean_ctor_get(v_cfg_2300_, 16);
lean_inc_ref(v_lintDriverArgs_2301_);
return v_lintDriverArgs_2301_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0___boxed(lean_object* v_cfg_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__0(v_cfg_2302_);
lean_dec_ref(v_cfg_2302_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__1(lean_object* v_val_2304_, lean_object* v_cfg_2305_){
_start:
{
lean_object* v_toWorkspaceConfig_2306_; lean_object* v_toLeanConfig_2307_; uint8_t v_bootstrap_2308_; lean_object* v_extraDepTargets_2309_; uint8_t v_precompileModules_2310_; lean_object* v_moreGlobalServerArgs_2311_; lean_object* v_srcDir_2312_; lean_object* v_buildDir_2313_; lean_object* v_leanLibDir_2314_; lean_object* v_nativeLibDir_2315_; lean_object* v_binDir_2316_; lean_object* v_irDir_2317_; lean_object* v_releaseRepo_2318_; lean_object* v_buildArchive_2319_; uint8_t v_preferReleaseBuild_2320_; lean_object* v_downloadCacheService_x3f_2321_; lean_object* v_testDriver_2322_; lean_object* v_testDriverArgs_2323_; lean_object* v_lintDriver_2324_; lean_object* v_version_2325_; lean_object* v_versionTags_2326_; lean_object* v_description_2327_; lean_object* v_keywords_2328_; lean_object* v_homepage_2329_; lean_object* v_license_2330_; lean_object* v_licenseFiles_2331_; lean_object* v_readmeFile_2332_; uint8_t v_reservoir_2333_; lean_object* v_enableArtifactCache_x3f_2334_; lean_object* v_restoreAllArtifacts_x3f_2335_; uint8_t v_libPrefixOnWindows_2336_; uint8_t v_allowImportAll_2337_; lean_object* v_builtinLint_x3f_2338_; lean_object* v_checks_2339_; uint8_t v_fixedToolchain_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_toWorkspaceConfig_2306_ = lean_ctor_get(v_cfg_2305_, 0);
v_toLeanConfig_2307_ = lean_ctor_get(v_cfg_2305_, 1);
v_bootstrap_2308_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29);
v_extraDepTargets_2309_ = lean_ctor_get(v_cfg_2305_, 2);
v_precompileModules_2310_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2311_ = lean_ctor_get(v_cfg_2305_, 3);
v_srcDir_2312_ = lean_ctor_get(v_cfg_2305_, 4);
v_buildDir_2313_ = lean_ctor_get(v_cfg_2305_, 5);
v_leanLibDir_2314_ = lean_ctor_get(v_cfg_2305_, 6);
v_nativeLibDir_2315_ = lean_ctor_get(v_cfg_2305_, 7);
v_binDir_2316_ = lean_ctor_get(v_cfg_2305_, 8);
v_irDir_2317_ = lean_ctor_get(v_cfg_2305_, 9);
v_releaseRepo_2318_ = lean_ctor_get(v_cfg_2305_, 10);
v_buildArchive_2319_ = lean_ctor_get(v_cfg_2305_, 11);
v_preferReleaseBuild_2320_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2321_ = lean_ctor_get(v_cfg_2305_, 12);
v_testDriver_2322_ = lean_ctor_get(v_cfg_2305_, 13);
v_testDriverArgs_2323_ = lean_ctor_get(v_cfg_2305_, 14);
v_lintDriver_2324_ = lean_ctor_get(v_cfg_2305_, 15);
v_version_2325_ = lean_ctor_get(v_cfg_2305_, 17);
v_versionTags_2326_ = lean_ctor_get(v_cfg_2305_, 18);
v_description_2327_ = lean_ctor_get(v_cfg_2305_, 19);
v_keywords_2328_ = lean_ctor_get(v_cfg_2305_, 20);
v_homepage_2329_ = lean_ctor_get(v_cfg_2305_, 21);
v_license_2330_ = lean_ctor_get(v_cfg_2305_, 22);
v_licenseFiles_2331_ = lean_ctor_get(v_cfg_2305_, 23);
v_readmeFile_2332_ = lean_ctor_get(v_cfg_2305_, 24);
v_reservoir_2333_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2334_ = lean_ctor_get(v_cfg_2305_, 25);
v_restoreAllArtifacts_x3f_2335_ = lean_ctor_get(v_cfg_2305_, 26);
v_libPrefixOnWindows_2336_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29 + 4);
v_allowImportAll_2337_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2338_ = lean_ctor_get(v_cfg_2305_, 27);
v_checks_2339_ = lean_ctor_get(v_cfg_2305_, 28);
v_fixedToolchain_2340_ = lean_ctor_get_uint8(v_cfg_2305_, sizeof(void*)*29 + 6);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_cfg_2305_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v_cfg_2305_, 16);
lean_dec(v_unused_2348_);
v___x_2342_ = v_cfg_2305_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_checks_2339_);
lean_inc(v_builtinLint_x3f_2338_);
lean_inc(v_restoreAllArtifacts_x3f_2335_);
lean_inc(v_enableArtifactCache_x3f_2334_);
lean_inc(v_readmeFile_2332_);
lean_inc(v_licenseFiles_2331_);
lean_inc(v_license_2330_);
lean_inc(v_homepage_2329_);
lean_inc(v_keywords_2328_);
lean_inc(v_description_2327_);
lean_inc(v_versionTags_2326_);
lean_inc(v_version_2325_);
lean_inc(v_lintDriver_2324_);
lean_inc(v_testDriverArgs_2323_);
lean_inc(v_testDriver_2322_);
lean_inc(v_downloadCacheService_x3f_2321_);
lean_inc(v_buildArchive_2319_);
lean_inc(v_releaseRepo_2318_);
lean_inc(v_irDir_2317_);
lean_inc(v_binDir_2316_);
lean_inc(v_nativeLibDir_2315_);
lean_inc(v_leanLibDir_2314_);
lean_inc(v_buildDir_2313_);
lean_inc(v_srcDir_2312_);
lean_inc(v_moreGlobalServerArgs_2311_);
lean_inc(v_extraDepTargets_2309_);
lean_inc(v_toLeanConfig_2307_);
lean_inc(v_toWorkspaceConfig_2306_);
lean_dec(v_cfg_2305_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 16, v_val_2304_);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_toWorkspaceConfig_2306_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_toLeanConfig_2307_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_extraDepTargets_2309_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_moreGlobalServerArgs_2311_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_srcDir_2312_);
lean_ctor_set(v_reuseFailAlloc_2346_, 5, v_buildDir_2313_);
lean_ctor_set(v_reuseFailAlloc_2346_, 6, v_leanLibDir_2314_);
lean_ctor_set(v_reuseFailAlloc_2346_, 7, v_nativeLibDir_2315_);
lean_ctor_set(v_reuseFailAlloc_2346_, 8, v_binDir_2316_);
lean_ctor_set(v_reuseFailAlloc_2346_, 9, v_irDir_2317_);
lean_ctor_set(v_reuseFailAlloc_2346_, 10, v_releaseRepo_2318_);
lean_ctor_set(v_reuseFailAlloc_2346_, 11, v_buildArchive_2319_);
lean_ctor_set(v_reuseFailAlloc_2346_, 12, v_downloadCacheService_x3f_2321_);
lean_ctor_set(v_reuseFailAlloc_2346_, 13, v_testDriver_2322_);
lean_ctor_set(v_reuseFailAlloc_2346_, 14, v_testDriverArgs_2323_);
lean_ctor_set(v_reuseFailAlloc_2346_, 15, v_lintDriver_2324_);
lean_ctor_set(v_reuseFailAlloc_2346_, 16, v_val_2304_);
lean_ctor_set(v_reuseFailAlloc_2346_, 17, v_version_2325_);
lean_ctor_set(v_reuseFailAlloc_2346_, 18, v_versionTags_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 19, v_description_2327_);
lean_ctor_set(v_reuseFailAlloc_2346_, 20, v_keywords_2328_);
lean_ctor_set(v_reuseFailAlloc_2346_, 21, v_homepage_2329_);
lean_ctor_set(v_reuseFailAlloc_2346_, 22, v_license_2330_);
lean_ctor_set(v_reuseFailAlloc_2346_, 23, v_licenseFiles_2331_);
lean_ctor_set(v_reuseFailAlloc_2346_, 24, v_readmeFile_2332_);
lean_ctor_set(v_reuseFailAlloc_2346_, 25, v_enableArtifactCache_x3f_2334_);
lean_ctor_set(v_reuseFailAlloc_2346_, 26, v_restoreAllArtifacts_x3f_2335_);
lean_ctor_set(v_reuseFailAlloc_2346_, 27, v_builtinLint_x3f_2338_);
lean_ctor_set(v_reuseFailAlloc_2346_, 28, v_checks_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29, v_bootstrap_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29 + 1, v_precompileModules_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29 + 3, v_reservoir_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29 + 5, v_allowImportAll_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2346_, sizeof(void*)*29 + 6, v_fixedToolchain_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___lam__2(lean_object* v_f_2349_, lean_object* v_cfg_2350_){
_start:
{
lean_object* v_toWorkspaceConfig_2351_; lean_object* v_toLeanConfig_2352_; uint8_t v_bootstrap_2353_; lean_object* v_extraDepTargets_2354_; uint8_t v_precompileModules_2355_; lean_object* v_moreGlobalServerArgs_2356_; lean_object* v_srcDir_2357_; lean_object* v_buildDir_2358_; lean_object* v_leanLibDir_2359_; lean_object* v_nativeLibDir_2360_; lean_object* v_binDir_2361_; lean_object* v_irDir_2362_; lean_object* v_releaseRepo_2363_; lean_object* v_buildArchive_2364_; uint8_t v_preferReleaseBuild_2365_; lean_object* v_downloadCacheService_x3f_2366_; lean_object* v_testDriver_2367_; lean_object* v_testDriverArgs_2368_; lean_object* v_lintDriver_2369_; lean_object* v_lintDriverArgs_2370_; lean_object* v_version_2371_; lean_object* v_versionTags_2372_; lean_object* v_description_2373_; lean_object* v_keywords_2374_; lean_object* v_homepage_2375_; lean_object* v_license_2376_; lean_object* v_licenseFiles_2377_; lean_object* v_readmeFile_2378_; uint8_t v_reservoir_2379_; lean_object* v_enableArtifactCache_x3f_2380_; lean_object* v_restoreAllArtifacts_x3f_2381_; uint8_t v_libPrefixOnWindows_2382_; uint8_t v_allowImportAll_2383_; lean_object* v_builtinLint_x3f_2384_; lean_object* v_checks_2385_; uint8_t v_fixedToolchain_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2394_; 
v_toWorkspaceConfig_2351_ = lean_ctor_get(v_cfg_2350_, 0);
v_toLeanConfig_2352_ = lean_ctor_get(v_cfg_2350_, 1);
v_bootstrap_2353_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29);
v_extraDepTargets_2354_ = lean_ctor_get(v_cfg_2350_, 2);
v_precompileModules_2355_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2356_ = lean_ctor_get(v_cfg_2350_, 3);
v_srcDir_2357_ = lean_ctor_get(v_cfg_2350_, 4);
v_buildDir_2358_ = lean_ctor_get(v_cfg_2350_, 5);
v_leanLibDir_2359_ = lean_ctor_get(v_cfg_2350_, 6);
v_nativeLibDir_2360_ = lean_ctor_get(v_cfg_2350_, 7);
v_binDir_2361_ = lean_ctor_get(v_cfg_2350_, 8);
v_irDir_2362_ = lean_ctor_get(v_cfg_2350_, 9);
v_releaseRepo_2363_ = lean_ctor_get(v_cfg_2350_, 10);
v_buildArchive_2364_ = lean_ctor_get(v_cfg_2350_, 11);
v_preferReleaseBuild_2365_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2366_ = lean_ctor_get(v_cfg_2350_, 12);
v_testDriver_2367_ = lean_ctor_get(v_cfg_2350_, 13);
v_testDriverArgs_2368_ = lean_ctor_get(v_cfg_2350_, 14);
v_lintDriver_2369_ = lean_ctor_get(v_cfg_2350_, 15);
v_lintDriverArgs_2370_ = lean_ctor_get(v_cfg_2350_, 16);
v_version_2371_ = lean_ctor_get(v_cfg_2350_, 17);
v_versionTags_2372_ = lean_ctor_get(v_cfg_2350_, 18);
v_description_2373_ = lean_ctor_get(v_cfg_2350_, 19);
v_keywords_2374_ = lean_ctor_get(v_cfg_2350_, 20);
v_homepage_2375_ = lean_ctor_get(v_cfg_2350_, 21);
v_license_2376_ = lean_ctor_get(v_cfg_2350_, 22);
v_licenseFiles_2377_ = lean_ctor_get(v_cfg_2350_, 23);
v_readmeFile_2378_ = lean_ctor_get(v_cfg_2350_, 24);
v_reservoir_2379_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2380_ = lean_ctor_get(v_cfg_2350_, 25);
v_restoreAllArtifacts_x3f_2381_ = lean_ctor_get(v_cfg_2350_, 26);
v_libPrefixOnWindows_2382_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29 + 4);
v_allowImportAll_2383_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2384_ = lean_ctor_get(v_cfg_2350_, 27);
v_checks_2385_ = lean_ctor_get(v_cfg_2350_, 28);
v_fixedToolchain_2386_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*29 + 6);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_cfg_2350_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2388_ = v_cfg_2350_;
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_checks_2385_);
lean_inc(v_builtinLint_x3f_2384_);
lean_inc(v_restoreAllArtifacts_x3f_2381_);
lean_inc(v_enableArtifactCache_x3f_2380_);
lean_inc(v_readmeFile_2378_);
lean_inc(v_licenseFiles_2377_);
lean_inc(v_license_2376_);
lean_inc(v_homepage_2375_);
lean_inc(v_keywords_2374_);
lean_inc(v_description_2373_);
lean_inc(v_versionTags_2372_);
lean_inc(v_version_2371_);
lean_inc(v_lintDriverArgs_2370_);
lean_inc(v_lintDriver_2369_);
lean_inc(v_testDriverArgs_2368_);
lean_inc(v_testDriver_2367_);
lean_inc(v_downloadCacheService_x3f_2366_);
lean_inc(v_buildArchive_2364_);
lean_inc(v_releaseRepo_2363_);
lean_inc(v_irDir_2362_);
lean_inc(v_binDir_2361_);
lean_inc(v_nativeLibDir_2360_);
lean_inc(v_leanLibDir_2359_);
lean_inc(v_buildDir_2358_);
lean_inc(v_srcDir_2357_);
lean_inc(v_moreGlobalServerArgs_2356_);
lean_inc(v_extraDepTargets_2354_);
lean_inc(v_toLeanConfig_2352_);
lean_inc(v_toWorkspaceConfig_2351_);
lean_dec(v_cfg_2350_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = lean_apply_1(v_f_2349_, v_lintDriverArgs_2370_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 16, v___x_2390_);
v___x_2392_ = v___x_2388_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_toWorkspaceConfig_2351_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_toLeanConfig_2352_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_extraDepTargets_2354_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_moreGlobalServerArgs_2356_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v_srcDir_2357_);
lean_ctor_set(v_reuseFailAlloc_2393_, 5, v_buildDir_2358_);
lean_ctor_set(v_reuseFailAlloc_2393_, 6, v_leanLibDir_2359_);
lean_ctor_set(v_reuseFailAlloc_2393_, 7, v_nativeLibDir_2360_);
lean_ctor_set(v_reuseFailAlloc_2393_, 8, v_binDir_2361_);
lean_ctor_set(v_reuseFailAlloc_2393_, 9, v_irDir_2362_);
lean_ctor_set(v_reuseFailAlloc_2393_, 10, v_releaseRepo_2363_);
lean_ctor_set(v_reuseFailAlloc_2393_, 11, v_buildArchive_2364_);
lean_ctor_set(v_reuseFailAlloc_2393_, 12, v_downloadCacheService_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2393_, 13, v_testDriver_2367_);
lean_ctor_set(v_reuseFailAlloc_2393_, 14, v_testDriverArgs_2368_);
lean_ctor_set(v_reuseFailAlloc_2393_, 15, v_lintDriver_2369_);
lean_ctor_set(v_reuseFailAlloc_2393_, 16, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2393_, 17, v_version_2371_);
lean_ctor_set(v_reuseFailAlloc_2393_, 18, v_versionTags_2372_);
lean_ctor_set(v_reuseFailAlloc_2393_, 19, v_description_2373_);
lean_ctor_set(v_reuseFailAlloc_2393_, 20, v_keywords_2374_);
lean_ctor_set(v_reuseFailAlloc_2393_, 21, v_homepage_2375_);
lean_ctor_set(v_reuseFailAlloc_2393_, 22, v_license_2376_);
lean_ctor_set(v_reuseFailAlloc_2393_, 23, v_licenseFiles_2377_);
lean_ctor_set(v_reuseFailAlloc_2393_, 24, v_readmeFile_2378_);
lean_ctor_set(v_reuseFailAlloc_2393_, 25, v_enableArtifactCache_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2393_, 26, v_restoreAllArtifacts_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2393_, 27, v_builtinLint_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2393_, 28, v_checks_2385_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29, v_bootstrap_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29 + 1, v_precompileModules_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2365_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29 + 3, v_reservoir_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29 + 5, v_allowImportAll_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*29 + 6, v_fixedToolchain_2386_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg(){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = ((lean_object*)(l_Lake_PackageConfig_lintDriverArgs___proj___redArg___closed__3));
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___redArg___boxed(lean_object* v___dummy_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
return v_res_2406_;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0(void){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lake_PackageConfig_lintDriverArgs___proj___redArg();
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj(lean_object* v_p_2408_, lean_object* v_n_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___proj___boxed(lean_object* v_p_2411_, lean_object* v_n_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lake_PackageConfig_lintDriverArgs___proj(v_p_2411_, v_n_2412_);
lean_dec(v_n_2412_);
lean_dec(v_p_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg(){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg___boxed(lean_object* v___dummy_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField___redArg();
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField(lean_object* v_p_2418_, lean_object* v_n_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_obj_once(&l_Lake_PackageConfig_lintDriverArgs___proj___closed__0, &l_Lake_PackageConfig_lintDriverArgs___proj___closed__0_once, _init_l_Lake_PackageConfig_lintDriverArgs___proj___closed__0);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs_instConfigField___boxed(lean_object* v_p_2421_, lean_object* v_n_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lake_PackageConfig_lintDriverArgs_instConfigField(v_p_2421_, v_n_2422_);
lean_dec(v_n_2422_);
lean_dec(v_p_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0(lean_object* v_cfg_2424_){
_start:
{
lean_object* v_version_2425_; 
v_version_2425_ = lean_ctor_get(v_cfg_2424_, 17);
lean_inc_ref(v_version_2425_);
return v_version_2425_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__0___boxed(lean_object* v_cfg_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lake_PackageConfig_version___proj___redArg___lam__0(v_cfg_2426_);
lean_dec_ref(v_cfg_2426_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__1(lean_object* v_val_2428_, lean_object* v_cfg_2429_){
_start:
{
lean_object* v_toWorkspaceConfig_2430_; lean_object* v_toLeanConfig_2431_; uint8_t v_bootstrap_2432_; lean_object* v_extraDepTargets_2433_; uint8_t v_precompileModules_2434_; lean_object* v_moreGlobalServerArgs_2435_; lean_object* v_srcDir_2436_; lean_object* v_buildDir_2437_; lean_object* v_leanLibDir_2438_; lean_object* v_nativeLibDir_2439_; lean_object* v_binDir_2440_; lean_object* v_irDir_2441_; lean_object* v_releaseRepo_2442_; lean_object* v_buildArchive_2443_; uint8_t v_preferReleaseBuild_2444_; lean_object* v_downloadCacheService_x3f_2445_; lean_object* v_testDriver_2446_; lean_object* v_testDriverArgs_2447_; lean_object* v_lintDriver_2448_; lean_object* v_lintDriverArgs_2449_; lean_object* v_versionTags_2450_; lean_object* v_description_2451_; lean_object* v_keywords_2452_; lean_object* v_homepage_2453_; lean_object* v_license_2454_; lean_object* v_licenseFiles_2455_; lean_object* v_readmeFile_2456_; uint8_t v_reservoir_2457_; lean_object* v_enableArtifactCache_x3f_2458_; lean_object* v_restoreAllArtifacts_x3f_2459_; uint8_t v_libPrefixOnWindows_2460_; uint8_t v_allowImportAll_2461_; lean_object* v_builtinLint_x3f_2462_; lean_object* v_checks_2463_; uint8_t v_fixedToolchain_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v_toWorkspaceConfig_2430_ = lean_ctor_get(v_cfg_2429_, 0);
v_toLeanConfig_2431_ = lean_ctor_get(v_cfg_2429_, 1);
v_bootstrap_2432_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29);
v_extraDepTargets_2433_ = lean_ctor_get(v_cfg_2429_, 2);
v_precompileModules_2434_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2435_ = lean_ctor_get(v_cfg_2429_, 3);
v_srcDir_2436_ = lean_ctor_get(v_cfg_2429_, 4);
v_buildDir_2437_ = lean_ctor_get(v_cfg_2429_, 5);
v_leanLibDir_2438_ = lean_ctor_get(v_cfg_2429_, 6);
v_nativeLibDir_2439_ = lean_ctor_get(v_cfg_2429_, 7);
v_binDir_2440_ = lean_ctor_get(v_cfg_2429_, 8);
v_irDir_2441_ = lean_ctor_get(v_cfg_2429_, 9);
v_releaseRepo_2442_ = lean_ctor_get(v_cfg_2429_, 10);
v_buildArchive_2443_ = lean_ctor_get(v_cfg_2429_, 11);
v_preferReleaseBuild_2444_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2445_ = lean_ctor_get(v_cfg_2429_, 12);
v_testDriver_2446_ = lean_ctor_get(v_cfg_2429_, 13);
v_testDriverArgs_2447_ = lean_ctor_get(v_cfg_2429_, 14);
v_lintDriver_2448_ = lean_ctor_get(v_cfg_2429_, 15);
v_lintDriverArgs_2449_ = lean_ctor_get(v_cfg_2429_, 16);
v_versionTags_2450_ = lean_ctor_get(v_cfg_2429_, 18);
v_description_2451_ = lean_ctor_get(v_cfg_2429_, 19);
v_keywords_2452_ = lean_ctor_get(v_cfg_2429_, 20);
v_homepage_2453_ = lean_ctor_get(v_cfg_2429_, 21);
v_license_2454_ = lean_ctor_get(v_cfg_2429_, 22);
v_licenseFiles_2455_ = lean_ctor_get(v_cfg_2429_, 23);
v_readmeFile_2456_ = lean_ctor_get(v_cfg_2429_, 24);
v_reservoir_2457_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2458_ = lean_ctor_get(v_cfg_2429_, 25);
v_restoreAllArtifacts_x3f_2459_ = lean_ctor_get(v_cfg_2429_, 26);
v_libPrefixOnWindows_2460_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29 + 4);
v_allowImportAll_2461_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2462_ = lean_ctor_get(v_cfg_2429_, 27);
v_checks_2463_ = lean_ctor_get(v_cfg_2429_, 28);
v_fixedToolchain_2464_ = lean_ctor_get_uint8(v_cfg_2429_, sizeof(void*)*29 + 6);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_cfg_2429_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v_cfg_2429_, 17);
lean_dec(v_unused_2472_);
v___x_2466_ = v_cfg_2429_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_checks_2463_);
lean_inc(v_builtinLint_x3f_2462_);
lean_inc(v_restoreAllArtifacts_x3f_2459_);
lean_inc(v_enableArtifactCache_x3f_2458_);
lean_inc(v_readmeFile_2456_);
lean_inc(v_licenseFiles_2455_);
lean_inc(v_license_2454_);
lean_inc(v_homepage_2453_);
lean_inc(v_keywords_2452_);
lean_inc(v_description_2451_);
lean_inc(v_versionTags_2450_);
lean_inc(v_lintDriverArgs_2449_);
lean_inc(v_lintDriver_2448_);
lean_inc(v_testDriverArgs_2447_);
lean_inc(v_testDriver_2446_);
lean_inc(v_downloadCacheService_x3f_2445_);
lean_inc(v_buildArchive_2443_);
lean_inc(v_releaseRepo_2442_);
lean_inc(v_irDir_2441_);
lean_inc(v_binDir_2440_);
lean_inc(v_nativeLibDir_2439_);
lean_inc(v_leanLibDir_2438_);
lean_inc(v_buildDir_2437_);
lean_inc(v_srcDir_2436_);
lean_inc(v_moreGlobalServerArgs_2435_);
lean_inc(v_extraDepTargets_2433_);
lean_inc(v_toLeanConfig_2431_);
lean_inc(v_toWorkspaceConfig_2430_);
lean_dec(v_cfg_2429_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 17, v_val_2428_);
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_toWorkspaceConfig_2430_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_toLeanConfig_2431_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_extraDepTargets_2433_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_moreGlobalServerArgs_2435_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_srcDir_2436_);
lean_ctor_set(v_reuseFailAlloc_2470_, 5, v_buildDir_2437_);
lean_ctor_set(v_reuseFailAlloc_2470_, 6, v_leanLibDir_2438_);
lean_ctor_set(v_reuseFailAlloc_2470_, 7, v_nativeLibDir_2439_);
lean_ctor_set(v_reuseFailAlloc_2470_, 8, v_binDir_2440_);
lean_ctor_set(v_reuseFailAlloc_2470_, 9, v_irDir_2441_);
lean_ctor_set(v_reuseFailAlloc_2470_, 10, v_releaseRepo_2442_);
lean_ctor_set(v_reuseFailAlloc_2470_, 11, v_buildArchive_2443_);
lean_ctor_set(v_reuseFailAlloc_2470_, 12, v_downloadCacheService_x3f_2445_);
lean_ctor_set(v_reuseFailAlloc_2470_, 13, v_testDriver_2446_);
lean_ctor_set(v_reuseFailAlloc_2470_, 14, v_testDriverArgs_2447_);
lean_ctor_set(v_reuseFailAlloc_2470_, 15, v_lintDriver_2448_);
lean_ctor_set(v_reuseFailAlloc_2470_, 16, v_lintDriverArgs_2449_);
lean_ctor_set(v_reuseFailAlloc_2470_, 17, v_val_2428_);
lean_ctor_set(v_reuseFailAlloc_2470_, 18, v_versionTags_2450_);
lean_ctor_set(v_reuseFailAlloc_2470_, 19, v_description_2451_);
lean_ctor_set(v_reuseFailAlloc_2470_, 20, v_keywords_2452_);
lean_ctor_set(v_reuseFailAlloc_2470_, 21, v_homepage_2453_);
lean_ctor_set(v_reuseFailAlloc_2470_, 22, v_license_2454_);
lean_ctor_set(v_reuseFailAlloc_2470_, 23, v_licenseFiles_2455_);
lean_ctor_set(v_reuseFailAlloc_2470_, 24, v_readmeFile_2456_);
lean_ctor_set(v_reuseFailAlloc_2470_, 25, v_enableArtifactCache_x3f_2458_);
lean_ctor_set(v_reuseFailAlloc_2470_, 26, v_restoreAllArtifacts_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2470_, 27, v_builtinLint_x3f_2462_);
lean_ctor_set(v_reuseFailAlloc_2470_, 28, v_checks_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29, v_bootstrap_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29 + 1, v_precompileModules_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29 + 3, v_reservoir_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29 + 5, v_allowImportAll_2461_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*29 + 6, v_fixedToolchain_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__2(lean_object* v_f_2473_, lean_object* v_cfg_2474_){
_start:
{
lean_object* v_toWorkspaceConfig_2475_; lean_object* v_toLeanConfig_2476_; uint8_t v_bootstrap_2477_; lean_object* v_extraDepTargets_2478_; uint8_t v_precompileModules_2479_; lean_object* v_moreGlobalServerArgs_2480_; lean_object* v_srcDir_2481_; lean_object* v_buildDir_2482_; lean_object* v_leanLibDir_2483_; lean_object* v_nativeLibDir_2484_; lean_object* v_binDir_2485_; lean_object* v_irDir_2486_; lean_object* v_releaseRepo_2487_; lean_object* v_buildArchive_2488_; uint8_t v_preferReleaseBuild_2489_; lean_object* v_downloadCacheService_x3f_2490_; lean_object* v_testDriver_2491_; lean_object* v_testDriverArgs_2492_; lean_object* v_lintDriver_2493_; lean_object* v_lintDriverArgs_2494_; lean_object* v_version_2495_; lean_object* v_versionTags_2496_; lean_object* v_description_2497_; lean_object* v_keywords_2498_; lean_object* v_homepage_2499_; lean_object* v_license_2500_; lean_object* v_licenseFiles_2501_; lean_object* v_readmeFile_2502_; uint8_t v_reservoir_2503_; lean_object* v_enableArtifactCache_x3f_2504_; lean_object* v_restoreAllArtifacts_x3f_2505_; uint8_t v_libPrefixOnWindows_2506_; uint8_t v_allowImportAll_2507_; lean_object* v_builtinLint_x3f_2508_; lean_object* v_checks_2509_; uint8_t v_fixedToolchain_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2518_; 
v_toWorkspaceConfig_2475_ = lean_ctor_get(v_cfg_2474_, 0);
v_toLeanConfig_2476_ = lean_ctor_get(v_cfg_2474_, 1);
v_bootstrap_2477_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29);
v_extraDepTargets_2478_ = lean_ctor_get(v_cfg_2474_, 2);
v_precompileModules_2479_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2480_ = lean_ctor_get(v_cfg_2474_, 3);
v_srcDir_2481_ = lean_ctor_get(v_cfg_2474_, 4);
v_buildDir_2482_ = lean_ctor_get(v_cfg_2474_, 5);
v_leanLibDir_2483_ = lean_ctor_get(v_cfg_2474_, 6);
v_nativeLibDir_2484_ = lean_ctor_get(v_cfg_2474_, 7);
v_binDir_2485_ = lean_ctor_get(v_cfg_2474_, 8);
v_irDir_2486_ = lean_ctor_get(v_cfg_2474_, 9);
v_releaseRepo_2487_ = lean_ctor_get(v_cfg_2474_, 10);
v_buildArchive_2488_ = lean_ctor_get(v_cfg_2474_, 11);
v_preferReleaseBuild_2489_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2490_ = lean_ctor_get(v_cfg_2474_, 12);
v_testDriver_2491_ = lean_ctor_get(v_cfg_2474_, 13);
v_testDriverArgs_2492_ = lean_ctor_get(v_cfg_2474_, 14);
v_lintDriver_2493_ = lean_ctor_get(v_cfg_2474_, 15);
v_lintDriverArgs_2494_ = lean_ctor_get(v_cfg_2474_, 16);
v_version_2495_ = lean_ctor_get(v_cfg_2474_, 17);
v_versionTags_2496_ = lean_ctor_get(v_cfg_2474_, 18);
v_description_2497_ = lean_ctor_get(v_cfg_2474_, 19);
v_keywords_2498_ = lean_ctor_get(v_cfg_2474_, 20);
v_homepage_2499_ = lean_ctor_get(v_cfg_2474_, 21);
v_license_2500_ = lean_ctor_get(v_cfg_2474_, 22);
v_licenseFiles_2501_ = lean_ctor_get(v_cfg_2474_, 23);
v_readmeFile_2502_ = lean_ctor_get(v_cfg_2474_, 24);
v_reservoir_2503_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2504_ = lean_ctor_get(v_cfg_2474_, 25);
v_restoreAllArtifacts_x3f_2505_ = lean_ctor_get(v_cfg_2474_, 26);
v_libPrefixOnWindows_2506_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29 + 4);
v_allowImportAll_2507_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2508_ = lean_ctor_get(v_cfg_2474_, 27);
v_checks_2509_ = lean_ctor_get(v_cfg_2474_, 28);
v_fixedToolchain_2510_ = lean_ctor_get_uint8(v_cfg_2474_, sizeof(void*)*29 + 6);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_cfg_2474_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2512_ = v_cfg_2474_;
v_isShared_2513_ = v_isSharedCheck_2518_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_checks_2509_);
lean_inc(v_builtinLint_x3f_2508_);
lean_inc(v_restoreAllArtifacts_x3f_2505_);
lean_inc(v_enableArtifactCache_x3f_2504_);
lean_inc(v_readmeFile_2502_);
lean_inc(v_licenseFiles_2501_);
lean_inc(v_license_2500_);
lean_inc(v_homepage_2499_);
lean_inc(v_keywords_2498_);
lean_inc(v_description_2497_);
lean_inc(v_versionTags_2496_);
lean_inc(v_version_2495_);
lean_inc(v_lintDriverArgs_2494_);
lean_inc(v_lintDriver_2493_);
lean_inc(v_testDriverArgs_2492_);
lean_inc(v_testDriver_2491_);
lean_inc(v_downloadCacheService_x3f_2490_);
lean_inc(v_buildArchive_2488_);
lean_inc(v_releaseRepo_2487_);
lean_inc(v_irDir_2486_);
lean_inc(v_binDir_2485_);
lean_inc(v_nativeLibDir_2484_);
lean_inc(v_leanLibDir_2483_);
lean_inc(v_buildDir_2482_);
lean_inc(v_srcDir_2481_);
lean_inc(v_moreGlobalServerArgs_2480_);
lean_inc(v_extraDepTargets_2478_);
lean_inc(v_toLeanConfig_2476_);
lean_inc(v_toWorkspaceConfig_2475_);
lean_dec(v_cfg_2474_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2518_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2514_ = lean_apply_1(v_f_2473_, v_version_2495_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 17, v___x_2514_);
v___x_2516_ = v___x_2512_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_toWorkspaceConfig_2475_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_toLeanConfig_2476_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_extraDepTargets_2478_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_moreGlobalServerArgs_2480_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_srcDir_2481_);
lean_ctor_set(v_reuseFailAlloc_2517_, 5, v_buildDir_2482_);
lean_ctor_set(v_reuseFailAlloc_2517_, 6, v_leanLibDir_2483_);
lean_ctor_set(v_reuseFailAlloc_2517_, 7, v_nativeLibDir_2484_);
lean_ctor_set(v_reuseFailAlloc_2517_, 8, v_binDir_2485_);
lean_ctor_set(v_reuseFailAlloc_2517_, 9, v_irDir_2486_);
lean_ctor_set(v_reuseFailAlloc_2517_, 10, v_releaseRepo_2487_);
lean_ctor_set(v_reuseFailAlloc_2517_, 11, v_buildArchive_2488_);
lean_ctor_set(v_reuseFailAlloc_2517_, 12, v_downloadCacheService_x3f_2490_);
lean_ctor_set(v_reuseFailAlloc_2517_, 13, v_testDriver_2491_);
lean_ctor_set(v_reuseFailAlloc_2517_, 14, v_testDriverArgs_2492_);
lean_ctor_set(v_reuseFailAlloc_2517_, 15, v_lintDriver_2493_);
lean_ctor_set(v_reuseFailAlloc_2517_, 16, v_lintDriverArgs_2494_);
lean_ctor_set(v_reuseFailAlloc_2517_, 17, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2517_, 18, v_versionTags_2496_);
lean_ctor_set(v_reuseFailAlloc_2517_, 19, v_description_2497_);
lean_ctor_set(v_reuseFailAlloc_2517_, 20, v_keywords_2498_);
lean_ctor_set(v_reuseFailAlloc_2517_, 21, v_homepage_2499_);
lean_ctor_set(v_reuseFailAlloc_2517_, 22, v_license_2500_);
lean_ctor_set(v_reuseFailAlloc_2517_, 23, v_licenseFiles_2501_);
lean_ctor_set(v_reuseFailAlloc_2517_, 24, v_readmeFile_2502_);
lean_ctor_set(v_reuseFailAlloc_2517_, 25, v_enableArtifactCache_x3f_2504_);
lean_ctor_set(v_reuseFailAlloc_2517_, 26, v_restoreAllArtifacts_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2517_, 27, v_builtinLint_x3f_2508_);
lean_ctor_set(v_reuseFailAlloc_2517_, 28, v_checks_2509_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29, v_bootstrap_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29 + 1, v_precompileModules_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2489_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29 + 3, v_reservoir_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29 + 5, v_allowImportAll_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*29 + 6, v_fixedToolchain_2510_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3(lean_object* v_x_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___lam__3___boxed(lean_object* v_x_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lake_PackageConfig_version___proj___redArg___lam__3(v_x_2521_);
lean_dec_ref(v_x_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg(){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = ((lean_object*)(l_Lake_PackageConfig_version___proj___redArg___closed__4));
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___redArg___boxed(lean_object* v___dummy_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lake_PackageConfig_version___proj___redArg();
return v_res_2535_;
}
}
static lean_object* _init_l_Lake_PackageConfig_version___proj___closed__0(void){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lake_PackageConfig_version___proj___redArg();
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj(lean_object* v_p_2537_, lean_object* v_n_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version___proj___boxed(lean_object* v_p_2540_, lean_object* v_n_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lake_PackageConfig_version___proj(v_p_2540_, v_n_2541_);
lean_dec(v_n_2541_);
lean_dec(v_p_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg(){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___redArg___boxed(lean_object* v___dummy_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lake_PackageConfig_version_instConfigField___redArg();
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField(lean_object* v_p_2547_, lean_object* v_n_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_obj_once(&l_Lake_PackageConfig_version___proj___closed__0, &l_Lake_PackageConfig_version___proj___closed__0_once, _init_l_Lake_PackageConfig_version___proj___closed__0);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_version_instConfigField___boxed(lean_object* v_p_2550_, lean_object* v_n_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lake_PackageConfig_version_instConfigField(v_p_2550_, v_n_2551_);
lean_dec(v_n_2551_);
lean_dec(v_p_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(lean_object* v_cfg_2553_){
_start:
{
lean_object* v_versionTags_2554_; 
v_versionTags_2554_ = lean_ctor_get(v_cfg_2553_, 18);
lean_inc_ref(v_versionTags_2554_);
return v_versionTags_2554_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__0___boxed(lean_object* v_cfg_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lake_PackageConfig_versionTags___proj___redArg___lam__0(v_cfg_2555_);
lean_dec_ref(v_cfg_2555_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__1(lean_object* v_val_2557_, lean_object* v_cfg_2558_){
_start:
{
lean_object* v_toWorkspaceConfig_2559_; lean_object* v_toLeanConfig_2560_; uint8_t v_bootstrap_2561_; lean_object* v_extraDepTargets_2562_; uint8_t v_precompileModules_2563_; lean_object* v_moreGlobalServerArgs_2564_; lean_object* v_srcDir_2565_; lean_object* v_buildDir_2566_; lean_object* v_leanLibDir_2567_; lean_object* v_nativeLibDir_2568_; lean_object* v_binDir_2569_; lean_object* v_irDir_2570_; lean_object* v_releaseRepo_2571_; lean_object* v_buildArchive_2572_; uint8_t v_preferReleaseBuild_2573_; lean_object* v_downloadCacheService_x3f_2574_; lean_object* v_testDriver_2575_; lean_object* v_testDriverArgs_2576_; lean_object* v_lintDriver_2577_; lean_object* v_lintDriverArgs_2578_; lean_object* v_version_2579_; lean_object* v_description_2580_; lean_object* v_keywords_2581_; lean_object* v_homepage_2582_; lean_object* v_license_2583_; lean_object* v_licenseFiles_2584_; lean_object* v_readmeFile_2585_; uint8_t v_reservoir_2586_; lean_object* v_enableArtifactCache_x3f_2587_; lean_object* v_restoreAllArtifacts_x3f_2588_; uint8_t v_libPrefixOnWindows_2589_; uint8_t v_allowImportAll_2590_; lean_object* v_builtinLint_x3f_2591_; lean_object* v_checks_2592_; uint8_t v_fixedToolchain_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
v_toWorkspaceConfig_2559_ = lean_ctor_get(v_cfg_2558_, 0);
v_toLeanConfig_2560_ = lean_ctor_get(v_cfg_2558_, 1);
v_bootstrap_2561_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29);
v_extraDepTargets_2562_ = lean_ctor_get(v_cfg_2558_, 2);
v_precompileModules_2563_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2564_ = lean_ctor_get(v_cfg_2558_, 3);
v_srcDir_2565_ = lean_ctor_get(v_cfg_2558_, 4);
v_buildDir_2566_ = lean_ctor_get(v_cfg_2558_, 5);
v_leanLibDir_2567_ = lean_ctor_get(v_cfg_2558_, 6);
v_nativeLibDir_2568_ = lean_ctor_get(v_cfg_2558_, 7);
v_binDir_2569_ = lean_ctor_get(v_cfg_2558_, 8);
v_irDir_2570_ = lean_ctor_get(v_cfg_2558_, 9);
v_releaseRepo_2571_ = lean_ctor_get(v_cfg_2558_, 10);
v_buildArchive_2572_ = lean_ctor_get(v_cfg_2558_, 11);
v_preferReleaseBuild_2573_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2574_ = lean_ctor_get(v_cfg_2558_, 12);
v_testDriver_2575_ = lean_ctor_get(v_cfg_2558_, 13);
v_testDriverArgs_2576_ = lean_ctor_get(v_cfg_2558_, 14);
v_lintDriver_2577_ = lean_ctor_get(v_cfg_2558_, 15);
v_lintDriverArgs_2578_ = lean_ctor_get(v_cfg_2558_, 16);
v_version_2579_ = lean_ctor_get(v_cfg_2558_, 17);
v_description_2580_ = lean_ctor_get(v_cfg_2558_, 19);
v_keywords_2581_ = lean_ctor_get(v_cfg_2558_, 20);
v_homepage_2582_ = lean_ctor_get(v_cfg_2558_, 21);
v_license_2583_ = lean_ctor_get(v_cfg_2558_, 22);
v_licenseFiles_2584_ = lean_ctor_get(v_cfg_2558_, 23);
v_readmeFile_2585_ = lean_ctor_get(v_cfg_2558_, 24);
v_reservoir_2586_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2587_ = lean_ctor_get(v_cfg_2558_, 25);
v_restoreAllArtifacts_x3f_2588_ = lean_ctor_get(v_cfg_2558_, 26);
v_libPrefixOnWindows_2589_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29 + 4);
v_allowImportAll_2590_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2591_ = lean_ctor_get(v_cfg_2558_, 27);
v_checks_2592_ = lean_ctor_get(v_cfg_2558_, 28);
v_fixedToolchain_2593_ = lean_ctor_get_uint8(v_cfg_2558_, sizeof(void*)*29 + 6);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_cfg_2558_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v_cfg_2558_, 18);
lean_dec(v_unused_2601_);
v___x_2595_ = v_cfg_2558_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_checks_2592_);
lean_inc(v_builtinLint_x3f_2591_);
lean_inc(v_restoreAllArtifacts_x3f_2588_);
lean_inc(v_enableArtifactCache_x3f_2587_);
lean_inc(v_readmeFile_2585_);
lean_inc(v_licenseFiles_2584_);
lean_inc(v_license_2583_);
lean_inc(v_homepage_2582_);
lean_inc(v_keywords_2581_);
lean_inc(v_description_2580_);
lean_inc(v_version_2579_);
lean_inc(v_lintDriverArgs_2578_);
lean_inc(v_lintDriver_2577_);
lean_inc(v_testDriverArgs_2576_);
lean_inc(v_testDriver_2575_);
lean_inc(v_downloadCacheService_x3f_2574_);
lean_inc(v_buildArchive_2572_);
lean_inc(v_releaseRepo_2571_);
lean_inc(v_irDir_2570_);
lean_inc(v_binDir_2569_);
lean_inc(v_nativeLibDir_2568_);
lean_inc(v_leanLibDir_2567_);
lean_inc(v_buildDir_2566_);
lean_inc(v_srcDir_2565_);
lean_inc(v_moreGlobalServerArgs_2564_);
lean_inc(v_extraDepTargets_2562_);
lean_inc(v_toLeanConfig_2560_);
lean_inc(v_toWorkspaceConfig_2559_);
lean_dec(v_cfg_2558_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 18, v_val_2557_);
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_toWorkspaceConfig_2559_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_toLeanConfig_2560_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_extraDepTargets_2562_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_moreGlobalServerArgs_2564_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_srcDir_2565_);
lean_ctor_set(v_reuseFailAlloc_2599_, 5, v_buildDir_2566_);
lean_ctor_set(v_reuseFailAlloc_2599_, 6, v_leanLibDir_2567_);
lean_ctor_set(v_reuseFailAlloc_2599_, 7, v_nativeLibDir_2568_);
lean_ctor_set(v_reuseFailAlloc_2599_, 8, v_binDir_2569_);
lean_ctor_set(v_reuseFailAlloc_2599_, 9, v_irDir_2570_);
lean_ctor_set(v_reuseFailAlloc_2599_, 10, v_releaseRepo_2571_);
lean_ctor_set(v_reuseFailAlloc_2599_, 11, v_buildArchive_2572_);
lean_ctor_set(v_reuseFailAlloc_2599_, 12, v_downloadCacheService_x3f_2574_);
lean_ctor_set(v_reuseFailAlloc_2599_, 13, v_testDriver_2575_);
lean_ctor_set(v_reuseFailAlloc_2599_, 14, v_testDriverArgs_2576_);
lean_ctor_set(v_reuseFailAlloc_2599_, 15, v_lintDriver_2577_);
lean_ctor_set(v_reuseFailAlloc_2599_, 16, v_lintDriverArgs_2578_);
lean_ctor_set(v_reuseFailAlloc_2599_, 17, v_version_2579_);
lean_ctor_set(v_reuseFailAlloc_2599_, 18, v_val_2557_);
lean_ctor_set(v_reuseFailAlloc_2599_, 19, v_description_2580_);
lean_ctor_set(v_reuseFailAlloc_2599_, 20, v_keywords_2581_);
lean_ctor_set(v_reuseFailAlloc_2599_, 21, v_homepage_2582_);
lean_ctor_set(v_reuseFailAlloc_2599_, 22, v_license_2583_);
lean_ctor_set(v_reuseFailAlloc_2599_, 23, v_licenseFiles_2584_);
lean_ctor_set(v_reuseFailAlloc_2599_, 24, v_readmeFile_2585_);
lean_ctor_set(v_reuseFailAlloc_2599_, 25, v_enableArtifactCache_x3f_2587_);
lean_ctor_set(v_reuseFailAlloc_2599_, 26, v_restoreAllArtifacts_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2599_, 27, v_builtinLint_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2599_, 28, v_checks_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29, v_bootstrap_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29 + 1, v_precompileModules_2563_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29 + 3, v_reservoir_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29 + 5, v_allowImportAll_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2599_, sizeof(void*)*29 + 6, v_fixedToolchain_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__2(lean_object* v_f_2602_, lean_object* v_cfg_2603_){
_start:
{
lean_object* v_toWorkspaceConfig_2604_; lean_object* v_toLeanConfig_2605_; uint8_t v_bootstrap_2606_; lean_object* v_extraDepTargets_2607_; uint8_t v_precompileModules_2608_; lean_object* v_moreGlobalServerArgs_2609_; lean_object* v_srcDir_2610_; lean_object* v_buildDir_2611_; lean_object* v_leanLibDir_2612_; lean_object* v_nativeLibDir_2613_; lean_object* v_binDir_2614_; lean_object* v_irDir_2615_; lean_object* v_releaseRepo_2616_; lean_object* v_buildArchive_2617_; uint8_t v_preferReleaseBuild_2618_; lean_object* v_downloadCacheService_x3f_2619_; lean_object* v_testDriver_2620_; lean_object* v_testDriverArgs_2621_; lean_object* v_lintDriver_2622_; lean_object* v_lintDriverArgs_2623_; lean_object* v_version_2624_; lean_object* v_versionTags_2625_; lean_object* v_description_2626_; lean_object* v_keywords_2627_; lean_object* v_homepage_2628_; lean_object* v_license_2629_; lean_object* v_licenseFiles_2630_; lean_object* v_readmeFile_2631_; uint8_t v_reservoir_2632_; lean_object* v_enableArtifactCache_x3f_2633_; lean_object* v_restoreAllArtifacts_x3f_2634_; uint8_t v_libPrefixOnWindows_2635_; uint8_t v_allowImportAll_2636_; lean_object* v_builtinLint_x3f_2637_; lean_object* v_checks_2638_; uint8_t v_fixedToolchain_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2647_; 
v_toWorkspaceConfig_2604_ = lean_ctor_get(v_cfg_2603_, 0);
v_toLeanConfig_2605_ = lean_ctor_get(v_cfg_2603_, 1);
v_bootstrap_2606_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29);
v_extraDepTargets_2607_ = lean_ctor_get(v_cfg_2603_, 2);
v_precompileModules_2608_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2609_ = lean_ctor_get(v_cfg_2603_, 3);
v_srcDir_2610_ = lean_ctor_get(v_cfg_2603_, 4);
v_buildDir_2611_ = lean_ctor_get(v_cfg_2603_, 5);
v_leanLibDir_2612_ = lean_ctor_get(v_cfg_2603_, 6);
v_nativeLibDir_2613_ = lean_ctor_get(v_cfg_2603_, 7);
v_binDir_2614_ = lean_ctor_get(v_cfg_2603_, 8);
v_irDir_2615_ = lean_ctor_get(v_cfg_2603_, 9);
v_releaseRepo_2616_ = lean_ctor_get(v_cfg_2603_, 10);
v_buildArchive_2617_ = lean_ctor_get(v_cfg_2603_, 11);
v_preferReleaseBuild_2618_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2619_ = lean_ctor_get(v_cfg_2603_, 12);
v_testDriver_2620_ = lean_ctor_get(v_cfg_2603_, 13);
v_testDriverArgs_2621_ = lean_ctor_get(v_cfg_2603_, 14);
v_lintDriver_2622_ = lean_ctor_get(v_cfg_2603_, 15);
v_lintDriverArgs_2623_ = lean_ctor_get(v_cfg_2603_, 16);
v_version_2624_ = lean_ctor_get(v_cfg_2603_, 17);
v_versionTags_2625_ = lean_ctor_get(v_cfg_2603_, 18);
v_description_2626_ = lean_ctor_get(v_cfg_2603_, 19);
v_keywords_2627_ = lean_ctor_get(v_cfg_2603_, 20);
v_homepage_2628_ = lean_ctor_get(v_cfg_2603_, 21);
v_license_2629_ = lean_ctor_get(v_cfg_2603_, 22);
v_licenseFiles_2630_ = lean_ctor_get(v_cfg_2603_, 23);
v_readmeFile_2631_ = lean_ctor_get(v_cfg_2603_, 24);
v_reservoir_2632_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2633_ = lean_ctor_get(v_cfg_2603_, 25);
v_restoreAllArtifacts_x3f_2634_ = lean_ctor_get(v_cfg_2603_, 26);
v_libPrefixOnWindows_2635_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29 + 4);
v_allowImportAll_2636_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2637_ = lean_ctor_get(v_cfg_2603_, 27);
v_checks_2638_ = lean_ctor_get(v_cfg_2603_, 28);
v_fixedToolchain_2639_ = lean_ctor_get_uint8(v_cfg_2603_, sizeof(void*)*29 + 6);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_cfg_2603_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2641_ = v_cfg_2603_;
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_checks_2638_);
lean_inc(v_builtinLint_x3f_2637_);
lean_inc(v_restoreAllArtifacts_x3f_2634_);
lean_inc(v_enableArtifactCache_x3f_2633_);
lean_inc(v_readmeFile_2631_);
lean_inc(v_licenseFiles_2630_);
lean_inc(v_license_2629_);
lean_inc(v_homepage_2628_);
lean_inc(v_keywords_2627_);
lean_inc(v_description_2626_);
lean_inc(v_versionTags_2625_);
lean_inc(v_version_2624_);
lean_inc(v_lintDriverArgs_2623_);
lean_inc(v_lintDriver_2622_);
lean_inc(v_testDriverArgs_2621_);
lean_inc(v_testDriver_2620_);
lean_inc(v_downloadCacheService_x3f_2619_);
lean_inc(v_buildArchive_2617_);
lean_inc(v_releaseRepo_2616_);
lean_inc(v_irDir_2615_);
lean_inc(v_binDir_2614_);
lean_inc(v_nativeLibDir_2613_);
lean_inc(v_leanLibDir_2612_);
lean_inc(v_buildDir_2611_);
lean_inc(v_srcDir_2610_);
lean_inc(v_moreGlobalServerArgs_2609_);
lean_inc(v_extraDepTargets_2607_);
lean_inc(v_toLeanConfig_2605_);
lean_inc(v_toWorkspaceConfig_2604_);
lean_dec(v_cfg_2603_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_apply_1(v_f_2602_, v_versionTags_2625_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 18, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_toWorkspaceConfig_2604_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_toLeanConfig_2605_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_extraDepTargets_2607_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_moreGlobalServerArgs_2609_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v_srcDir_2610_);
lean_ctor_set(v_reuseFailAlloc_2646_, 5, v_buildDir_2611_);
lean_ctor_set(v_reuseFailAlloc_2646_, 6, v_leanLibDir_2612_);
lean_ctor_set(v_reuseFailAlloc_2646_, 7, v_nativeLibDir_2613_);
lean_ctor_set(v_reuseFailAlloc_2646_, 8, v_binDir_2614_);
lean_ctor_set(v_reuseFailAlloc_2646_, 9, v_irDir_2615_);
lean_ctor_set(v_reuseFailAlloc_2646_, 10, v_releaseRepo_2616_);
lean_ctor_set(v_reuseFailAlloc_2646_, 11, v_buildArchive_2617_);
lean_ctor_set(v_reuseFailAlloc_2646_, 12, v_downloadCacheService_x3f_2619_);
lean_ctor_set(v_reuseFailAlloc_2646_, 13, v_testDriver_2620_);
lean_ctor_set(v_reuseFailAlloc_2646_, 14, v_testDriverArgs_2621_);
lean_ctor_set(v_reuseFailAlloc_2646_, 15, v_lintDriver_2622_);
lean_ctor_set(v_reuseFailAlloc_2646_, 16, v_lintDriverArgs_2623_);
lean_ctor_set(v_reuseFailAlloc_2646_, 17, v_version_2624_);
lean_ctor_set(v_reuseFailAlloc_2646_, 18, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2646_, 19, v_description_2626_);
lean_ctor_set(v_reuseFailAlloc_2646_, 20, v_keywords_2627_);
lean_ctor_set(v_reuseFailAlloc_2646_, 21, v_homepage_2628_);
lean_ctor_set(v_reuseFailAlloc_2646_, 22, v_license_2629_);
lean_ctor_set(v_reuseFailAlloc_2646_, 23, v_licenseFiles_2630_);
lean_ctor_set(v_reuseFailAlloc_2646_, 24, v_readmeFile_2631_);
lean_ctor_set(v_reuseFailAlloc_2646_, 25, v_enableArtifactCache_x3f_2633_);
lean_ctor_set(v_reuseFailAlloc_2646_, 26, v_restoreAllArtifacts_x3f_2634_);
lean_ctor_set(v_reuseFailAlloc_2646_, 27, v_builtinLint_x3f_2637_);
lean_ctor_set(v_reuseFailAlloc_2646_, 28, v_checks_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29, v_bootstrap_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29 + 1, v_precompileModules_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29 + 3, v_reservoir_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29 + 5, v_allowImportAll_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*29 + 6, v_fixedToolchain_2639_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(lean_object* v_x_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lake_defaultVersionTags;
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___lam__3___boxed(lean_object* v_x_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lake_PackageConfig_versionTags___proj___redArg___lam__3(v_x_2650_);
lean_dec_ref(v_x_2650_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg(){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = ((lean_object*)(l_Lake_PackageConfig_versionTags___proj___redArg___closed__4));
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___redArg___boxed(lean_object* v___dummy_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lake_PackageConfig_versionTags___proj___redArg();
return v_res_2664_;
}
}
static lean_object* _init_l_Lake_PackageConfig_versionTags___proj___closed__0(void){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lake_PackageConfig_versionTags___proj___redArg();
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj(lean_object* v_p_2666_, lean_object* v_n_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags___proj___boxed(lean_object* v_p_2669_, lean_object* v_n_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lake_PackageConfig_versionTags___proj(v_p_2669_, v_n_2670_);
lean_dec(v_n_2670_);
lean_dec(v_p_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg(){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___redArg___boxed(lean_object* v___dummy_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lake_PackageConfig_versionTags_instConfigField___redArg();
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField(lean_object* v_p_2676_, lean_object* v_n_2677_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Lake_PackageConfig_versionTags___proj___closed__0, &l_Lake_PackageConfig_versionTags___proj___closed__0_once, _init_l_Lake_PackageConfig_versionTags___proj___closed__0);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_versionTags_instConfigField___boxed(lean_object* v_p_2679_, lean_object* v_n_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lake_PackageConfig_versionTags_instConfigField(v_p_2679_, v_n_2680_);
lean_dec(v_n_2680_);
lean_dec(v_p_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0(lean_object* v_cfg_2682_){
_start:
{
lean_object* v_description_2683_; 
v_description_2683_ = lean_ctor_get(v_cfg_2682_, 19);
lean_inc_ref(v_description_2683_);
return v_description_2683_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__0___boxed(lean_object* v_cfg_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lake_PackageConfig_description___proj___redArg___lam__0(v_cfg_2684_);
lean_dec_ref(v_cfg_2684_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__1(lean_object* v_val_2686_, lean_object* v_cfg_2687_){
_start:
{
lean_object* v_toWorkspaceConfig_2688_; lean_object* v_toLeanConfig_2689_; uint8_t v_bootstrap_2690_; lean_object* v_extraDepTargets_2691_; uint8_t v_precompileModules_2692_; lean_object* v_moreGlobalServerArgs_2693_; lean_object* v_srcDir_2694_; lean_object* v_buildDir_2695_; lean_object* v_leanLibDir_2696_; lean_object* v_nativeLibDir_2697_; lean_object* v_binDir_2698_; lean_object* v_irDir_2699_; lean_object* v_releaseRepo_2700_; lean_object* v_buildArchive_2701_; uint8_t v_preferReleaseBuild_2702_; lean_object* v_downloadCacheService_x3f_2703_; lean_object* v_testDriver_2704_; lean_object* v_testDriverArgs_2705_; lean_object* v_lintDriver_2706_; lean_object* v_lintDriverArgs_2707_; lean_object* v_version_2708_; lean_object* v_versionTags_2709_; lean_object* v_keywords_2710_; lean_object* v_homepage_2711_; lean_object* v_license_2712_; lean_object* v_licenseFiles_2713_; lean_object* v_readmeFile_2714_; uint8_t v_reservoir_2715_; lean_object* v_enableArtifactCache_x3f_2716_; lean_object* v_restoreAllArtifacts_x3f_2717_; uint8_t v_libPrefixOnWindows_2718_; uint8_t v_allowImportAll_2719_; lean_object* v_builtinLint_x3f_2720_; lean_object* v_checks_2721_; uint8_t v_fixedToolchain_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
v_toWorkspaceConfig_2688_ = lean_ctor_get(v_cfg_2687_, 0);
v_toLeanConfig_2689_ = lean_ctor_get(v_cfg_2687_, 1);
v_bootstrap_2690_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29);
v_extraDepTargets_2691_ = lean_ctor_get(v_cfg_2687_, 2);
v_precompileModules_2692_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2693_ = lean_ctor_get(v_cfg_2687_, 3);
v_srcDir_2694_ = lean_ctor_get(v_cfg_2687_, 4);
v_buildDir_2695_ = lean_ctor_get(v_cfg_2687_, 5);
v_leanLibDir_2696_ = lean_ctor_get(v_cfg_2687_, 6);
v_nativeLibDir_2697_ = lean_ctor_get(v_cfg_2687_, 7);
v_binDir_2698_ = lean_ctor_get(v_cfg_2687_, 8);
v_irDir_2699_ = lean_ctor_get(v_cfg_2687_, 9);
v_releaseRepo_2700_ = lean_ctor_get(v_cfg_2687_, 10);
v_buildArchive_2701_ = lean_ctor_get(v_cfg_2687_, 11);
v_preferReleaseBuild_2702_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2703_ = lean_ctor_get(v_cfg_2687_, 12);
v_testDriver_2704_ = lean_ctor_get(v_cfg_2687_, 13);
v_testDriverArgs_2705_ = lean_ctor_get(v_cfg_2687_, 14);
v_lintDriver_2706_ = lean_ctor_get(v_cfg_2687_, 15);
v_lintDriverArgs_2707_ = lean_ctor_get(v_cfg_2687_, 16);
v_version_2708_ = lean_ctor_get(v_cfg_2687_, 17);
v_versionTags_2709_ = lean_ctor_get(v_cfg_2687_, 18);
v_keywords_2710_ = lean_ctor_get(v_cfg_2687_, 20);
v_homepage_2711_ = lean_ctor_get(v_cfg_2687_, 21);
v_license_2712_ = lean_ctor_get(v_cfg_2687_, 22);
v_licenseFiles_2713_ = lean_ctor_get(v_cfg_2687_, 23);
v_readmeFile_2714_ = lean_ctor_get(v_cfg_2687_, 24);
v_reservoir_2715_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2716_ = lean_ctor_get(v_cfg_2687_, 25);
v_restoreAllArtifacts_x3f_2717_ = lean_ctor_get(v_cfg_2687_, 26);
v_libPrefixOnWindows_2718_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29 + 4);
v_allowImportAll_2719_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2720_ = lean_ctor_get(v_cfg_2687_, 27);
v_checks_2721_ = lean_ctor_get(v_cfg_2687_, 28);
v_fixedToolchain_2722_ = lean_ctor_get_uint8(v_cfg_2687_, sizeof(void*)*29 + 6);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_cfg_2687_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v_cfg_2687_, 19);
lean_dec(v_unused_2730_);
v___x_2724_ = v_cfg_2687_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_checks_2721_);
lean_inc(v_builtinLint_x3f_2720_);
lean_inc(v_restoreAllArtifacts_x3f_2717_);
lean_inc(v_enableArtifactCache_x3f_2716_);
lean_inc(v_readmeFile_2714_);
lean_inc(v_licenseFiles_2713_);
lean_inc(v_license_2712_);
lean_inc(v_homepage_2711_);
lean_inc(v_keywords_2710_);
lean_inc(v_versionTags_2709_);
lean_inc(v_version_2708_);
lean_inc(v_lintDriverArgs_2707_);
lean_inc(v_lintDriver_2706_);
lean_inc(v_testDriverArgs_2705_);
lean_inc(v_testDriver_2704_);
lean_inc(v_downloadCacheService_x3f_2703_);
lean_inc(v_buildArchive_2701_);
lean_inc(v_releaseRepo_2700_);
lean_inc(v_irDir_2699_);
lean_inc(v_binDir_2698_);
lean_inc(v_nativeLibDir_2697_);
lean_inc(v_leanLibDir_2696_);
lean_inc(v_buildDir_2695_);
lean_inc(v_srcDir_2694_);
lean_inc(v_moreGlobalServerArgs_2693_);
lean_inc(v_extraDepTargets_2691_);
lean_inc(v_toLeanConfig_2689_);
lean_inc(v_toWorkspaceConfig_2688_);
lean_dec(v_cfg_2687_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 19, v_val_2686_);
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_toWorkspaceConfig_2688_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_toLeanConfig_2689_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_extraDepTargets_2691_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_moreGlobalServerArgs_2693_);
lean_ctor_set(v_reuseFailAlloc_2728_, 4, v_srcDir_2694_);
lean_ctor_set(v_reuseFailAlloc_2728_, 5, v_buildDir_2695_);
lean_ctor_set(v_reuseFailAlloc_2728_, 6, v_leanLibDir_2696_);
lean_ctor_set(v_reuseFailAlloc_2728_, 7, v_nativeLibDir_2697_);
lean_ctor_set(v_reuseFailAlloc_2728_, 8, v_binDir_2698_);
lean_ctor_set(v_reuseFailAlloc_2728_, 9, v_irDir_2699_);
lean_ctor_set(v_reuseFailAlloc_2728_, 10, v_releaseRepo_2700_);
lean_ctor_set(v_reuseFailAlloc_2728_, 11, v_buildArchive_2701_);
lean_ctor_set(v_reuseFailAlloc_2728_, 12, v_downloadCacheService_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2728_, 13, v_testDriver_2704_);
lean_ctor_set(v_reuseFailAlloc_2728_, 14, v_testDriverArgs_2705_);
lean_ctor_set(v_reuseFailAlloc_2728_, 15, v_lintDriver_2706_);
lean_ctor_set(v_reuseFailAlloc_2728_, 16, v_lintDriverArgs_2707_);
lean_ctor_set(v_reuseFailAlloc_2728_, 17, v_version_2708_);
lean_ctor_set(v_reuseFailAlloc_2728_, 18, v_versionTags_2709_);
lean_ctor_set(v_reuseFailAlloc_2728_, 19, v_val_2686_);
lean_ctor_set(v_reuseFailAlloc_2728_, 20, v_keywords_2710_);
lean_ctor_set(v_reuseFailAlloc_2728_, 21, v_homepage_2711_);
lean_ctor_set(v_reuseFailAlloc_2728_, 22, v_license_2712_);
lean_ctor_set(v_reuseFailAlloc_2728_, 23, v_licenseFiles_2713_);
lean_ctor_set(v_reuseFailAlloc_2728_, 24, v_readmeFile_2714_);
lean_ctor_set(v_reuseFailAlloc_2728_, 25, v_enableArtifactCache_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2728_, 26, v_restoreAllArtifacts_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2728_, 27, v_builtinLint_x3f_2720_);
lean_ctor_set(v_reuseFailAlloc_2728_, 28, v_checks_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29, v_bootstrap_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29 + 1, v_precompileModules_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29 + 3, v_reservoir_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2718_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29 + 5, v_allowImportAll_2719_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, sizeof(void*)*29 + 6, v_fixedToolchain_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___lam__2(lean_object* v_f_2731_, lean_object* v_cfg_2732_){
_start:
{
lean_object* v_toWorkspaceConfig_2733_; lean_object* v_toLeanConfig_2734_; uint8_t v_bootstrap_2735_; lean_object* v_extraDepTargets_2736_; uint8_t v_precompileModules_2737_; lean_object* v_moreGlobalServerArgs_2738_; lean_object* v_srcDir_2739_; lean_object* v_buildDir_2740_; lean_object* v_leanLibDir_2741_; lean_object* v_nativeLibDir_2742_; lean_object* v_binDir_2743_; lean_object* v_irDir_2744_; lean_object* v_releaseRepo_2745_; lean_object* v_buildArchive_2746_; uint8_t v_preferReleaseBuild_2747_; lean_object* v_downloadCacheService_x3f_2748_; lean_object* v_testDriver_2749_; lean_object* v_testDriverArgs_2750_; lean_object* v_lintDriver_2751_; lean_object* v_lintDriverArgs_2752_; lean_object* v_version_2753_; lean_object* v_versionTags_2754_; lean_object* v_description_2755_; lean_object* v_keywords_2756_; lean_object* v_homepage_2757_; lean_object* v_license_2758_; lean_object* v_licenseFiles_2759_; lean_object* v_readmeFile_2760_; uint8_t v_reservoir_2761_; lean_object* v_enableArtifactCache_x3f_2762_; lean_object* v_restoreAllArtifacts_x3f_2763_; uint8_t v_libPrefixOnWindows_2764_; uint8_t v_allowImportAll_2765_; lean_object* v_builtinLint_x3f_2766_; lean_object* v_checks_2767_; uint8_t v_fixedToolchain_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2776_; 
v_toWorkspaceConfig_2733_ = lean_ctor_get(v_cfg_2732_, 0);
v_toLeanConfig_2734_ = lean_ctor_get(v_cfg_2732_, 1);
v_bootstrap_2735_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29);
v_extraDepTargets_2736_ = lean_ctor_get(v_cfg_2732_, 2);
v_precompileModules_2737_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2738_ = lean_ctor_get(v_cfg_2732_, 3);
v_srcDir_2739_ = lean_ctor_get(v_cfg_2732_, 4);
v_buildDir_2740_ = lean_ctor_get(v_cfg_2732_, 5);
v_leanLibDir_2741_ = lean_ctor_get(v_cfg_2732_, 6);
v_nativeLibDir_2742_ = lean_ctor_get(v_cfg_2732_, 7);
v_binDir_2743_ = lean_ctor_get(v_cfg_2732_, 8);
v_irDir_2744_ = lean_ctor_get(v_cfg_2732_, 9);
v_releaseRepo_2745_ = lean_ctor_get(v_cfg_2732_, 10);
v_buildArchive_2746_ = lean_ctor_get(v_cfg_2732_, 11);
v_preferReleaseBuild_2747_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2748_ = lean_ctor_get(v_cfg_2732_, 12);
v_testDriver_2749_ = lean_ctor_get(v_cfg_2732_, 13);
v_testDriverArgs_2750_ = lean_ctor_get(v_cfg_2732_, 14);
v_lintDriver_2751_ = lean_ctor_get(v_cfg_2732_, 15);
v_lintDriverArgs_2752_ = lean_ctor_get(v_cfg_2732_, 16);
v_version_2753_ = lean_ctor_get(v_cfg_2732_, 17);
v_versionTags_2754_ = lean_ctor_get(v_cfg_2732_, 18);
v_description_2755_ = lean_ctor_get(v_cfg_2732_, 19);
v_keywords_2756_ = lean_ctor_get(v_cfg_2732_, 20);
v_homepage_2757_ = lean_ctor_get(v_cfg_2732_, 21);
v_license_2758_ = lean_ctor_get(v_cfg_2732_, 22);
v_licenseFiles_2759_ = lean_ctor_get(v_cfg_2732_, 23);
v_readmeFile_2760_ = lean_ctor_get(v_cfg_2732_, 24);
v_reservoir_2761_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2762_ = lean_ctor_get(v_cfg_2732_, 25);
v_restoreAllArtifacts_x3f_2763_ = lean_ctor_get(v_cfg_2732_, 26);
v_libPrefixOnWindows_2764_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29 + 4);
v_allowImportAll_2765_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2766_ = lean_ctor_get(v_cfg_2732_, 27);
v_checks_2767_ = lean_ctor_get(v_cfg_2732_, 28);
v_fixedToolchain_2768_ = lean_ctor_get_uint8(v_cfg_2732_, sizeof(void*)*29 + 6);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_cfg_2732_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2770_ = v_cfg_2732_;
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_checks_2767_);
lean_inc(v_builtinLint_x3f_2766_);
lean_inc(v_restoreAllArtifacts_x3f_2763_);
lean_inc(v_enableArtifactCache_x3f_2762_);
lean_inc(v_readmeFile_2760_);
lean_inc(v_licenseFiles_2759_);
lean_inc(v_license_2758_);
lean_inc(v_homepage_2757_);
lean_inc(v_keywords_2756_);
lean_inc(v_description_2755_);
lean_inc(v_versionTags_2754_);
lean_inc(v_version_2753_);
lean_inc(v_lintDriverArgs_2752_);
lean_inc(v_lintDriver_2751_);
lean_inc(v_testDriverArgs_2750_);
lean_inc(v_testDriver_2749_);
lean_inc(v_downloadCacheService_x3f_2748_);
lean_inc(v_buildArchive_2746_);
lean_inc(v_releaseRepo_2745_);
lean_inc(v_irDir_2744_);
lean_inc(v_binDir_2743_);
lean_inc(v_nativeLibDir_2742_);
lean_inc(v_leanLibDir_2741_);
lean_inc(v_buildDir_2740_);
lean_inc(v_srcDir_2739_);
lean_inc(v_moreGlobalServerArgs_2738_);
lean_inc(v_extraDepTargets_2736_);
lean_inc(v_toLeanConfig_2734_);
lean_inc(v_toWorkspaceConfig_2733_);
lean_dec(v_cfg_2732_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_apply_1(v_f_2731_, v_description_2755_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 19, v___x_2772_);
v___x_2774_ = v___x_2770_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_toWorkspaceConfig_2733_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_toLeanConfig_2734_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_extraDepTargets_2736_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_moreGlobalServerArgs_2738_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_srcDir_2739_);
lean_ctor_set(v_reuseFailAlloc_2775_, 5, v_buildDir_2740_);
lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_leanLibDir_2741_);
lean_ctor_set(v_reuseFailAlloc_2775_, 7, v_nativeLibDir_2742_);
lean_ctor_set(v_reuseFailAlloc_2775_, 8, v_binDir_2743_);
lean_ctor_set(v_reuseFailAlloc_2775_, 9, v_irDir_2744_);
lean_ctor_set(v_reuseFailAlloc_2775_, 10, v_releaseRepo_2745_);
lean_ctor_set(v_reuseFailAlloc_2775_, 11, v_buildArchive_2746_);
lean_ctor_set(v_reuseFailAlloc_2775_, 12, v_downloadCacheService_x3f_2748_);
lean_ctor_set(v_reuseFailAlloc_2775_, 13, v_testDriver_2749_);
lean_ctor_set(v_reuseFailAlloc_2775_, 14, v_testDriverArgs_2750_);
lean_ctor_set(v_reuseFailAlloc_2775_, 15, v_lintDriver_2751_);
lean_ctor_set(v_reuseFailAlloc_2775_, 16, v_lintDriverArgs_2752_);
lean_ctor_set(v_reuseFailAlloc_2775_, 17, v_version_2753_);
lean_ctor_set(v_reuseFailAlloc_2775_, 18, v_versionTags_2754_);
lean_ctor_set(v_reuseFailAlloc_2775_, 19, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2775_, 20, v_keywords_2756_);
lean_ctor_set(v_reuseFailAlloc_2775_, 21, v_homepage_2757_);
lean_ctor_set(v_reuseFailAlloc_2775_, 22, v_license_2758_);
lean_ctor_set(v_reuseFailAlloc_2775_, 23, v_licenseFiles_2759_);
lean_ctor_set(v_reuseFailAlloc_2775_, 24, v_readmeFile_2760_);
lean_ctor_set(v_reuseFailAlloc_2775_, 25, v_enableArtifactCache_x3f_2762_);
lean_ctor_set(v_reuseFailAlloc_2775_, 26, v_restoreAllArtifacts_x3f_2763_);
lean_ctor_set(v_reuseFailAlloc_2775_, 27, v_builtinLint_x3f_2766_);
lean_ctor_set(v_reuseFailAlloc_2775_, 28, v_checks_2767_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29, v_bootstrap_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29 + 1, v_precompileModules_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29 + 3, v_reservoir_2761_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2764_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29 + 5, v_allowImportAll_2765_);
lean_ctor_set_uint8(v_reuseFailAlloc_2775_, sizeof(void*)*29 + 6, v_fixedToolchain_2768_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg(){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = ((lean_object*)(l_Lake_PackageConfig_description___proj___redArg___closed__3));
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___redArg___boxed(lean_object* v___dummy_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lake_PackageConfig_description___proj___redArg();
return v_res_2788_;
}
}
static lean_object* _init_l_Lake_PackageConfig_description___proj___closed__0(void){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lake_PackageConfig_description___proj___redArg();
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj(lean_object* v_p_2790_, lean_object* v_n_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description___proj___boxed(lean_object* v_p_2793_, lean_object* v_n_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lake_PackageConfig_description___proj(v_p_2793_, v_n_2794_);
lean_dec(v_n_2794_);
lean_dec(v_p_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg(){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___redArg___boxed(lean_object* v___dummy_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lake_PackageConfig_description_instConfigField___redArg();
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField(lean_object* v_p_2800_, lean_object* v_n_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_obj_once(&l_Lake_PackageConfig_description___proj___closed__0, &l_Lake_PackageConfig_description___proj___closed__0_once, _init_l_Lake_PackageConfig_description___proj___closed__0);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_description_instConfigField___boxed(lean_object* v_p_2803_, lean_object* v_n_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lake_PackageConfig_description_instConfigField(v_p_2803_, v_n_2804_);
lean_dec(v_n_2804_);
lean_dec(v_p_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0(lean_object* v_cfg_2806_){
_start:
{
lean_object* v_keywords_2807_; 
v_keywords_2807_ = lean_ctor_get(v_cfg_2806_, 20);
lean_inc_ref(v_keywords_2807_);
return v_keywords_2807_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__0___boxed(lean_object* v_cfg_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lake_PackageConfig_keywords___proj___redArg___lam__0(v_cfg_2808_);
lean_dec_ref(v_cfg_2808_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__1(lean_object* v_val_2810_, lean_object* v_cfg_2811_){
_start:
{
lean_object* v_toWorkspaceConfig_2812_; lean_object* v_toLeanConfig_2813_; uint8_t v_bootstrap_2814_; lean_object* v_extraDepTargets_2815_; uint8_t v_precompileModules_2816_; lean_object* v_moreGlobalServerArgs_2817_; lean_object* v_srcDir_2818_; lean_object* v_buildDir_2819_; lean_object* v_leanLibDir_2820_; lean_object* v_nativeLibDir_2821_; lean_object* v_binDir_2822_; lean_object* v_irDir_2823_; lean_object* v_releaseRepo_2824_; lean_object* v_buildArchive_2825_; uint8_t v_preferReleaseBuild_2826_; lean_object* v_downloadCacheService_x3f_2827_; lean_object* v_testDriver_2828_; lean_object* v_testDriverArgs_2829_; lean_object* v_lintDriver_2830_; lean_object* v_lintDriverArgs_2831_; lean_object* v_version_2832_; lean_object* v_versionTags_2833_; lean_object* v_description_2834_; lean_object* v_homepage_2835_; lean_object* v_license_2836_; lean_object* v_licenseFiles_2837_; lean_object* v_readmeFile_2838_; uint8_t v_reservoir_2839_; lean_object* v_enableArtifactCache_x3f_2840_; lean_object* v_restoreAllArtifacts_x3f_2841_; uint8_t v_libPrefixOnWindows_2842_; uint8_t v_allowImportAll_2843_; lean_object* v_builtinLint_x3f_2844_; lean_object* v_checks_2845_; uint8_t v_fixedToolchain_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_toWorkspaceConfig_2812_ = lean_ctor_get(v_cfg_2811_, 0);
v_toLeanConfig_2813_ = lean_ctor_get(v_cfg_2811_, 1);
v_bootstrap_2814_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29);
v_extraDepTargets_2815_ = lean_ctor_get(v_cfg_2811_, 2);
v_precompileModules_2816_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2817_ = lean_ctor_get(v_cfg_2811_, 3);
v_srcDir_2818_ = lean_ctor_get(v_cfg_2811_, 4);
v_buildDir_2819_ = lean_ctor_get(v_cfg_2811_, 5);
v_leanLibDir_2820_ = lean_ctor_get(v_cfg_2811_, 6);
v_nativeLibDir_2821_ = lean_ctor_get(v_cfg_2811_, 7);
v_binDir_2822_ = lean_ctor_get(v_cfg_2811_, 8);
v_irDir_2823_ = lean_ctor_get(v_cfg_2811_, 9);
v_releaseRepo_2824_ = lean_ctor_get(v_cfg_2811_, 10);
v_buildArchive_2825_ = lean_ctor_get(v_cfg_2811_, 11);
v_preferReleaseBuild_2826_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2827_ = lean_ctor_get(v_cfg_2811_, 12);
v_testDriver_2828_ = lean_ctor_get(v_cfg_2811_, 13);
v_testDriverArgs_2829_ = lean_ctor_get(v_cfg_2811_, 14);
v_lintDriver_2830_ = lean_ctor_get(v_cfg_2811_, 15);
v_lintDriverArgs_2831_ = lean_ctor_get(v_cfg_2811_, 16);
v_version_2832_ = lean_ctor_get(v_cfg_2811_, 17);
v_versionTags_2833_ = lean_ctor_get(v_cfg_2811_, 18);
v_description_2834_ = lean_ctor_get(v_cfg_2811_, 19);
v_homepage_2835_ = lean_ctor_get(v_cfg_2811_, 21);
v_license_2836_ = lean_ctor_get(v_cfg_2811_, 22);
v_licenseFiles_2837_ = lean_ctor_get(v_cfg_2811_, 23);
v_readmeFile_2838_ = lean_ctor_get(v_cfg_2811_, 24);
v_reservoir_2839_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2840_ = lean_ctor_get(v_cfg_2811_, 25);
v_restoreAllArtifacts_x3f_2841_ = lean_ctor_get(v_cfg_2811_, 26);
v_libPrefixOnWindows_2842_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29 + 4);
v_allowImportAll_2843_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2844_ = lean_ctor_get(v_cfg_2811_, 27);
v_checks_2845_ = lean_ctor_get(v_cfg_2811_, 28);
v_fixedToolchain_2846_ = lean_ctor_get_uint8(v_cfg_2811_, sizeof(void*)*29 + 6);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_cfg_2811_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; 
v_unused_2854_ = lean_ctor_get(v_cfg_2811_, 20);
lean_dec(v_unused_2854_);
v___x_2848_ = v_cfg_2811_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_checks_2845_);
lean_inc(v_builtinLint_x3f_2844_);
lean_inc(v_restoreAllArtifacts_x3f_2841_);
lean_inc(v_enableArtifactCache_x3f_2840_);
lean_inc(v_readmeFile_2838_);
lean_inc(v_licenseFiles_2837_);
lean_inc(v_license_2836_);
lean_inc(v_homepage_2835_);
lean_inc(v_description_2834_);
lean_inc(v_versionTags_2833_);
lean_inc(v_version_2832_);
lean_inc(v_lintDriverArgs_2831_);
lean_inc(v_lintDriver_2830_);
lean_inc(v_testDriverArgs_2829_);
lean_inc(v_testDriver_2828_);
lean_inc(v_downloadCacheService_x3f_2827_);
lean_inc(v_buildArchive_2825_);
lean_inc(v_releaseRepo_2824_);
lean_inc(v_irDir_2823_);
lean_inc(v_binDir_2822_);
lean_inc(v_nativeLibDir_2821_);
lean_inc(v_leanLibDir_2820_);
lean_inc(v_buildDir_2819_);
lean_inc(v_srcDir_2818_);
lean_inc(v_moreGlobalServerArgs_2817_);
lean_inc(v_extraDepTargets_2815_);
lean_inc(v_toLeanConfig_2813_);
lean_inc(v_toWorkspaceConfig_2812_);
lean_dec(v_cfg_2811_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 20, v_val_2810_);
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_toWorkspaceConfig_2812_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_toLeanConfig_2813_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_extraDepTargets_2815_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_moreGlobalServerArgs_2817_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v_srcDir_2818_);
lean_ctor_set(v_reuseFailAlloc_2852_, 5, v_buildDir_2819_);
lean_ctor_set(v_reuseFailAlloc_2852_, 6, v_leanLibDir_2820_);
lean_ctor_set(v_reuseFailAlloc_2852_, 7, v_nativeLibDir_2821_);
lean_ctor_set(v_reuseFailAlloc_2852_, 8, v_binDir_2822_);
lean_ctor_set(v_reuseFailAlloc_2852_, 9, v_irDir_2823_);
lean_ctor_set(v_reuseFailAlloc_2852_, 10, v_releaseRepo_2824_);
lean_ctor_set(v_reuseFailAlloc_2852_, 11, v_buildArchive_2825_);
lean_ctor_set(v_reuseFailAlloc_2852_, 12, v_downloadCacheService_x3f_2827_);
lean_ctor_set(v_reuseFailAlloc_2852_, 13, v_testDriver_2828_);
lean_ctor_set(v_reuseFailAlloc_2852_, 14, v_testDriverArgs_2829_);
lean_ctor_set(v_reuseFailAlloc_2852_, 15, v_lintDriver_2830_);
lean_ctor_set(v_reuseFailAlloc_2852_, 16, v_lintDriverArgs_2831_);
lean_ctor_set(v_reuseFailAlloc_2852_, 17, v_version_2832_);
lean_ctor_set(v_reuseFailAlloc_2852_, 18, v_versionTags_2833_);
lean_ctor_set(v_reuseFailAlloc_2852_, 19, v_description_2834_);
lean_ctor_set(v_reuseFailAlloc_2852_, 20, v_val_2810_);
lean_ctor_set(v_reuseFailAlloc_2852_, 21, v_homepage_2835_);
lean_ctor_set(v_reuseFailAlloc_2852_, 22, v_license_2836_);
lean_ctor_set(v_reuseFailAlloc_2852_, 23, v_licenseFiles_2837_);
lean_ctor_set(v_reuseFailAlloc_2852_, 24, v_readmeFile_2838_);
lean_ctor_set(v_reuseFailAlloc_2852_, 25, v_enableArtifactCache_x3f_2840_);
lean_ctor_set(v_reuseFailAlloc_2852_, 26, v_restoreAllArtifacts_x3f_2841_);
lean_ctor_set(v_reuseFailAlloc_2852_, 27, v_builtinLint_x3f_2844_);
lean_ctor_set(v_reuseFailAlloc_2852_, 28, v_checks_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29, v_bootstrap_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29 + 1, v_precompileModules_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2826_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29 + 3, v_reservoir_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29 + 5, v_allowImportAll_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*29 + 6, v_fixedToolchain_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___lam__2(lean_object* v_f_2855_, lean_object* v_cfg_2856_){
_start:
{
lean_object* v_toWorkspaceConfig_2857_; lean_object* v_toLeanConfig_2858_; uint8_t v_bootstrap_2859_; lean_object* v_extraDepTargets_2860_; uint8_t v_precompileModules_2861_; lean_object* v_moreGlobalServerArgs_2862_; lean_object* v_srcDir_2863_; lean_object* v_buildDir_2864_; lean_object* v_leanLibDir_2865_; lean_object* v_nativeLibDir_2866_; lean_object* v_binDir_2867_; lean_object* v_irDir_2868_; lean_object* v_releaseRepo_2869_; lean_object* v_buildArchive_2870_; uint8_t v_preferReleaseBuild_2871_; lean_object* v_downloadCacheService_x3f_2872_; lean_object* v_testDriver_2873_; lean_object* v_testDriverArgs_2874_; lean_object* v_lintDriver_2875_; lean_object* v_lintDriverArgs_2876_; lean_object* v_version_2877_; lean_object* v_versionTags_2878_; lean_object* v_description_2879_; lean_object* v_keywords_2880_; lean_object* v_homepage_2881_; lean_object* v_license_2882_; lean_object* v_licenseFiles_2883_; lean_object* v_readmeFile_2884_; uint8_t v_reservoir_2885_; lean_object* v_enableArtifactCache_x3f_2886_; lean_object* v_restoreAllArtifacts_x3f_2887_; uint8_t v_libPrefixOnWindows_2888_; uint8_t v_allowImportAll_2889_; lean_object* v_builtinLint_x3f_2890_; lean_object* v_checks_2891_; uint8_t v_fixedToolchain_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
v_toWorkspaceConfig_2857_ = lean_ctor_get(v_cfg_2856_, 0);
v_toLeanConfig_2858_ = lean_ctor_get(v_cfg_2856_, 1);
v_bootstrap_2859_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29);
v_extraDepTargets_2860_ = lean_ctor_get(v_cfg_2856_, 2);
v_precompileModules_2861_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2862_ = lean_ctor_get(v_cfg_2856_, 3);
v_srcDir_2863_ = lean_ctor_get(v_cfg_2856_, 4);
v_buildDir_2864_ = lean_ctor_get(v_cfg_2856_, 5);
v_leanLibDir_2865_ = lean_ctor_get(v_cfg_2856_, 6);
v_nativeLibDir_2866_ = lean_ctor_get(v_cfg_2856_, 7);
v_binDir_2867_ = lean_ctor_get(v_cfg_2856_, 8);
v_irDir_2868_ = lean_ctor_get(v_cfg_2856_, 9);
v_releaseRepo_2869_ = lean_ctor_get(v_cfg_2856_, 10);
v_buildArchive_2870_ = lean_ctor_get(v_cfg_2856_, 11);
v_preferReleaseBuild_2871_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2872_ = lean_ctor_get(v_cfg_2856_, 12);
v_testDriver_2873_ = lean_ctor_get(v_cfg_2856_, 13);
v_testDriverArgs_2874_ = lean_ctor_get(v_cfg_2856_, 14);
v_lintDriver_2875_ = lean_ctor_get(v_cfg_2856_, 15);
v_lintDriverArgs_2876_ = lean_ctor_get(v_cfg_2856_, 16);
v_version_2877_ = lean_ctor_get(v_cfg_2856_, 17);
v_versionTags_2878_ = lean_ctor_get(v_cfg_2856_, 18);
v_description_2879_ = lean_ctor_get(v_cfg_2856_, 19);
v_keywords_2880_ = lean_ctor_get(v_cfg_2856_, 20);
v_homepage_2881_ = lean_ctor_get(v_cfg_2856_, 21);
v_license_2882_ = lean_ctor_get(v_cfg_2856_, 22);
v_licenseFiles_2883_ = lean_ctor_get(v_cfg_2856_, 23);
v_readmeFile_2884_ = lean_ctor_get(v_cfg_2856_, 24);
v_reservoir_2885_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2886_ = lean_ctor_get(v_cfg_2856_, 25);
v_restoreAllArtifacts_x3f_2887_ = lean_ctor_get(v_cfg_2856_, 26);
v_libPrefixOnWindows_2888_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29 + 4);
v_allowImportAll_2889_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2890_ = lean_ctor_get(v_cfg_2856_, 27);
v_checks_2891_ = lean_ctor_get(v_cfg_2856_, 28);
v_fixedToolchain_2892_ = lean_ctor_get_uint8(v_cfg_2856_, sizeof(void*)*29 + 6);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_cfg_2856_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v_cfg_2856_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_checks_2891_);
lean_inc(v_builtinLint_x3f_2890_);
lean_inc(v_restoreAllArtifacts_x3f_2887_);
lean_inc(v_enableArtifactCache_x3f_2886_);
lean_inc(v_readmeFile_2884_);
lean_inc(v_licenseFiles_2883_);
lean_inc(v_license_2882_);
lean_inc(v_homepage_2881_);
lean_inc(v_keywords_2880_);
lean_inc(v_description_2879_);
lean_inc(v_versionTags_2878_);
lean_inc(v_version_2877_);
lean_inc(v_lintDriverArgs_2876_);
lean_inc(v_lintDriver_2875_);
lean_inc(v_testDriverArgs_2874_);
lean_inc(v_testDriver_2873_);
lean_inc(v_downloadCacheService_x3f_2872_);
lean_inc(v_buildArchive_2870_);
lean_inc(v_releaseRepo_2869_);
lean_inc(v_irDir_2868_);
lean_inc(v_binDir_2867_);
lean_inc(v_nativeLibDir_2866_);
lean_inc(v_leanLibDir_2865_);
lean_inc(v_buildDir_2864_);
lean_inc(v_srcDir_2863_);
lean_inc(v_moreGlobalServerArgs_2862_);
lean_inc(v_extraDepTargets_2860_);
lean_inc(v_toLeanConfig_2858_);
lean_inc(v_toWorkspaceConfig_2857_);
lean_dec(v_cfg_2856_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_apply_1(v_f_2855_, v_keywords_2880_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 20, v___x_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_toWorkspaceConfig_2857_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_toLeanConfig_2858_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_extraDepTargets_2860_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_moreGlobalServerArgs_2862_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_srcDir_2863_);
lean_ctor_set(v_reuseFailAlloc_2899_, 5, v_buildDir_2864_);
lean_ctor_set(v_reuseFailAlloc_2899_, 6, v_leanLibDir_2865_);
lean_ctor_set(v_reuseFailAlloc_2899_, 7, v_nativeLibDir_2866_);
lean_ctor_set(v_reuseFailAlloc_2899_, 8, v_binDir_2867_);
lean_ctor_set(v_reuseFailAlloc_2899_, 9, v_irDir_2868_);
lean_ctor_set(v_reuseFailAlloc_2899_, 10, v_releaseRepo_2869_);
lean_ctor_set(v_reuseFailAlloc_2899_, 11, v_buildArchive_2870_);
lean_ctor_set(v_reuseFailAlloc_2899_, 12, v_downloadCacheService_x3f_2872_);
lean_ctor_set(v_reuseFailAlloc_2899_, 13, v_testDriver_2873_);
lean_ctor_set(v_reuseFailAlloc_2899_, 14, v_testDriverArgs_2874_);
lean_ctor_set(v_reuseFailAlloc_2899_, 15, v_lintDriver_2875_);
lean_ctor_set(v_reuseFailAlloc_2899_, 16, v_lintDriverArgs_2876_);
lean_ctor_set(v_reuseFailAlloc_2899_, 17, v_version_2877_);
lean_ctor_set(v_reuseFailAlloc_2899_, 18, v_versionTags_2878_);
lean_ctor_set(v_reuseFailAlloc_2899_, 19, v_description_2879_);
lean_ctor_set(v_reuseFailAlloc_2899_, 20, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2899_, 21, v_homepage_2881_);
lean_ctor_set(v_reuseFailAlloc_2899_, 22, v_license_2882_);
lean_ctor_set(v_reuseFailAlloc_2899_, 23, v_licenseFiles_2883_);
lean_ctor_set(v_reuseFailAlloc_2899_, 24, v_readmeFile_2884_);
lean_ctor_set(v_reuseFailAlloc_2899_, 25, v_enableArtifactCache_x3f_2886_);
lean_ctor_set(v_reuseFailAlloc_2899_, 26, v_restoreAllArtifacts_x3f_2887_);
lean_ctor_set(v_reuseFailAlloc_2899_, 27, v_builtinLint_x3f_2890_);
lean_ctor_set(v_reuseFailAlloc_2899_, 28, v_checks_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29, v_bootstrap_2859_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29 + 1, v_precompileModules_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2871_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29 + 3, v_reservoir_2885_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29 + 5, v_allowImportAll_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*29 + 6, v_fixedToolchain_2892_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg(){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = ((lean_object*)(l_Lake_PackageConfig_keywords___proj___redArg___closed__3));
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___redArg___boxed(lean_object* v___dummy_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lake_PackageConfig_keywords___proj___redArg();
return v_res_2912_;
}
}
static lean_object* _init_l_Lake_PackageConfig_keywords___proj___closed__0(void){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lake_PackageConfig_keywords___proj___redArg();
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj(lean_object* v_p_2914_, lean_object* v_n_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords___proj___boxed(lean_object* v_p_2917_, lean_object* v_n_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lake_PackageConfig_keywords___proj(v_p_2917_, v_n_2918_);
lean_dec(v_n_2918_);
lean_dec(v_p_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg(){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___redArg___boxed(lean_object* v___dummy_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lake_PackageConfig_keywords_instConfigField___redArg();
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField(lean_object* v_p_2924_, lean_object* v_n_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_obj_once(&l_Lake_PackageConfig_keywords___proj___closed__0, &l_Lake_PackageConfig_keywords___proj___closed__0_once, _init_l_Lake_PackageConfig_keywords___proj___closed__0);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_keywords_instConfigField___boxed(lean_object* v_p_2927_, lean_object* v_n_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lake_PackageConfig_keywords_instConfigField(v_p_2927_, v_n_2928_);
lean_dec(v_n_2928_);
lean_dec(v_p_2927_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0(lean_object* v_cfg_2930_){
_start:
{
lean_object* v_homepage_2931_; 
v_homepage_2931_ = lean_ctor_get(v_cfg_2930_, 21);
lean_inc_ref(v_homepage_2931_);
return v_homepage_2931_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__0___boxed(lean_object* v_cfg_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lake_PackageConfig_homepage___proj___redArg___lam__0(v_cfg_2932_);
lean_dec_ref(v_cfg_2932_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__1(lean_object* v_val_2934_, lean_object* v_cfg_2935_){
_start:
{
lean_object* v_toWorkspaceConfig_2936_; lean_object* v_toLeanConfig_2937_; uint8_t v_bootstrap_2938_; lean_object* v_extraDepTargets_2939_; uint8_t v_precompileModules_2940_; lean_object* v_moreGlobalServerArgs_2941_; lean_object* v_srcDir_2942_; lean_object* v_buildDir_2943_; lean_object* v_leanLibDir_2944_; lean_object* v_nativeLibDir_2945_; lean_object* v_binDir_2946_; lean_object* v_irDir_2947_; lean_object* v_releaseRepo_2948_; lean_object* v_buildArchive_2949_; uint8_t v_preferReleaseBuild_2950_; lean_object* v_downloadCacheService_x3f_2951_; lean_object* v_testDriver_2952_; lean_object* v_testDriverArgs_2953_; lean_object* v_lintDriver_2954_; lean_object* v_lintDriverArgs_2955_; lean_object* v_version_2956_; lean_object* v_versionTags_2957_; lean_object* v_description_2958_; lean_object* v_keywords_2959_; lean_object* v_license_2960_; lean_object* v_licenseFiles_2961_; lean_object* v_readmeFile_2962_; uint8_t v_reservoir_2963_; lean_object* v_enableArtifactCache_x3f_2964_; lean_object* v_restoreAllArtifacts_x3f_2965_; uint8_t v_libPrefixOnWindows_2966_; uint8_t v_allowImportAll_2967_; lean_object* v_builtinLint_x3f_2968_; lean_object* v_checks_2969_; uint8_t v_fixedToolchain_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_toWorkspaceConfig_2936_ = lean_ctor_get(v_cfg_2935_, 0);
v_toLeanConfig_2937_ = lean_ctor_get(v_cfg_2935_, 1);
v_bootstrap_2938_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29);
v_extraDepTargets_2939_ = lean_ctor_get(v_cfg_2935_, 2);
v_precompileModules_2940_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2941_ = lean_ctor_get(v_cfg_2935_, 3);
v_srcDir_2942_ = lean_ctor_get(v_cfg_2935_, 4);
v_buildDir_2943_ = lean_ctor_get(v_cfg_2935_, 5);
v_leanLibDir_2944_ = lean_ctor_get(v_cfg_2935_, 6);
v_nativeLibDir_2945_ = lean_ctor_get(v_cfg_2935_, 7);
v_binDir_2946_ = lean_ctor_get(v_cfg_2935_, 8);
v_irDir_2947_ = lean_ctor_get(v_cfg_2935_, 9);
v_releaseRepo_2948_ = lean_ctor_get(v_cfg_2935_, 10);
v_buildArchive_2949_ = lean_ctor_get(v_cfg_2935_, 11);
v_preferReleaseBuild_2950_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2951_ = lean_ctor_get(v_cfg_2935_, 12);
v_testDriver_2952_ = lean_ctor_get(v_cfg_2935_, 13);
v_testDriverArgs_2953_ = lean_ctor_get(v_cfg_2935_, 14);
v_lintDriver_2954_ = lean_ctor_get(v_cfg_2935_, 15);
v_lintDriverArgs_2955_ = lean_ctor_get(v_cfg_2935_, 16);
v_version_2956_ = lean_ctor_get(v_cfg_2935_, 17);
v_versionTags_2957_ = lean_ctor_get(v_cfg_2935_, 18);
v_description_2958_ = lean_ctor_get(v_cfg_2935_, 19);
v_keywords_2959_ = lean_ctor_get(v_cfg_2935_, 20);
v_license_2960_ = lean_ctor_get(v_cfg_2935_, 22);
v_licenseFiles_2961_ = lean_ctor_get(v_cfg_2935_, 23);
v_readmeFile_2962_ = lean_ctor_get(v_cfg_2935_, 24);
v_reservoir_2963_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_2964_ = lean_ctor_get(v_cfg_2935_, 25);
v_restoreAllArtifacts_x3f_2965_ = lean_ctor_get(v_cfg_2935_, 26);
v_libPrefixOnWindows_2966_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29 + 4);
v_allowImportAll_2967_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_2968_ = lean_ctor_get(v_cfg_2935_, 27);
v_checks_2969_ = lean_ctor_get(v_cfg_2935_, 28);
v_fixedToolchain_2970_ = lean_ctor_get_uint8(v_cfg_2935_, sizeof(void*)*29 + 6);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_cfg_2935_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v_cfg_2935_, 21);
lean_dec(v_unused_2978_);
v___x_2972_ = v_cfg_2935_;
v_isShared_2973_ = v_isSharedCheck_2977_;
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
lean_inc(v_keywords_2959_);
lean_inc(v_description_2958_);
lean_inc(v_versionTags_2957_);
lean_inc(v_version_2956_);
lean_inc(v_lintDriverArgs_2955_);
lean_inc(v_lintDriver_2954_);
lean_inc(v_testDriverArgs_2953_);
lean_inc(v_testDriver_2952_);
lean_inc(v_downloadCacheService_x3f_2951_);
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
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 21, v_val_2934_);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_toWorkspaceConfig_2936_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_toLeanConfig_2937_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_extraDepTargets_2939_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_moreGlobalServerArgs_2941_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_srcDir_2942_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v_buildDir_2943_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v_leanLibDir_2944_);
lean_ctor_set(v_reuseFailAlloc_2976_, 7, v_nativeLibDir_2945_);
lean_ctor_set(v_reuseFailAlloc_2976_, 8, v_binDir_2946_);
lean_ctor_set(v_reuseFailAlloc_2976_, 9, v_irDir_2947_);
lean_ctor_set(v_reuseFailAlloc_2976_, 10, v_releaseRepo_2948_);
lean_ctor_set(v_reuseFailAlloc_2976_, 11, v_buildArchive_2949_);
lean_ctor_set(v_reuseFailAlloc_2976_, 12, v_downloadCacheService_x3f_2951_);
lean_ctor_set(v_reuseFailAlloc_2976_, 13, v_testDriver_2952_);
lean_ctor_set(v_reuseFailAlloc_2976_, 14, v_testDriverArgs_2953_);
lean_ctor_set(v_reuseFailAlloc_2976_, 15, v_lintDriver_2954_);
lean_ctor_set(v_reuseFailAlloc_2976_, 16, v_lintDriverArgs_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 17, v_version_2956_);
lean_ctor_set(v_reuseFailAlloc_2976_, 18, v_versionTags_2957_);
lean_ctor_set(v_reuseFailAlloc_2976_, 19, v_description_2958_);
lean_ctor_set(v_reuseFailAlloc_2976_, 20, v_keywords_2959_);
lean_ctor_set(v_reuseFailAlloc_2976_, 21, v_val_2934_);
lean_ctor_set(v_reuseFailAlloc_2976_, 22, v_license_2960_);
lean_ctor_set(v_reuseFailAlloc_2976_, 23, v_licenseFiles_2961_);
lean_ctor_set(v_reuseFailAlloc_2976_, 24, v_readmeFile_2962_);
lean_ctor_set(v_reuseFailAlloc_2976_, 25, v_enableArtifactCache_x3f_2964_);
lean_ctor_set(v_reuseFailAlloc_2976_, 26, v_restoreAllArtifacts_x3f_2965_);
lean_ctor_set(v_reuseFailAlloc_2976_, 27, v_builtinLint_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_2976_, 28, v_checks_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29, v_bootstrap_2938_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29 + 1, v_precompileModules_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29 + 3, v_reservoir_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29 + 5, v_allowImportAll_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*29 + 6, v_fixedToolchain_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___lam__2(lean_object* v_f_2979_, lean_object* v_cfg_2980_){
_start:
{
lean_object* v_toWorkspaceConfig_2981_; lean_object* v_toLeanConfig_2982_; uint8_t v_bootstrap_2983_; lean_object* v_extraDepTargets_2984_; uint8_t v_precompileModules_2985_; lean_object* v_moreGlobalServerArgs_2986_; lean_object* v_srcDir_2987_; lean_object* v_buildDir_2988_; lean_object* v_leanLibDir_2989_; lean_object* v_nativeLibDir_2990_; lean_object* v_binDir_2991_; lean_object* v_irDir_2992_; lean_object* v_releaseRepo_2993_; lean_object* v_buildArchive_2994_; uint8_t v_preferReleaseBuild_2995_; lean_object* v_downloadCacheService_x3f_2996_; lean_object* v_testDriver_2997_; lean_object* v_testDriverArgs_2998_; lean_object* v_lintDriver_2999_; lean_object* v_lintDriverArgs_3000_; lean_object* v_version_3001_; lean_object* v_versionTags_3002_; lean_object* v_description_3003_; lean_object* v_keywords_3004_; lean_object* v_homepage_3005_; lean_object* v_license_3006_; lean_object* v_licenseFiles_3007_; lean_object* v_readmeFile_3008_; uint8_t v_reservoir_3009_; lean_object* v_enableArtifactCache_x3f_3010_; lean_object* v_restoreAllArtifacts_x3f_3011_; uint8_t v_libPrefixOnWindows_3012_; uint8_t v_allowImportAll_3013_; lean_object* v_builtinLint_x3f_3014_; lean_object* v_checks_3015_; uint8_t v_fixedToolchain_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3024_; 
v_toWorkspaceConfig_2981_ = lean_ctor_get(v_cfg_2980_, 0);
v_toLeanConfig_2982_ = lean_ctor_get(v_cfg_2980_, 1);
v_bootstrap_2983_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29);
v_extraDepTargets_2984_ = lean_ctor_get(v_cfg_2980_, 2);
v_precompileModules_2985_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_2986_ = lean_ctor_get(v_cfg_2980_, 3);
v_srcDir_2987_ = lean_ctor_get(v_cfg_2980_, 4);
v_buildDir_2988_ = lean_ctor_get(v_cfg_2980_, 5);
v_leanLibDir_2989_ = lean_ctor_get(v_cfg_2980_, 6);
v_nativeLibDir_2990_ = lean_ctor_get(v_cfg_2980_, 7);
v_binDir_2991_ = lean_ctor_get(v_cfg_2980_, 8);
v_irDir_2992_ = lean_ctor_get(v_cfg_2980_, 9);
v_releaseRepo_2993_ = lean_ctor_get(v_cfg_2980_, 10);
v_buildArchive_2994_ = lean_ctor_get(v_cfg_2980_, 11);
v_preferReleaseBuild_2995_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_2996_ = lean_ctor_get(v_cfg_2980_, 12);
v_testDriver_2997_ = lean_ctor_get(v_cfg_2980_, 13);
v_testDriverArgs_2998_ = lean_ctor_get(v_cfg_2980_, 14);
v_lintDriver_2999_ = lean_ctor_get(v_cfg_2980_, 15);
v_lintDriverArgs_3000_ = lean_ctor_get(v_cfg_2980_, 16);
v_version_3001_ = lean_ctor_get(v_cfg_2980_, 17);
v_versionTags_3002_ = lean_ctor_get(v_cfg_2980_, 18);
v_description_3003_ = lean_ctor_get(v_cfg_2980_, 19);
v_keywords_3004_ = lean_ctor_get(v_cfg_2980_, 20);
v_homepage_3005_ = lean_ctor_get(v_cfg_2980_, 21);
v_license_3006_ = lean_ctor_get(v_cfg_2980_, 22);
v_licenseFiles_3007_ = lean_ctor_get(v_cfg_2980_, 23);
v_readmeFile_3008_ = lean_ctor_get(v_cfg_2980_, 24);
v_reservoir_3009_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3010_ = lean_ctor_get(v_cfg_2980_, 25);
v_restoreAllArtifacts_x3f_3011_ = lean_ctor_get(v_cfg_2980_, 26);
v_libPrefixOnWindows_3012_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29 + 4);
v_allowImportAll_3013_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3014_ = lean_ctor_get(v_cfg_2980_, 27);
v_checks_3015_ = lean_ctor_get(v_cfg_2980_, 28);
v_fixedToolchain_3016_ = lean_ctor_get_uint8(v_cfg_2980_, sizeof(void*)*29 + 6);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_cfg_2980_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3018_ = v_cfg_2980_;
v_isShared_3019_ = v_isSharedCheck_3024_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_checks_3015_);
lean_inc(v_builtinLint_x3f_3014_);
lean_inc(v_restoreAllArtifacts_x3f_3011_);
lean_inc(v_enableArtifactCache_x3f_3010_);
lean_inc(v_readmeFile_3008_);
lean_inc(v_licenseFiles_3007_);
lean_inc(v_license_3006_);
lean_inc(v_homepage_3005_);
lean_inc(v_keywords_3004_);
lean_inc(v_description_3003_);
lean_inc(v_versionTags_3002_);
lean_inc(v_version_3001_);
lean_inc(v_lintDriverArgs_3000_);
lean_inc(v_lintDriver_2999_);
lean_inc(v_testDriverArgs_2998_);
lean_inc(v_testDriver_2997_);
lean_inc(v_downloadCacheService_x3f_2996_);
lean_inc(v_buildArchive_2994_);
lean_inc(v_releaseRepo_2993_);
lean_inc(v_irDir_2992_);
lean_inc(v_binDir_2991_);
lean_inc(v_nativeLibDir_2990_);
lean_inc(v_leanLibDir_2989_);
lean_inc(v_buildDir_2988_);
lean_inc(v_srcDir_2987_);
lean_inc(v_moreGlobalServerArgs_2986_);
lean_inc(v_extraDepTargets_2984_);
lean_inc(v_toLeanConfig_2982_);
lean_inc(v_toWorkspaceConfig_2981_);
lean_dec(v_cfg_2980_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3024_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3020_ = lean_apply_1(v_f_2979_, v_homepage_3005_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 21, v___x_3020_);
v___x_3022_ = v___x_3018_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_toWorkspaceConfig_2981_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_toLeanConfig_2982_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_extraDepTargets_2984_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_moreGlobalServerArgs_2986_);
lean_ctor_set(v_reuseFailAlloc_3023_, 4, v_srcDir_2987_);
lean_ctor_set(v_reuseFailAlloc_3023_, 5, v_buildDir_2988_);
lean_ctor_set(v_reuseFailAlloc_3023_, 6, v_leanLibDir_2989_);
lean_ctor_set(v_reuseFailAlloc_3023_, 7, v_nativeLibDir_2990_);
lean_ctor_set(v_reuseFailAlloc_3023_, 8, v_binDir_2991_);
lean_ctor_set(v_reuseFailAlloc_3023_, 9, v_irDir_2992_);
lean_ctor_set(v_reuseFailAlloc_3023_, 10, v_releaseRepo_2993_);
lean_ctor_set(v_reuseFailAlloc_3023_, 11, v_buildArchive_2994_);
lean_ctor_set(v_reuseFailAlloc_3023_, 12, v_downloadCacheService_x3f_2996_);
lean_ctor_set(v_reuseFailAlloc_3023_, 13, v_testDriver_2997_);
lean_ctor_set(v_reuseFailAlloc_3023_, 14, v_testDriverArgs_2998_);
lean_ctor_set(v_reuseFailAlloc_3023_, 15, v_lintDriver_2999_);
lean_ctor_set(v_reuseFailAlloc_3023_, 16, v_lintDriverArgs_3000_);
lean_ctor_set(v_reuseFailAlloc_3023_, 17, v_version_3001_);
lean_ctor_set(v_reuseFailAlloc_3023_, 18, v_versionTags_3002_);
lean_ctor_set(v_reuseFailAlloc_3023_, 19, v_description_3003_);
lean_ctor_set(v_reuseFailAlloc_3023_, 20, v_keywords_3004_);
lean_ctor_set(v_reuseFailAlloc_3023_, 21, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3023_, 22, v_license_3006_);
lean_ctor_set(v_reuseFailAlloc_3023_, 23, v_licenseFiles_3007_);
lean_ctor_set(v_reuseFailAlloc_3023_, 24, v_readmeFile_3008_);
lean_ctor_set(v_reuseFailAlloc_3023_, 25, v_enableArtifactCache_x3f_3010_);
lean_ctor_set(v_reuseFailAlloc_3023_, 26, v_restoreAllArtifacts_x3f_3011_);
lean_ctor_set(v_reuseFailAlloc_3023_, 27, v_builtinLint_x3f_3014_);
lean_ctor_set(v_reuseFailAlloc_3023_, 28, v_checks_3015_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29, v_bootstrap_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29 + 1, v_precompileModules_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29 + 2, v_preferReleaseBuild_2995_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29 + 3, v_reservoir_3009_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3012_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29 + 5, v_allowImportAll_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*29 + 6, v_fixedToolchain_3016_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg(){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = ((lean_object*)(l_Lake_PackageConfig_homepage___proj___redArg___closed__3));
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___redArg___boxed(lean_object* v___dummy_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lake_PackageConfig_homepage___proj___redArg();
return v_res_3036_;
}
}
static lean_object* _init_l_Lake_PackageConfig_homepage___proj___closed__0(void){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lake_PackageConfig_homepage___proj___redArg();
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj(lean_object* v_p_3038_, lean_object* v_n_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage___proj___boxed(lean_object* v_p_3041_, lean_object* v_n_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lake_PackageConfig_homepage___proj(v_p_3041_, v_n_3042_);
lean_dec(v_n_3042_);
lean_dec(v_p_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg(){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___redArg___boxed(lean_object* v___dummy_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lake_PackageConfig_homepage_instConfigField___redArg();
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField(lean_object* v_p_3048_, lean_object* v_n_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_obj_once(&l_Lake_PackageConfig_homepage___proj___closed__0, &l_Lake_PackageConfig_homepage___proj___closed__0_once, _init_l_Lake_PackageConfig_homepage___proj___closed__0);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_homepage_instConfigField___boxed(lean_object* v_p_3051_, lean_object* v_n_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lake_PackageConfig_homepage_instConfigField(v_p_3051_, v_n_3052_);
lean_dec(v_n_3052_);
lean_dec(v_p_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0(lean_object* v_cfg_3054_){
_start:
{
lean_object* v_license_3055_; 
v_license_3055_ = lean_ctor_get(v_cfg_3054_, 22);
lean_inc_ref(v_license_3055_);
return v_license_3055_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__0___boxed(lean_object* v_cfg_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lake_PackageConfig_license___proj___redArg___lam__0(v_cfg_3056_);
lean_dec_ref(v_cfg_3056_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__1(lean_object* v_val_3058_, lean_object* v_cfg_3059_){
_start:
{
lean_object* v_toWorkspaceConfig_3060_; lean_object* v_toLeanConfig_3061_; uint8_t v_bootstrap_3062_; lean_object* v_extraDepTargets_3063_; uint8_t v_precompileModules_3064_; lean_object* v_moreGlobalServerArgs_3065_; lean_object* v_srcDir_3066_; lean_object* v_buildDir_3067_; lean_object* v_leanLibDir_3068_; lean_object* v_nativeLibDir_3069_; lean_object* v_binDir_3070_; lean_object* v_irDir_3071_; lean_object* v_releaseRepo_3072_; lean_object* v_buildArchive_3073_; uint8_t v_preferReleaseBuild_3074_; lean_object* v_downloadCacheService_x3f_3075_; lean_object* v_testDriver_3076_; lean_object* v_testDriverArgs_3077_; lean_object* v_lintDriver_3078_; lean_object* v_lintDriverArgs_3079_; lean_object* v_version_3080_; lean_object* v_versionTags_3081_; lean_object* v_description_3082_; lean_object* v_keywords_3083_; lean_object* v_homepage_3084_; lean_object* v_licenseFiles_3085_; lean_object* v_readmeFile_3086_; uint8_t v_reservoir_3087_; lean_object* v_enableArtifactCache_x3f_3088_; lean_object* v_restoreAllArtifacts_x3f_3089_; uint8_t v_libPrefixOnWindows_3090_; uint8_t v_allowImportAll_3091_; lean_object* v_builtinLint_x3f_3092_; lean_object* v_checks_3093_; uint8_t v_fixedToolchain_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
v_toWorkspaceConfig_3060_ = lean_ctor_get(v_cfg_3059_, 0);
v_toLeanConfig_3061_ = lean_ctor_get(v_cfg_3059_, 1);
v_bootstrap_3062_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29);
v_extraDepTargets_3063_ = lean_ctor_get(v_cfg_3059_, 2);
v_precompileModules_3064_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3065_ = lean_ctor_get(v_cfg_3059_, 3);
v_srcDir_3066_ = lean_ctor_get(v_cfg_3059_, 4);
v_buildDir_3067_ = lean_ctor_get(v_cfg_3059_, 5);
v_leanLibDir_3068_ = lean_ctor_get(v_cfg_3059_, 6);
v_nativeLibDir_3069_ = lean_ctor_get(v_cfg_3059_, 7);
v_binDir_3070_ = lean_ctor_get(v_cfg_3059_, 8);
v_irDir_3071_ = lean_ctor_get(v_cfg_3059_, 9);
v_releaseRepo_3072_ = lean_ctor_get(v_cfg_3059_, 10);
v_buildArchive_3073_ = lean_ctor_get(v_cfg_3059_, 11);
v_preferReleaseBuild_3074_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3075_ = lean_ctor_get(v_cfg_3059_, 12);
v_testDriver_3076_ = lean_ctor_get(v_cfg_3059_, 13);
v_testDriverArgs_3077_ = lean_ctor_get(v_cfg_3059_, 14);
v_lintDriver_3078_ = lean_ctor_get(v_cfg_3059_, 15);
v_lintDriverArgs_3079_ = lean_ctor_get(v_cfg_3059_, 16);
v_version_3080_ = lean_ctor_get(v_cfg_3059_, 17);
v_versionTags_3081_ = lean_ctor_get(v_cfg_3059_, 18);
v_description_3082_ = lean_ctor_get(v_cfg_3059_, 19);
v_keywords_3083_ = lean_ctor_get(v_cfg_3059_, 20);
v_homepage_3084_ = lean_ctor_get(v_cfg_3059_, 21);
v_licenseFiles_3085_ = lean_ctor_get(v_cfg_3059_, 23);
v_readmeFile_3086_ = lean_ctor_get(v_cfg_3059_, 24);
v_reservoir_3087_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3088_ = lean_ctor_get(v_cfg_3059_, 25);
v_restoreAllArtifacts_x3f_3089_ = lean_ctor_get(v_cfg_3059_, 26);
v_libPrefixOnWindows_3090_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29 + 4);
v_allowImportAll_3091_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3092_ = lean_ctor_get(v_cfg_3059_, 27);
v_checks_3093_ = lean_ctor_get(v_cfg_3059_, 28);
v_fixedToolchain_3094_ = lean_ctor_get_uint8(v_cfg_3059_, sizeof(void*)*29 + 6);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_cfg_3059_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v_cfg_3059_, 22);
lean_dec(v_unused_3102_);
v___x_3096_ = v_cfg_3059_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_checks_3093_);
lean_inc(v_builtinLint_x3f_3092_);
lean_inc(v_restoreAllArtifacts_x3f_3089_);
lean_inc(v_enableArtifactCache_x3f_3088_);
lean_inc(v_readmeFile_3086_);
lean_inc(v_licenseFiles_3085_);
lean_inc(v_homepage_3084_);
lean_inc(v_keywords_3083_);
lean_inc(v_description_3082_);
lean_inc(v_versionTags_3081_);
lean_inc(v_version_3080_);
lean_inc(v_lintDriverArgs_3079_);
lean_inc(v_lintDriver_3078_);
lean_inc(v_testDriverArgs_3077_);
lean_inc(v_testDriver_3076_);
lean_inc(v_downloadCacheService_x3f_3075_);
lean_inc(v_buildArchive_3073_);
lean_inc(v_releaseRepo_3072_);
lean_inc(v_irDir_3071_);
lean_inc(v_binDir_3070_);
lean_inc(v_nativeLibDir_3069_);
lean_inc(v_leanLibDir_3068_);
lean_inc(v_buildDir_3067_);
lean_inc(v_srcDir_3066_);
lean_inc(v_moreGlobalServerArgs_3065_);
lean_inc(v_extraDepTargets_3063_);
lean_inc(v_toLeanConfig_3061_);
lean_inc(v_toWorkspaceConfig_3060_);
lean_dec(v_cfg_3059_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 22, v_val_3058_);
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_toWorkspaceConfig_3060_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_toLeanConfig_3061_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_extraDepTargets_3063_);
lean_ctor_set(v_reuseFailAlloc_3100_, 3, v_moreGlobalServerArgs_3065_);
lean_ctor_set(v_reuseFailAlloc_3100_, 4, v_srcDir_3066_);
lean_ctor_set(v_reuseFailAlloc_3100_, 5, v_buildDir_3067_);
lean_ctor_set(v_reuseFailAlloc_3100_, 6, v_leanLibDir_3068_);
lean_ctor_set(v_reuseFailAlloc_3100_, 7, v_nativeLibDir_3069_);
lean_ctor_set(v_reuseFailAlloc_3100_, 8, v_binDir_3070_);
lean_ctor_set(v_reuseFailAlloc_3100_, 9, v_irDir_3071_);
lean_ctor_set(v_reuseFailAlloc_3100_, 10, v_releaseRepo_3072_);
lean_ctor_set(v_reuseFailAlloc_3100_, 11, v_buildArchive_3073_);
lean_ctor_set(v_reuseFailAlloc_3100_, 12, v_downloadCacheService_x3f_3075_);
lean_ctor_set(v_reuseFailAlloc_3100_, 13, v_testDriver_3076_);
lean_ctor_set(v_reuseFailAlloc_3100_, 14, v_testDriverArgs_3077_);
lean_ctor_set(v_reuseFailAlloc_3100_, 15, v_lintDriver_3078_);
lean_ctor_set(v_reuseFailAlloc_3100_, 16, v_lintDriverArgs_3079_);
lean_ctor_set(v_reuseFailAlloc_3100_, 17, v_version_3080_);
lean_ctor_set(v_reuseFailAlloc_3100_, 18, v_versionTags_3081_);
lean_ctor_set(v_reuseFailAlloc_3100_, 19, v_description_3082_);
lean_ctor_set(v_reuseFailAlloc_3100_, 20, v_keywords_3083_);
lean_ctor_set(v_reuseFailAlloc_3100_, 21, v_homepage_3084_);
lean_ctor_set(v_reuseFailAlloc_3100_, 22, v_val_3058_);
lean_ctor_set(v_reuseFailAlloc_3100_, 23, v_licenseFiles_3085_);
lean_ctor_set(v_reuseFailAlloc_3100_, 24, v_readmeFile_3086_);
lean_ctor_set(v_reuseFailAlloc_3100_, 25, v_enableArtifactCache_x3f_3088_);
lean_ctor_set(v_reuseFailAlloc_3100_, 26, v_restoreAllArtifacts_x3f_3089_);
lean_ctor_set(v_reuseFailAlloc_3100_, 27, v_builtinLint_x3f_3092_);
lean_ctor_set(v_reuseFailAlloc_3100_, 28, v_checks_3093_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29, v_bootstrap_3062_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29 + 1, v_precompileModules_3064_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3074_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29 + 3, v_reservoir_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3090_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29 + 5, v_allowImportAll_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3100_, sizeof(void*)*29 + 6, v_fixedToolchain_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___lam__2(lean_object* v_f_3103_, lean_object* v_cfg_3104_){
_start:
{
lean_object* v_toWorkspaceConfig_3105_; lean_object* v_toLeanConfig_3106_; uint8_t v_bootstrap_3107_; lean_object* v_extraDepTargets_3108_; uint8_t v_precompileModules_3109_; lean_object* v_moreGlobalServerArgs_3110_; lean_object* v_srcDir_3111_; lean_object* v_buildDir_3112_; lean_object* v_leanLibDir_3113_; lean_object* v_nativeLibDir_3114_; lean_object* v_binDir_3115_; lean_object* v_irDir_3116_; lean_object* v_releaseRepo_3117_; lean_object* v_buildArchive_3118_; uint8_t v_preferReleaseBuild_3119_; lean_object* v_downloadCacheService_x3f_3120_; lean_object* v_testDriver_3121_; lean_object* v_testDriverArgs_3122_; lean_object* v_lintDriver_3123_; lean_object* v_lintDriverArgs_3124_; lean_object* v_version_3125_; lean_object* v_versionTags_3126_; lean_object* v_description_3127_; lean_object* v_keywords_3128_; lean_object* v_homepage_3129_; lean_object* v_license_3130_; lean_object* v_licenseFiles_3131_; lean_object* v_readmeFile_3132_; uint8_t v_reservoir_3133_; lean_object* v_enableArtifactCache_x3f_3134_; lean_object* v_restoreAllArtifacts_x3f_3135_; uint8_t v_libPrefixOnWindows_3136_; uint8_t v_allowImportAll_3137_; lean_object* v_builtinLint_x3f_3138_; lean_object* v_checks_3139_; uint8_t v_fixedToolchain_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3148_; 
v_toWorkspaceConfig_3105_ = lean_ctor_get(v_cfg_3104_, 0);
v_toLeanConfig_3106_ = lean_ctor_get(v_cfg_3104_, 1);
v_bootstrap_3107_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29);
v_extraDepTargets_3108_ = lean_ctor_get(v_cfg_3104_, 2);
v_precompileModules_3109_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3110_ = lean_ctor_get(v_cfg_3104_, 3);
v_srcDir_3111_ = lean_ctor_get(v_cfg_3104_, 4);
v_buildDir_3112_ = lean_ctor_get(v_cfg_3104_, 5);
v_leanLibDir_3113_ = lean_ctor_get(v_cfg_3104_, 6);
v_nativeLibDir_3114_ = lean_ctor_get(v_cfg_3104_, 7);
v_binDir_3115_ = lean_ctor_get(v_cfg_3104_, 8);
v_irDir_3116_ = lean_ctor_get(v_cfg_3104_, 9);
v_releaseRepo_3117_ = lean_ctor_get(v_cfg_3104_, 10);
v_buildArchive_3118_ = lean_ctor_get(v_cfg_3104_, 11);
v_preferReleaseBuild_3119_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3120_ = lean_ctor_get(v_cfg_3104_, 12);
v_testDriver_3121_ = lean_ctor_get(v_cfg_3104_, 13);
v_testDriverArgs_3122_ = lean_ctor_get(v_cfg_3104_, 14);
v_lintDriver_3123_ = lean_ctor_get(v_cfg_3104_, 15);
v_lintDriverArgs_3124_ = lean_ctor_get(v_cfg_3104_, 16);
v_version_3125_ = lean_ctor_get(v_cfg_3104_, 17);
v_versionTags_3126_ = lean_ctor_get(v_cfg_3104_, 18);
v_description_3127_ = lean_ctor_get(v_cfg_3104_, 19);
v_keywords_3128_ = lean_ctor_get(v_cfg_3104_, 20);
v_homepage_3129_ = lean_ctor_get(v_cfg_3104_, 21);
v_license_3130_ = lean_ctor_get(v_cfg_3104_, 22);
v_licenseFiles_3131_ = lean_ctor_get(v_cfg_3104_, 23);
v_readmeFile_3132_ = lean_ctor_get(v_cfg_3104_, 24);
v_reservoir_3133_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3134_ = lean_ctor_get(v_cfg_3104_, 25);
v_restoreAllArtifacts_x3f_3135_ = lean_ctor_get(v_cfg_3104_, 26);
v_libPrefixOnWindows_3136_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29 + 4);
v_allowImportAll_3137_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3138_ = lean_ctor_get(v_cfg_3104_, 27);
v_checks_3139_ = lean_ctor_get(v_cfg_3104_, 28);
v_fixedToolchain_3140_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*29 + 6);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_cfg_3104_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3142_ = v_cfg_3104_;
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_checks_3139_);
lean_inc(v_builtinLint_x3f_3138_);
lean_inc(v_restoreAllArtifacts_x3f_3135_);
lean_inc(v_enableArtifactCache_x3f_3134_);
lean_inc(v_readmeFile_3132_);
lean_inc(v_licenseFiles_3131_);
lean_inc(v_license_3130_);
lean_inc(v_homepage_3129_);
lean_inc(v_keywords_3128_);
lean_inc(v_description_3127_);
lean_inc(v_versionTags_3126_);
lean_inc(v_version_3125_);
lean_inc(v_lintDriverArgs_3124_);
lean_inc(v_lintDriver_3123_);
lean_inc(v_testDriverArgs_3122_);
lean_inc(v_testDriver_3121_);
lean_inc(v_downloadCacheService_x3f_3120_);
lean_inc(v_buildArchive_3118_);
lean_inc(v_releaseRepo_3117_);
lean_inc(v_irDir_3116_);
lean_inc(v_binDir_3115_);
lean_inc(v_nativeLibDir_3114_);
lean_inc(v_leanLibDir_3113_);
lean_inc(v_buildDir_3112_);
lean_inc(v_srcDir_3111_);
lean_inc(v_moreGlobalServerArgs_3110_);
lean_inc(v_extraDepTargets_3108_);
lean_inc(v_toLeanConfig_3106_);
lean_inc(v_toWorkspaceConfig_3105_);
lean_dec(v_cfg_3104_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3144_ = lean_apply_1(v_f_3103_, v_license_3130_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 22, v___x_3144_);
v___x_3146_ = v___x_3142_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_toWorkspaceConfig_3105_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_toLeanConfig_3106_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_extraDepTargets_3108_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_moreGlobalServerArgs_3110_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_srcDir_3111_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v_buildDir_3112_);
lean_ctor_set(v_reuseFailAlloc_3147_, 6, v_leanLibDir_3113_);
lean_ctor_set(v_reuseFailAlloc_3147_, 7, v_nativeLibDir_3114_);
lean_ctor_set(v_reuseFailAlloc_3147_, 8, v_binDir_3115_);
lean_ctor_set(v_reuseFailAlloc_3147_, 9, v_irDir_3116_);
lean_ctor_set(v_reuseFailAlloc_3147_, 10, v_releaseRepo_3117_);
lean_ctor_set(v_reuseFailAlloc_3147_, 11, v_buildArchive_3118_);
lean_ctor_set(v_reuseFailAlloc_3147_, 12, v_downloadCacheService_x3f_3120_);
lean_ctor_set(v_reuseFailAlloc_3147_, 13, v_testDriver_3121_);
lean_ctor_set(v_reuseFailAlloc_3147_, 14, v_testDriverArgs_3122_);
lean_ctor_set(v_reuseFailAlloc_3147_, 15, v_lintDriver_3123_);
lean_ctor_set(v_reuseFailAlloc_3147_, 16, v_lintDriverArgs_3124_);
lean_ctor_set(v_reuseFailAlloc_3147_, 17, v_version_3125_);
lean_ctor_set(v_reuseFailAlloc_3147_, 18, v_versionTags_3126_);
lean_ctor_set(v_reuseFailAlloc_3147_, 19, v_description_3127_);
lean_ctor_set(v_reuseFailAlloc_3147_, 20, v_keywords_3128_);
lean_ctor_set(v_reuseFailAlloc_3147_, 21, v_homepage_3129_);
lean_ctor_set(v_reuseFailAlloc_3147_, 22, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3147_, 23, v_licenseFiles_3131_);
lean_ctor_set(v_reuseFailAlloc_3147_, 24, v_readmeFile_3132_);
lean_ctor_set(v_reuseFailAlloc_3147_, 25, v_enableArtifactCache_x3f_3134_);
lean_ctor_set(v_reuseFailAlloc_3147_, 26, v_restoreAllArtifacts_x3f_3135_);
lean_ctor_set(v_reuseFailAlloc_3147_, 27, v_builtinLint_x3f_3138_);
lean_ctor_set(v_reuseFailAlloc_3147_, 28, v_checks_3139_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29, v_bootstrap_3107_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29 + 1, v_precompileModules_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3119_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29 + 3, v_reservoir_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29 + 5, v_allowImportAll_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*29 + 6, v_fixedToolchain_3140_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg(){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = ((lean_object*)(l_Lake_PackageConfig_license___proj___redArg___closed__3));
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___redArg___boxed(lean_object* v___dummy_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lake_PackageConfig_license___proj___redArg();
return v_res_3160_;
}
}
static lean_object* _init_l_Lake_PackageConfig_license___proj___closed__0(void){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lake_PackageConfig_license___proj___redArg();
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj(lean_object* v_p_3162_, lean_object* v_n_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license___proj___boxed(lean_object* v_p_3165_, lean_object* v_n_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lake_PackageConfig_license___proj(v_p_3165_, v_n_3166_);
lean_dec(v_n_3166_);
lean_dec(v_p_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg(){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___redArg___boxed(lean_object* v___dummy_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lake_PackageConfig_license_instConfigField___redArg();
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField(lean_object* v_p_3172_, lean_object* v_n_3173_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_obj_once(&l_Lake_PackageConfig_license___proj___closed__0, &l_Lake_PackageConfig_license___proj___closed__0_once, _init_l_Lake_PackageConfig_license___proj___closed__0);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_license_instConfigField___boxed(lean_object* v_p_3175_, lean_object* v_n_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lake_PackageConfig_license_instConfigField(v_p_3175_, v_n_3176_);
lean_dec(v_n_3176_);
lean_dec(v_p_3175_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(lean_object* v_cfg_3178_){
_start:
{
lean_object* v_licenseFiles_3179_; 
v_licenseFiles_3179_ = lean_ctor_get(v_cfg_3178_, 23);
lean_inc_ref(v_licenseFiles_3179_);
return v_licenseFiles_3179_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0___boxed(lean_object* v_cfg_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__0(v_cfg_3180_);
lean_dec_ref(v_cfg_3180_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__1(lean_object* v_val_3182_, lean_object* v_cfg_3183_){
_start:
{
lean_object* v_toWorkspaceConfig_3184_; lean_object* v_toLeanConfig_3185_; uint8_t v_bootstrap_3186_; lean_object* v_extraDepTargets_3187_; uint8_t v_precompileModules_3188_; lean_object* v_moreGlobalServerArgs_3189_; lean_object* v_srcDir_3190_; lean_object* v_buildDir_3191_; lean_object* v_leanLibDir_3192_; lean_object* v_nativeLibDir_3193_; lean_object* v_binDir_3194_; lean_object* v_irDir_3195_; lean_object* v_releaseRepo_3196_; lean_object* v_buildArchive_3197_; uint8_t v_preferReleaseBuild_3198_; lean_object* v_downloadCacheService_x3f_3199_; lean_object* v_testDriver_3200_; lean_object* v_testDriverArgs_3201_; lean_object* v_lintDriver_3202_; lean_object* v_lintDriverArgs_3203_; lean_object* v_version_3204_; lean_object* v_versionTags_3205_; lean_object* v_description_3206_; lean_object* v_keywords_3207_; lean_object* v_homepage_3208_; lean_object* v_license_3209_; lean_object* v_readmeFile_3210_; uint8_t v_reservoir_3211_; lean_object* v_enableArtifactCache_x3f_3212_; lean_object* v_restoreAllArtifacts_x3f_3213_; uint8_t v_libPrefixOnWindows_3214_; uint8_t v_allowImportAll_3215_; lean_object* v_builtinLint_x3f_3216_; lean_object* v_checks_3217_; uint8_t v_fixedToolchain_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_toWorkspaceConfig_3184_ = lean_ctor_get(v_cfg_3183_, 0);
v_toLeanConfig_3185_ = lean_ctor_get(v_cfg_3183_, 1);
v_bootstrap_3186_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29);
v_extraDepTargets_3187_ = lean_ctor_get(v_cfg_3183_, 2);
v_precompileModules_3188_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3189_ = lean_ctor_get(v_cfg_3183_, 3);
v_srcDir_3190_ = lean_ctor_get(v_cfg_3183_, 4);
v_buildDir_3191_ = lean_ctor_get(v_cfg_3183_, 5);
v_leanLibDir_3192_ = lean_ctor_get(v_cfg_3183_, 6);
v_nativeLibDir_3193_ = lean_ctor_get(v_cfg_3183_, 7);
v_binDir_3194_ = lean_ctor_get(v_cfg_3183_, 8);
v_irDir_3195_ = lean_ctor_get(v_cfg_3183_, 9);
v_releaseRepo_3196_ = lean_ctor_get(v_cfg_3183_, 10);
v_buildArchive_3197_ = lean_ctor_get(v_cfg_3183_, 11);
v_preferReleaseBuild_3198_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3199_ = lean_ctor_get(v_cfg_3183_, 12);
v_testDriver_3200_ = lean_ctor_get(v_cfg_3183_, 13);
v_testDriverArgs_3201_ = lean_ctor_get(v_cfg_3183_, 14);
v_lintDriver_3202_ = lean_ctor_get(v_cfg_3183_, 15);
v_lintDriverArgs_3203_ = lean_ctor_get(v_cfg_3183_, 16);
v_version_3204_ = lean_ctor_get(v_cfg_3183_, 17);
v_versionTags_3205_ = lean_ctor_get(v_cfg_3183_, 18);
v_description_3206_ = lean_ctor_get(v_cfg_3183_, 19);
v_keywords_3207_ = lean_ctor_get(v_cfg_3183_, 20);
v_homepage_3208_ = lean_ctor_get(v_cfg_3183_, 21);
v_license_3209_ = lean_ctor_get(v_cfg_3183_, 22);
v_readmeFile_3210_ = lean_ctor_get(v_cfg_3183_, 24);
v_reservoir_3211_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3212_ = lean_ctor_get(v_cfg_3183_, 25);
v_restoreAllArtifacts_x3f_3213_ = lean_ctor_get(v_cfg_3183_, 26);
v_libPrefixOnWindows_3214_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29 + 4);
v_allowImportAll_3215_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3216_ = lean_ctor_get(v_cfg_3183_, 27);
v_checks_3217_ = lean_ctor_get(v_cfg_3183_, 28);
v_fixedToolchain_3218_ = lean_ctor_get_uint8(v_cfg_3183_, sizeof(void*)*29 + 6);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_cfg_3183_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v_cfg_3183_, 23);
lean_dec(v_unused_3226_);
v___x_3220_ = v_cfg_3183_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_checks_3217_);
lean_inc(v_builtinLint_x3f_3216_);
lean_inc(v_restoreAllArtifacts_x3f_3213_);
lean_inc(v_enableArtifactCache_x3f_3212_);
lean_inc(v_readmeFile_3210_);
lean_inc(v_license_3209_);
lean_inc(v_homepage_3208_);
lean_inc(v_keywords_3207_);
lean_inc(v_description_3206_);
lean_inc(v_versionTags_3205_);
lean_inc(v_version_3204_);
lean_inc(v_lintDriverArgs_3203_);
lean_inc(v_lintDriver_3202_);
lean_inc(v_testDriverArgs_3201_);
lean_inc(v_testDriver_3200_);
lean_inc(v_downloadCacheService_x3f_3199_);
lean_inc(v_buildArchive_3197_);
lean_inc(v_releaseRepo_3196_);
lean_inc(v_irDir_3195_);
lean_inc(v_binDir_3194_);
lean_inc(v_nativeLibDir_3193_);
lean_inc(v_leanLibDir_3192_);
lean_inc(v_buildDir_3191_);
lean_inc(v_srcDir_3190_);
lean_inc(v_moreGlobalServerArgs_3189_);
lean_inc(v_extraDepTargets_3187_);
lean_inc(v_toLeanConfig_3185_);
lean_inc(v_toWorkspaceConfig_3184_);
lean_dec(v_cfg_3183_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 23, v_val_3182_);
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_toWorkspaceConfig_3184_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_toLeanConfig_3185_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_extraDepTargets_3187_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_moreGlobalServerArgs_3189_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_srcDir_3190_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v_buildDir_3191_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v_leanLibDir_3192_);
lean_ctor_set(v_reuseFailAlloc_3224_, 7, v_nativeLibDir_3193_);
lean_ctor_set(v_reuseFailAlloc_3224_, 8, v_binDir_3194_);
lean_ctor_set(v_reuseFailAlloc_3224_, 9, v_irDir_3195_);
lean_ctor_set(v_reuseFailAlloc_3224_, 10, v_releaseRepo_3196_);
lean_ctor_set(v_reuseFailAlloc_3224_, 11, v_buildArchive_3197_);
lean_ctor_set(v_reuseFailAlloc_3224_, 12, v_downloadCacheService_x3f_3199_);
lean_ctor_set(v_reuseFailAlloc_3224_, 13, v_testDriver_3200_);
lean_ctor_set(v_reuseFailAlloc_3224_, 14, v_testDriverArgs_3201_);
lean_ctor_set(v_reuseFailAlloc_3224_, 15, v_lintDriver_3202_);
lean_ctor_set(v_reuseFailAlloc_3224_, 16, v_lintDriverArgs_3203_);
lean_ctor_set(v_reuseFailAlloc_3224_, 17, v_version_3204_);
lean_ctor_set(v_reuseFailAlloc_3224_, 18, v_versionTags_3205_);
lean_ctor_set(v_reuseFailAlloc_3224_, 19, v_description_3206_);
lean_ctor_set(v_reuseFailAlloc_3224_, 20, v_keywords_3207_);
lean_ctor_set(v_reuseFailAlloc_3224_, 21, v_homepage_3208_);
lean_ctor_set(v_reuseFailAlloc_3224_, 22, v_license_3209_);
lean_ctor_set(v_reuseFailAlloc_3224_, 23, v_val_3182_);
lean_ctor_set(v_reuseFailAlloc_3224_, 24, v_readmeFile_3210_);
lean_ctor_set(v_reuseFailAlloc_3224_, 25, v_enableArtifactCache_x3f_3212_);
lean_ctor_set(v_reuseFailAlloc_3224_, 26, v_restoreAllArtifacts_x3f_3213_);
lean_ctor_set(v_reuseFailAlloc_3224_, 27, v_builtinLint_x3f_3216_);
lean_ctor_set(v_reuseFailAlloc_3224_, 28, v_checks_3217_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29, v_bootstrap_3186_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29 + 1, v_precompileModules_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29 + 3, v_reservoir_3211_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3214_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29 + 5, v_allowImportAll_3215_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*29 + 6, v_fixedToolchain_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__2(lean_object* v_f_3227_, lean_object* v_cfg_3228_){
_start:
{
lean_object* v_toWorkspaceConfig_3229_; lean_object* v_toLeanConfig_3230_; uint8_t v_bootstrap_3231_; lean_object* v_extraDepTargets_3232_; uint8_t v_precompileModules_3233_; lean_object* v_moreGlobalServerArgs_3234_; lean_object* v_srcDir_3235_; lean_object* v_buildDir_3236_; lean_object* v_leanLibDir_3237_; lean_object* v_nativeLibDir_3238_; lean_object* v_binDir_3239_; lean_object* v_irDir_3240_; lean_object* v_releaseRepo_3241_; lean_object* v_buildArchive_3242_; uint8_t v_preferReleaseBuild_3243_; lean_object* v_downloadCacheService_x3f_3244_; lean_object* v_testDriver_3245_; lean_object* v_testDriverArgs_3246_; lean_object* v_lintDriver_3247_; lean_object* v_lintDriverArgs_3248_; lean_object* v_version_3249_; lean_object* v_versionTags_3250_; lean_object* v_description_3251_; lean_object* v_keywords_3252_; lean_object* v_homepage_3253_; lean_object* v_license_3254_; lean_object* v_licenseFiles_3255_; lean_object* v_readmeFile_3256_; uint8_t v_reservoir_3257_; lean_object* v_enableArtifactCache_x3f_3258_; lean_object* v_restoreAllArtifacts_x3f_3259_; uint8_t v_libPrefixOnWindows_3260_; uint8_t v_allowImportAll_3261_; lean_object* v_builtinLint_x3f_3262_; lean_object* v_checks_3263_; uint8_t v_fixedToolchain_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3272_; 
v_toWorkspaceConfig_3229_ = lean_ctor_get(v_cfg_3228_, 0);
v_toLeanConfig_3230_ = lean_ctor_get(v_cfg_3228_, 1);
v_bootstrap_3231_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29);
v_extraDepTargets_3232_ = lean_ctor_get(v_cfg_3228_, 2);
v_precompileModules_3233_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3234_ = lean_ctor_get(v_cfg_3228_, 3);
v_srcDir_3235_ = lean_ctor_get(v_cfg_3228_, 4);
v_buildDir_3236_ = lean_ctor_get(v_cfg_3228_, 5);
v_leanLibDir_3237_ = lean_ctor_get(v_cfg_3228_, 6);
v_nativeLibDir_3238_ = lean_ctor_get(v_cfg_3228_, 7);
v_binDir_3239_ = lean_ctor_get(v_cfg_3228_, 8);
v_irDir_3240_ = lean_ctor_get(v_cfg_3228_, 9);
v_releaseRepo_3241_ = lean_ctor_get(v_cfg_3228_, 10);
v_buildArchive_3242_ = lean_ctor_get(v_cfg_3228_, 11);
v_preferReleaseBuild_3243_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3244_ = lean_ctor_get(v_cfg_3228_, 12);
v_testDriver_3245_ = lean_ctor_get(v_cfg_3228_, 13);
v_testDriverArgs_3246_ = lean_ctor_get(v_cfg_3228_, 14);
v_lintDriver_3247_ = lean_ctor_get(v_cfg_3228_, 15);
v_lintDriverArgs_3248_ = lean_ctor_get(v_cfg_3228_, 16);
v_version_3249_ = lean_ctor_get(v_cfg_3228_, 17);
v_versionTags_3250_ = lean_ctor_get(v_cfg_3228_, 18);
v_description_3251_ = lean_ctor_get(v_cfg_3228_, 19);
v_keywords_3252_ = lean_ctor_get(v_cfg_3228_, 20);
v_homepage_3253_ = lean_ctor_get(v_cfg_3228_, 21);
v_license_3254_ = lean_ctor_get(v_cfg_3228_, 22);
v_licenseFiles_3255_ = lean_ctor_get(v_cfg_3228_, 23);
v_readmeFile_3256_ = lean_ctor_get(v_cfg_3228_, 24);
v_reservoir_3257_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3258_ = lean_ctor_get(v_cfg_3228_, 25);
v_restoreAllArtifacts_x3f_3259_ = lean_ctor_get(v_cfg_3228_, 26);
v_libPrefixOnWindows_3260_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29 + 4);
v_allowImportAll_3261_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3262_ = lean_ctor_get(v_cfg_3228_, 27);
v_checks_3263_ = lean_ctor_get(v_cfg_3228_, 28);
v_fixedToolchain_3264_ = lean_ctor_get_uint8(v_cfg_3228_, sizeof(void*)*29 + 6);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_cfg_3228_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3266_ = v_cfg_3228_;
v_isShared_3267_ = v_isSharedCheck_3272_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_checks_3263_);
lean_inc(v_builtinLint_x3f_3262_);
lean_inc(v_restoreAllArtifacts_x3f_3259_);
lean_inc(v_enableArtifactCache_x3f_3258_);
lean_inc(v_readmeFile_3256_);
lean_inc(v_licenseFiles_3255_);
lean_inc(v_license_3254_);
lean_inc(v_homepage_3253_);
lean_inc(v_keywords_3252_);
lean_inc(v_description_3251_);
lean_inc(v_versionTags_3250_);
lean_inc(v_version_3249_);
lean_inc(v_lintDriverArgs_3248_);
lean_inc(v_lintDriver_3247_);
lean_inc(v_testDriverArgs_3246_);
lean_inc(v_testDriver_3245_);
lean_inc(v_downloadCacheService_x3f_3244_);
lean_inc(v_buildArchive_3242_);
lean_inc(v_releaseRepo_3241_);
lean_inc(v_irDir_3240_);
lean_inc(v_binDir_3239_);
lean_inc(v_nativeLibDir_3238_);
lean_inc(v_leanLibDir_3237_);
lean_inc(v_buildDir_3236_);
lean_inc(v_srcDir_3235_);
lean_inc(v_moreGlobalServerArgs_3234_);
lean_inc(v_extraDepTargets_3232_);
lean_inc(v_toLeanConfig_3230_);
lean_inc(v_toWorkspaceConfig_3229_);
lean_dec(v_cfg_3228_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3272_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = lean_apply_1(v_f_3227_, v_licenseFiles_3255_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 23, v___x_3268_);
v___x_3270_ = v___x_3266_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_toWorkspaceConfig_3229_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_toLeanConfig_3230_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_extraDepTargets_3232_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_moreGlobalServerArgs_3234_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_srcDir_3235_);
lean_ctor_set(v_reuseFailAlloc_3271_, 5, v_buildDir_3236_);
lean_ctor_set(v_reuseFailAlloc_3271_, 6, v_leanLibDir_3237_);
lean_ctor_set(v_reuseFailAlloc_3271_, 7, v_nativeLibDir_3238_);
lean_ctor_set(v_reuseFailAlloc_3271_, 8, v_binDir_3239_);
lean_ctor_set(v_reuseFailAlloc_3271_, 9, v_irDir_3240_);
lean_ctor_set(v_reuseFailAlloc_3271_, 10, v_releaseRepo_3241_);
lean_ctor_set(v_reuseFailAlloc_3271_, 11, v_buildArchive_3242_);
lean_ctor_set(v_reuseFailAlloc_3271_, 12, v_downloadCacheService_x3f_3244_);
lean_ctor_set(v_reuseFailAlloc_3271_, 13, v_testDriver_3245_);
lean_ctor_set(v_reuseFailAlloc_3271_, 14, v_testDriverArgs_3246_);
lean_ctor_set(v_reuseFailAlloc_3271_, 15, v_lintDriver_3247_);
lean_ctor_set(v_reuseFailAlloc_3271_, 16, v_lintDriverArgs_3248_);
lean_ctor_set(v_reuseFailAlloc_3271_, 17, v_version_3249_);
lean_ctor_set(v_reuseFailAlloc_3271_, 18, v_versionTags_3250_);
lean_ctor_set(v_reuseFailAlloc_3271_, 19, v_description_3251_);
lean_ctor_set(v_reuseFailAlloc_3271_, 20, v_keywords_3252_);
lean_ctor_set(v_reuseFailAlloc_3271_, 21, v_homepage_3253_);
lean_ctor_set(v_reuseFailAlloc_3271_, 22, v_license_3254_);
lean_ctor_set(v_reuseFailAlloc_3271_, 23, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3271_, 24, v_readmeFile_3256_);
lean_ctor_set(v_reuseFailAlloc_3271_, 25, v_enableArtifactCache_x3f_3258_);
lean_ctor_set(v_reuseFailAlloc_3271_, 26, v_restoreAllArtifacts_x3f_3259_);
lean_ctor_set(v_reuseFailAlloc_3271_, 27, v_builtinLint_x3f_3262_);
lean_ctor_set(v_reuseFailAlloc_3271_, 28, v_checks_3263_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29, v_bootstrap_3231_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29 + 1, v_precompileModules_3233_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3243_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29 + 3, v_reservoir_3257_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3260_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29 + 5, v_allowImportAll_3261_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*29 + 6, v_fixedToolchain_3264_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = lean_unsigned_to_nat(1u);
v___x_3275_ = lean_mk_empty_array_with_capacity(v___x_3274_);
lean_dec_ref(v___x_3275_);
v___x_3276_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3___boxed(lean_object* v_x_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lake_PackageConfig_licenseFiles___proj___redArg___lam__3(v_x_3277_);
lean_dec_ref(v_x_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg(){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = ((lean_object*)(l_Lake_PackageConfig_licenseFiles___proj___redArg___closed__4));
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___redArg___boxed(lean_object* v___dummy_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
return v_res_3291_;
}
}
static lean_object* _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0(void){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lake_PackageConfig_licenseFiles___proj___redArg();
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj(lean_object* v_p_3293_, lean_object* v_n_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles___proj___boxed(lean_object* v_p_3296_, lean_object* v_n_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lake_PackageConfig_licenseFiles___proj(v_p_3296_, v_n_3297_);
lean_dec(v_n_3297_);
lean_dec(v_p_3296_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg(){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___redArg___boxed(lean_object* v___dummy_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lake_PackageConfig_licenseFiles_instConfigField___redArg();
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField(lean_object* v_p_3303_, lean_object* v_n_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_obj_once(&l_Lake_PackageConfig_licenseFiles___proj___closed__0, &l_Lake_PackageConfig_licenseFiles___proj___closed__0_once, _init_l_Lake_PackageConfig_licenseFiles___proj___closed__0);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_licenseFiles_instConfigField___boxed(lean_object* v_p_3306_, lean_object* v_n_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lake_PackageConfig_licenseFiles_instConfigField(v_p_3306_, v_n_3307_);
lean_dec(v_n_3307_);
lean_dec(v_p_3306_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(lean_object* v_cfg_3309_){
_start:
{
lean_object* v_readmeFile_3310_; 
v_readmeFile_3310_ = lean_ctor_get(v_cfg_3309_, 24);
lean_inc_ref(v_readmeFile_3310_);
return v_readmeFile_3310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0___boxed(lean_object* v_cfg_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lake_PackageConfig_readmeFile___proj___redArg___lam__0(v_cfg_3311_);
lean_dec_ref(v_cfg_3311_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__1(lean_object* v_val_3313_, lean_object* v_cfg_3314_){
_start:
{
lean_object* v_toWorkspaceConfig_3315_; lean_object* v_toLeanConfig_3316_; uint8_t v_bootstrap_3317_; lean_object* v_extraDepTargets_3318_; uint8_t v_precompileModules_3319_; lean_object* v_moreGlobalServerArgs_3320_; lean_object* v_srcDir_3321_; lean_object* v_buildDir_3322_; lean_object* v_leanLibDir_3323_; lean_object* v_nativeLibDir_3324_; lean_object* v_binDir_3325_; lean_object* v_irDir_3326_; lean_object* v_releaseRepo_3327_; lean_object* v_buildArchive_3328_; uint8_t v_preferReleaseBuild_3329_; lean_object* v_downloadCacheService_x3f_3330_; lean_object* v_testDriver_3331_; lean_object* v_testDriverArgs_3332_; lean_object* v_lintDriver_3333_; lean_object* v_lintDriverArgs_3334_; lean_object* v_version_3335_; lean_object* v_versionTags_3336_; lean_object* v_description_3337_; lean_object* v_keywords_3338_; lean_object* v_homepage_3339_; lean_object* v_license_3340_; lean_object* v_licenseFiles_3341_; uint8_t v_reservoir_3342_; lean_object* v_enableArtifactCache_x3f_3343_; lean_object* v_restoreAllArtifacts_x3f_3344_; uint8_t v_libPrefixOnWindows_3345_; uint8_t v_allowImportAll_3346_; lean_object* v_builtinLint_x3f_3347_; lean_object* v_checks_3348_; uint8_t v_fixedToolchain_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_toWorkspaceConfig_3315_ = lean_ctor_get(v_cfg_3314_, 0);
v_toLeanConfig_3316_ = lean_ctor_get(v_cfg_3314_, 1);
v_bootstrap_3317_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29);
v_extraDepTargets_3318_ = lean_ctor_get(v_cfg_3314_, 2);
v_precompileModules_3319_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3320_ = lean_ctor_get(v_cfg_3314_, 3);
v_srcDir_3321_ = lean_ctor_get(v_cfg_3314_, 4);
v_buildDir_3322_ = lean_ctor_get(v_cfg_3314_, 5);
v_leanLibDir_3323_ = lean_ctor_get(v_cfg_3314_, 6);
v_nativeLibDir_3324_ = lean_ctor_get(v_cfg_3314_, 7);
v_binDir_3325_ = lean_ctor_get(v_cfg_3314_, 8);
v_irDir_3326_ = lean_ctor_get(v_cfg_3314_, 9);
v_releaseRepo_3327_ = lean_ctor_get(v_cfg_3314_, 10);
v_buildArchive_3328_ = lean_ctor_get(v_cfg_3314_, 11);
v_preferReleaseBuild_3329_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3330_ = lean_ctor_get(v_cfg_3314_, 12);
v_testDriver_3331_ = lean_ctor_get(v_cfg_3314_, 13);
v_testDriverArgs_3332_ = lean_ctor_get(v_cfg_3314_, 14);
v_lintDriver_3333_ = lean_ctor_get(v_cfg_3314_, 15);
v_lintDriverArgs_3334_ = lean_ctor_get(v_cfg_3314_, 16);
v_version_3335_ = lean_ctor_get(v_cfg_3314_, 17);
v_versionTags_3336_ = lean_ctor_get(v_cfg_3314_, 18);
v_description_3337_ = lean_ctor_get(v_cfg_3314_, 19);
v_keywords_3338_ = lean_ctor_get(v_cfg_3314_, 20);
v_homepage_3339_ = lean_ctor_get(v_cfg_3314_, 21);
v_license_3340_ = lean_ctor_get(v_cfg_3314_, 22);
v_licenseFiles_3341_ = lean_ctor_get(v_cfg_3314_, 23);
v_reservoir_3342_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3343_ = lean_ctor_get(v_cfg_3314_, 25);
v_restoreAllArtifacts_x3f_3344_ = lean_ctor_get(v_cfg_3314_, 26);
v_libPrefixOnWindows_3345_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29 + 4);
v_allowImportAll_3346_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3347_ = lean_ctor_get(v_cfg_3314_, 27);
v_checks_3348_ = lean_ctor_get(v_cfg_3314_, 28);
v_fixedToolchain_3349_ = lean_ctor_get_uint8(v_cfg_3314_, sizeof(void*)*29 + 6);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_cfg_3314_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v_cfg_3314_, 24);
lean_dec(v_unused_3357_);
v___x_3351_ = v_cfg_3314_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_checks_3348_);
lean_inc(v_builtinLint_x3f_3347_);
lean_inc(v_restoreAllArtifacts_x3f_3344_);
lean_inc(v_enableArtifactCache_x3f_3343_);
lean_inc(v_licenseFiles_3341_);
lean_inc(v_license_3340_);
lean_inc(v_homepage_3339_);
lean_inc(v_keywords_3338_);
lean_inc(v_description_3337_);
lean_inc(v_versionTags_3336_);
lean_inc(v_version_3335_);
lean_inc(v_lintDriverArgs_3334_);
lean_inc(v_lintDriver_3333_);
lean_inc(v_testDriverArgs_3332_);
lean_inc(v_testDriver_3331_);
lean_inc(v_downloadCacheService_x3f_3330_);
lean_inc(v_buildArchive_3328_);
lean_inc(v_releaseRepo_3327_);
lean_inc(v_irDir_3326_);
lean_inc(v_binDir_3325_);
lean_inc(v_nativeLibDir_3324_);
lean_inc(v_leanLibDir_3323_);
lean_inc(v_buildDir_3322_);
lean_inc(v_srcDir_3321_);
lean_inc(v_moreGlobalServerArgs_3320_);
lean_inc(v_extraDepTargets_3318_);
lean_inc(v_toLeanConfig_3316_);
lean_inc(v_toWorkspaceConfig_3315_);
lean_dec(v_cfg_3314_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 24, v_val_3313_);
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_toWorkspaceConfig_3315_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_toLeanConfig_3316_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_extraDepTargets_3318_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_moreGlobalServerArgs_3320_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_srcDir_3321_);
lean_ctor_set(v_reuseFailAlloc_3355_, 5, v_buildDir_3322_);
lean_ctor_set(v_reuseFailAlloc_3355_, 6, v_leanLibDir_3323_);
lean_ctor_set(v_reuseFailAlloc_3355_, 7, v_nativeLibDir_3324_);
lean_ctor_set(v_reuseFailAlloc_3355_, 8, v_binDir_3325_);
lean_ctor_set(v_reuseFailAlloc_3355_, 9, v_irDir_3326_);
lean_ctor_set(v_reuseFailAlloc_3355_, 10, v_releaseRepo_3327_);
lean_ctor_set(v_reuseFailAlloc_3355_, 11, v_buildArchive_3328_);
lean_ctor_set(v_reuseFailAlloc_3355_, 12, v_downloadCacheService_x3f_3330_);
lean_ctor_set(v_reuseFailAlloc_3355_, 13, v_testDriver_3331_);
lean_ctor_set(v_reuseFailAlloc_3355_, 14, v_testDriverArgs_3332_);
lean_ctor_set(v_reuseFailAlloc_3355_, 15, v_lintDriver_3333_);
lean_ctor_set(v_reuseFailAlloc_3355_, 16, v_lintDriverArgs_3334_);
lean_ctor_set(v_reuseFailAlloc_3355_, 17, v_version_3335_);
lean_ctor_set(v_reuseFailAlloc_3355_, 18, v_versionTags_3336_);
lean_ctor_set(v_reuseFailAlloc_3355_, 19, v_description_3337_);
lean_ctor_set(v_reuseFailAlloc_3355_, 20, v_keywords_3338_);
lean_ctor_set(v_reuseFailAlloc_3355_, 21, v_homepage_3339_);
lean_ctor_set(v_reuseFailAlloc_3355_, 22, v_license_3340_);
lean_ctor_set(v_reuseFailAlloc_3355_, 23, v_licenseFiles_3341_);
lean_ctor_set(v_reuseFailAlloc_3355_, 24, v_val_3313_);
lean_ctor_set(v_reuseFailAlloc_3355_, 25, v_enableArtifactCache_x3f_3343_);
lean_ctor_set(v_reuseFailAlloc_3355_, 26, v_restoreAllArtifacts_x3f_3344_);
lean_ctor_set(v_reuseFailAlloc_3355_, 27, v_builtinLint_x3f_3347_);
lean_ctor_set(v_reuseFailAlloc_3355_, 28, v_checks_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29, v_bootstrap_3317_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29 + 1, v_precompileModules_3319_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3329_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29 + 3, v_reservoir_3342_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3345_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29 + 5, v_allowImportAll_3346_);
lean_ctor_set_uint8(v_reuseFailAlloc_3355_, sizeof(void*)*29 + 6, v_fixedToolchain_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__2(lean_object* v_f_3358_, lean_object* v_cfg_3359_){
_start:
{
lean_object* v_toWorkspaceConfig_3360_; lean_object* v_toLeanConfig_3361_; uint8_t v_bootstrap_3362_; lean_object* v_extraDepTargets_3363_; uint8_t v_precompileModules_3364_; lean_object* v_moreGlobalServerArgs_3365_; lean_object* v_srcDir_3366_; lean_object* v_buildDir_3367_; lean_object* v_leanLibDir_3368_; lean_object* v_nativeLibDir_3369_; lean_object* v_binDir_3370_; lean_object* v_irDir_3371_; lean_object* v_releaseRepo_3372_; lean_object* v_buildArchive_3373_; uint8_t v_preferReleaseBuild_3374_; lean_object* v_downloadCacheService_x3f_3375_; lean_object* v_testDriver_3376_; lean_object* v_testDriverArgs_3377_; lean_object* v_lintDriver_3378_; lean_object* v_lintDriverArgs_3379_; lean_object* v_version_3380_; lean_object* v_versionTags_3381_; lean_object* v_description_3382_; lean_object* v_keywords_3383_; lean_object* v_homepage_3384_; lean_object* v_license_3385_; lean_object* v_licenseFiles_3386_; lean_object* v_readmeFile_3387_; uint8_t v_reservoir_3388_; lean_object* v_enableArtifactCache_x3f_3389_; lean_object* v_restoreAllArtifacts_x3f_3390_; uint8_t v_libPrefixOnWindows_3391_; uint8_t v_allowImportAll_3392_; lean_object* v_builtinLint_x3f_3393_; lean_object* v_checks_3394_; uint8_t v_fixedToolchain_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3403_; 
v_toWorkspaceConfig_3360_ = lean_ctor_get(v_cfg_3359_, 0);
v_toLeanConfig_3361_ = lean_ctor_get(v_cfg_3359_, 1);
v_bootstrap_3362_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29);
v_extraDepTargets_3363_ = lean_ctor_get(v_cfg_3359_, 2);
v_precompileModules_3364_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3365_ = lean_ctor_get(v_cfg_3359_, 3);
v_srcDir_3366_ = lean_ctor_get(v_cfg_3359_, 4);
v_buildDir_3367_ = lean_ctor_get(v_cfg_3359_, 5);
v_leanLibDir_3368_ = lean_ctor_get(v_cfg_3359_, 6);
v_nativeLibDir_3369_ = lean_ctor_get(v_cfg_3359_, 7);
v_binDir_3370_ = lean_ctor_get(v_cfg_3359_, 8);
v_irDir_3371_ = lean_ctor_get(v_cfg_3359_, 9);
v_releaseRepo_3372_ = lean_ctor_get(v_cfg_3359_, 10);
v_buildArchive_3373_ = lean_ctor_get(v_cfg_3359_, 11);
v_preferReleaseBuild_3374_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3375_ = lean_ctor_get(v_cfg_3359_, 12);
v_testDriver_3376_ = lean_ctor_get(v_cfg_3359_, 13);
v_testDriverArgs_3377_ = lean_ctor_get(v_cfg_3359_, 14);
v_lintDriver_3378_ = lean_ctor_get(v_cfg_3359_, 15);
v_lintDriverArgs_3379_ = lean_ctor_get(v_cfg_3359_, 16);
v_version_3380_ = lean_ctor_get(v_cfg_3359_, 17);
v_versionTags_3381_ = lean_ctor_get(v_cfg_3359_, 18);
v_description_3382_ = lean_ctor_get(v_cfg_3359_, 19);
v_keywords_3383_ = lean_ctor_get(v_cfg_3359_, 20);
v_homepage_3384_ = lean_ctor_get(v_cfg_3359_, 21);
v_license_3385_ = lean_ctor_get(v_cfg_3359_, 22);
v_licenseFiles_3386_ = lean_ctor_get(v_cfg_3359_, 23);
v_readmeFile_3387_ = lean_ctor_get(v_cfg_3359_, 24);
v_reservoir_3388_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3389_ = lean_ctor_get(v_cfg_3359_, 25);
v_restoreAllArtifacts_x3f_3390_ = lean_ctor_get(v_cfg_3359_, 26);
v_libPrefixOnWindows_3391_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29 + 4);
v_allowImportAll_3392_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3393_ = lean_ctor_get(v_cfg_3359_, 27);
v_checks_3394_ = lean_ctor_get(v_cfg_3359_, 28);
v_fixedToolchain_3395_ = lean_ctor_get_uint8(v_cfg_3359_, sizeof(void*)*29 + 6);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_cfg_3359_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3397_ = v_cfg_3359_;
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_checks_3394_);
lean_inc(v_builtinLint_x3f_3393_);
lean_inc(v_restoreAllArtifacts_x3f_3390_);
lean_inc(v_enableArtifactCache_x3f_3389_);
lean_inc(v_readmeFile_3387_);
lean_inc(v_licenseFiles_3386_);
lean_inc(v_license_3385_);
lean_inc(v_homepage_3384_);
lean_inc(v_keywords_3383_);
lean_inc(v_description_3382_);
lean_inc(v_versionTags_3381_);
lean_inc(v_version_3380_);
lean_inc(v_lintDriverArgs_3379_);
lean_inc(v_lintDriver_3378_);
lean_inc(v_testDriverArgs_3377_);
lean_inc(v_testDriver_3376_);
lean_inc(v_downloadCacheService_x3f_3375_);
lean_inc(v_buildArchive_3373_);
lean_inc(v_releaseRepo_3372_);
lean_inc(v_irDir_3371_);
lean_inc(v_binDir_3370_);
lean_inc(v_nativeLibDir_3369_);
lean_inc(v_leanLibDir_3368_);
lean_inc(v_buildDir_3367_);
lean_inc(v_srcDir_3366_);
lean_inc(v_moreGlobalServerArgs_3365_);
lean_inc(v_extraDepTargets_3363_);
lean_inc(v_toLeanConfig_3361_);
lean_inc(v_toWorkspaceConfig_3360_);
lean_dec(v_cfg_3359_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_apply_1(v_f_3358_, v_readmeFile_3387_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 24, v___x_3399_);
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_toWorkspaceConfig_3360_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_toLeanConfig_3361_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_extraDepTargets_3363_);
lean_ctor_set(v_reuseFailAlloc_3402_, 3, v_moreGlobalServerArgs_3365_);
lean_ctor_set(v_reuseFailAlloc_3402_, 4, v_srcDir_3366_);
lean_ctor_set(v_reuseFailAlloc_3402_, 5, v_buildDir_3367_);
lean_ctor_set(v_reuseFailAlloc_3402_, 6, v_leanLibDir_3368_);
lean_ctor_set(v_reuseFailAlloc_3402_, 7, v_nativeLibDir_3369_);
lean_ctor_set(v_reuseFailAlloc_3402_, 8, v_binDir_3370_);
lean_ctor_set(v_reuseFailAlloc_3402_, 9, v_irDir_3371_);
lean_ctor_set(v_reuseFailAlloc_3402_, 10, v_releaseRepo_3372_);
lean_ctor_set(v_reuseFailAlloc_3402_, 11, v_buildArchive_3373_);
lean_ctor_set(v_reuseFailAlloc_3402_, 12, v_downloadCacheService_x3f_3375_);
lean_ctor_set(v_reuseFailAlloc_3402_, 13, v_testDriver_3376_);
lean_ctor_set(v_reuseFailAlloc_3402_, 14, v_testDriverArgs_3377_);
lean_ctor_set(v_reuseFailAlloc_3402_, 15, v_lintDriver_3378_);
lean_ctor_set(v_reuseFailAlloc_3402_, 16, v_lintDriverArgs_3379_);
lean_ctor_set(v_reuseFailAlloc_3402_, 17, v_version_3380_);
lean_ctor_set(v_reuseFailAlloc_3402_, 18, v_versionTags_3381_);
lean_ctor_set(v_reuseFailAlloc_3402_, 19, v_description_3382_);
lean_ctor_set(v_reuseFailAlloc_3402_, 20, v_keywords_3383_);
lean_ctor_set(v_reuseFailAlloc_3402_, 21, v_homepage_3384_);
lean_ctor_set(v_reuseFailAlloc_3402_, 22, v_license_3385_);
lean_ctor_set(v_reuseFailAlloc_3402_, 23, v_licenseFiles_3386_);
lean_ctor_set(v_reuseFailAlloc_3402_, 24, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3402_, 25, v_enableArtifactCache_x3f_3389_);
lean_ctor_set(v_reuseFailAlloc_3402_, 26, v_restoreAllArtifacts_x3f_3390_);
lean_ctor_set(v_reuseFailAlloc_3402_, 27, v_builtinLint_x3f_3393_);
lean_ctor_set(v_reuseFailAlloc_3402_, 28, v_checks_3394_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29, v_bootstrap_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29 + 1, v_precompileModules_3364_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3374_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29 + 3, v_reservoir_3388_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3391_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29 + 5, v_allowImportAll_3392_);
lean_ctor_set_uint8(v_reuseFailAlloc_3402_, sizeof(void*)*29 + 6, v_fixedToolchain_3395_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(lean_object* v_x_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3___boxed(lean_object* v_x_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lake_PackageConfig_readmeFile___proj___redArg___lam__3(v_x_3406_);
lean_dec_ref(v_x_3406_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg(){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = ((lean_object*)(l_Lake_PackageConfig_readmeFile___proj___redArg___closed__4));
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___redArg___boxed(lean_object* v___dummy_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
return v_res_3420_;
}
}
static lean_object* _init_l_Lake_PackageConfig_readmeFile___proj___closed__0(void){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lake_PackageConfig_readmeFile___proj___redArg();
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj(lean_object* v_p_3422_, lean_object* v_n_3423_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile___proj___boxed(lean_object* v_p_3425_, lean_object* v_n_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lake_PackageConfig_readmeFile___proj(v_p_3425_, v_n_3426_);
lean_dec(v_n_3426_);
lean_dec(v_p_3425_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg(){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___redArg___boxed(lean_object* v___dummy_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lake_PackageConfig_readmeFile_instConfigField___redArg();
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField(lean_object* v_p_3432_, lean_object* v_n_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_obj_once(&l_Lake_PackageConfig_readmeFile___proj___closed__0, &l_Lake_PackageConfig_readmeFile___proj___closed__0_once, _init_l_Lake_PackageConfig_readmeFile___proj___closed__0);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_readmeFile_instConfigField___boxed(lean_object* v_p_3435_, lean_object* v_n_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lake_PackageConfig_readmeFile_instConfigField(v_p_3435_, v_n_3436_);
lean_dec(v_n_3436_);
lean_dec(v_p_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(lean_object* v_cfg_3438_){
_start:
{
uint8_t v_reservoir_3439_; 
v_reservoir_3439_ = lean_ctor_get_uint8(v_cfg_3438_, sizeof(void*)*29 + 3);
return v_reservoir_3439_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__0___boxed(lean_object* v_cfg_3440_){
_start:
{
uint8_t v_res_3441_; lean_object* v_r_3442_; 
v_res_3441_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__0(v_cfg_3440_);
lean_dec_ref(v_cfg_3440_);
v_r_3442_ = lean_box(v_res_3441_);
return v_r_3442_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(uint8_t v_val_3443_, lean_object* v_cfg_3444_){
_start:
{
lean_object* v_toWorkspaceConfig_3445_; lean_object* v_toLeanConfig_3446_; uint8_t v_bootstrap_3447_; lean_object* v_extraDepTargets_3448_; uint8_t v_precompileModules_3449_; lean_object* v_moreGlobalServerArgs_3450_; lean_object* v_srcDir_3451_; lean_object* v_buildDir_3452_; lean_object* v_leanLibDir_3453_; lean_object* v_nativeLibDir_3454_; lean_object* v_binDir_3455_; lean_object* v_irDir_3456_; lean_object* v_releaseRepo_3457_; lean_object* v_buildArchive_3458_; uint8_t v_preferReleaseBuild_3459_; lean_object* v_downloadCacheService_x3f_3460_; lean_object* v_testDriver_3461_; lean_object* v_testDriverArgs_3462_; lean_object* v_lintDriver_3463_; lean_object* v_lintDriverArgs_3464_; lean_object* v_version_3465_; lean_object* v_versionTags_3466_; lean_object* v_description_3467_; lean_object* v_keywords_3468_; lean_object* v_homepage_3469_; lean_object* v_license_3470_; lean_object* v_licenseFiles_3471_; lean_object* v_readmeFile_3472_; lean_object* v_enableArtifactCache_x3f_3473_; lean_object* v_restoreAllArtifacts_x3f_3474_; uint8_t v_libPrefixOnWindows_3475_; uint8_t v_allowImportAll_3476_; lean_object* v_builtinLint_x3f_3477_; lean_object* v_checks_3478_; uint8_t v_fixedToolchain_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
v_toWorkspaceConfig_3445_ = lean_ctor_get(v_cfg_3444_, 0);
v_toLeanConfig_3446_ = lean_ctor_get(v_cfg_3444_, 1);
v_bootstrap_3447_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*29);
v_extraDepTargets_3448_ = lean_ctor_get(v_cfg_3444_, 2);
v_precompileModules_3449_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3450_ = lean_ctor_get(v_cfg_3444_, 3);
v_srcDir_3451_ = lean_ctor_get(v_cfg_3444_, 4);
v_buildDir_3452_ = lean_ctor_get(v_cfg_3444_, 5);
v_leanLibDir_3453_ = lean_ctor_get(v_cfg_3444_, 6);
v_nativeLibDir_3454_ = lean_ctor_get(v_cfg_3444_, 7);
v_binDir_3455_ = lean_ctor_get(v_cfg_3444_, 8);
v_irDir_3456_ = lean_ctor_get(v_cfg_3444_, 9);
v_releaseRepo_3457_ = lean_ctor_get(v_cfg_3444_, 10);
v_buildArchive_3458_ = lean_ctor_get(v_cfg_3444_, 11);
v_preferReleaseBuild_3459_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3460_ = lean_ctor_get(v_cfg_3444_, 12);
v_testDriver_3461_ = lean_ctor_get(v_cfg_3444_, 13);
v_testDriverArgs_3462_ = lean_ctor_get(v_cfg_3444_, 14);
v_lintDriver_3463_ = lean_ctor_get(v_cfg_3444_, 15);
v_lintDriverArgs_3464_ = lean_ctor_get(v_cfg_3444_, 16);
v_version_3465_ = lean_ctor_get(v_cfg_3444_, 17);
v_versionTags_3466_ = lean_ctor_get(v_cfg_3444_, 18);
v_description_3467_ = lean_ctor_get(v_cfg_3444_, 19);
v_keywords_3468_ = lean_ctor_get(v_cfg_3444_, 20);
v_homepage_3469_ = lean_ctor_get(v_cfg_3444_, 21);
v_license_3470_ = lean_ctor_get(v_cfg_3444_, 22);
v_licenseFiles_3471_ = lean_ctor_get(v_cfg_3444_, 23);
v_readmeFile_3472_ = lean_ctor_get(v_cfg_3444_, 24);
v_enableArtifactCache_x3f_3473_ = lean_ctor_get(v_cfg_3444_, 25);
v_restoreAllArtifacts_x3f_3474_ = lean_ctor_get(v_cfg_3444_, 26);
v_libPrefixOnWindows_3475_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*29 + 4);
v_allowImportAll_3476_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3477_ = lean_ctor_get(v_cfg_3444_, 27);
v_checks_3478_ = lean_ctor_get(v_cfg_3444_, 28);
v_fixedToolchain_3479_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*29 + 6);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_cfg_3444_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v_cfg_3444_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_checks_3478_);
lean_inc(v_builtinLint_x3f_3477_);
lean_inc(v_restoreAllArtifacts_x3f_3474_);
lean_inc(v_enableArtifactCache_x3f_3473_);
lean_inc(v_readmeFile_3472_);
lean_inc(v_licenseFiles_3471_);
lean_inc(v_license_3470_);
lean_inc(v_homepage_3469_);
lean_inc(v_keywords_3468_);
lean_inc(v_description_3467_);
lean_inc(v_versionTags_3466_);
lean_inc(v_version_3465_);
lean_inc(v_lintDriverArgs_3464_);
lean_inc(v_lintDriver_3463_);
lean_inc(v_testDriverArgs_3462_);
lean_inc(v_testDriver_3461_);
lean_inc(v_downloadCacheService_x3f_3460_);
lean_inc(v_buildArchive_3458_);
lean_inc(v_releaseRepo_3457_);
lean_inc(v_irDir_3456_);
lean_inc(v_binDir_3455_);
lean_inc(v_nativeLibDir_3454_);
lean_inc(v_leanLibDir_3453_);
lean_inc(v_buildDir_3452_);
lean_inc(v_srcDir_3451_);
lean_inc(v_moreGlobalServerArgs_3450_);
lean_inc(v_extraDepTargets_3448_);
lean_inc(v_toLeanConfig_3446_);
lean_inc(v_toWorkspaceConfig_3445_);
lean_dec(v_cfg_3444_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_toWorkspaceConfig_3445_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_toLeanConfig_3446_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_extraDepTargets_3448_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_moreGlobalServerArgs_3450_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_srcDir_3451_);
lean_ctor_set(v_reuseFailAlloc_3485_, 5, v_buildDir_3452_);
lean_ctor_set(v_reuseFailAlloc_3485_, 6, v_leanLibDir_3453_);
lean_ctor_set(v_reuseFailAlloc_3485_, 7, v_nativeLibDir_3454_);
lean_ctor_set(v_reuseFailAlloc_3485_, 8, v_binDir_3455_);
lean_ctor_set(v_reuseFailAlloc_3485_, 9, v_irDir_3456_);
lean_ctor_set(v_reuseFailAlloc_3485_, 10, v_releaseRepo_3457_);
lean_ctor_set(v_reuseFailAlloc_3485_, 11, v_buildArchive_3458_);
lean_ctor_set(v_reuseFailAlloc_3485_, 12, v_downloadCacheService_x3f_3460_);
lean_ctor_set(v_reuseFailAlloc_3485_, 13, v_testDriver_3461_);
lean_ctor_set(v_reuseFailAlloc_3485_, 14, v_testDriverArgs_3462_);
lean_ctor_set(v_reuseFailAlloc_3485_, 15, v_lintDriver_3463_);
lean_ctor_set(v_reuseFailAlloc_3485_, 16, v_lintDriverArgs_3464_);
lean_ctor_set(v_reuseFailAlloc_3485_, 17, v_version_3465_);
lean_ctor_set(v_reuseFailAlloc_3485_, 18, v_versionTags_3466_);
lean_ctor_set(v_reuseFailAlloc_3485_, 19, v_description_3467_);
lean_ctor_set(v_reuseFailAlloc_3485_, 20, v_keywords_3468_);
lean_ctor_set(v_reuseFailAlloc_3485_, 21, v_homepage_3469_);
lean_ctor_set(v_reuseFailAlloc_3485_, 22, v_license_3470_);
lean_ctor_set(v_reuseFailAlloc_3485_, 23, v_licenseFiles_3471_);
lean_ctor_set(v_reuseFailAlloc_3485_, 24, v_readmeFile_3472_);
lean_ctor_set(v_reuseFailAlloc_3485_, 25, v_enableArtifactCache_x3f_3473_);
lean_ctor_set(v_reuseFailAlloc_3485_, 26, v_restoreAllArtifacts_x3f_3474_);
lean_ctor_set(v_reuseFailAlloc_3485_, 27, v_builtinLint_x3f_3477_);
lean_ctor_set(v_reuseFailAlloc_3485_, 28, v_checks_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*29, v_bootstrap_3447_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*29 + 1, v_precompileModules_3449_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*29 + 5, v_allowImportAll_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*29 + 6, v_fixedToolchain_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*29 + 3, v_val_3443_);
return v___x_3484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__1___boxed(lean_object* v_val_3487_, lean_object* v_cfg_3488_){
_start:
{
uint8_t v_val_144__boxed_3489_; lean_object* v_res_3490_; 
v_val_144__boxed_3489_ = lean_unbox(v_val_3487_);
v_res_3490_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__1(v_val_144__boxed_3489_, v_cfg_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__2(lean_object* v_f_3491_, lean_object* v_cfg_3492_){
_start:
{
lean_object* v_toWorkspaceConfig_3493_; lean_object* v_toLeanConfig_3494_; uint8_t v_bootstrap_3495_; lean_object* v_extraDepTargets_3496_; uint8_t v_precompileModules_3497_; lean_object* v_moreGlobalServerArgs_3498_; lean_object* v_srcDir_3499_; lean_object* v_buildDir_3500_; lean_object* v_leanLibDir_3501_; lean_object* v_nativeLibDir_3502_; lean_object* v_binDir_3503_; lean_object* v_irDir_3504_; lean_object* v_releaseRepo_3505_; lean_object* v_buildArchive_3506_; uint8_t v_preferReleaseBuild_3507_; lean_object* v_downloadCacheService_x3f_3508_; lean_object* v_testDriver_3509_; lean_object* v_testDriverArgs_3510_; lean_object* v_lintDriver_3511_; lean_object* v_lintDriverArgs_3512_; lean_object* v_version_3513_; lean_object* v_versionTags_3514_; lean_object* v_description_3515_; lean_object* v_keywords_3516_; lean_object* v_homepage_3517_; lean_object* v_license_3518_; lean_object* v_licenseFiles_3519_; lean_object* v_readmeFile_3520_; uint8_t v_reservoir_3521_; lean_object* v_enableArtifactCache_x3f_3522_; lean_object* v_restoreAllArtifacts_x3f_3523_; uint8_t v_libPrefixOnWindows_3524_; uint8_t v_allowImportAll_3525_; lean_object* v_builtinLint_x3f_3526_; lean_object* v_checks_3527_; uint8_t v_fixedToolchain_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3538_; 
v_toWorkspaceConfig_3493_ = lean_ctor_get(v_cfg_3492_, 0);
v_toLeanConfig_3494_ = lean_ctor_get(v_cfg_3492_, 1);
v_bootstrap_3495_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29);
v_extraDepTargets_3496_ = lean_ctor_get(v_cfg_3492_, 2);
v_precompileModules_3497_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3498_ = lean_ctor_get(v_cfg_3492_, 3);
v_srcDir_3499_ = lean_ctor_get(v_cfg_3492_, 4);
v_buildDir_3500_ = lean_ctor_get(v_cfg_3492_, 5);
v_leanLibDir_3501_ = lean_ctor_get(v_cfg_3492_, 6);
v_nativeLibDir_3502_ = lean_ctor_get(v_cfg_3492_, 7);
v_binDir_3503_ = lean_ctor_get(v_cfg_3492_, 8);
v_irDir_3504_ = lean_ctor_get(v_cfg_3492_, 9);
v_releaseRepo_3505_ = lean_ctor_get(v_cfg_3492_, 10);
v_buildArchive_3506_ = lean_ctor_get(v_cfg_3492_, 11);
v_preferReleaseBuild_3507_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3508_ = lean_ctor_get(v_cfg_3492_, 12);
v_testDriver_3509_ = lean_ctor_get(v_cfg_3492_, 13);
v_testDriverArgs_3510_ = lean_ctor_get(v_cfg_3492_, 14);
v_lintDriver_3511_ = lean_ctor_get(v_cfg_3492_, 15);
v_lintDriverArgs_3512_ = lean_ctor_get(v_cfg_3492_, 16);
v_version_3513_ = lean_ctor_get(v_cfg_3492_, 17);
v_versionTags_3514_ = lean_ctor_get(v_cfg_3492_, 18);
v_description_3515_ = lean_ctor_get(v_cfg_3492_, 19);
v_keywords_3516_ = lean_ctor_get(v_cfg_3492_, 20);
v_homepage_3517_ = lean_ctor_get(v_cfg_3492_, 21);
v_license_3518_ = lean_ctor_get(v_cfg_3492_, 22);
v_licenseFiles_3519_ = lean_ctor_get(v_cfg_3492_, 23);
v_readmeFile_3520_ = lean_ctor_get(v_cfg_3492_, 24);
v_reservoir_3521_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3522_ = lean_ctor_get(v_cfg_3492_, 25);
v_restoreAllArtifacts_x3f_3523_ = lean_ctor_get(v_cfg_3492_, 26);
v_libPrefixOnWindows_3524_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29 + 4);
v_allowImportAll_3525_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3526_ = lean_ctor_get(v_cfg_3492_, 27);
v_checks_3527_ = lean_ctor_get(v_cfg_3492_, 28);
v_fixedToolchain_3528_ = lean_ctor_get_uint8(v_cfg_3492_, sizeof(void*)*29 + 6);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_cfg_3492_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3530_ = v_cfg_3492_;
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_checks_3527_);
lean_inc(v_builtinLint_x3f_3526_);
lean_inc(v_restoreAllArtifacts_x3f_3523_);
lean_inc(v_enableArtifactCache_x3f_3522_);
lean_inc(v_readmeFile_3520_);
lean_inc(v_licenseFiles_3519_);
lean_inc(v_license_3518_);
lean_inc(v_homepage_3517_);
lean_inc(v_keywords_3516_);
lean_inc(v_description_3515_);
lean_inc(v_versionTags_3514_);
lean_inc(v_version_3513_);
lean_inc(v_lintDriverArgs_3512_);
lean_inc(v_lintDriver_3511_);
lean_inc(v_testDriverArgs_3510_);
lean_inc(v_testDriver_3509_);
lean_inc(v_downloadCacheService_x3f_3508_);
lean_inc(v_buildArchive_3506_);
lean_inc(v_releaseRepo_3505_);
lean_inc(v_irDir_3504_);
lean_inc(v_binDir_3503_);
lean_inc(v_nativeLibDir_3502_);
lean_inc(v_leanLibDir_3501_);
lean_inc(v_buildDir_3500_);
lean_inc(v_srcDir_3499_);
lean_inc(v_moreGlobalServerArgs_3498_);
lean_inc(v_extraDepTargets_3496_);
lean_inc(v_toLeanConfig_3494_);
lean_inc(v_toWorkspaceConfig_3493_);
lean_dec(v_cfg_3492_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3532_ = lean_box(v_reservoir_3521_);
v___x_3533_ = lean_apply_1(v_f_3491_, v___x_3532_);
if (v_isShared_3531_ == 0)
{
v___x_3535_ = v___x_3530_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_toWorkspaceConfig_3493_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_toLeanConfig_3494_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_extraDepTargets_3496_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_moreGlobalServerArgs_3498_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_srcDir_3499_);
lean_ctor_set(v_reuseFailAlloc_3537_, 5, v_buildDir_3500_);
lean_ctor_set(v_reuseFailAlloc_3537_, 6, v_leanLibDir_3501_);
lean_ctor_set(v_reuseFailAlloc_3537_, 7, v_nativeLibDir_3502_);
lean_ctor_set(v_reuseFailAlloc_3537_, 8, v_binDir_3503_);
lean_ctor_set(v_reuseFailAlloc_3537_, 9, v_irDir_3504_);
lean_ctor_set(v_reuseFailAlloc_3537_, 10, v_releaseRepo_3505_);
lean_ctor_set(v_reuseFailAlloc_3537_, 11, v_buildArchive_3506_);
lean_ctor_set(v_reuseFailAlloc_3537_, 12, v_downloadCacheService_x3f_3508_);
lean_ctor_set(v_reuseFailAlloc_3537_, 13, v_testDriver_3509_);
lean_ctor_set(v_reuseFailAlloc_3537_, 14, v_testDriverArgs_3510_);
lean_ctor_set(v_reuseFailAlloc_3537_, 15, v_lintDriver_3511_);
lean_ctor_set(v_reuseFailAlloc_3537_, 16, v_lintDriverArgs_3512_);
lean_ctor_set(v_reuseFailAlloc_3537_, 17, v_version_3513_);
lean_ctor_set(v_reuseFailAlloc_3537_, 18, v_versionTags_3514_);
lean_ctor_set(v_reuseFailAlloc_3537_, 19, v_description_3515_);
lean_ctor_set(v_reuseFailAlloc_3537_, 20, v_keywords_3516_);
lean_ctor_set(v_reuseFailAlloc_3537_, 21, v_homepage_3517_);
lean_ctor_set(v_reuseFailAlloc_3537_, 22, v_license_3518_);
lean_ctor_set(v_reuseFailAlloc_3537_, 23, v_licenseFiles_3519_);
lean_ctor_set(v_reuseFailAlloc_3537_, 24, v_readmeFile_3520_);
lean_ctor_set(v_reuseFailAlloc_3537_, 25, v_enableArtifactCache_x3f_3522_);
lean_ctor_set(v_reuseFailAlloc_3537_, 26, v_restoreAllArtifacts_x3f_3523_);
lean_ctor_set(v_reuseFailAlloc_3537_, 27, v_builtinLint_x3f_3526_);
lean_ctor_set(v_reuseFailAlloc_3537_, 28, v_checks_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*29, v_bootstrap_3495_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*29 + 1, v_precompileModules_3497_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3507_);
v___x_3535_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_unbox(v___x_3533_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*29 + 3, v___x_3536_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3524_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*29 + 5, v_allowImportAll_3525_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*29 + 6, v_fixedToolchain_3528_);
return v___x_3535_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(lean_object* v_x_3539_){
_start:
{
uint8_t v___x_3540_; 
v___x_3540_ = 1;
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___lam__3___boxed(lean_object* v_x_3541_){
_start:
{
uint8_t v_res_3542_; lean_object* v_r_3543_; 
v_res_3542_ = l_Lake_PackageConfig_reservoir___proj___redArg___lam__3(v_x_3541_);
lean_dec_ref(v_x_3541_);
v_r_3543_ = lean_box(v_res_3542_);
return v_r_3543_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg(){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = ((lean_object*)(l_Lake_PackageConfig_reservoir___proj___redArg___closed__4));
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___redArg___boxed(lean_object* v___dummy_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lake_PackageConfig_reservoir___proj___redArg();
return v_res_3556_;
}
}
static lean_object* _init_l_Lake_PackageConfig_reservoir___proj___closed__0(void){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lake_PackageConfig_reservoir___proj___redArg();
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj(lean_object* v_p_3558_, lean_object* v_n_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir___proj___boxed(lean_object* v_p_3561_, lean_object* v_n_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lake_PackageConfig_reservoir___proj(v_p_3561_, v_n_3562_);
lean_dec(v_n_3562_);
lean_dec(v_p_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg(){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___redArg___boxed(lean_object* v___dummy_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lake_PackageConfig_reservoir_instConfigField___redArg();
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField(lean_object* v_p_3568_, lean_object* v_n_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_obj_once(&l_Lake_PackageConfig_reservoir___proj___closed__0, &l_Lake_PackageConfig_reservoir___proj___closed__0_once, _init_l_Lake_PackageConfig_reservoir___proj___closed__0);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_reservoir_instConfigField___boxed(lean_object* v_p_3571_, lean_object* v_n_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lake_PackageConfig_reservoir_instConfigField(v_p_3571_, v_n_3572_);
lean_dec(v_n_3572_);
lean_dec(v_p_3571_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(lean_object* v_cfg_3574_){
_start:
{
lean_object* v_enableArtifactCache_x3f_3575_; 
v_enableArtifactCache_x3f_3575_ = lean_ctor_get(v_cfg_3574_, 25);
lean_inc(v_enableArtifactCache_x3f_3575_);
return v_enableArtifactCache_x3f_3575_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__0(v_cfg_3576_);
lean_dec_ref(v_cfg_3576_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__1(lean_object* v_val_3578_, lean_object* v_cfg_3579_){
_start:
{
lean_object* v_toWorkspaceConfig_3580_; lean_object* v_toLeanConfig_3581_; uint8_t v_bootstrap_3582_; lean_object* v_extraDepTargets_3583_; uint8_t v_precompileModules_3584_; lean_object* v_moreGlobalServerArgs_3585_; lean_object* v_srcDir_3586_; lean_object* v_buildDir_3587_; lean_object* v_leanLibDir_3588_; lean_object* v_nativeLibDir_3589_; lean_object* v_binDir_3590_; lean_object* v_irDir_3591_; lean_object* v_releaseRepo_3592_; lean_object* v_buildArchive_3593_; uint8_t v_preferReleaseBuild_3594_; lean_object* v_downloadCacheService_x3f_3595_; lean_object* v_testDriver_3596_; lean_object* v_testDriverArgs_3597_; lean_object* v_lintDriver_3598_; lean_object* v_lintDriverArgs_3599_; lean_object* v_version_3600_; lean_object* v_versionTags_3601_; lean_object* v_description_3602_; lean_object* v_keywords_3603_; lean_object* v_homepage_3604_; lean_object* v_license_3605_; lean_object* v_licenseFiles_3606_; lean_object* v_readmeFile_3607_; uint8_t v_reservoir_3608_; lean_object* v_restoreAllArtifacts_x3f_3609_; uint8_t v_libPrefixOnWindows_3610_; uint8_t v_allowImportAll_3611_; lean_object* v_builtinLint_x3f_3612_; lean_object* v_checks_3613_; uint8_t v_fixedToolchain_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
v_toWorkspaceConfig_3580_ = lean_ctor_get(v_cfg_3579_, 0);
v_toLeanConfig_3581_ = lean_ctor_get(v_cfg_3579_, 1);
v_bootstrap_3582_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29);
v_extraDepTargets_3583_ = lean_ctor_get(v_cfg_3579_, 2);
v_precompileModules_3584_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3585_ = lean_ctor_get(v_cfg_3579_, 3);
v_srcDir_3586_ = lean_ctor_get(v_cfg_3579_, 4);
v_buildDir_3587_ = lean_ctor_get(v_cfg_3579_, 5);
v_leanLibDir_3588_ = lean_ctor_get(v_cfg_3579_, 6);
v_nativeLibDir_3589_ = lean_ctor_get(v_cfg_3579_, 7);
v_binDir_3590_ = lean_ctor_get(v_cfg_3579_, 8);
v_irDir_3591_ = lean_ctor_get(v_cfg_3579_, 9);
v_releaseRepo_3592_ = lean_ctor_get(v_cfg_3579_, 10);
v_buildArchive_3593_ = lean_ctor_get(v_cfg_3579_, 11);
v_preferReleaseBuild_3594_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3595_ = lean_ctor_get(v_cfg_3579_, 12);
v_testDriver_3596_ = lean_ctor_get(v_cfg_3579_, 13);
v_testDriverArgs_3597_ = lean_ctor_get(v_cfg_3579_, 14);
v_lintDriver_3598_ = lean_ctor_get(v_cfg_3579_, 15);
v_lintDriverArgs_3599_ = lean_ctor_get(v_cfg_3579_, 16);
v_version_3600_ = lean_ctor_get(v_cfg_3579_, 17);
v_versionTags_3601_ = lean_ctor_get(v_cfg_3579_, 18);
v_description_3602_ = lean_ctor_get(v_cfg_3579_, 19);
v_keywords_3603_ = lean_ctor_get(v_cfg_3579_, 20);
v_homepage_3604_ = lean_ctor_get(v_cfg_3579_, 21);
v_license_3605_ = lean_ctor_get(v_cfg_3579_, 22);
v_licenseFiles_3606_ = lean_ctor_get(v_cfg_3579_, 23);
v_readmeFile_3607_ = lean_ctor_get(v_cfg_3579_, 24);
v_reservoir_3608_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29 + 3);
v_restoreAllArtifacts_x3f_3609_ = lean_ctor_get(v_cfg_3579_, 26);
v_libPrefixOnWindows_3610_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29 + 4);
v_allowImportAll_3611_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3612_ = lean_ctor_get(v_cfg_3579_, 27);
v_checks_3613_ = lean_ctor_get(v_cfg_3579_, 28);
v_fixedToolchain_3614_ = lean_ctor_get_uint8(v_cfg_3579_, sizeof(void*)*29 + 6);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_cfg_3579_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v_cfg_3579_, 25);
lean_dec(v_unused_3622_);
v___x_3616_ = v_cfg_3579_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_checks_3613_);
lean_inc(v_builtinLint_x3f_3612_);
lean_inc(v_restoreAllArtifacts_x3f_3609_);
lean_inc(v_readmeFile_3607_);
lean_inc(v_licenseFiles_3606_);
lean_inc(v_license_3605_);
lean_inc(v_homepage_3604_);
lean_inc(v_keywords_3603_);
lean_inc(v_description_3602_);
lean_inc(v_versionTags_3601_);
lean_inc(v_version_3600_);
lean_inc(v_lintDriverArgs_3599_);
lean_inc(v_lintDriver_3598_);
lean_inc(v_testDriverArgs_3597_);
lean_inc(v_testDriver_3596_);
lean_inc(v_downloadCacheService_x3f_3595_);
lean_inc(v_buildArchive_3593_);
lean_inc(v_releaseRepo_3592_);
lean_inc(v_irDir_3591_);
lean_inc(v_binDir_3590_);
lean_inc(v_nativeLibDir_3589_);
lean_inc(v_leanLibDir_3588_);
lean_inc(v_buildDir_3587_);
lean_inc(v_srcDir_3586_);
lean_inc(v_moreGlobalServerArgs_3585_);
lean_inc(v_extraDepTargets_3583_);
lean_inc(v_toLeanConfig_3581_);
lean_inc(v_toWorkspaceConfig_3580_);
lean_dec(v_cfg_3579_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 25, v_val_3578_);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_toWorkspaceConfig_3580_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_toLeanConfig_3581_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_extraDepTargets_3583_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_moreGlobalServerArgs_3585_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_srcDir_3586_);
lean_ctor_set(v_reuseFailAlloc_3620_, 5, v_buildDir_3587_);
lean_ctor_set(v_reuseFailAlloc_3620_, 6, v_leanLibDir_3588_);
lean_ctor_set(v_reuseFailAlloc_3620_, 7, v_nativeLibDir_3589_);
lean_ctor_set(v_reuseFailAlloc_3620_, 8, v_binDir_3590_);
lean_ctor_set(v_reuseFailAlloc_3620_, 9, v_irDir_3591_);
lean_ctor_set(v_reuseFailAlloc_3620_, 10, v_releaseRepo_3592_);
lean_ctor_set(v_reuseFailAlloc_3620_, 11, v_buildArchive_3593_);
lean_ctor_set(v_reuseFailAlloc_3620_, 12, v_downloadCacheService_x3f_3595_);
lean_ctor_set(v_reuseFailAlloc_3620_, 13, v_testDriver_3596_);
lean_ctor_set(v_reuseFailAlloc_3620_, 14, v_testDriverArgs_3597_);
lean_ctor_set(v_reuseFailAlloc_3620_, 15, v_lintDriver_3598_);
lean_ctor_set(v_reuseFailAlloc_3620_, 16, v_lintDriverArgs_3599_);
lean_ctor_set(v_reuseFailAlloc_3620_, 17, v_version_3600_);
lean_ctor_set(v_reuseFailAlloc_3620_, 18, v_versionTags_3601_);
lean_ctor_set(v_reuseFailAlloc_3620_, 19, v_description_3602_);
lean_ctor_set(v_reuseFailAlloc_3620_, 20, v_keywords_3603_);
lean_ctor_set(v_reuseFailAlloc_3620_, 21, v_homepage_3604_);
lean_ctor_set(v_reuseFailAlloc_3620_, 22, v_license_3605_);
lean_ctor_set(v_reuseFailAlloc_3620_, 23, v_licenseFiles_3606_);
lean_ctor_set(v_reuseFailAlloc_3620_, 24, v_readmeFile_3607_);
lean_ctor_set(v_reuseFailAlloc_3620_, 25, v_val_3578_);
lean_ctor_set(v_reuseFailAlloc_3620_, 26, v_restoreAllArtifacts_x3f_3609_);
lean_ctor_set(v_reuseFailAlloc_3620_, 27, v_builtinLint_x3f_3612_);
lean_ctor_set(v_reuseFailAlloc_3620_, 28, v_checks_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29, v_bootstrap_3582_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29 + 1, v_precompileModules_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3594_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29 + 3, v_reservoir_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3610_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29 + 5, v_allowImportAll_3611_);
lean_ctor_set_uint8(v_reuseFailAlloc_3620_, sizeof(void*)*29 + 6, v_fixedToolchain_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__2(lean_object* v_f_3623_, lean_object* v_cfg_3624_){
_start:
{
lean_object* v_toWorkspaceConfig_3625_; lean_object* v_toLeanConfig_3626_; uint8_t v_bootstrap_3627_; lean_object* v_extraDepTargets_3628_; uint8_t v_precompileModules_3629_; lean_object* v_moreGlobalServerArgs_3630_; lean_object* v_srcDir_3631_; lean_object* v_buildDir_3632_; lean_object* v_leanLibDir_3633_; lean_object* v_nativeLibDir_3634_; lean_object* v_binDir_3635_; lean_object* v_irDir_3636_; lean_object* v_releaseRepo_3637_; lean_object* v_buildArchive_3638_; uint8_t v_preferReleaseBuild_3639_; lean_object* v_downloadCacheService_x3f_3640_; lean_object* v_testDriver_3641_; lean_object* v_testDriverArgs_3642_; lean_object* v_lintDriver_3643_; lean_object* v_lintDriverArgs_3644_; lean_object* v_version_3645_; lean_object* v_versionTags_3646_; lean_object* v_description_3647_; lean_object* v_keywords_3648_; lean_object* v_homepage_3649_; lean_object* v_license_3650_; lean_object* v_licenseFiles_3651_; lean_object* v_readmeFile_3652_; uint8_t v_reservoir_3653_; lean_object* v_enableArtifactCache_x3f_3654_; lean_object* v_restoreAllArtifacts_x3f_3655_; uint8_t v_libPrefixOnWindows_3656_; uint8_t v_allowImportAll_3657_; lean_object* v_builtinLint_x3f_3658_; lean_object* v_checks_3659_; uint8_t v_fixedToolchain_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3668_; 
v_toWorkspaceConfig_3625_ = lean_ctor_get(v_cfg_3624_, 0);
v_toLeanConfig_3626_ = lean_ctor_get(v_cfg_3624_, 1);
v_bootstrap_3627_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29);
v_extraDepTargets_3628_ = lean_ctor_get(v_cfg_3624_, 2);
v_precompileModules_3629_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3630_ = lean_ctor_get(v_cfg_3624_, 3);
v_srcDir_3631_ = lean_ctor_get(v_cfg_3624_, 4);
v_buildDir_3632_ = lean_ctor_get(v_cfg_3624_, 5);
v_leanLibDir_3633_ = lean_ctor_get(v_cfg_3624_, 6);
v_nativeLibDir_3634_ = lean_ctor_get(v_cfg_3624_, 7);
v_binDir_3635_ = lean_ctor_get(v_cfg_3624_, 8);
v_irDir_3636_ = lean_ctor_get(v_cfg_3624_, 9);
v_releaseRepo_3637_ = lean_ctor_get(v_cfg_3624_, 10);
v_buildArchive_3638_ = lean_ctor_get(v_cfg_3624_, 11);
v_preferReleaseBuild_3639_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3640_ = lean_ctor_get(v_cfg_3624_, 12);
v_testDriver_3641_ = lean_ctor_get(v_cfg_3624_, 13);
v_testDriverArgs_3642_ = lean_ctor_get(v_cfg_3624_, 14);
v_lintDriver_3643_ = lean_ctor_get(v_cfg_3624_, 15);
v_lintDriverArgs_3644_ = lean_ctor_get(v_cfg_3624_, 16);
v_version_3645_ = lean_ctor_get(v_cfg_3624_, 17);
v_versionTags_3646_ = lean_ctor_get(v_cfg_3624_, 18);
v_description_3647_ = lean_ctor_get(v_cfg_3624_, 19);
v_keywords_3648_ = lean_ctor_get(v_cfg_3624_, 20);
v_homepage_3649_ = lean_ctor_get(v_cfg_3624_, 21);
v_license_3650_ = lean_ctor_get(v_cfg_3624_, 22);
v_licenseFiles_3651_ = lean_ctor_get(v_cfg_3624_, 23);
v_readmeFile_3652_ = lean_ctor_get(v_cfg_3624_, 24);
v_reservoir_3653_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3654_ = lean_ctor_get(v_cfg_3624_, 25);
v_restoreAllArtifacts_x3f_3655_ = lean_ctor_get(v_cfg_3624_, 26);
v_libPrefixOnWindows_3656_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29 + 4);
v_allowImportAll_3657_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3658_ = lean_ctor_get(v_cfg_3624_, 27);
v_checks_3659_ = lean_ctor_get(v_cfg_3624_, 28);
v_fixedToolchain_3660_ = lean_ctor_get_uint8(v_cfg_3624_, sizeof(void*)*29 + 6);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_cfg_3624_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3662_ = v_cfg_3624_;
v_isShared_3663_ = v_isSharedCheck_3668_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_checks_3659_);
lean_inc(v_builtinLint_x3f_3658_);
lean_inc(v_restoreAllArtifacts_x3f_3655_);
lean_inc(v_enableArtifactCache_x3f_3654_);
lean_inc(v_readmeFile_3652_);
lean_inc(v_licenseFiles_3651_);
lean_inc(v_license_3650_);
lean_inc(v_homepage_3649_);
lean_inc(v_keywords_3648_);
lean_inc(v_description_3647_);
lean_inc(v_versionTags_3646_);
lean_inc(v_version_3645_);
lean_inc(v_lintDriverArgs_3644_);
lean_inc(v_lintDriver_3643_);
lean_inc(v_testDriverArgs_3642_);
lean_inc(v_testDriver_3641_);
lean_inc(v_downloadCacheService_x3f_3640_);
lean_inc(v_buildArchive_3638_);
lean_inc(v_releaseRepo_3637_);
lean_inc(v_irDir_3636_);
lean_inc(v_binDir_3635_);
lean_inc(v_nativeLibDir_3634_);
lean_inc(v_leanLibDir_3633_);
lean_inc(v_buildDir_3632_);
lean_inc(v_srcDir_3631_);
lean_inc(v_moreGlobalServerArgs_3630_);
lean_inc(v_extraDepTargets_3628_);
lean_inc(v_toLeanConfig_3626_);
lean_inc(v_toWorkspaceConfig_3625_);
lean_dec(v_cfg_3624_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3668_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_apply_1(v_f_3623_, v_enableArtifactCache_x3f_3654_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 25, v___x_3664_);
v___x_3666_ = v___x_3662_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_toWorkspaceConfig_3625_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_toLeanConfig_3626_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_extraDepTargets_3628_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_moreGlobalServerArgs_3630_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_srcDir_3631_);
lean_ctor_set(v_reuseFailAlloc_3667_, 5, v_buildDir_3632_);
lean_ctor_set(v_reuseFailAlloc_3667_, 6, v_leanLibDir_3633_);
lean_ctor_set(v_reuseFailAlloc_3667_, 7, v_nativeLibDir_3634_);
lean_ctor_set(v_reuseFailAlloc_3667_, 8, v_binDir_3635_);
lean_ctor_set(v_reuseFailAlloc_3667_, 9, v_irDir_3636_);
lean_ctor_set(v_reuseFailAlloc_3667_, 10, v_releaseRepo_3637_);
lean_ctor_set(v_reuseFailAlloc_3667_, 11, v_buildArchive_3638_);
lean_ctor_set(v_reuseFailAlloc_3667_, 12, v_downloadCacheService_x3f_3640_);
lean_ctor_set(v_reuseFailAlloc_3667_, 13, v_testDriver_3641_);
lean_ctor_set(v_reuseFailAlloc_3667_, 14, v_testDriverArgs_3642_);
lean_ctor_set(v_reuseFailAlloc_3667_, 15, v_lintDriver_3643_);
lean_ctor_set(v_reuseFailAlloc_3667_, 16, v_lintDriverArgs_3644_);
lean_ctor_set(v_reuseFailAlloc_3667_, 17, v_version_3645_);
lean_ctor_set(v_reuseFailAlloc_3667_, 18, v_versionTags_3646_);
lean_ctor_set(v_reuseFailAlloc_3667_, 19, v_description_3647_);
lean_ctor_set(v_reuseFailAlloc_3667_, 20, v_keywords_3648_);
lean_ctor_set(v_reuseFailAlloc_3667_, 21, v_homepage_3649_);
lean_ctor_set(v_reuseFailAlloc_3667_, 22, v_license_3650_);
lean_ctor_set(v_reuseFailAlloc_3667_, 23, v_licenseFiles_3651_);
lean_ctor_set(v_reuseFailAlloc_3667_, 24, v_readmeFile_3652_);
lean_ctor_set(v_reuseFailAlloc_3667_, 25, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3667_, 26, v_restoreAllArtifacts_x3f_3655_);
lean_ctor_set(v_reuseFailAlloc_3667_, 27, v_builtinLint_x3f_3658_);
lean_ctor_set(v_reuseFailAlloc_3667_, 28, v_checks_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29, v_bootstrap_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29 + 1, v_precompileModules_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29 + 3, v_reservoir_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29 + 5, v_allowImportAll_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*29 + 6, v_fixedToolchain_3660_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(lean_object* v_x_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_box(0);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3___boxed(lean_object* v_x_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___lam__3(v_x_3671_);
lean_dec_ref(v_x_3671_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg(){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = ((lean_object*)(l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___closed__4));
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg___boxed(lean_object* v___dummy_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
return v_res_3685_;
}
}
static lean_object* _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj___redArg();
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj(lean_object* v_p_3687_, lean_object* v_n_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f___proj___boxed(lean_object* v_p_3690_, lean_object* v_n_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lake_PackageConfig_enableArtifactCache_x3f___proj(v_p_3690_, v_n_3691_);
lean_dec(v_n_3691_);
lean_dec(v_p_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg(){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg___boxed(lean_object* v___dummy_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField___redArg();
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField(lean_object* v_p_3697_, lean_object* v_n_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_instConfigField___boxed(lean_object* v_p_3700_, lean_object* v_n_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lake_PackageConfig_enableArtifactCache_instConfigField(v_p_3700_, v_n_3701_);
lean_dec(v_n_3701_);
lean_dec(v_p_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___redArg();
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(lean_object* v_p_3707_, lean_object* v_n_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_obj_once(&l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0, &l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_enableArtifactCache_x3f___proj___closed__0);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField___boxed(lean_object* v_p_3710_, lean_object* v_n_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lake_PackageConfig_enableArtifactCache_x3f_instConfigField(v_p_3710_, v_n_3711_);
lean_dec(v_n_3711_);
lean_dec(v_p_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(lean_object* v_cfg_3713_){
_start:
{
lean_object* v_restoreAllArtifacts_x3f_3714_; 
v_restoreAllArtifacts_x3f_3714_ = lean_ctor_get(v_cfg_3713_, 26);
lean_inc(v_restoreAllArtifacts_x3f_3714_);
return v_restoreAllArtifacts_x3f_3714_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__0(v_cfg_3715_);
lean_dec_ref(v_cfg_3715_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__1(lean_object* v_val_3717_, lean_object* v_cfg_3718_){
_start:
{
lean_object* v_toWorkspaceConfig_3719_; lean_object* v_toLeanConfig_3720_; uint8_t v_bootstrap_3721_; lean_object* v_extraDepTargets_3722_; uint8_t v_precompileModules_3723_; lean_object* v_moreGlobalServerArgs_3724_; lean_object* v_srcDir_3725_; lean_object* v_buildDir_3726_; lean_object* v_leanLibDir_3727_; lean_object* v_nativeLibDir_3728_; lean_object* v_binDir_3729_; lean_object* v_irDir_3730_; lean_object* v_releaseRepo_3731_; lean_object* v_buildArchive_3732_; uint8_t v_preferReleaseBuild_3733_; lean_object* v_downloadCacheService_x3f_3734_; lean_object* v_testDriver_3735_; lean_object* v_testDriverArgs_3736_; lean_object* v_lintDriver_3737_; lean_object* v_lintDriverArgs_3738_; lean_object* v_version_3739_; lean_object* v_versionTags_3740_; lean_object* v_description_3741_; lean_object* v_keywords_3742_; lean_object* v_homepage_3743_; lean_object* v_license_3744_; lean_object* v_licenseFiles_3745_; lean_object* v_readmeFile_3746_; uint8_t v_reservoir_3747_; lean_object* v_enableArtifactCache_x3f_3748_; uint8_t v_libPrefixOnWindows_3749_; uint8_t v_allowImportAll_3750_; lean_object* v_builtinLint_x3f_3751_; lean_object* v_checks_3752_; uint8_t v_fixedToolchain_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_toWorkspaceConfig_3719_ = lean_ctor_get(v_cfg_3718_, 0);
v_toLeanConfig_3720_ = lean_ctor_get(v_cfg_3718_, 1);
v_bootstrap_3721_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29);
v_extraDepTargets_3722_ = lean_ctor_get(v_cfg_3718_, 2);
v_precompileModules_3723_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3724_ = lean_ctor_get(v_cfg_3718_, 3);
v_srcDir_3725_ = lean_ctor_get(v_cfg_3718_, 4);
v_buildDir_3726_ = lean_ctor_get(v_cfg_3718_, 5);
v_leanLibDir_3727_ = lean_ctor_get(v_cfg_3718_, 6);
v_nativeLibDir_3728_ = lean_ctor_get(v_cfg_3718_, 7);
v_binDir_3729_ = lean_ctor_get(v_cfg_3718_, 8);
v_irDir_3730_ = lean_ctor_get(v_cfg_3718_, 9);
v_releaseRepo_3731_ = lean_ctor_get(v_cfg_3718_, 10);
v_buildArchive_3732_ = lean_ctor_get(v_cfg_3718_, 11);
v_preferReleaseBuild_3733_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3734_ = lean_ctor_get(v_cfg_3718_, 12);
v_testDriver_3735_ = lean_ctor_get(v_cfg_3718_, 13);
v_testDriverArgs_3736_ = lean_ctor_get(v_cfg_3718_, 14);
v_lintDriver_3737_ = lean_ctor_get(v_cfg_3718_, 15);
v_lintDriverArgs_3738_ = lean_ctor_get(v_cfg_3718_, 16);
v_version_3739_ = lean_ctor_get(v_cfg_3718_, 17);
v_versionTags_3740_ = lean_ctor_get(v_cfg_3718_, 18);
v_description_3741_ = lean_ctor_get(v_cfg_3718_, 19);
v_keywords_3742_ = lean_ctor_get(v_cfg_3718_, 20);
v_homepage_3743_ = lean_ctor_get(v_cfg_3718_, 21);
v_license_3744_ = lean_ctor_get(v_cfg_3718_, 22);
v_licenseFiles_3745_ = lean_ctor_get(v_cfg_3718_, 23);
v_readmeFile_3746_ = lean_ctor_get(v_cfg_3718_, 24);
v_reservoir_3747_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3748_ = lean_ctor_get(v_cfg_3718_, 25);
v_libPrefixOnWindows_3749_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29 + 4);
v_allowImportAll_3750_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3751_ = lean_ctor_get(v_cfg_3718_, 27);
v_checks_3752_ = lean_ctor_get(v_cfg_3718_, 28);
v_fixedToolchain_3753_ = lean_ctor_get_uint8(v_cfg_3718_, sizeof(void*)*29 + 6);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_cfg_3718_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; 
v_unused_3761_ = lean_ctor_get(v_cfg_3718_, 26);
lean_dec(v_unused_3761_);
v___x_3755_ = v_cfg_3718_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_checks_3752_);
lean_inc(v_builtinLint_x3f_3751_);
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
lean_inc(v_downloadCacheService_x3f_3734_);
lean_inc(v_buildArchive_3732_);
lean_inc(v_releaseRepo_3731_);
lean_inc(v_irDir_3730_);
lean_inc(v_binDir_3729_);
lean_inc(v_nativeLibDir_3728_);
lean_inc(v_leanLibDir_3727_);
lean_inc(v_buildDir_3726_);
lean_inc(v_srcDir_3725_);
lean_inc(v_moreGlobalServerArgs_3724_);
lean_inc(v_extraDepTargets_3722_);
lean_inc(v_toLeanConfig_3720_);
lean_inc(v_toWorkspaceConfig_3719_);
lean_dec(v_cfg_3718_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 26, v_val_3717_);
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_toWorkspaceConfig_3719_);
lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_toLeanConfig_3720_);
lean_ctor_set(v_reuseFailAlloc_3759_, 2, v_extraDepTargets_3722_);
lean_ctor_set(v_reuseFailAlloc_3759_, 3, v_moreGlobalServerArgs_3724_);
lean_ctor_set(v_reuseFailAlloc_3759_, 4, v_srcDir_3725_);
lean_ctor_set(v_reuseFailAlloc_3759_, 5, v_buildDir_3726_);
lean_ctor_set(v_reuseFailAlloc_3759_, 6, v_leanLibDir_3727_);
lean_ctor_set(v_reuseFailAlloc_3759_, 7, v_nativeLibDir_3728_);
lean_ctor_set(v_reuseFailAlloc_3759_, 8, v_binDir_3729_);
lean_ctor_set(v_reuseFailAlloc_3759_, 9, v_irDir_3730_);
lean_ctor_set(v_reuseFailAlloc_3759_, 10, v_releaseRepo_3731_);
lean_ctor_set(v_reuseFailAlloc_3759_, 11, v_buildArchive_3732_);
lean_ctor_set(v_reuseFailAlloc_3759_, 12, v_downloadCacheService_x3f_3734_);
lean_ctor_set(v_reuseFailAlloc_3759_, 13, v_testDriver_3735_);
lean_ctor_set(v_reuseFailAlloc_3759_, 14, v_testDriverArgs_3736_);
lean_ctor_set(v_reuseFailAlloc_3759_, 15, v_lintDriver_3737_);
lean_ctor_set(v_reuseFailAlloc_3759_, 16, v_lintDriverArgs_3738_);
lean_ctor_set(v_reuseFailAlloc_3759_, 17, v_version_3739_);
lean_ctor_set(v_reuseFailAlloc_3759_, 18, v_versionTags_3740_);
lean_ctor_set(v_reuseFailAlloc_3759_, 19, v_description_3741_);
lean_ctor_set(v_reuseFailAlloc_3759_, 20, v_keywords_3742_);
lean_ctor_set(v_reuseFailAlloc_3759_, 21, v_homepage_3743_);
lean_ctor_set(v_reuseFailAlloc_3759_, 22, v_license_3744_);
lean_ctor_set(v_reuseFailAlloc_3759_, 23, v_licenseFiles_3745_);
lean_ctor_set(v_reuseFailAlloc_3759_, 24, v_readmeFile_3746_);
lean_ctor_set(v_reuseFailAlloc_3759_, 25, v_enableArtifactCache_x3f_3748_);
lean_ctor_set(v_reuseFailAlloc_3759_, 26, v_val_3717_);
lean_ctor_set(v_reuseFailAlloc_3759_, 27, v_builtinLint_x3f_3751_);
lean_ctor_set(v_reuseFailAlloc_3759_, 28, v_checks_3752_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29, v_bootstrap_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29 + 1, v_precompileModules_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29 + 3, v_reservoir_3747_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3749_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29 + 5, v_allowImportAll_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*29 + 6, v_fixedToolchain_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___lam__2(lean_object* v_f_3762_, lean_object* v_cfg_3763_){
_start:
{
lean_object* v_toWorkspaceConfig_3764_; lean_object* v_toLeanConfig_3765_; uint8_t v_bootstrap_3766_; lean_object* v_extraDepTargets_3767_; uint8_t v_precompileModules_3768_; lean_object* v_moreGlobalServerArgs_3769_; lean_object* v_srcDir_3770_; lean_object* v_buildDir_3771_; lean_object* v_leanLibDir_3772_; lean_object* v_nativeLibDir_3773_; lean_object* v_binDir_3774_; lean_object* v_irDir_3775_; lean_object* v_releaseRepo_3776_; lean_object* v_buildArchive_3777_; uint8_t v_preferReleaseBuild_3778_; lean_object* v_downloadCacheService_x3f_3779_; lean_object* v_testDriver_3780_; lean_object* v_testDriverArgs_3781_; lean_object* v_lintDriver_3782_; lean_object* v_lintDriverArgs_3783_; lean_object* v_version_3784_; lean_object* v_versionTags_3785_; lean_object* v_description_3786_; lean_object* v_keywords_3787_; lean_object* v_homepage_3788_; lean_object* v_license_3789_; lean_object* v_licenseFiles_3790_; lean_object* v_readmeFile_3791_; uint8_t v_reservoir_3792_; lean_object* v_enableArtifactCache_x3f_3793_; lean_object* v_restoreAllArtifacts_x3f_3794_; uint8_t v_libPrefixOnWindows_3795_; uint8_t v_allowImportAll_3796_; lean_object* v_builtinLint_x3f_3797_; lean_object* v_checks_3798_; uint8_t v_fixedToolchain_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
v_toWorkspaceConfig_3764_ = lean_ctor_get(v_cfg_3763_, 0);
v_toLeanConfig_3765_ = lean_ctor_get(v_cfg_3763_, 1);
v_bootstrap_3766_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29);
v_extraDepTargets_3767_ = lean_ctor_get(v_cfg_3763_, 2);
v_precompileModules_3768_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3769_ = lean_ctor_get(v_cfg_3763_, 3);
v_srcDir_3770_ = lean_ctor_get(v_cfg_3763_, 4);
v_buildDir_3771_ = lean_ctor_get(v_cfg_3763_, 5);
v_leanLibDir_3772_ = lean_ctor_get(v_cfg_3763_, 6);
v_nativeLibDir_3773_ = lean_ctor_get(v_cfg_3763_, 7);
v_binDir_3774_ = lean_ctor_get(v_cfg_3763_, 8);
v_irDir_3775_ = lean_ctor_get(v_cfg_3763_, 9);
v_releaseRepo_3776_ = lean_ctor_get(v_cfg_3763_, 10);
v_buildArchive_3777_ = lean_ctor_get(v_cfg_3763_, 11);
v_preferReleaseBuild_3778_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3779_ = lean_ctor_get(v_cfg_3763_, 12);
v_testDriver_3780_ = lean_ctor_get(v_cfg_3763_, 13);
v_testDriverArgs_3781_ = lean_ctor_get(v_cfg_3763_, 14);
v_lintDriver_3782_ = lean_ctor_get(v_cfg_3763_, 15);
v_lintDriverArgs_3783_ = lean_ctor_get(v_cfg_3763_, 16);
v_version_3784_ = lean_ctor_get(v_cfg_3763_, 17);
v_versionTags_3785_ = lean_ctor_get(v_cfg_3763_, 18);
v_description_3786_ = lean_ctor_get(v_cfg_3763_, 19);
v_keywords_3787_ = lean_ctor_get(v_cfg_3763_, 20);
v_homepage_3788_ = lean_ctor_get(v_cfg_3763_, 21);
v_license_3789_ = lean_ctor_get(v_cfg_3763_, 22);
v_licenseFiles_3790_ = lean_ctor_get(v_cfg_3763_, 23);
v_readmeFile_3791_ = lean_ctor_get(v_cfg_3763_, 24);
v_reservoir_3792_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3793_ = lean_ctor_get(v_cfg_3763_, 25);
v_restoreAllArtifacts_x3f_3794_ = lean_ctor_get(v_cfg_3763_, 26);
v_libPrefixOnWindows_3795_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29 + 4);
v_allowImportAll_3796_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3797_ = lean_ctor_get(v_cfg_3763_, 27);
v_checks_3798_ = lean_ctor_get(v_cfg_3763_, 28);
v_fixedToolchain_3799_ = lean_ctor_get_uint8(v_cfg_3763_, sizeof(void*)*29 + 6);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_cfg_3763_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3801_ = v_cfg_3763_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_checks_3798_);
lean_inc(v_builtinLint_x3f_3797_);
lean_inc(v_restoreAllArtifacts_x3f_3794_);
lean_inc(v_enableArtifactCache_x3f_3793_);
lean_inc(v_readmeFile_3791_);
lean_inc(v_licenseFiles_3790_);
lean_inc(v_license_3789_);
lean_inc(v_homepage_3788_);
lean_inc(v_keywords_3787_);
lean_inc(v_description_3786_);
lean_inc(v_versionTags_3785_);
lean_inc(v_version_3784_);
lean_inc(v_lintDriverArgs_3783_);
lean_inc(v_lintDriver_3782_);
lean_inc(v_testDriverArgs_3781_);
lean_inc(v_testDriver_3780_);
lean_inc(v_downloadCacheService_x3f_3779_);
lean_inc(v_buildArchive_3777_);
lean_inc(v_releaseRepo_3776_);
lean_inc(v_irDir_3775_);
lean_inc(v_binDir_3774_);
lean_inc(v_nativeLibDir_3773_);
lean_inc(v_leanLibDir_3772_);
lean_inc(v_buildDir_3771_);
lean_inc(v_srcDir_3770_);
lean_inc(v_moreGlobalServerArgs_3769_);
lean_inc(v_extraDepTargets_3767_);
lean_inc(v_toLeanConfig_3765_);
lean_inc(v_toWorkspaceConfig_3764_);
lean_dec(v_cfg_3763_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_apply_1(v_f_3762_, v_restoreAllArtifacts_x3f_3794_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 26, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_toWorkspaceConfig_3764_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_toLeanConfig_3765_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_extraDepTargets_3767_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_moreGlobalServerArgs_3769_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v_srcDir_3770_);
lean_ctor_set(v_reuseFailAlloc_3806_, 5, v_buildDir_3771_);
lean_ctor_set(v_reuseFailAlloc_3806_, 6, v_leanLibDir_3772_);
lean_ctor_set(v_reuseFailAlloc_3806_, 7, v_nativeLibDir_3773_);
lean_ctor_set(v_reuseFailAlloc_3806_, 8, v_binDir_3774_);
lean_ctor_set(v_reuseFailAlloc_3806_, 9, v_irDir_3775_);
lean_ctor_set(v_reuseFailAlloc_3806_, 10, v_releaseRepo_3776_);
lean_ctor_set(v_reuseFailAlloc_3806_, 11, v_buildArchive_3777_);
lean_ctor_set(v_reuseFailAlloc_3806_, 12, v_downloadCacheService_x3f_3779_);
lean_ctor_set(v_reuseFailAlloc_3806_, 13, v_testDriver_3780_);
lean_ctor_set(v_reuseFailAlloc_3806_, 14, v_testDriverArgs_3781_);
lean_ctor_set(v_reuseFailAlloc_3806_, 15, v_lintDriver_3782_);
lean_ctor_set(v_reuseFailAlloc_3806_, 16, v_lintDriverArgs_3783_);
lean_ctor_set(v_reuseFailAlloc_3806_, 17, v_version_3784_);
lean_ctor_set(v_reuseFailAlloc_3806_, 18, v_versionTags_3785_);
lean_ctor_set(v_reuseFailAlloc_3806_, 19, v_description_3786_);
lean_ctor_set(v_reuseFailAlloc_3806_, 20, v_keywords_3787_);
lean_ctor_set(v_reuseFailAlloc_3806_, 21, v_homepage_3788_);
lean_ctor_set(v_reuseFailAlloc_3806_, 22, v_license_3789_);
lean_ctor_set(v_reuseFailAlloc_3806_, 23, v_licenseFiles_3790_);
lean_ctor_set(v_reuseFailAlloc_3806_, 24, v_readmeFile_3791_);
lean_ctor_set(v_reuseFailAlloc_3806_, 25, v_enableArtifactCache_x3f_3793_);
lean_ctor_set(v_reuseFailAlloc_3806_, 26, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3806_, 27, v_builtinLint_x3f_3797_);
lean_ctor_set(v_reuseFailAlloc_3806_, 28, v_checks_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29, v_bootstrap_3766_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29 + 1, v_precompileModules_3768_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3778_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29 + 3, v_reservoir_3792_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_3795_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29 + 5, v_allowImportAll_3796_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*29 + 6, v_fixedToolchain_3799_);
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
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg(){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = ((lean_object*)(l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___closed__3));
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg___boxed(lean_object* v___dummy_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
return v_res_3819_;
}
}
static lean_object* _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___redArg();
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(lean_object* v_p_3821_, lean_object* v_n_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___boxed(lean_object* v_p_3824_, lean_object* v_n_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj(v_p_3824_, v_n_3825_);
lean_dec(v_n_3825_);
lean_dec(v_p_3824_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg(){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg___boxed(lean_object* v___dummy_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___redArg();
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(lean_object* v_p_3831_, lean_object* v_n_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_instConfigField___boxed(lean_object* v_p_3834_, lean_object* v_n_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lake_PackageConfig_restoreAllArtifacts_instConfigField(v_p_3834_, v_n_3835_);
lean_dec(v_n_3835_);
lean_dec(v_p_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___redArg();
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(lean_object* v_p_3841_, lean_object* v_n_3842_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_obj_once(&l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0, &l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_restoreAllArtifacts_x3f___proj___closed__0);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField___boxed(lean_object* v_p_3844_, lean_object* v_n_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lake_PackageConfig_restoreAllArtifacts_x3f_instConfigField(v_p_3844_, v_n_3845_);
lean_dec(v_n_3845_);
lean_dec(v_p_3844_);
return v_res_3846_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(lean_object* v_cfg_3847_){
_start:
{
uint8_t v_libPrefixOnWindows_3848_; 
v_libPrefixOnWindows_3848_ = lean_ctor_get_uint8(v_cfg_3847_, sizeof(void*)*29 + 4);
return v_libPrefixOnWindows_3848_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0___boxed(lean_object* v_cfg_3849_){
_start:
{
uint8_t v_res_3850_; lean_object* v_r_3851_; 
v_res_3850_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__0(v_cfg_3849_);
lean_dec_ref(v_cfg_3849_);
v_r_3851_ = lean_box(v_res_3850_);
return v_r_3851_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(uint8_t v_val_3852_, lean_object* v_cfg_3853_){
_start:
{
lean_object* v_toWorkspaceConfig_3854_; lean_object* v_toLeanConfig_3855_; uint8_t v_bootstrap_3856_; lean_object* v_extraDepTargets_3857_; uint8_t v_precompileModules_3858_; lean_object* v_moreGlobalServerArgs_3859_; lean_object* v_srcDir_3860_; lean_object* v_buildDir_3861_; lean_object* v_leanLibDir_3862_; lean_object* v_nativeLibDir_3863_; lean_object* v_binDir_3864_; lean_object* v_irDir_3865_; lean_object* v_releaseRepo_3866_; lean_object* v_buildArchive_3867_; uint8_t v_preferReleaseBuild_3868_; lean_object* v_downloadCacheService_x3f_3869_; lean_object* v_testDriver_3870_; lean_object* v_testDriverArgs_3871_; lean_object* v_lintDriver_3872_; lean_object* v_lintDriverArgs_3873_; lean_object* v_version_3874_; lean_object* v_versionTags_3875_; lean_object* v_description_3876_; lean_object* v_keywords_3877_; lean_object* v_homepage_3878_; lean_object* v_license_3879_; lean_object* v_licenseFiles_3880_; lean_object* v_readmeFile_3881_; uint8_t v_reservoir_3882_; lean_object* v_enableArtifactCache_x3f_3883_; lean_object* v_restoreAllArtifacts_x3f_3884_; uint8_t v_allowImportAll_3885_; lean_object* v_builtinLint_x3f_3886_; lean_object* v_checks_3887_; uint8_t v_fixedToolchain_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_toWorkspaceConfig_3854_ = lean_ctor_get(v_cfg_3853_, 0);
v_toLeanConfig_3855_ = lean_ctor_get(v_cfg_3853_, 1);
v_bootstrap_3856_ = lean_ctor_get_uint8(v_cfg_3853_, sizeof(void*)*29);
v_extraDepTargets_3857_ = lean_ctor_get(v_cfg_3853_, 2);
v_precompileModules_3858_ = lean_ctor_get_uint8(v_cfg_3853_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3859_ = lean_ctor_get(v_cfg_3853_, 3);
v_srcDir_3860_ = lean_ctor_get(v_cfg_3853_, 4);
v_buildDir_3861_ = lean_ctor_get(v_cfg_3853_, 5);
v_leanLibDir_3862_ = lean_ctor_get(v_cfg_3853_, 6);
v_nativeLibDir_3863_ = lean_ctor_get(v_cfg_3853_, 7);
v_binDir_3864_ = lean_ctor_get(v_cfg_3853_, 8);
v_irDir_3865_ = lean_ctor_get(v_cfg_3853_, 9);
v_releaseRepo_3866_ = lean_ctor_get(v_cfg_3853_, 10);
v_buildArchive_3867_ = lean_ctor_get(v_cfg_3853_, 11);
v_preferReleaseBuild_3868_ = lean_ctor_get_uint8(v_cfg_3853_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3869_ = lean_ctor_get(v_cfg_3853_, 12);
v_testDriver_3870_ = lean_ctor_get(v_cfg_3853_, 13);
v_testDriverArgs_3871_ = lean_ctor_get(v_cfg_3853_, 14);
v_lintDriver_3872_ = lean_ctor_get(v_cfg_3853_, 15);
v_lintDriverArgs_3873_ = lean_ctor_get(v_cfg_3853_, 16);
v_version_3874_ = lean_ctor_get(v_cfg_3853_, 17);
v_versionTags_3875_ = lean_ctor_get(v_cfg_3853_, 18);
v_description_3876_ = lean_ctor_get(v_cfg_3853_, 19);
v_keywords_3877_ = lean_ctor_get(v_cfg_3853_, 20);
v_homepage_3878_ = lean_ctor_get(v_cfg_3853_, 21);
v_license_3879_ = lean_ctor_get(v_cfg_3853_, 22);
v_licenseFiles_3880_ = lean_ctor_get(v_cfg_3853_, 23);
v_readmeFile_3881_ = lean_ctor_get(v_cfg_3853_, 24);
v_reservoir_3882_ = lean_ctor_get_uint8(v_cfg_3853_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3883_ = lean_ctor_get(v_cfg_3853_, 25);
v_restoreAllArtifacts_x3f_3884_ = lean_ctor_get(v_cfg_3853_, 26);
v_allowImportAll_3885_ = lean_ctor_get_uint8(v_cfg_3853_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3886_ = lean_ctor_get(v_cfg_3853_, 27);
v_checks_3887_ = lean_ctor_get(v_cfg_3853_, 28);
v_fixedToolchain_3888_ = lean_ctor_get_uint8(v_cfg_3853_, sizeof(void*)*29 + 6);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_cfg_3853_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v_cfg_3853_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_checks_3887_);
lean_inc(v_builtinLint_x3f_3886_);
lean_inc(v_restoreAllArtifacts_x3f_3884_);
lean_inc(v_enableArtifactCache_x3f_3883_);
lean_inc(v_readmeFile_3881_);
lean_inc(v_licenseFiles_3880_);
lean_inc(v_license_3879_);
lean_inc(v_homepage_3878_);
lean_inc(v_keywords_3877_);
lean_inc(v_description_3876_);
lean_inc(v_versionTags_3875_);
lean_inc(v_version_3874_);
lean_inc(v_lintDriverArgs_3873_);
lean_inc(v_lintDriver_3872_);
lean_inc(v_testDriverArgs_3871_);
lean_inc(v_testDriver_3870_);
lean_inc(v_downloadCacheService_x3f_3869_);
lean_inc(v_buildArchive_3867_);
lean_inc(v_releaseRepo_3866_);
lean_inc(v_irDir_3865_);
lean_inc(v_binDir_3864_);
lean_inc(v_nativeLibDir_3863_);
lean_inc(v_leanLibDir_3862_);
lean_inc(v_buildDir_3861_);
lean_inc(v_srcDir_3860_);
lean_inc(v_moreGlobalServerArgs_3859_);
lean_inc(v_extraDepTargets_3857_);
lean_inc(v_toLeanConfig_3855_);
lean_inc(v_toWorkspaceConfig_3854_);
lean_dec(v_cfg_3853_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_toWorkspaceConfig_3854_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_toLeanConfig_3855_);
lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_extraDepTargets_3857_);
lean_ctor_set(v_reuseFailAlloc_3894_, 3, v_moreGlobalServerArgs_3859_);
lean_ctor_set(v_reuseFailAlloc_3894_, 4, v_srcDir_3860_);
lean_ctor_set(v_reuseFailAlloc_3894_, 5, v_buildDir_3861_);
lean_ctor_set(v_reuseFailAlloc_3894_, 6, v_leanLibDir_3862_);
lean_ctor_set(v_reuseFailAlloc_3894_, 7, v_nativeLibDir_3863_);
lean_ctor_set(v_reuseFailAlloc_3894_, 8, v_binDir_3864_);
lean_ctor_set(v_reuseFailAlloc_3894_, 9, v_irDir_3865_);
lean_ctor_set(v_reuseFailAlloc_3894_, 10, v_releaseRepo_3866_);
lean_ctor_set(v_reuseFailAlloc_3894_, 11, v_buildArchive_3867_);
lean_ctor_set(v_reuseFailAlloc_3894_, 12, v_downloadCacheService_x3f_3869_);
lean_ctor_set(v_reuseFailAlloc_3894_, 13, v_testDriver_3870_);
lean_ctor_set(v_reuseFailAlloc_3894_, 14, v_testDriverArgs_3871_);
lean_ctor_set(v_reuseFailAlloc_3894_, 15, v_lintDriver_3872_);
lean_ctor_set(v_reuseFailAlloc_3894_, 16, v_lintDriverArgs_3873_);
lean_ctor_set(v_reuseFailAlloc_3894_, 17, v_version_3874_);
lean_ctor_set(v_reuseFailAlloc_3894_, 18, v_versionTags_3875_);
lean_ctor_set(v_reuseFailAlloc_3894_, 19, v_description_3876_);
lean_ctor_set(v_reuseFailAlloc_3894_, 20, v_keywords_3877_);
lean_ctor_set(v_reuseFailAlloc_3894_, 21, v_homepage_3878_);
lean_ctor_set(v_reuseFailAlloc_3894_, 22, v_license_3879_);
lean_ctor_set(v_reuseFailAlloc_3894_, 23, v_licenseFiles_3880_);
lean_ctor_set(v_reuseFailAlloc_3894_, 24, v_readmeFile_3881_);
lean_ctor_set(v_reuseFailAlloc_3894_, 25, v_enableArtifactCache_x3f_3883_);
lean_ctor_set(v_reuseFailAlloc_3894_, 26, v_restoreAllArtifacts_x3f_3884_);
lean_ctor_set(v_reuseFailAlloc_3894_, 27, v_builtinLint_x3f_3886_);
lean_ctor_set(v_reuseFailAlloc_3894_, 28, v_checks_3887_);
lean_ctor_set_uint8(v_reuseFailAlloc_3894_, sizeof(void*)*29, v_bootstrap_3856_);
lean_ctor_set_uint8(v_reuseFailAlloc_3894_, sizeof(void*)*29 + 1, v_precompileModules_3858_);
lean_ctor_set_uint8(v_reuseFailAlloc_3894_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3868_);
lean_ctor_set_uint8(v_reuseFailAlloc_3894_, sizeof(void*)*29 + 3, v_reservoir_3882_);
lean_ctor_set_uint8(v_reuseFailAlloc_3894_, sizeof(void*)*29 + 5, v_allowImportAll_3885_);
lean_ctor_set_uint8(v_reuseFailAlloc_3894_, sizeof(void*)*29 + 6, v_fixedToolchain_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_ctor_set_uint8(v___x_3893_, sizeof(void*)*29 + 4, v_val_3852_);
return v___x_3893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1___boxed(lean_object* v_val_3896_, lean_object* v_cfg_3897_){
_start:
{
uint8_t v_val_144__boxed_3898_; lean_object* v_res_3899_; 
v_val_144__boxed_3898_ = lean_unbox(v_val_3896_);
v_res_3899_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__1(v_val_144__boxed_3898_, v_cfg_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___lam__2(lean_object* v_f_3900_, lean_object* v_cfg_3901_){
_start:
{
lean_object* v_toWorkspaceConfig_3902_; lean_object* v_toLeanConfig_3903_; uint8_t v_bootstrap_3904_; lean_object* v_extraDepTargets_3905_; uint8_t v_precompileModules_3906_; lean_object* v_moreGlobalServerArgs_3907_; lean_object* v_srcDir_3908_; lean_object* v_buildDir_3909_; lean_object* v_leanLibDir_3910_; lean_object* v_nativeLibDir_3911_; lean_object* v_binDir_3912_; lean_object* v_irDir_3913_; lean_object* v_releaseRepo_3914_; lean_object* v_buildArchive_3915_; uint8_t v_preferReleaseBuild_3916_; lean_object* v_downloadCacheService_x3f_3917_; lean_object* v_testDriver_3918_; lean_object* v_testDriverArgs_3919_; lean_object* v_lintDriver_3920_; lean_object* v_lintDriverArgs_3921_; lean_object* v_version_3922_; lean_object* v_versionTags_3923_; lean_object* v_description_3924_; lean_object* v_keywords_3925_; lean_object* v_homepage_3926_; lean_object* v_license_3927_; lean_object* v_licenseFiles_3928_; lean_object* v_readmeFile_3929_; uint8_t v_reservoir_3930_; lean_object* v_enableArtifactCache_x3f_3931_; lean_object* v_restoreAllArtifacts_x3f_3932_; uint8_t v_libPrefixOnWindows_3933_; uint8_t v_allowImportAll_3934_; lean_object* v_builtinLint_x3f_3935_; lean_object* v_checks_3936_; uint8_t v_fixedToolchain_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3947_; 
v_toWorkspaceConfig_3902_ = lean_ctor_get(v_cfg_3901_, 0);
v_toLeanConfig_3903_ = lean_ctor_get(v_cfg_3901_, 1);
v_bootstrap_3904_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29);
v_extraDepTargets_3905_ = lean_ctor_get(v_cfg_3901_, 2);
v_precompileModules_3906_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3907_ = lean_ctor_get(v_cfg_3901_, 3);
v_srcDir_3908_ = lean_ctor_get(v_cfg_3901_, 4);
v_buildDir_3909_ = lean_ctor_get(v_cfg_3901_, 5);
v_leanLibDir_3910_ = lean_ctor_get(v_cfg_3901_, 6);
v_nativeLibDir_3911_ = lean_ctor_get(v_cfg_3901_, 7);
v_binDir_3912_ = lean_ctor_get(v_cfg_3901_, 8);
v_irDir_3913_ = lean_ctor_get(v_cfg_3901_, 9);
v_releaseRepo_3914_ = lean_ctor_get(v_cfg_3901_, 10);
v_buildArchive_3915_ = lean_ctor_get(v_cfg_3901_, 11);
v_preferReleaseBuild_3916_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3917_ = lean_ctor_get(v_cfg_3901_, 12);
v_testDriver_3918_ = lean_ctor_get(v_cfg_3901_, 13);
v_testDriverArgs_3919_ = lean_ctor_get(v_cfg_3901_, 14);
v_lintDriver_3920_ = lean_ctor_get(v_cfg_3901_, 15);
v_lintDriverArgs_3921_ = lean_ctor_get(v_cfg_3901_, 16);
v_version_3922_ = lean_ctor_get(v_cfg_3901_, 17);
v_versionTags_3923_ = lean_ctor_get(v_cfg_3901_, 18);
v_description_3924_ = lean_ctor_get(v_cfg_3901_, 19);
v_keywords_3925_ = lean_ctor_get(v_cfg_3901_, 20);
v_homepage_3926_ = lean_ctor_get(v_cfg_3901_, 21);
v_license_3927_ = lean_ctor_get(v_cfg_3901_, 22);
v_licenseFiles_3928_ = lean_ctor_get(v_cfg_3901_, 23);
v_readmeFile_3929_ = lean_ctor_get(v_cfg_3901_, 24);
v_reservoir_3930_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_3931_ = lean_ctor_get(v_cfg_3901_, 25);
v_restoreAllArtifacts_x3f_3932_ = lean_ctor_get(v_cfg_3901_, 26);
v_libPrefixOnWindows_3933_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29 + 4);
v_allowImportAll_3934_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_3935_ = lean_ctor_get(v_cfg_3901_, 27);
v_checks_3936_ = lean_ctor_get(v_cfg_3901_, 28);
v_fixedToolchain_3937_ = lean_ctor_get_uint8(v_cfg_3901_, sizeof(void*)*29 + 6);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_cfg_3901_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3939_ = v_cfg_3901_;
v_isShared_3940_ = v_isSharedCheck_3947_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_checks_3936_);
lean_inc(v_builtinLint_x3f_3935_);
lean_inc(v_restoreAllArtifacts_x3f_3932_);
lean_inc(v_enableArtifactCache_x3f_3931_);
lean_inc(v_readmeFile_3929_);
lean_inc(v_licenseFiles_3928_);
lean_inc(v_license_3927_);
lean_inc(v_homepage_3926_);
lean_inc(v_keywords_3925_);
lean_inc(v_description_3924_);
lean_inc(v_versionTags_3923_);
lean_inc(v_version_3922_);
lean_inc(v_lintDriverArgs_3921_);
lean_inc(v_lintDriver_3920_);
lean_inc(v_testDriverArgs_3919_);
lean_inc(v_testDriver_3918_);
lean_inc(v_downloadCacheService_x3f_3917_);
lean_inc(v_buildArchive_3915_);
lean_inc(v_releaseRepo_3914_);
lean_inc(v_irDir_3913_);
lean_inc(v_binDir_3912_);
lean_inc(v_nativeLibDir_3911_);
lean_inc(v_leanLibDir_3910_);
lean_inc(v_buildDir_3909_);
lean_inc(v_srcDir_3908_);
lean_inc(v_moreGlobalServerArgs_3907_);
lean_inc(v_extraDepTargets_3905_);
lean_inc(v_toLeanConfig_3903_);
lean_inc(v_toWorkspaceConfig_3902_);
lean_dec(v_cfg_3901_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3947_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3941_ = lean_box(v_libPrefixOnWindows_3933_);
v___x_3942_ = lean_apply_1(v_f_3900_, v___x_3941_);
if (v_isShared_3940_ == 0)
{
v___x_3944_ = v___x_3939_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_toWorkspaceConfig_3902_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_toLeanConfig_3903_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_extraDepTargets_3905_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_moreGlobalServerArgs_3907_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_srcDir_3908_);
lean_ctor_set(v_reuseFailAlloc_3946_, 5, v_buildDir_3909_);
lean_ctor_set(v_reuseFailAlloc_3946_, 6, v_leanLibDir_3910_);
lean_ctor_set(v_reuseFailAlloc_3946_, 7, v_nativeLibDir_3911_);
lean_ctor_set(v_reuseFailAlloc_3946_, 8, v_binDir_3912_);
lean_ctor_set(v_reuseFailAlloc_3946_, 9, v_irDir_3913_);
lean_ctor_set(v_reuseFailAlloc_3946_, 10, v_releaseRepo_3914_);
lean_ctor_set(v_reuseFailAlloc_3946_, 11, v_buildArchive_3915_);
lean_ctor_set(v_reuseFailAlloc_3946_, 12, v_downloadCacheService_x3f_3917_);
lean_ctor_set(v_reuseFailAlloc_3946_, 13, v_testDriver_3918_);
lean_ctor_set(v_reuseFailAlloc_3946_, 14, v_testDriverArgs_3919_);
lean_ctor_set(v_reuseFailAlloc_3946_, 15, v_lintDriver_3920_);
lean_ctor_set(v_reuseFailAlloc_3946_, 16, v_lintDriverArgs_3921_);
lean_ctor_set(v_reuseFailAlloc_3946_, 17, v_version_3922_);
lean_ctor_set(v_reuseFailAlloc_3946_, 18, v_versionTags_3923_);
lean_ctor_set(v_reuseFailAlloc_3946_, 19, v_description_3924_);
lean_ctor_set(v_reuseFailAlloc_3946_, 20, v_keywords_3925_);
lean_ctor_set(v_reuseFailAlloc_3946_, 21, v_homepage_3926_);
lean_ctor_set(v_reuseFailAlloc_3946_, 22, v_license_3927_);
lean_ctor_set(v_reuseFailAlloc_3946_, 23, v_licenseFiles_3928_);
lean_ctor_set(v_reuseFailAlloc_3946_, 24, v_readmeFile_3929_);
lean_ctor_set(v_reuseFailAlloc_3946_, 25, v_enableArtifactCache_x3f_3931_);
lean_ctor_set(v_reuseFailAlloc_3946_, 26, v_restoreAllArtifacts_x3f_3932_);
lean_ctor_set(v_reuseFailAlloc_3946_, 27, v_builtinLint_x3f_3935_);
lean_ctor_set(v_reuseFailAlloc_3946_, 28, v_checks_3936_);
lean_ctor_set_uint8(v_reuseFailAlloc_3946_, sizeof(void*)*29, v_bootstrap_3904_);
lean_ctor_set_uint8(v_reuseFailAlloc_3946_, sizeof(void*)*29 + 1, v_precompileModules_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3946_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3946_, sizeof(void*)*29 + 3, v_reservoir_3930_);
v___x_3944_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
uint8_t v___x_3945_; 
v___x_3945_ = lean_unbox(v___x_3942_);
lean_ctor_set_uint8(v___x_3944_, sizeof(void*)*29 + 4, v___x_3945_);
lean_ctor_set_uint8(v___x_3944_, sizeof(void*)*29 + 5, v_allowImportAll_3934_);
lean_ctor_set_uint8(v___x_3944_, sizeof(void*)*29 + 6, v_fixedToolchain_3937_);
return v___x_3944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg(){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = ((lean_object*)(l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___closed__3));
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg___boxed(lean_object* v___dummy_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
return v_res_3959_;
}
}
static lean_object* _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0(void){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lake_PackageConfig_libPrefixOnWindows___proj___redArg();
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj(lean_object* v_p_3961_, lean_object* v_n_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows___proj___boxed(lean_object* v_p_3964_, lean_object* v_n_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Lake_PackageConfig_libPrefixOnWindows___proj(v_p_3964_, v_n_3965_);
lean_dec(v_n_3965_);
lean_dec(v_p_3964_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg(){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg___boxed(lean_object* v___dummy_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___redArg();
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(lean_object* v_p_3971_, lean_object* v_n_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_obj_once(&l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0, &l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0_once, _init_l_Lake_PackageConfig_libPrefixOnWindows___proj___closed__0);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_libPrefixOnWindows_instConfigField___boxed(lean_object* v_p_3974_, lean_object* v_n_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lake_PackageConfig_libPrefixOnWindows_instConfigField(v_p_3974_, v_n_3975_);
lean_dec(v_n_3975_);
lean_dec(v_p_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(lean_object* v_cfg_3977_){
_start:
{
uint8_t v_allowImportAll_3978_; 
v_allowImportAll_3978_ = lean_ctor_get_uint8(v_cfg_3977_, sizeof(void*)*29 + 5);
return v_allowImportAll_3978_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0___boxed(lean_object* v_cfg_3979_){
_start:
{
uint8_t v_res_3980_; lean_object* v_r_3981_; 
v_res_3980_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__0(v_cfg_3979_);
lean_dec_ref(v_cfg_3979_);
v_r_3981_ = lean_box(v_res_3980_);
return v_r_3981_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(uint8_t v_val_3982_, lean_object* v_cfg_3983_){
_start:
{
lean_object* v_toWorkspaceConfig_3984_; lean_object* v_toLeanConfig_3985_; uint8_t v_bootstrap_3986_; lean_object* v_extraDepTargets_3987_; uint8_t v_precompileModules_3988_; lean_object* v_moreGlobalServerArgs_3989_; lean_object* v_srcDir_3990_; lean_object* v_buildDir_3991_; lean_object* v_leanLibDir_3992_; lean_object* v_nativeLibDir_3993_; lean_object* v_binDir_3994_; lean_object* v_irDir_3995_; lean_object* v_releaseRepo_3996_; lean_object* v_buildArchive_3997_; uint8_t v_preferReleaseBuild_3998_; lean_object* v_downloadCacheService_x3f_3999_; lean_object* v_testDriver_4000_; lean_object* v_testDriverArgs_4001_; lean_object* v_lintDriver_4002_; lean_object* v_lintDriverArgs_4003_; lean_object* v_version_4004_; lean_object* v_versionTags_4005_; lean_object* v_description_4006_; lean_object* v_keywords_4007_; lean_object* v_homepage_4008_; lean_object* v_license_4009_; lean_object* v_licenseFiles_4010_; lean_object* v_readmeFile_4011_; uint8_t v_reservoir_4012_; lean_object* v_enableArtifactCache_x3f_4013_; lean_object* v_restoreAllArtifacts_x3f_4014_; uint8_t v_libPrefixOnWindows_4015_; lean_object* v_builtinLint_x3f_4016_; lean_object* v_checks_4017_; uint8_t v_fixedToolchain_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
v_toWorkspaceConfig_3984_ = lean_ctor_get(v_cfg_3983_, 0);
v_toLeanConfig_3985_ = lean_ctor_get(v_cfg_3983_, 1);
v_bootstrap_3986_ = lean_ctor_get_uint8(v_cfg_3983_, sizeof(void*)*29);
v_extraDepTargets_3987_ = lean_ctor_get(v_cfg_3983_, 2);
v_precompileModules_3988_ = lean_ctor_get_uint8(v_cfg_3983_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_3989_ = lean_ctor_get(v_cfg_3983_, 3);
v_srcDir_3990_ = lean_ctor_get(v_cfg_3983_, 4);
v_buildDir_3991_ = lean_ctor_get(v_cfg_3983_, 5);
v_leanLibDir_3992_ = lean_ctor_get(v_cfg_3983_, 6);
v_nativeLibDir_3993_ = lean_ctor_get(v_cfg_3983_, 7);
v_binDir_3994_ = lean_ctor_get(v_cfg_3983_, 8);
v_irDir_3995_ = lean_ctor_get(v_cfg_3983_, 9);
v_releaseRepo_3996_ = lean_ctor_get(v_cfg_3983_, 10);
v_buildArchive_3997_ = lean_ctor_get(v_cfg_3983_, 11);
v_preferReleaseBuild_3998_ = lean_ctor_get_uint8(v_cfg_3983_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_3999_ = lean_ctor_get(v_cfg_3983_, 12);
v_testDriver_4000_ = lean_ctor_get(v_cfg_3983_, 13);
v_testDriverArgs_4001_ = lean_ctor_get(v_cfg_3983_, 14);
v_lintDriver_4002_ = lean_ctor_get(v_cfg_3983_, 15);
v_lintDriverArgs_4003_ = lean_ctor_get(v_cfg_3983_, 16);
v_version_4004_ = lean_ctor_get(v_cfg_3983_, 17);
v_versionTags_4005_ = lean_ctor_get(v_cfg_3983_, 18);
v_description_4006_ = lean_ctor_get(v_cfg_3983_, 19);
v_keywords_4007_ = lean_ctor_get(v_cfg_3983_, 20);
v_homepage_4008_ = lean_ctor_get(v_cfg_3983_, 21);
v_license_4009_ = lean_ctor_get(v_cfg_3983_, 22);
v_licenseFiles_4010_ = lean_ctor_get(v_cfg_3983_, 23);
v_readmeFile_4011_ = lean_ctor_get(v_cfg_3983_, 24);
v_reservoir_4012_ = lean_ctor_get_uint8(v_cfg_3983_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4013_ = lean_ctor_get(v_cfg_3983_, 25);
v_restoreAllArtifacts_x3f_4014_ = lean_ctor_get(v_cfg_3983_, 26);
v_libPrefixOnWindows_4015_ = lean_ctor_get_uint8(v_cfg_3983_, sizeof(void*)*29 + 4);
v_builtinLint_x3f_4016_ = lean_ctor_get(v_cfg_3983_, 27);
v_checks_4017_ = lean_ctor_get(v_cfg_3983_, 28);
v_fixedToolchain_4018_ = lean_ctor_get_uint8(v_cfg_3983_, sizeof(void*)*29 + 6);
v_isSharedCheck_4025_ = !lean_is_exclusive(v_cfg_3983_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v_cfg_3983_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_checks_4017_);
lean_inc(v_builtinLint_x3f_4016_);
lean_inc(v_restoreAllArtifacts_x3f_4014_);
lean_inc(v_enableArtifactCache_x3f_4013_);
lean_inc(v_readmeFile_4011_);
lean_inc(v_licenseFiles_4010_);
lean_inc(v_license_4009_);
lean_inc(v_homepage_4008_);
lean_inc(v_keywords_4007_);
lean_inc(v_description_4006_);
lean_inc(v_versionTags_4005_);
lean_inc(v_version_4004_);
lean_inc(v_lintDriverArgs_4003_);
lean_inc(v_lintDriver_4002_);
lean_inc(v_testDriverArgs_4001_);
lean_inc(v_testDriver_4000_);
lean_inc(v_downloadCacheService_x3f_3999_);
lean_inc(v_buildArchive_3997_);
lean_inc(v_releaseRepo_3996_);
lean_inc(v_irDir_3995_);
lean_inc(v_binDir_3994_);
lean_inc(v_nativeLibDir_3993_);
lean_inc(v_leanLibDir_3992_);
lean_inc(v_buildDir_3991_);
lean_inc(v_srcDir_3990_);
lean_inc(v_moreGlobalServerArgs_3989_);
lean_inc(v_extraDepTargets_3987_);
lean_inc(v_toLeanConfig_3985_);
lean_inc(v_toWorkspaceConfig_3984_);
lean_dec(v_cfg_3983_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_toWorkspaceConfig_3984_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_toLeanConfig_3985_);
lean_ctor_set(v_reuseFailAlloc_4024_, 2, v_extraDepTargets_3987_);
lean_ctor_set(v_reuseFailAlloc_4024_, 3, v_moreGlobalServerArgs_3989_);
lean_ctor_set(v_reuseFailAlloc_4024_, 4, v_srcDir_3990_);
lean_ctor_set(v_reuseFailAlloc_4024_, 5, v_buildDir_3991_);
lean_ctor_set(v_reuseFailAlloc_4024_, 6, v_leanLibDir_3992_);
lean_ctor_set(v_reuseFailAlloc_4024_, 7, v_nativeLibDir_3993_);
lean_ctor_set(v_reuseFailAlloc_4024_, 8, v_binDir_3994_);
lean_ctor_set(v_reuseFailAlloc_4024_, 9, v_irDir_3995_);
lean_ctor_set(v_reuseFailAlloc_4024_, 10, v_releaseRepo_3996_);
lean_ctor_set(v_reuseFailAlloc_4024_, 11, v_buildArchive_3997_);
lean_ctor_set(v_reuseFailAlloc_4024_, 12, v_downloadCacheService_x3f_3999_);
lean_ctor_set(v_reuseFailAlloc_4024_, 13, v_testDriver_4000_);
lean_ctor_set(v_reuseFailAlloc_4024_, 14, v_testDriverArgs_4001_);
lean_ctor_set(v_reuseFailAlloc_4024_, 15, v_lintDriver_4002_);
lean_ctor_set(v_reuseFailAlloc_4024_, 16, v_lintDriverArgs_4003_);
lean_ctor_set(v_reuseFailAlloc_4024_, 17, v_version_4004_);
lean_ctor_set(v_reuseFailAlloc_4024_, 18, v_versionTags_4005_);
lean_ctor_set(v_reuseFailAlloc_4024_, 19, v_description_4006_);
lean_ctor_set(v_reuseFailAlloc_4024_, 20, v_keywords_4007_);
lean_ctor_set(v_reuseFailAlloc_4024_, 21, v_homepage_4008_);
lean_ctor_set(v_reuseFailAlloc_4024_, 22, v_license_4009_);
lean_ctor_set(v_reuseFailAlloc_4024_, 23, v_licenseFiles_4010_);
lean_ctor_set(v_reuseFailAlloc_4024_, 24, v_readmeFile_4011_);
lean_ctor_set(v_reuseFailAlloc_4024_, 25, v_enableArtifactCache_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4024_, 26, v_restoreAllArtifacts_x3f_4014_);
lean_ctor_set(v_reuseFailAlloc_4024_, 27, v_builtinLint_x3f_4016_);
lean_ctor_set(v_reuseFailAlloc_4024_, 28, v_checks_4017_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*29, v_bootstrap_3986_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*29 + 1, v_precompileModules_3988_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*29 + 2, v_preferReleaseBuild_3998_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*29 + 3, v_reservoir_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4015_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*29 + 6, v_fixedToolchain_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_ctor_set_uint8(v___x_4023_, sizeof(void*)*29 + 5, v_val_3982_);
return v___x_4023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1___boxed(lean_object* v_val_4026_, lean_object* v_cfg_4027_){
_start:
{
uint8_t v_val_144__boxed_4028_; lean_object* v_res_4029_; 
v_val_144__boxed_4028_ = lean_unbox(v_val_4026_);
v_res_4029_ = l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__1(v_val_144__boxed_4028_, v_cfg_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___lam__2(lean_object* v_f_4030_, lean_object* v_cfg_4031_){
_start:
{
lean_object* v_toWorkspaceConfig_4032_; lean_object* v_toLeanConfig_4033_; uint8_t v_bootstrap_4034_; lean_object* v_extraDepTargets_4035_; uint8_t v_precompileModules_4036_; lean_object* v_moreGlobalServerArgs_4037_; lean_object* v_srcDir_4038_; lean_object* v_buildDir_4039_; lean_object* v_leanLibDir_4040_; lean_object* v_nativeLibDir_4041_; lean_object* v_binDir_4042_; lean_object* v_irDir_4043_; lean_object* v_releaseRepo_4044_; lean_object* v_buildArchive_4045_; uint8_t v_preferReleaseBuild_4046_; lean_object* v_downloadCacheService_x3f_4047_; lean_object* v_testDriver_4048_; lean_object* v_testDriverArgs_4049_; lean_object* v_lintDriver_4050_; lean_object* v_lintDriverArgs_4051_; lean_object* v_version_4052_; lean_object* v_versionTags_4053_; lean_object* v_description_4054_; lean_object* v_keywords_4055_; lean_object* v_homepage_4056_; lean_object* v_license_4057_; lean_object* v_licenseFiles_4058_; lean_object* v_readmeFile_4059_; uint8_t v_reservoir_4060_; lean_object* v_enableArtifactCache_x3f_4061_; lean_object* v_restoreAllArtifacts_x3f_4062_; uint8_t v_libPrefixOnWindows_4063_; uint8_t v_allowImportAll_4064_; lean_object* v_builtinLint_x3f_4065_; lean_object* v_checks_4066_; uint8_t v_fixedToolchain_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4077_; 
v_toWorkspaceConfig_4032_ = lean_ctor_get(v_cfg_4031_, 0);
v_toLeanConfig_4033_ = lean_ctor_get(v_cfg_4031_, 1);
v_bootstrap_4034_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29);
v_extraDepTargets_4035_ = lean_ctor_get(v_cfg_4031_, 2);
v_precompileModules_4036_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4037_ = lean_ctor_get(v_cfg_4031_, 3);
v_srcDir_4038_ = lean_ctor_get(v_cfg_4031_, 4);
v_buildDir_4039_ = lean_ctor_get(v_cfg_4031_, 5);
v_leanLibDir_4040_ = lean_ctor_get(v_cfg_4031_, 6);
v_nativeLibDir_4041_ = lean_ctor_get(v_cfg_4031_, 7);
v_binDir_4042_ = lean_ctor_get(v_cfg_4031_, 8);
v_irDir_4043_ = lean_ctor_get(v_cfg_4031_, 9);
v_releaseRepo_4044_ = lean_ctor_get(v_cfg_4031_, 10);
v_buildArchive_4045_ = lean_ctor_get(v_cfg_4031_, 11);
v_preferReleaseBuild_4046_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4047_ = lean_ctor_get(v_cfg_4031_, 12);
v_testDriver_4048_ = lean_ctor_get(v_cfg_4031_, 13);
v_testDriverArgs_4049_ = lean_ctor_get(v_cfg_4031_, 14);
v_lintDriver_4050_ = lean_ctor_get(v_cfg_4031_, 15);
v_lintDriverArgs_4051_ = lean_ctor_get(v_cfg_4031_, 16);
v_version_4052_ = lean_ctor_get(v_cfg_4031_, 17);
v_versionTags_4053_ = lean_ctor_get(v_cfg_4031_, 18);
v_description_4054_ = lean_ctor_get(v_cfg_4031_, 19);
v_keywords_4055_ = lean_ctor_get(v_cfg_4031_, 20);
v_homepage_4056_ = lean_ctor_get(v_cfg_4031_, 21);
v_license_4057_ = lean_ctor_get(v_cfg_4031_, 22);
v_licenseFiles_4058_ = lean_ctor_get(v_cfg_4031_, 23);
v_readmeFile_4059_ = lean_ctor_get(v_cfg_4031_, 24);
v_reservoir_4060_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4061_ = lean_ctor_get(v_cfg_4031_, 25);
v_restoreAllArtifacts_x3f_4062_ = lean_ctor_get(v_cfg_4031_, 26);
v_libPrefixOnWindows_4063_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29 + 4);
v_allowImportAll_4064_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4065_ = lean_ctor_get(v_cfg_4031_, 27);
v_checks_4066_ = lean_ctor_get(v_cfg_4031_, 28);
v_fixedToolchain_4067_ = lean_ctor_get_uint8(v_cfg_4031_, sizeof(void*)*29 + 6);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_cfg_4031_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4069_ = v_cfg_4031_;
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_checks_4066_);
lean_inc(v_builtinLint_x3f_4065_);
lean_inc(v_restoreAllArtifacts_x3f_4062_);
lean_inc(v_enableArtifactCache_x3f_4061_);
lean_inc(v_readmeFile_4059_);
lean_inc(v_licenseFiles_4058_);
lean_inc(v_license_4057_);
lean_inc(v_homepage_4056_);
lean_inc(v_keywords_4055_);
lean_inc(v_description_4054_);
lean_inc(v_versionTags_4053_);
lean_inc(v_version_4052_);
lean_inc(v_lintDriverArgs_4051_);
lean_inc(v_lintDriver_4050_);
lean_inc(v_testDriverArgs_4049_);
lean_inc(v_testDriver_4048_);
lean_inc(v_downloadCacheService_x3f_4047_);
lean_inc(v_buildArchive_4045_);
lean_inc(v_releaseRepo_4044_);
lean_inc(v_irDir_4043_);
lean_inc(v_binDir_4042_);
lean_inc(v_nativeLibDir_4041_);
lean_inc(v_leanLibDir_4040_);
lean_inc(v_buildDir_4039_);
lean_inc(v_srcDir_4038_);
lean_inc(v_moreGlobalServerArgs_4037_);
lean_inc(v_extraDepTargets_4035_);
lean_inc(v_toLeanConfig_4033_);
lean_inc(v_toWorkspaceConfig_4032_);
lean_dec(v_cfg_4031_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4077_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4071_ = lean_box(v_allowImportAll_4064_);
v___x_4072_ = lean_apply_1(v_f_4030_, v___x_4071_);
if (v_isShared_4070_ == 0)
{
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_toWorkspaceConfig_4032_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_toLeanConfig_4033_);
lean_ctor_set(v_reuseFailAlloc_4076_, 2, v_extraDepTargets_4035_);
lean_ctor_set(v_reuseFailAlloc_4076_, 3, v_moreGlobalServerArgs_4037_);
lean_ctor_set(v_reuseFailAlloc_4076_, 4, v_srcDir_4038_);
lean_ctor_set(v_reuseFailAlloc_4076_, 5, v_buildDir_4039_);
lean_ctor_set(v_reuseFailAlloc_4076_, 6, v_leanLibDir_4040_);
lean_ctor_set(v_reuseFailAlloc_4076_, 7, v_nativeLibDir_4041_);
lean_ctor_set(v_reuseFailAlloc_4076_, 8, v_binDir_4042_);
lean_ctor_set(v_reuseFailAlloc_4076_, 9, v_irDir_4043_);
lean_ctor_set(v_reuseFailAlloc_4076_, 10, v_releaseRepo_4044_);
lean_ctor_set(v_reuseFailAlloc_4076_, 11, v_buildArchive_4045_);
lean_ctor_set(v_reuseFailAlloc_4076_, 12, v_downloadCacheService_x3f_4047_);
lean_ctor_set(v_reuseFailAlloc_4076_, 13, v_testDriver_4048_);
lean_ctor_set(v_reuseFailAlloc_4076_, 14, v_testDriverArgs_4049_);
lean_ctor_set(v_reuseFailAlloc_4076_, 15, v_lintDriver_4050_);
lean_ctor_set(v_reuseFailAlloc_4076_, 16, v_lintDriverArgs_4051_);
lean_ctor_set(v_reuseFailAlloc_4076_, 17, v_version_4052_);
lean_ctor_set(v_reuseFailAlloc_4076_, 18, v_versionTags_4053_);
lean_ctor_set(v_reuseFailAlloc_4076_, 19, v_description_4054_);
lean_ctor_set(v_reuseFailAlloc_4076_, 20, v_keywords_4055_);
lean_ctor_set(v_reuseFailAlloc_4076_, 21, v_homepage_4056_);
lean_ctor_set(v_reuseFailAlloc_4076_, 22, v_license_4057_);
lean_ctor_set(v_reuseFailAlloc_4076_, 23, v_licenseFiles_4058_);
lean_ctor_set(v_reuseFailAlloc_4076_, 24, v_readmeFile_4059_);
lean_ctor_set(v_reuseFailAlloc_4076_, 25, v_enableArtifactCache_x3f_4061_);
lean_ctor_set(v_reuseFailAlloc_4076_, 26, v_restoreAllArtifacts_x3f_4062_);
lean_ctor_set(v_reuseFailAlloc_4076_, 27, v_builtinLint_x3f_4065_);
lean_ctor_set(v_reuseFailAlloc_4076_, 28, v_checks_4066_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*29, v_bootstrap_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*29 + 1, v_precompileModules_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4046_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*29 + 3, v_reservoir_4060_);
lean_ctor_set_uint8(v_reuseFailAlloc_4076_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4063_);
v___x_4074_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
uint8_t v___x_4075_; 
v___x_4075_ = lean_unbox(v___x_4072_);
lean_ctor_set_uint8(v___x_4074_, sizeof(void*)*29 + 5, v___x_4075_);
lean_ctor_set_uint8(v___x_4074_, sizeof(void*)*29 + 6, v_fixedToolchain_4067_);
return v___x_4074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg(){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = ((lean_object*)(l_Lake_PackageConfig_allowImportAll___proj___redArg___closed__3));
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___redArg___boxed(lean_object* v___dummy_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
return v_res_4089_;
}
}
static lean_object* _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0(void){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lake_PackageConfig_allowImportAll___proj___redArg();
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj(lean_object* v_p_4091_, lean_object* v_n_4092_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll___proj___boxed(lean_object* v_p_4094_, lean_object* v_n_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lake_PackageConfig_allowImportAll___proj(v_p_4094_, v_n_4095_);
lean_dec(v_n_4095_);
lean_dec(v_p_4094_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg(){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___redArg___boxed(lean_object* v___dummy_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lake_PackageConfig_allowImportAll_instConfigField___redArg();
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField(lean_object* v_p_4101_, lean_object* v_n_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_obj_once(&l_Lake_PackageConfig_allowImportAll___proj___closed__0, &l_Lake_PackageConfig_allowImportAll___proj___closed__0_once, _init_l_Lake_PackageConfig_allowImportAll___proj___closed__0);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_allowImportAll_instConfigField___boxed(lean_object* v_p_4104_, lean_object* v_n_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lake_PackageConfig_allowImportAll_instConfigField(v_p_4104_, v_n_4105_);
lean_dec(v_n_4105_);
lean_dec(v_p_4104_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(lean_object* v_cfg_4107_){
_start:
{
lean_object* v_builtinLint_x3f_4108_; 
v_builtinLint_x3f_4108_ = lean_ctor_get(v_cfg_4107_, 27);
lean_inc(v_builtinLint_x3f_4108_);
return v_builtinLint_x3f_4108_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0___boxed(lean_object* v_cfg_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__0(v_cfg_4109_);
lean_dec_ref(v_cfg_4109_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__1(lean_object* v_val_4111_, lean_object* v_cfg_4112_){
_start:
{
lean_object* v_toWorkspaceConfig_4113_; lean_object* v_toLeanConfig_4114_; uint8_t v_bootstrap_4115_; lean_object* v_extraDepTargets_4116_; uint8_t v_precompileModules_4117_; lean_object* v_moreGlobalServerArgs_4118_; lean_object* v_srcDir_4119_; lean_object* v_buildDir_4120_; lean_object* v_leanLibDir_4121_; lean_object* v_nativeLibDir_4122_; lean_object* v_binDir_4123_; lean_object* v_irDir_4124_; lean_object* v_releaseRepo_4125_; lean_object* v_buildArchive_4126_; uint8_t v_preferReleaseBuild_4127_; lean_object* v_downloadCacheService_x3f_4128_; lean_object* v_testDriver_4129_; lean_object* v_testDriverArgs_4130_; lean_object* v_lintDriver_4131_; lean_object* v_lintDriverArgs_4132_; lean_object* v_version_4133_; lean_object* v_versionTags_4134_; lean_object* v_description_4135_; lean_object* v_keywords_4136_; lean_object* v_homepage_4137_; lean_object* v_license_4138_; lean_object* v_licenseFiles_4139_; lean_object* v_readmeFile_4140_; uint8_t v_reservoir_4141_; lean_object* v_enableArtifactCache_x3f_4142_; lean_object* v_restoreAllArtifacts_x3f_4143_; uint8_t v_libPrefixOnWindows_4144_; uint8_t v_allowImportAll_4145_; lean_object* v_checks_4146_; uint8_t v_fixedToolchain_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
v_toWorkspaceConfig_4113_ = lean_ctor_get(v_cfg_4112_, 0);
v_toLeanConfig_4114_ = lean_ctor_get(v_cfg_4112_, 1);
v_bootstrap_4115_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29);
v_extraDepTargets_4116_ = lean_ctor_get(v_cfg_4112_, 2);
v_precompileModules_4117_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4118_ = lean_ctor_get(v_cfg_4112_, 3);
v_srcDir_4119_ = lean_ctor_get(v_cfg_4112_, 4);
v_buildDir_4120_ = lean_ctor_get(v_cfg_4112_, 5);
v_leanLibDir_4121_ = lean_ctor_get(v_cfg_4112_, 6);
v_nativeLibDir_4122_ = lean_ctor_get(v_cfg_4112_, 7);
v_binDir_4123_ = lean_ctor_get(v_cfg_4112_, 8);
v_irDir_4124_ = lean_ctor_get(v_cfg_4112_, 9);
v_releaseRepo_4125_ = lean_ctor_get(v_cfg_4112_, 10);
v_buildArchive_4126_ = lean_ctor_get(v_cfg_4112_, 11);
v_preferReleaseBuild_4127_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4128_ = lean_ctor_get(v_cfg_4112_, 12);
v_testDriver_4129_ = lean_ctor_get(v_cfg_4112_, 13);
v_testDriverArgs_4130_ = lean_ctor_get(v_cfg_4112_, 14);
v_lintDriver_4131_ = lean_ctor_get(v_cfg_4112_, 15);
v_lintDriverArgs_4132_ = lean_ctor_get(v_cfg_4112_, 16);
v_version_4133_ = lean_ctor_get(v_cfg_4112_, 17);
v_versionTags_4134_ = lean_ctor_get(v_cfg_4112_, 18);
v_description_4135_ = lean_ctor_get(v_cfg_4112_, 19);
v_keywords_4136_ = lean_ctor_get(v_cfg_4112_, 20);
v_homepage_4137_ = lean_ctor_get(v_cfg_4112_, 21);
v_license_4138_ = lean_ctor_get(v_cfg_4112_, 22);
v_licenseFiles_4139_ = lean_ctor_get(v_cfg_4112_, 23);
v_readmeFile_4140_ = lean_ctor_get(v_cfg_4112_, 24);
v_reservoir_4141_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4142_ = lean_ctor_get(v_cfg_4112_, 25);
v_restoreAllArtifacts_x3f_4143_ = lean_ctor_get(v_cfg_4112_, 26);
v_libPrefixOnWindows_4144_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29 + 4);
v_allowImportAll_4145_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29 + 5);
v_checks_4146_ = lean_ctor_get(v_cfg_4112_, 28);
v_fixedToolchain_4147_ = lean_ctor_get_uint8(v_cfg_4112_, sizeof(void*)*29 + 6);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_cfg_4112_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v_cfg_4112_, 27);
lean_dec(v_unused_4155_);
v___x_4149_ = v_cfg_4112_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_checks_4146_);
lean_inc(v_restoreAllArtifacts_x3f_4143_);
lean_inc(v_enableArtifactCache_x3f_4142_);
lean_inc(v_readmeFile_4140_);
lean_inc(v_licenseFiles_4139_);
lean_inc(v_license_4138_);
lean_inc(v_homepage_4137_);
lean_inc(v_keywords_4136_);
lean_inc(v_description_4135_);
lean_inc(v_versionTags_4134_);
lean_inc(v_version_4133_);
lean_inc(v_lintDriverArgs_4132_);
lean_inc(v_lintDriver_4131_);
lean_inc(v_testDriverArgs_4130_);
lean_inc(v_testDriver_4129_);
lean_inc(v_downloadCacheService_x3f_4128_);
lean_inc(v_buildArchive_4126_);
lean_inc(v_releaseRepo_4125_);
lean_inc(v_irDir_4124_);
lean_inc(v_binDir_4123_);
lean_inc(v_nativeLibDir_4122_);
lean_inc(v_leanLibDir_4121_);
lean_inc(v_buildDir_4120_);
lean_inc(v_srcDir_4119_);
lean_inc(v_moreGlobalServerArgs_4118_);
lean_inc(v_extraDepTargets_4116_);
lean_inc(v_toLeanConfig_4114_);
lean_inc(v_toWorkspaceConfig_4113_);
lean_dec(v_cfg_4112_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 27, v_val_4111_);
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_toWorkspaceConfig_4113_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_toLeanConfig_4114_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_extraDepTargets_4116_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v_moreGlobalServerArgs_4118_);
lean_ctor_set(v_reuseFailAlloc_4153_, 4, v_srcDir_4119_);
lean_ctor_set(v_reuseFailAlloc_4153_, 5, v_buildDir_4120_);
lean_ctor_set(v_reuseFailAlloc_4153_, 6, v_leanLibDir_4121_);
lean_ctor_set(v_reuseFailAlloc_4153_, 7, v_nativeLibDir_4122_);
lean_ctor_set(v_reuseFailAlloc_4153_, 8, v_binDir_4123_);
lean_ctor_set(v_reuseFailAlloc_4153_, 9, v_irDir_4124_);
lean_ctor_set(v_reuseFailAlloc_4153_, 10, v_releaseRepo_4125_);
lean_ctor_set(v_reuseFailAlloc_4153_, 11, v_buildArchive_4126_);
lean_ctor_set(v_reuseFailAlloc_4153_, 12, v_downloadCacheService_x3f_4128_);
lean_ctor_set(v_reuseFailAlloc_4153_, 13, v_testDriver_4129_);
lean_ctor_set(v_reuseFailAlloc_4153_, 14, v_testDriverArgs_4130_);
lean_ctor_set(v_reuseFailAlloc_4153_, 15, v_lintDriver_4131_);
lean_ctor_set(v_reuseFailAlloc_4153_, 16, v_lintDriverArgs_4132_);
lean_ctor_set(v_reuseFailAlloc_4153_, 17, v_version_4133_);
lean_ctor_set(v_reuseFailAlloc_4153_, 18, v_versionTags_4134_);
lean_ctor_set(v_reuseFailAlloc_4153_, 19, v_description_4135_);
lean_ctor_set(v_reuseFailAlloc_4153_, 20, v_keywords_4136_);
lean_ctor_set(v_reuseFailAlloc_4153_, 21, v_homepage_4137_);
lean_ctor_set(v_reuseFailAlloc_4153_, 22, v_license_4138_);
lean_ctor_set(v_reuseFailAlloc_4153_, 23, v_licenseFiles_4139_);
lean_ctor_set(v_reuseFailAlloc_4153_, 24, v_readmeFile_4140_);
lean_ctor_set(v_reuseFailAlloc_4153_, 25, v_enableArtifactCache_x3f_4142_);
lean_ctor_set(v_reuseFailAlloc_4153_, 26, v_restoreAllArtifacts_x3f_4143_);
lean_ctor_set(v_reuseFailAlloc_4153_, 27, v_val_4111_);
lean_ctor_set(v_reuseFailAlloc_4153_, 28, v_checks_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29, v_bootstrap_4115_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29 + 1, v_precompileModules_4117_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4127_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29 + 3, v_reservoir_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29 + 5, v_allowImportAll_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*29 + 6, v_fixedToolchain_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___lam__2(lean_object* v_f_4156_, lean_object* v_cfg_4157_){
_start:
{
lean_object* v_toWorkspaceConfig_4158_; lean_object* v_toLeanConfig_4159_; uint8_t v_bootstrap_4160_; lean_object* v_extraDepTargets_4161_; uint8_t v_precompileModules_4162_; lean_object* v_moreGlobalServerArgs_4163_; lean_object* v_srcDir_4164_; lean_object* v_buildDir_4165_; lean_object* v_leanLibDir_4166_; lean_object* v_nativeLibDir_4167_; lean_object* v_binDir_4168_; lean_object* v_irDir_4169_; lean_object* v_releaseRepo_4170_; lean_object* v_buildArchive_4171_; uint8_t v_preferReleaseBuild_4172_; lean_object* v_downloadCacheService_x3f_4173_; lean_object* v_testDriver_4174_; lean_object* v_testDriverArgs_4175_; lean_object* v_lintDriver_4176_; lean_object* v_lintDriverArgs_4177_; lean_object* v_version_4178_; lean_object* v_versionTags_4179_; lean_object* v_description_4180_; lean_object* v_keywords_4181_; lean_object* v_homepage_4182_; lean_object* v_license_4183_; lean_object* v_licenseFiles_4184_; lean_object* v_readmeFile_4185_; uint8_t v_reservoir_4186_; lean_object* v_enableArtifactCache_x3f_4187_; lean_object* v_restoreAllArtifacts_x3f_4188_; uint8_t v_libPrefixOnWindows_4189_; uint8_t v_allowImportAll_4190_; lean_object* v_builtinLint_x3f_4191_; lean_object* v_checks_4192_; uint8_t v_fixedToolchain_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4201_; 
v_toWorkspaceConfig_4158_ = lean_ctor_get(v_cfg_4157_, 0);
v_toLeanConfig_4159_ = lean_ctor_get(v_cfg_4157_, 1);
v_bootstrap_4160_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29);
v_extraDepTargets_4161_ = lean_ctor_get(v_cfg_4157_, 2);
v_precompileModules_4162_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4163_ = lean_ctor_get(v_cfg_4157_, 3);
v_srcDir_4164_ = lean_ctor_get(v_cfg_4157_, 4);
v_buildDir_4165_ = lean_ctor_get(v_cfg_4157_, 5);
v_leanLibDir_4166_ = lean_ctor_get(v_cfg_4157_, 6);
v_nativeLibDir_4167_ = lean_ctor_get(v_cfg_4157_, 7);
v_binDir_4168_ = lean_ctor_get(v_cfg_4157_, 8);
v_irDir_4169_ = lean_ctor_get(v_cfg_4157_, 9);
v_releaseRepo_4170_ = lean_ctor_get(v_cfg_4157_, 10);
v_buildArchive_4171_ = lean_ctor_get(v_cfg_4157_, 11);
v_preferReleaseBuild_4172_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4173_ = lean_ctor_get(v_cfg_4157_, 12);
v_testDriver_4174_ = lean_ctor_get(v_cfg_4157_, 13);
v_testDriverArgs_4175_ = lean_ctor_get(v_cfg_4157_, 14);
v_lintDriver_4176_ = lean_ctor_get(v_cfg_4157_, 15);
v_lintDriverArgs_4177_ = lean_ctor_get(v_cfg_4157_, 16);
v_version_4178_ = lean_ctor_get(v_cfg_4157_, 17);
v_versionTags_4179_ = lean_ctor_get(v_cfg_4157_, 18);
v_description_4180_ = lean_ctor_get(v_cfg_4157_, 19);
v_keywords_4181_ = lean_ctor_get(v_cfg_4157_, 20);
v_homepage_4182_ = lean_ctor_get(v_cfg_4157_, 21);
v_license_4183_ = lean_ctor_get(v_cfg_4157_, 22);
v_licenseFiles_4184_ = lean_ctor_get(v_cfg_4157_, 23);
v_readmeFile_4185_ = lean_ctor_get(v_cfg_4157_, 24);
v_reservoir_4186_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4187_ = lean_ctor_get(v_cfg_4157_, 25);
v_restoreAllArtifacts_x3f_4188_ = lean_ctor_get(v_cfg_4157_, 26);
v_libPrefixOnWindows_4189_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29 + 4);
v_allowImportAll_4190_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4191_ = lean_ctor_get(v_cfg_4157_, 27);
v_checks_4192_ = lean_ctor_get(v_cfg_4157_, 28);
v_fixedToolchain_4193_ = lean_ctor_get_uint8(v_cfg_4157_, sizeof(void*)*29 + 6);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_cfg_4157_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4195_ = v_cfg_4157_;
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_checks_4192_);
lean_inc(v_builtinLint_x3f_4191_);
lean_inc(v_restoreAllArtifacts_x3f_4188_);
lean_inc(v_enableArtifactCache_x3f_4187_);
lean_inc(v_readmeFile_4185_);
lean_inc(v_licenseFiles_4184_);
lean_inc(v_license_4183_);
lean_inc(v_homepage_4182_);
lean_inc(v_keywords_4181_);
lean_inc(v_description_4180_);
lean_inc(v_versionTags_4179_);
lean_inc(v_version_4178_);
lean_inc(v_lintDriverArgs_4177_);
lean_inc(v_lintDriver_4176_);
lean_inc(v_testDriverArgs_4175_);
lean_inc(v_testDriver_4174_);
lean_inc(v_downloadCacheService_x3f_4173_);
lean_inc(v_buildArchive_4171_);
lean_inc(v_releaseRepo_4170_);
lean_inc(v_irDir_4169_);
lean_inc(v_binDir_4168_);
lean_inc(v_nativeLibDir_4167_);
lean_inc(v_leanLibDir_4166_);
lean_inc(v_buildDir_4165_);
lean_inc(v_srcDir_4164_);
lean_inc(v_moreGlobalServerArgs_4163_);
lean_inc(v_extraDepTargets_4161_);
lean_inc(v_toLeanConfig_4159_);
lean_inc(v_toWorkspaceConfig_4158_);
lean_dec(v_cfg_4157_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4197_ = lean_apply_1(v_f_4156_, v_builtinLint_x3f_4191_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 27, v___x_4197_);
v___x_4199_ = v___x_4195_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_toWorkspaceConfig_4158_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_toLeanConfig_4159_);
lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_extraDepTargets_4161_);
lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_moreGlobalServerArgs_4163_);
lean_ctor_set(v_reuseFailAlloc_4200_, 4, v_srcDir_4164_);
lean_ctor_set(v_reuseFailAlloc_4200_, 5, v_buildDir_4165_);
lean_ctor_set(v_reuseFailAlloc_4200_, 6, v_leanLibDir_4166_);
lean_ctor_set(v_reuseFailAlloc_4200_, 7, v_nativeLibDir_4167_);
lean_ctor_set(v_reuseFailAlloc_4200_, 8, v_binDir_4168_);
lean_ctor_set(v_reuseFailAlloc_4200_, 9, v_irDir_4169_);
lean_ctor_set(v_reuseFailAlloc_4200_, 10, v_releaseRepo_4170_);
lean_ctor_set(v_reuseFailAlloc_4200_, 11, v_buildArchive_4171_);
lean_ctor_set(v_reuseFailAlloc_4200_, 12, v_downloadCacheService_x3f_4173_);
lean_ctor_set(v_reuseFailAlloc_4200_, 13, v_testDriver_4174_);
lean_ctor_set(v_reuseFailAlloc_4200_, 14, v_testDriverArgs_4175_);
lean_ctor_set(v_reuseFailAlloc_4200_, 15, v_lintDriver_4176_);
lean_ctor_set(v_reuseFailAlloc_4200_, 16, v_lintDriverArgs_4177_);
lean_ctor_set(v_reuseFailAlloc_4200_, 17, v_version_4178_);
lean_ctor_set(v_reuseFailAlloc_4200_, 18, v_versionTags_4179_);
lean_ctor_set(v_reuseFailAlloc_4200_, 19, v_description_4180_);
lean_ctor_set(v_reuseFailAlloc_4200_, 20, v_keywords_4181_);
lean_ctor_set(v_reuseFailAlloc_4200_, 21, v_homepage_4182_);
lean_ctor_set(v_reuseFailAlloc_4200_, 22, v_license_4183_);
lean_ctor_set(v_reuseFailAlloc_4200_, 23, v_licenseFiles_4184_);
lean_ctor_set(v_reuseFailAlloc_4200_, 24, v_readmeFile_4185_);
lean_ctor_set(v_reuseFailAlloc_4200_, 25, v_enableArtifactCache_x3f_4187_);
lean_ctor_set(v_reuseFailAlloc_4200_, 26, v_restoreAllArtifacts_x3f_4188_);
lean_ctor_set(v_reuseFailAlloc_4200_, 27, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4200_, 28, v_checks_4192_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29, v_bootstrap_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29 + 1, v_precompileModules_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4172_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29 + 3, v_reservoir_4186_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29 + 5, v_allowImportAll_4190_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*29 + 6, v_fixedToolchain_4193_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg(){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = ((lean_object*)(l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___closed__3));
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___redArg___boxed(lean_object* v___dummy_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
return v_res_4213_;
}
}
static lean_object* _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0(void){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lake_PackageConfig_builtinLint_x3f___proj___redArg();
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj(lean_object* v_p_4215_, lean_object* v_n_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f___proj___boxed(lean_object* v_p_4218_, lean_object* v_n_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lake_PackageConfig_builtinLint_x3f___proj(v_p_4218_, v_n_4219_);
lean_dec(v_n_4219_);
lean_dec(v_p_4218_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg(){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___redArg___boxed(lean_object* v___dummy_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lake_PackageConfig_builtinLint_instConfigField___redArg();
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField(lean_object* v_p_4225_, lean_object* v_n_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_instConfigField___boxed(lean_object* v_p_4228_, lean_object* v_n_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lake_PackageConfig_builtinLint_instConfigField(v_p_4228_, v_n_4229_);
lean_dec(v_n_4229_);
lean_dec(v_p_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg(){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg___boxed(lean_object* v___dummy_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField___redArg();
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField(lean_object* v_p_4235_, lean_object* v_n_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_obj_once(&l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0, &l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0_once, _init_l_Lake_PackageConfig_builtinLint_x3f___proj___closed__0);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_builtinLint_x3f_instConfigField___boxed(lean_object* v_p_4238_, lean_object* v_n_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lake_PackageConfig_builtinLint_x3f_instConfigField(v_p_4238_, v_n_4239_);
lean_dec(v_n_4239_);
lean_dec(v_p_4238_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0(lean_object* v_cfg_4241_){
_start:
{
lean_object* v_checks_4242_; 
v_checks_4242_ = lean_ctor_get(v_cfg_4241_, 28);
lean_inc_ref(v_checks_4242_);
return v_checks_4242_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__0___boxed(lean_object* v_cfg_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lake_PackageConfig_checks___proj___redArg___lam__0(v_cfg_4243_);
lean_dec_ref(v_cfg_4243_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__1(lean_object* v_val_4245_, lean_object* v_cfg_4246_){
_start:
{
lean_object* v_toWorkspaceConfig_4247_; lean_object* v_toLeanConfig_4248_; uint8_t v_bootstrap_4249_; lean_object* v_extraDepTargets_4250_; uint8_t v_precompileModules_4251_; lean_object* v_moreGlobalServerArgs_4252_; lean_object* v_srcDir_4253_; lean_object* v_buildDir_4254_; lean_object* v_leanLibDir_4255_; lean_object* v_nativeLibDir_4256_; lean_object* v_binDir_4257_; lean_object* v_irDir_4258_; lean_object* v_releaseRepo_4259_; lean_object* v_buildArchive_4260_; uint8_t v_preferReleaseBuild_4261_; lean_object* v_downloadCacheService_x3f_4262_; lean_object* v_testDriver_4263_; lean_object* v_testDriverArgs_4264_; lean_object* v_lintDriver_4265_; lean_object* v_lintDriverArgs_4266_; lean_object* v_version_4267_; lean_object* v_versionTags_4268_; lean_object* v_description_4269_; lean_object* v_keywords_4270_; lean_object* v_homepage_4271_; lean_object* v_license_4272_; lean_object* v_licenseFiles_4273_; lean_object* v_readmeFile_4274_; uint8_t v_reservoir_4275_; lean_object* v_enableArtifactCache_x3f_4276_; lean_object* v_restoreAllArtifacts_x3f_4277_; uint8_t v_libPrefixOnWindows_4278_; uint8_t v_allowImportAll_4279_; lean_object* v_builtinLint_x3f_4280_; uint8_t v_fixedToolchain_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
v_toWorkspaceConfig_4247_ = lean_ctor_get(v_cfg_4246_, 0);
v_toLeanConfig_4248_ = lean_ctor_get(v_cfg_4246_, 1);
v_bootstrap_4249_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29);
v_extraDepTargets_4250_ = lean_ctor_get(v_cfg_4246_, 2);
v_precompileModules_4251_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4252_ = lean_ctor_get(v_cfg_4246_, 3);
v_srcDir_4253_ = lean_ctor_get(v_cfg_4246_, 4);
v_buildDir_4254_ = lean_ctor_get(v_cfg_4246_, 5);
v_leanLibDir_4255_ = lean_ctor_get(v_cfg_4246_, 6);
v_nativeLibDir_4256_ = lean_ctor_get(v_cfg_4246_, 7);
v_binDir_4257_ = lean_ctor_get(v_cfg_4246_, 8);
v_irDir_4258_ = lean_ctor_get(v_cfg_4246_, 9);
v_releaseRepo_4259_ = lean_ctor_get(v_cfg_4246_, 10);
v_buildArchive_4260_ = lean_ctor_get(v_cfg_4246_, 11);
v_preferReleaseBuild_4261_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4262_ = lean_ctor_get(v_cfg_4246_, 12);
v_testDriver_4263_ = lean_ctor_get(v_cfg_4246_, 13);
v_testDriverArgs_4264_ = lean_ctor_get(v_cfg_4246_, 14);
v_lintDriver_4265_ = lean_ctor_get(v_cfg_4246_, 15);
v_lintDriverArgs_4266_ = lean_ctor_get(v_cfg_4246_, 16);
v_version_4267_ = lean_ctor_get(v_cfg_4246_, 17);
v_versionTags_4268_ = lean_ctor_get(v_cfg_4246_, 18);
v_description_4269_ = lean_ctor_get(v_cfg_4246_, 19);
v_keywords_4270_ = lean_ctor_get(v_cfg_4246_, 20);
v_homepage_4271_ = lean_ctor_get(v_cfg_4246_, 21);
v_license_4272_ = lean_ctor_get(v_cfg_4246_, 22);
v_licenseFiles_4273_ = lean_ctor_get(v_cfg_4246_, 23);
v_readmeFile_4274_ = lean_ctor_get(v_cfg_4246_, 24);
v_reservoir_4275_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4276_ = lean_ctor_get(v_cfg_4246_, 25);
v_restoreAllArtifacts_x3f_4277_ = lean_ctor_get(v_cfg_4246_, 26);
v_libPrefixOnWindows_4278_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29 + 4);
v_allowImportAll_4279_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4280_ = lean_ctor_get(v_cfg_4246_, 27);
v_fixedToolchain_4281_ = lean_ctor_get_uint8(v_cfg_4246_, sizeof(void*)*29 + 6);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_cfg_4246_);
if (v_isSharedCheck_4288_ == 0)
{
lean_object* v_unused_4289_; 
v_unused_4289_ = lean_ctor_get(v_cfg_4246_, 28);
lean_dec(v_unused_4289_);
v___x_4283_ = v_cfg_4246_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_builtinLint_x3f_4280_);
lean_inc(v_restoreAllArtifacts_x3f_4277_);
lean_inc(v_enableArtifactCache_x3f_4276_);
lean_inc(v_readmeFile_4274_);
lean_inc(v_licenseFiles_4273_);
lean_inc(v_license_4272_);
lean_inc(v_homepage_4271_);
lean_inc(v_keywords_4270_);
lean_inc(v_description_4269_);
lean_inc(v_versionTags_4268_);
lean_inc(v_version_4267_);
lean_inc(v_lintDriverArgs_4266_);
lean_inc(v_lintDriver_4265_);
lean_inc(v_testDriverArgs_4264_);
lean_inc(v_testDriver_4263_);
lean_inc(v_downloadCacheService_x3f_4262_);
lean_inc(v_buildArchive_4260_);
lean_inc(v_releaseRepo_4259_);
lean_inc(v_irDir_4258_);
lean_inc(v_binDir_4257_);
lean_inc(v_nativeLibDir_4256_);
lean_inc(v_leanLibDir_4255_);
lean_inc(v_buildDir_4254_);
lean_inc(v_srcDir_4253_);
lean_inc(v_moreGlobalServerArgs_4252_);
lean_inc(v_extraDepTargets_4250_);
lean_inc(v_toLeanConfig_4248_);
lean_inc(v_toWorkspaceConfig_4247_);
lean_dec(v_cfg_4246_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 28, v_val_4245_);
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_toWorkspaceConfig_4247_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_toLeanConfig_4248_);
lean_ctor_set(v_reuseFailAlloc_4287_, 2, v_extraDepTargets_4250_);
lean_ctor_set(v_reuseFailAlloc_4287_, 3, v_moreGlobalServerArgs_4252_);
lean_ctor_set(v_reuseFailAlloc_4287_, 4, v_srcDir_4253_);
lean_ctor_set(v_reuseFailAlloc_4287_, 5, v_buildDir_4254_);
lean_ctor_set(v_reuseFailAlloc_4287_, 6, v_leanLibDir_4255_);
lean_ctor_set(v_reuseFailAlloc_4287_, 7, v_nativeLibDir_4256_);
lean_ctor_set(v_reuseFailAlloc_4287_, 8, v_binDir_4257_);
lean_ctor_set(v_reuseFailAlloc_4287_, 9, v_irDir_4258_);
lean_ctor_set(v_reuseFailAlloc_4287_, 10, v_releaseRepo_4259_);
lean_ctor_set(v_reuseFailAlloc_4287_, 11, v_buildArchive_4260_);
lean_ctor_set(v_reuseFailAlloc_4287_, 12, v_downloadCacheService_x3f_4262_);
lean_ctor_set(v_reuseFailAlloc_4287_, 13, v_testDriver_4263_);
lean_ctor_set(v_reuseFailAlloc_4287_, 14, v_testDriverArgs_4264_);
lean_ctor_set(v_reuseFailAlloc_4287_, 15, v_lintDriver_4265_);
lean_ctor_set(v_reuseFailAlloc_4287_, 16, v_lintDriverArgs_4266_);
lean_ctor_set(v_reuseFailAlloc_4287_, 17, v_version_4267_);
lean_ctor_set(v_reuseFailAlloc_4287_, 18, v_versionTags_4268_);
lean_ctor_set(v_reuseFailAlloc_4287_, 19, v_description_4269_);
lean_ctor_set(v_reuseFailAlloc_4287_, 20, v_keywords_4270_);
lean_ctor_set(v_reuseFailAlloc_4287_, 21, v_homepage_4271_);
lean_ctor_set(v_reuseFailAlloc_4287_, 22, v_license_4272_);
lean_ctor_set(v_reuseFailAlloc_4287_, 23, v_licenseFiles_4273_);
lean_ctor_set(v_reuseFailAlloc_4287_, 24, v_readmeFile_4274_);
lean_ctor_set(v_reuseFailAlloc_4287_, 25, v_enableArtifactCache_x3f_4276_);
lean_ctor_set(v_reuseFailAlloc_4287_, 26, v_restoreAllArtifacts_x3f_4277_);
lean_ctor_set(v_reuseFailAlloc_4287_, 27, v_builtinLint_x3f_4280_);
lean_ctor_set(v_reuseFailAlloc_4287_, 28, v_val_4245_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29, v_bootstrap_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29 + 1, v_precompileModules_4251_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4261_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29 + 3, v_reservoir_4275_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4278_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29 + 5, v_allowImportAll_4279_);
lean_ctor_set_uint8(v_reuseFailAlloc_4287_, sizeof(void*)*29 + 6, v_fixedToolchain_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___lam__2(lean_object* v_f_4290_, lean_object* v_cfg_4291_){
_start:
{
lean_object* v_toWorkspaceConfig_4292_; lean_object* v_toLeanConfig_4293_; uint8_t v_bootstrap_4294_; lean_object* v_extraDepTargets_4295_; uint8_t v_precompileModules_4296_; lean_object* v_moreGlobalServerArgs_4297_; lean_object* v_srcDir_4298_; lean_object* v_buildDir_4299_; lean_object* v_leanLibDir_4300_; lean_object* v_nativeLibDir_4301_; lean_object* v_binDir_4302_; lean_object* v_irDir_4303_; lean_object* v_releaseRepo_4304_; lean_object* v_buildArchive_4305_; uint8_t v_preferReleaseBuild_4306_; lean_object* v_downloadCacheService_x3f_4307_; lean_object* v_testDriver_4308_; lean_object* v_testDriverArgs_4309_; lean_object* v_lintDriver_4310_; lean_object* v_lintDriverArgs_4311_; lean_object* v_version_4312_; lean_object* v_versionTags_4313_; lean_object* v_description_4314_; lean_object* v_keywords_4315_; lean_object* v_homepage_4316_; lean_object* v_license_4317_; lean_object* v_licenseFiles_4318_; lean_object* v_readmeFile_4319_; uint8_t v_reservoir_4320_; lean_object* v_enableArtifactCache_x3f_4321_; lean_object* v_restoreAllArtifacts_x3f_4322_; uint8_t v_libPrefixOnWindows_4323_; uint8_t v_allowImportAll_4324_; lean_object* v_builtinLint_x3f_4325_; lean_object* v_checks_4326_; uint8_t v_fixedToolchain_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4335_; 
v_toWorkspaceConfig_4292_ = lean_ctor_get(v_cfg_4291_, 0);
v_toLeanConfig_4293_ = lean_ctor_get(v_cfg_4291_, 1);
v_bootstrap_4294_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29);
v_extraDepTargets_4295_ = lean_ctor_get(v_cfg_4291_, 2);
v_precompileModules_4296_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4297_ = lean_ctor_get(v_cfg_4291_, 3);
v_srcDir_4298_ = lean_ctor_get(v_cfg_4291_, 4);
v_buildDir_4299_ = lean_ctor_get(v_cfg_4291_, 5);
v_leanLibDir_4300_ = lean_ctor_get(v_cfg_4291_, 6);
v_nativeLibDir_4301_ = lean_ctor_get(v_cfg_4291_, 7);
v_binDir_4302_ = lean_ctor_get(v_cfg_4291_, 8);
v_irDir_4303_ = lean_ctor_get(v_cfg_4291_, 9);
v_releaseRepo_4304_ = lean_ctor_get(v_cfg_4291_, 10);
v_buildArchive_4305_ = lean_ctor_get(v_cfg_4291_, 11);
v_preferReleaseBuild_4306_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4307_ = lean_ctor_get(v_cfg_4291_, 12);
v_testDriver_4308_ = lean_ctor_get(v_cfg_4291_, 13);
v_testDriverArgs_4309_ = lean_ctor_get(v_cfg_4291_, 14);
v_lintDriver_4310_ = lean_ctor_get(v_cfg_4291_, 15);
v_lintDriverArgs_4311_ = lean_ctor_get(v_cfg_4291_, 16);
v_version_4312_ = lean_ctor_get(v_cfg_4291_, 17);
v_versionTags_4313_ = lean_ctor_get(v_cfg_4291_, 18);
v_description_4314_ = lean_ctor_get(v_cfg_4291_, 19);
v_keywords_4315_ = lean_ctor_get(v_cfg_4291_, 20);
v_homepage_4316_ = lean_ctor_get(v_cfg_4291_, 21);
v_license_4317_ = lean_ctor_get(v_cfg_4291_, 22);
v_licenseFiles_4318_ = lean_ctor_get(v_cfg_4291_, 23);
v_readmeFile_4319_ = lean_ctor_get(v_cfg_4291_, 24);
v_reservoir_4320_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4321_ = lean_ctor_get(v_cfg_4291_, 25);
v_restoreAllArtifacts_x3f_4322_ = lean_ctor_get(v_cfg_4291_, 26);
v_libPrefixOnWindows_4323_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29 + 4);
v_allowImportAll_4324_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4325_ = lean_ctor_get(v_cfg_4291_, 27);
v_checks_4326_ = lean_ctor_get(v_cfg_4291_, 28);
v_fixedToolchain_4327_ = lean_ctor_get_uint8(v_cfg_4291_, sizeof(void*)*29 + 6);
v_isSharedCheck_4335_ = !lean_is_exclusive(v_cfg_4291_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4329_ = v_cfg_4291_;
v_isShared_4330_ = v_isSharedCheck_4335_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_checks_4326_);
lean_inc(v_builtinLint_x3f_4325_);
lean_inc(v_restoreAllArtifacts_x3f_4322_);
lean_inc(v_enableArtifactCache_x3f_4321_);
lean_inc(v_readmeFile_4319_);
lean_inc(v_licenseFiles_4318_);
lean_inc(v_license_4317_);
lean_inc(v_homepage_4316_);
lean_inc(v_keywords_4315_);
lean_inc(v_description_4314_);
lean_inc(v_versionTags_4313_);
lean_inc(v_version_4312_);
lean_inc(v_lintDriverArgs_4311_);
lean_inc(v_lintDriver_4310_);
lean_inc(v_testDriverArgs_4309_);
lean_inc(v_testDriver_4308_);
lean_inc(v_downloadCacheService_x3f_4307_);
lean_inc(v_buildArchive_4305_);
lean_inc(v_releaseRepo_4304_);
lean_inc(v_irDir_4303_);
lean_inc(v_binDir_4302_);
lean_inc(v_nativeLibDir_4301_);
lean_inc(v_leanLibDir_4300_);
lean_inc(v_buildDir_4299_);
lean_inc(v_srcDir_4298_);
lean_inc(v_moreGlobalServerArgs_4297_);
lean_inc(v_extraDepTargets_4295_);
lean_inc(v_toLeanConfig_4293_);
lean_inc(v_toWorkspaceConfig_4292_);
lean_dec(v_cfg_4291_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4335_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4331_ = lean_apply_1(v_f_4290_, v_checks_4326_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 28, v___x_4331_);
v___x_4333_ = v___x_4329_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_toWorkspaceConfig_4292_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_toLeanConfig_4293_);
lean_ctor_set(v_reuseFailAlloc_4334_, 2, v_extraDepTargets_4295_);
lean_ctor_set(v_reuseFailAlloc_4334_, 3, v_moreGlobalServerArgs_4297_);
lean_ctor_set(v_reuseFailAlloc_4334_, 4, v_srcDir_4298_);
lean_ctor_set(v_reuseFailAlloc_4334_, 5, v_buildDir_4299_);
lean_ctor_set(v_reuseFailAlloc_4334_, 6, v_leanLibDir_4300_);
lean_ctor_set(v_reuseFailAlloc_4334_, 7, v_nativeLibDir_4301_);
lean_ctor_set(v_reuseFailAlloc_4334_, 8, v_binDir_4302_);
lean_ctor_set(v_reuseFailAlloc_4334_, 9, v_irDir_4303_);
lean_ctor_set(v_reuseFailAlloc_4334_, 10, v_releaseRepo_4304_);
lean_ctor_set(v_reuseFailAlloc_4334_, 11, v_buildArchive_4305_);
lean_ctor_set(v_reuseFailAlloc_4334_, 12, v_downloadCacheService_x3f_4307_);
lean_ctor_set(v_reuseFailAlloc_4334_, 13, v_testDriver_4308_);
lean_ctor_set(v_reuseFailAlloc_4334_, 14, v_testDriverArgs_4309_);
lean_ctor_set(v_reuseFailAlloc_4334_, 15, v_lintDriver_4310_);
lean_ctor_set(v_reuseFailAlloc_4334_, 16, v_lintDriverArgs_4311_);
lean_ctor_set(v_reuseFailAlloc_4334_, 17, v_version_4312_);
lean_ctor_set(v_reuseFailAlloc_4334_, 18, v_versionTags_4313_);
lean_ctor_set(v_reuseFailAlloc_4334_, 19, v_description_4314_);
lean_ctor_set(v_reuseFailAlloc_4334_, 20, v_keywords_4315_);
lean_ctor_set(v_reuseFailAlloc_4334_, 21, v_homepage_4316_);
lean_ctor_set(v_reuseFailAlloc_4334_, 22, v_license_4317_);
lean_ctor_set(v_reuseFailAlloc_4334_, 23, v_licenseFiles_4318_);
lean_ctor_set(v_reuseFailAlloc_4334_, 24, v_readmeFile_4319_);
lean_ctor_set(v_reuseFailAlloc_4334_, 25, v_enableArtifactCache_x3f_4321_);
lean_ctor_set(v_reuseFailAlloc_4334_, 26, v_restoreAllArtifacts_x3f_4322_);
lean_ctor_set(v_reuseFailAlloc_4334_, 27, v_builtinLint_x3f_4325_);
lean_ctor_set(v_reuseFailAlloc_4334_, 28, v___x_4331_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29, v_bootstrap_4294_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29 + 1, v_precompileModules_4296_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4306_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29 + 3, v_reservoir_4320_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4323_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29 + 5, v_allowImportAll_4324_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*29 + 6, v_fixedToolchain_4327_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg(){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = ((lean_object*)(l_Lake_PackageConfig_checks___proj___redArg___closed__3));
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___redArg___boxed(lean_object* v___dummy_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lake_PackageConfig_checks___proj___redArg();
return v_res_4347_;
}
}
static lean_object* _init_l_Lake_PackageConfig_checks___proj___closed__0(void){
_start:
{
lean_object* v___x_4348_; 
v___x_4348_ = l_Lake_PackageConfig_checks___proj___redArg();
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj(lean_object* v_p_4349_, lean_object* v_n_4350_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks___proj___boxed(lean_object* v_p_4352_, lean_object* v_n_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lake_PackageConfig_checks___proj(v_p_4352_, v_n_4353_);
lean_dec(v_n_4353_);
lean_dec(v_p_4352_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg(){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___redArg___boxed(lean_object* v___dummy_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lake_PackageConfig_checks_instConfigField___redArg();
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField(lean_object* v_p_4359_, lean_object* v_n_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = lean_obj_once(&l_Lake_PackageConfig_checks___proj___closed__0, &l_Lake_PackageConfig_checks___proj___closed__0_once, _init_l_Lake_PackageConfig_checks___proj___closed__0);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_checks_instConfigField___boxed(lean_object* v_p_4362_, lean_object* v_n_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lake_PackageConfig_checks_instConfigField(v_p_4362_, v_n_4363_);
lean_dec(v_n_4363_);
lean_dec(v_p_4362_);
return v_res_4364_;
}
}
LEAN_EXPORT uint8_t l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(lean_object* v_cfg_4365_){
_start:
{
uint8_t v_fixedToolchain_4366_; 
v_fixedToolchain_4366_ = lean_ctor_get_uint8(v_cfg_4365_, sizeof(void*)*29 + 6);
return v_fixedToolchain_4366_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0___boxed(lean_object* v_cfg_4367_){
_start:
{
uint8_t v_res_4368_; lean_object* v_r_4369_; 
v_res_4368_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__0(v_cfg_4367_);
lean_dec_ref(v_cfg_4367_);
v_r_4369_ = lean_box(v_res_4368_);
return v_r_4369_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(uint8_t v_val_4370_, lean_object* v_cfg_4371_){
_start:
{
lean_object* v_toWorkspaceConfig_4372_; lean_object* v_toLeanConfig_4373_; uint8_t v_bootstrap_4374_; lean_object* v_extraDepTargets_4375_; uint8_t v_precompileModules_4376_; lean_object* v_moreGlobalServerArgs_4377_; lean_object* v_srcDir_4378_; lean_object* v_buildDir_4379_; lean_object* v_leanLibDir_4380_; lean_object* v_nativeLibDir_4381_; lean_object* v_binDir_4382_; lean_object* v_irDir_4383_; lean_object* v_releaseRepo_4384_; lean_object* v_buildArchive_4385_; uint8_t v_preferReleaseBuild_4386_; lean_object* v_downloadCacheService_x3f_4387_; lean_object* v_testDriver_4388_; lean_object* v_testDriverArgs_4389_; lean_object* v_lintDriver_4390_; lean_object* v_lintDriverArgs_4391_; lean_object* v_version_4392_; lean_object* v_versionTags_4393_; lean_object* v_description_4394_; lean_object* v_keywords_4395_; lean_object* v_homepage_4396_; lean_object* v_license_4397_; lean_object* v_licenseFiles_4398_; lean_object* v_readmeFile_4399_; uint8_t v_reservoir_4400_; lean_object* v_enableArtifactCache_x3f_4401_; lean_object* v_restoreAllArtifacts_x3f_4402_; uint8_t v_libPrefixOnWindows_4403_; uint8_t v_allowImportAll_4404_; lean_object* v_builtinLint_x3f_4405_; lean_object* v_checks_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_toWorkspaceConfig_4372_ = lean_ctor_get(v_cfg_4371_, 0);
v_toLeanConfig_4373_ = lean_ctor_get(v_cfg_4371_, 1);
v_bootstrap_4374_ = lean_ctor_get_uint8(v_cfg_4371_, sizeof(void*)*29);
v_extraDepTargets_4375_ = lean_ctor_get(v_cfg_4371_, 2);
v_precompileModules_4376_ = lean_ctor_get_uint8(v_cfg_4371_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4377_ = lean_ctor_get(v_cfg_4371_, 3);
v_srcDir_4378_ = lean_ctor_get(v_cfg_4371_, 4);
v_buildDir_4379_ = lean_ctor_get(v_cfg_4371_, 5);
v_leanLibDir_4380_ = lean_ctor_get(v_cfg_4371_, 6);
v_nativeLibDir_4381_ = lean_ctor_get(v_cfg_4371_, 7);
v_binDir_4382_ = lean_ctor_get(v_cfg_4371_, 8);
v_irDir_4383_ = lean_ctor_get(v_cfg_4371_, 9);
v_releaseRepo_4384_ = lean_ctor_get(v_cfg_4371_, 10);
v_buildArchive_4385_ = lean_ctor_get(v_cfg_4371_, 11);
v_preferReleaseBuild_4386_ = lean_ctor_get_uint8(v_cfg_4371_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4387_ = lean_ctor_get(v_cfg_4371_, 12);
v_testDriver_4388_ = lean_ctor_get(v_cfg_4371_, 13);
v_testDriverArgs_4389_ = lean_ctor_get(v_cfg_4371_, 14);
v_lintDriver_4390_ = lean_ctor_get(v_cfg_4371_, 15);
v_lintDriverArgs_4391_ = lean_ctor_get(v_cfg_4371_, 16);
v_version_4392_ = lean_ctor_get(v_cfg_4371_, 17);
v_versionTags_4393_ = lean_ctor_get(v_cfg_4371_, 18);
v_description_4394_ = lean_ctor_get(v_cfg_4371_, 19);
v_keywords_4395_ = lean_ctor_get(v_cfg_4371_, 20);
v_homepage_4396_ = lean_ctor_get(v_cfg_4371_, 21);
v_license_4397_ = lean_ctor_get(v_cfg_4371_, 22);
v_licenseFiles_4398_ = lean_ctor_get(v_cfg_4371_, 23);
v_readmeFile_4399_ = lean_ctor_get(v_cfg_4371_, 24);
v_reservoir_4400_ = lean_ctor_get_uint8(v_cfg_4371_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4401_ = lean_ctor_get(v_cfg_4371_, 25);
v_restoreAllArtifacts_x3f_4402_ = lean_ctor_get(v_cfg_4371_, 26);
v_libPrefixOnWindows_4403_ = lean_ctor_get_uint8(v_cfg_4371_, sizeof(void*)*29 + 4);
v_allowImportAll_4404_ = lean_ctor_get_uint8(v_cfg_4371_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4405_ = lean_ctor_get(v_cfg_4371_, 27);
v_checks_4406_ = lean_ctor_get(v_cfg_4371_, 28);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_cfg_4371_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v_cfg_4371_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_checks_4406_);
lean_inc(v_builtinLint_x3f_4405_);
lean_inc(v_restoreAllArtifacts_x3f_4402_);
lean_inc(v_enableArtifactCache_x3f_4401_);
lean_inc(v_readmeFile_4399_);
lean_inc(v_licenseFiles_4398_);
lean_inc(v_license_4397_);
lean_inc(v_homepage_4396_);
lean_inc(v_keywords_4395_);
lean_inc(v_description_4394_);
lean_inc(v_versionTags_4393_);
lean_inc(v_version_4392_);
lean_inc(v_lintDriverArgs_4391_);
lean_inc(v_lintDriver_4390_);
lean_inc(v_testDriverArgs_4389_);
lean_inc(v_testDriver_4388_);
lean_inc(v_downloadCacheService_x3f_4387_);
lean_inc(v_buildArchive_4385_);
lean_inc(v_releaseRepo_4384_);
lean_inc(v_irDir_4383_);
lean_inc(v_binDir_4382_);
lean_inc(v_nativeLibDir_4381_);
lean_inc(v_leanLibDir_4380_);
lean_inc(v_buildDir_4379_);
lean_inc(v_srcDir_4378_);
lean_inc(v_moreGlobalServerArgs_4377_);
lean_inc(v_extraDepTargets_4375_);
lean_inc(v_toLeanConfig_4373_);
lean_inc(v_toWorkspaceConfig_4372_);
lean_dec(v_cfg_4371_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_toWorkspaceConfig_4372_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_toLeanConfig_4373_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_extraDepTargets_4375_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_moreGlobalServerArgs_4377_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_srcDir_4378_);
lean_ctor_set(v_reuseFailAlloc_4412_, 5, v_buildDir_4379_);
lean_ctor_set(v_reuseFailAlloc_4412_, 6, v_leanLibDir_4380_);
lean_ctor_set(v_reuseFailAlloc_4412_, 7, v_nativeLibDir_4381_);
lean_ctor_set(v_reuseFailAlloc_4412_, 8, v_binDir_4382_);
lean_ctor_set(v_reuseFailAlloc_4412_, 9, v_irDir_4383_);
lean_ctor_set(v_reuseFailAlloc_4412_, 10, v_releaseRepo_4384_);
lean_ctor_set(v_reuseFailAlloc_4412_, 11, v_buildArchive_4385_);
lean_ctor_set(v_reuseFailAlloc_4412_, 12, v_downloadCacheService_x3f_4387_);
lean_ctor_set(v_reuseFailAlloc_4412_, 13, v_testDriver_4388_);
lean_ctor_set(v_reuseFailAlloc_4412_, 14, v_testDriverArgs_4389_);
lean_ctor_set(v_reuseFailAlloc_4412_, 15, v_lintDriver_4390_);
lean_ctor_set(v_reuseFailAlloc_4412_, 16, v_lintDriverArgs_4391_);
lean_ctor_set(v_reuseFailAlloc_4412_, 17, v_version_4392_);
lean_ctor_set(v_reuseFailAlloc_4412_, 18, v_versionTags_4393_);
lean_ctor_set(v_reuseFailAlloc_4412_, 19, v_description_4394_);
lean_ctor_set(v_reuseFailAlloc_4412_, 20, v_keywords_4395_);
lean_ctor_set(v_reuseFailAlloc_4412_, 21, v_homepage_4396_);
lean_ctor_set(v_reuseFailAlloc_4412_, 22, v_license_4397_);
lean_ctor_set(v_reuseFailAlloc_4412_, 23, v_licenseFiles_4398_);
lean_ctor_set(v_reuseFailAlloc_4412_, 24, v_readmeFile_4399_);
lean_ctor_set(v_reuseFailAlloc_4412_, 25, v_enableArtifactCache_x3f_4401_);
lean_ctor_set(v_reuseFailAlloc_4412_, 26, v_restoreAllArtifacts_x3f_4402_);
lean_ctor_set(v_reuseFailAlloc_4412_, 27, v_builtinLint_x3f_4405_);
lean_ctor_set(v_reuseFailAlloc_4412_, 28, v_checks_4406_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*29, v_bootstrap_4374_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*29 + 1, v_precompileModules_4376_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4386_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*29 + 3, v_reservoir_4400_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4403_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*29 + 5, v_allowImportAll_4404_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_ctor_set_uint8(v___x_4411_, sizeof(void*)*29 + 6, v_val_4370_);
return v___x_4411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1___boxed(lean_object* v_val_4414_, lean_object* v_cfg_4415_){
_start:
{
uint8_t v_val_144__boxed_4416_; lean_object* v_res_4417_; 
v_val_144__boxed_4416_ = lean_unbox(v_val_4414_);
v_res_4417_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__1(v_val_144__boxed_4416_, v_cfg_4415_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___lam__2(lean_object* v_f_4418_, lean_object* v_cfg_4419_){
_start:
{
lean_object* v_toWorkspaceConfig_4420_; lean_object* v_toLeanConfig_4421_; uint8_t v_bootstrap_4422_; lean_object* v_extraDepTargets_4423_; uint8_t v_precompileModules_4424_; lean_object* v_moreGlobalServerArgs_4425_; lean_object* v_srcDir_4426_; lean_object* v_buildDir_4427_; lean_object* v_leanLibDir_4428_; lean_object* v_nativeLibDir_4429_; lean_object* v_binDir_4430_; lean_object* v_irDir_4431_; lean_object* v_releaseRepo_4432_; lean_object* v_buildArchive_4433_; uint8_t v_preferReleaseBuild_4434_; lean_object* v_downloadCacheService_x3f_4435_; lean_object* v_testDriver_4436_; lean_object* v_testDriverArgs_4437_; lean_object* v_lintDriver_4438_; lean_object* v_lintDriverArgs_4439_; lean_object* v_version_4440_; lean_object* v_versionTags_4441_; lean_object* v_description_4442_; lean_object* v_keywords_4443_; lean_object* v_homepage_4444_; lean_object* v_license_4445_; lean_object* v_licenseFiles_4446_; lean_object* v_readmeFile_4447_; uint8_t v_reservoir_4448_; lean_object* v_enableArtifactCache_x3f_4449_; lean_object* v_restoreAllArtifacts_x3f_4450_; uint8_t v_libPrefixOnWindows_4451_; uint8_t v_allowImportAll_4452_; lean_object* v_builtinLint_x3f_4453_; lean_object* v_checks_4454_; uint8_t v_fixedToolchain_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4465_; 
v_toWorkspaceConfig_4420_ = lean_ctor_get(v_cfg_4419_, 0);
v_toLeanConfig_4421_ = lean_ctor_get(v_cfg_4419_, 1);
v_bootstrap_4422_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29);
v_extraDepTargets_4423_ = lean_ctor_get(v_cfg_4419_, 2);
v_precompileModules_4424_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4425_ = lean_ctor_get(v_cfg_4419_, 3);
v_srcDir_4426_ = lean_ctor_get(v_cfg_4419_, 4);
v_buildDir_4427_ = lean_ctor_get(v_cfg_4419_, 5);
v_leanLibDir_4428_ = lean_ctor_get(v_cfg_4419_, 6);
v_nativeLibDir_4429_ = lean_ctor_get(v_cfg_4419_, 7);
v_binDir_4430_ = lean_ctor_get(v_cfg_4419_, 8);
v_irDir_4431_ = lean_ctor_get(v_cfg_4419_, 9);
v_releaseRepo_4432_ = lean_ctor_get(v_cfg_4419_, 10);
v_buildArchive_4433_ = lean_ctor_get(v_cfg_4419_, 11);
v_preferReleaseBuild_4434_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4435_ = lean_ctor_get(v_cfg_4419_, 12);
v_testDriver_4436_ = lean_ctor_get(v_cfg_4419_, 13);
v_testDriverArgs_4437_ = lean_ctor_get(v_cfg_4419_, 14);
v_lintDriver_4438_ = lean_ctor_get(v_cfg_4419_, 15);
v_lintDriverArgs_4439_ = lean_ctor_get(v_cfg_4419_, 16);
v_version_4440_ = lean_ctor_get(v_cfg_4419_, 17);
v_versionTags_4441_ = lean_ctor_get(v_cfg_4419_, 18);
v_description_4442_ = lean_ctor_get(v_cfg_4419_, 19);
v_keywords_4443_ = lean_ctor_get(v_cfg_4419_, 20);
v_homepage_4444_ = lean_ctor_get(v_cfg_4419_, 21);
v_license_4445_ = lean_ctor_get(v_cfg_4419_, 22);
v_licenseFiles_4446_ = lean_ctor_get(v_cfg_4419_, 23);
v_readmeFile_4447_ = lean_ctor_get(v_cfg_4419_, 24);
v_reservoir_4448_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4449_ = lean_ctor_get(v_cfg_4419_, 25);
v_restoreAllArtifacts_x3f_4450_ = lean_ctor_get(v_cfg_4419_, 26);
v_libPrefixOnWindows_4451_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29 + 4);
v_allowImportAll_4452_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4453_ = lean_ctor_get(v_cfg_4419_, 27);
v_checks_4454_ = lean_ctor_get(v_cfg_4419_, 28);
v_fixedToolchain_4455_ = lean_ctor_get_uint8(v_cfg_4419_, sizeof(void*)*29 + 6);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_cfg_4419_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4457_ = v_cfg_4419_;
v_isShared_4458_ = v_isSharedCheck_4465_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_checks_4454_);
lean_inc(v_builtinLint_x3f_4453_);
lean_inc(v_restoreAllArtifacts_x3f_4450_);
lean_inc(v_enableArtifactCache_x3f_4449_);
lean_inc(v_readmeFile_4447_);
lean_inc(v_licenseFiles_4446_);
lean_inc(v_license_4445_);
lean_inc(v_homepage_4444_);
lean_inc(v_keywords_4443_);
lean_inc(v_description_4442_);
lean_inc(v_versionTags_4441_);
lean_inc(v_version_4440_);
lean_inc(v_lintDriverArgs_4439_);
lean_inc(v_lintDriver_4438_);
lean_inc(v_testDriverArgs_4437_);
lean_inc(v_testDriver_4436_);
lean_inc(v_downloadCacheService_x3f_4435_);
lean_inc(v_buildArchive_4433_);
lean_inc(v_releaseRepo_4432_);
lean_inc(v_irDir_4431_);
lean_inc(v_binDir_4430_);
lean_inc(v_nativeLibDir_4429_);
lean_inc(v_leanLibDir_4428_);
lean_inc(v_buildDir_4427_);
lean_inc(v_srcDir_4426_);
lean_inc(v_moreGlobalServerArgs_4425_);
lean_inc(v_extraDepTargets_4423_);
lean_inc(v_toLeanConfig_4421_);
lean_inc(v_toWorkspaceConfig_4420_);
lean_dec(v_cfg_4419_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4465_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4459_ = lean_box(v_fixedToolchain_4455_);
v___x_4460_ = lean_apply_1(v_f_4418_, v___x_4459_);
if (v_isShared_4458_ == 0)
{
v___x_4462_ = v___x_4457_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_toWorkspaceConfig_4420_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_toLeanConfig_4421_);
lean_ctor_set(v_reuseFailAlloc_4464_, 2, v_extraDepTargets_4423_);
lean_ctor_set(v_reuseFailAlloc_4464_, 3, v_moreGlobalServerArgs_4425_);
lean_ctor_set(v_reuseFailAlloc_4464_, 4, v_srcDir_4426_);
lean_ctor_set(v_reuseFailAlloc_4464_, 5, v_buildDir_4427_);
lean_ctor_set(v_reuseFailAlloc_4464_, 6, v_leanLibDir_4428_);
lean_ctor_set(v_reuseFailAlloc_4464_, 7, v_nativeLibDir_4429_);
lean_ctor_set(v_reuseFailAlloc_4464_, 8, v_binDir_4430_);
lean_ctor_set(v_reuseFailAlloc_4464_, 9, v_irDir_4431_);
lean_ctor_set(v_reuseFailAlloc_4464_, 10, v_releaseRepo_4432_);
lean_ctor_set(v_reuseFailAlloc_4464_, 11, v_buildArchive_4433_);
lean_ctor_set(v_reuseFailAlloc_4464_, 12, v_downloadCacheService_x3f_4435_);
lean_ctor_set(v_reuseFailAlloc_4464_, 13, v_testDriver_4436_);
lean_ctor_set(v_reuseFailAlloc_4464_, 14, v_testDriverArgs_4437_);
lean_ctor_set(v_reuseFailAlloc_4464_, 15, v_lintDriver_4438_);
lean_ctor_set(v_reuseFailAlloc_4464_, 16, v_lintDriverArgs_4439_);
lean_ctor_set(v_reuseFailAlloc_4464_, 17, v_version_4440_);
lean_ctor_set(v_reuseFailAlloc_4464_, 18, v_versionTags_4441_);
lean_ctor_set(v_reuseFailAlloc_4464_, 19, v_description_4442_);
lean_ctor_set(v_reuseFailAlloc_4464_, 20, v_keywords_4443_);
lean_ctor_set(v_reuseFailAlloc_4464_, 21, v_homepage_4444_);
lean_ctor_set(v_reuseFailAlloc_4464_, 22, v_license_4445_);
lean_ctor_set(v_reuseFailAlloc_4464_, 23, v_licenseFiles_4446_);
lean_ctor_set(v_reuseFailAlloc_4464_, 24, v_readmeFile_4447_);
lean_ctor_set(v_reuseFailAlloc_4464_, 25, v_enableArtifactCache_x3f_4449_);
lean_ctor_set(v_reuseFailAlloc_4464_, 26, v_restoreAllArtifacts_x3f_4450_);
lean_ctor_set(v_reuseFailAlloc_4464_, 27, v_builtinLint_x3f_4453_);
lean_ctor_set(v_reuseFailAlloc_4464_, 28, v_checks_4454_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*29, v_bootstrap_4422_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*29 + 1, v_precompileModules_4424_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4434_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*29 + 3, v_reservoir_4448_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4451_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*29 + 5, v_allowImportAll_4452_);
v___x_4462_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_unbox(v___x_4460_);
lean_ctor_set_uint8(v___x_4462_, sizeof(void*)*29 + 6, v___x_4463_);
return v___x_4462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg(){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = ((lean_object*)(l_Lake_PackageConfig_fixedToolchain___proj___redArg___closed__3));
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___redArg___boxed(lean_object* v___dummy_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
return v_res_4477_;
}
}
static lean_object* _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0(void){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lake_PackageConfig_fixedToolchain___proj___redArg();
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj(lean_object* v_p_4479_, lean_object* v_n_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain___proj___boxed(lean_object* v_p_4482_, lean_object* v_n_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lake_PackageConfig_fixedToolchain___proj(v_p_4482_, v_n_4483_);
lean_dec(v_n_4483_);
lean_dec(v_p_4482_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg(){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg___boxed(lean_object* v___dummy_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lake_PackageConfig_fixedToolchain_instConfigField___redArg();
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField(lean_object* v_p_4489_, lean_object* v_n_4490_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_obj_once(&l_Lake_PackageConfig_fixedToolchain___proj___closed__0, &l_Lake_PackageConfig_fixedToolchain___proj___closed__0_once, _init_l_Lake_PackageConfig_fixedToolchain___proj___closed__0);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_fixedToolchain_instConfigField___boxed(lean_object* v_p_4492_, lean_object* v_n_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lake_PackageConfig_fixedToolchain_instConfigField(v_p_4492_, v_n_4493_);
lean_dec(v_n_4493_);
lean_dec(v_p_4492_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(lean_object* v_cfg_4495_){
_start:
{
lean_object* v_toWorkspaceConfig_4496_; 
v_toWorkspaceConfig_4496_ = lean_ctor_get(v_cfg_4495_, 0);
lean_inc_ref(v_toWorkspaceConfig_4496_);
return v_toWorkspaceConfig_4496_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__0(v_cfg_4497_);
lean_dec_ref(v_cfg_4497_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__1(lean_object* v_val_4499_, lean_object* v_cfg_4500_){
_start:
{
lean_object* v_toLeanConfig_4501_; uint8_t v_bootstrap_4502_; lean_object* v_extraDepTargets_4503_; uint8_t v_precompileModules_4504_; lean_object* v_moreGlobalServerArgs_4505_; lean_object* v_srcDir_4506_; lean_object* v_buildDir_4507_; lean_object* v_leanLibDir_4508_; lean_object* v_nativeLibDir_4509_; lean_object* v_binDir_4510_; lean_object* v_irDir_4511_; lean_object* v_releaseRepo_4512_; lean_object* v_buildArchive_4513_; uint8_t v_preferReleaseBuild_4514_; lean_object* v_downloadCacheService_x3f_4515_; lean_object* v_testDriver_4516_; lean_object* v_testDriverArgs_4517_; lean_object* v_lintDriver_4518_; lean_object* v_lintDriverArgs_4519_; lean_object* v_version_4520_; lean_object* v_versionTags_4521_; lean_object* v_description_4522_; lean_object* v_keywords_4523_; lean_object* v_homepage_4524_; lean_object* v_license_4525_; lean_object* v_licenseFiles_4526_; lean_object* v_readmeFile_4527_; uint8_t v_reservoir_4528_; lean_object* v_enableArtifactCache_x3f_4529_; lean_object* v_restoreAllArtifacts_x3f_4530_; uint8_t v_libPrefixOnWindows_4531_; uint8_t v_allowImportAll_4532_; lean_object* v_builtinLint_x3f_4533_; lean_object* v_checks_4534_; uint8_t v_fixedToolchain_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
v_toLeanConfig_4501_ = lean_ctor_get(v_cfg_4500_, 1);
v_bootstrap_4502_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29);
v_extraDepTargets_4503_ = lean_ctor_get(v_cfg_4500_, 2);
v_precompileModules_4504_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4505_ = lean_ctor_get(v_cfg_4500_, 3);
v_srcDir_4506_ = lean_ctor_get(v_cfg_4500_, 4);
v_buildDir_4507_ = lean_ctor_get(v_cfg_4500_, 5);
v_leanLibDir_4508_ = lean_ctor_get(v_cfg_4500_, 6);
v_nativeLibDir_4509_ = lean_ctor_get(v_cfg_4500_, 7);
v_binDir_4510_ = lean_ctor_get(v_cfg_4500_, 8);
v_irDir_4511_ = lean_ctor_get(v_cfg_4500_, 9);
v_releaseRepo_4512_ = lean_ctor_get(v_cfg_4500_, 10);
v_buildArchive_4513_ = lean_ctor_get(v_cfg_4500_, 11);
v_preferReleaseBuild_4514_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4515_ = lean_ctor_get(v_cfg_4500_, 12);
v_testDriver_4516_ = lean_ctor_get(v_cfg_4500_, 13);
v_testDriverArgs_4517_ = lean_ctor_get(v_cfg_4500_, 14);
v_lintDriver_4518_ = lean_ctor_get(v_cfg_4500_, 15);
v_lintDriverArgs_4519_ = lean_ctor_get(v_cfg_4500_, 16);
v_version_4520_ = lean_ctor_get(v_cfg_4500_, 17);
v_versionTags_4521_ = lean_ctor_get(v_cfg_4500_, 18);
v_description_4522_ = lean_ctor_get(v_cfg_4500_, 19);
v_keywords_4523_ = lean_ctor_get(v_cfg_4500_, 20);
v_homepage_4524_ = lean_ctor_get(v_cfg_4500_, 21);
v_license_4525_ = lean_ctor_get(v_cfg_4500_, 22);
v_licenseFiles_4526_ = lean_ctor_get(v_cfg_4500_, 23);
v_readmeFile_4527_ = lean_ctor_get(v_cfg_4500_, 24);
v_reservoir_4528_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4529_ = lean_ctor_get(v_cfg_4500_, 25);
v_restoreAllArtifacts_x3f_4530_ = lean_ctor_get(v_cfg_4500_, 26);
v_libPrefixOnWindows_4531_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29 + 4);
v_allowImportAll_4532_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4533_ = lean_ctor_get(v_cfg_4500_, 27);
v_checks_4534_ = lean_ctor_get(v_cfg_4500_, 28);
v_fixedToolchain_4535_ = lean_ctor_get_uint8(v_cfg_4500_, sizeof(void*)*29 + 6);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_cfg_4500_);
if (v_isSharedCheck_4542_ == 0)
{
lean_object* v_unused_4543_; 
v_unused_4543_ = lean_ctor_get(v_cfg_4500_, 0);
lean_dec(v_unused_4543_);
v___x_4537_ = v_cfg_4500_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_checks_4534_);
lean_inc(v_builtinLint_x3f_4533_);
lean_inc(v_restoreAllArtifacts_x3f_4530_);
lean_inc(v_enableArtifactCache_x3f_4529_);
lean_inc(v_readmeFile_4527_);
lean_inc(v_licenseFiles_4526_);
lean_inc(v_license_4525_);
lean_inc(v_homepage_4524_);
lean_inc(v_keywords_4523_);
lean_inc(v_description_4522_);
lean_inc(v_versionTags_4521_);
lean_inc(v_version_4520_);
lean_inc(v_lintDriverArgs_4519_);
lean_inc(v_lintDriver_4518_);
lean_inc(v_testDriverArgs_4517_);
lean_inc(v_testDriver_4516_);
lean_inc(v_downloadCacheService_x3f_4515_);
lean_inc(v_buildArchive_4513_);
lean_inc(v_releaseRepo_4512_);
lean_inc(v_irDir_4511_);
lean_inc(v_binDir_4510_);
lean_inc(v_nativeLibDir_4509_);
lean_inc(v_leanLibDir_4508_);
lean_inc(v_buildDir_4507_);
lean_inc(v_srcDir_4506_);
lean_inc(v_moreGlobalServerArgs_4505_);
lean_inc(v_extraDepTargets_4503_);
lean_inc(v_toLeanConfig_4501_);
lean_dec(v_cfg_4500_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v_val_4499_);
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_val_4499_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_toLeanConfig_4501_);
lean_ctor_set(v_reuseFailAlloc_4541_, 2, v_extraDepTargets_4503_);
lean_ctor_set(v_reuseFailAlloc_4541_, 3, v_moreGlobalServerArgs_4505_);
lean_ctor_set(v_reuseFailAlloc_4541_, 4, v_srcDir_4506_);
lean_ctor_set(v_reuseFailAlloc_4541_, 5, v_buildDir_4507_);
lean_ctor_set(v_reuseFailAlloc_4541_, 6, v_leanLibDir_4508_);
lean_ctor_set(v_reuseFailAlloc_4541_, 7, v_nativeLibDir_4509_);
lean_ctor_set(v_reuseFailAlloc_4541_, 8, v_binDir_4510_);
lean_ctor_set(v_reuseFailAlloc_4541_, 9, v_irDir_4511_);
lean_ctor_set(v_reuseFailAlloc_4541_, 10, v_releaseRepo_4512_);
lean_ctor_set(v_reuseFailAlloc_4541_, 11, v_buildArchive_4513_);
lean_ctor_set(v_reuseFailAlloc_4541_, 12, v_downloadCacheService_x3f_4515_);
lean_ctor_set(v_reuseFailAlloc_4541_, 13, v_testDriver_4516_);
lean_ctor_set(v_reuseFailAlloc_4541_, 14, v_testDriverArgs_4517_);
lean_ctor_set(v_reuseFailAlloc_4541_, 15, v_lintDriver_4518_);
lean_ctor_set(v_reuseFailAlloc_4541_, 16, v_lintDriverArgs_4519_);
lean_ctor_set(v_reuseFailAlloc_4541_, 17, v_version_4520_);
lean_ctor_set(v_reuseFailAlloc_4541_, 18, v_versionTags_4521_);
lean_ctor_set(v_reuseFailAlloc_4541_, 19, v_description_4522_);
lean_ctor_set(v_reuseFailAlloc_4541_, 20, v_keywords_4523_);
lean_ctor_set(v_reuseFailAlloc_4541_, 21, v_homepage_4524_);
lean_ctor_set(v_reuseFailAlloc_4541_, 22, v_license_4525_);
lean_ctor_set(v_reuseFailAlloc_4541_, 23, v_licenseFiles_4526_);
lean_ctor_set(v_reuseFailAlloc_4541_, 24, v_readmeFile_4527_);
lean_ctor_set(v_reuseFailAlloc_4541_, 25, v_enableArtifactCache_x3f_4529_);
lean_ctor_set(v_reuseFailAlloc_4541_, 26, v_restoreAllArtifacts_x3f_4530_);
lean_ctor_set(v_reuseFailAlloc_4541_, 27, v_builtinLint_x3f_4533_);
lean_ctor_set(v_reuseFailAlloc_4541_, 28, v_checks_4534_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29, v_bootstrap_4502_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29 + 1, v_precompileModules_4504_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4514_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29 + 3, v_reservoir_4528_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4531_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29 + 5, v_allowImportAll_4532_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*29 + 6, v_fixedToolchain_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__2(lean_object* v_f_4544_, lean_object* v_cfg_4545_){
_start:
{
lean_object* v_toWorkspaceConfig_4546_; lean_object* v_toLeanConfig_4547_; uint8_t v_bootstrap_4548_; lean_object* v_extraDepTargets_4549_; uint8_t v_precompileModules_4550_; lean_object* v_moreGlobalServerArgs_4551_; lean_object* v_srcDir_4552_; lean_object* v_buildDir_4553_; lean_object* v_leanLibDir_4554_; lean_object* v_nativeLibDir_4555_; lean_object* v_binDir_4556_; lean_object* v_irDir_4557_; lean_object* v_releaseRepo_4558_; lean_object* v_buildArchive_4559_; uint8_t v_preferReleaseBuild_4560_; lean_object* v_downloadCacheService_x3f_4561_; lean_object* v_testDriver_4562_; lean_object* v_testDriverArgs_4563_; lean_object* v_lintDriver_4564_; lean_object* v_lintDriverArgs_4565_; lean_object* v_version_4566_; lean_object* v_versionTags_4567_; lean_object* v_description_4568_; lean_object* v_keywords_4569_; lean_object* v_homepage_4570_; lean_object* v_license_4571_; lean_object* v_licenseFiles_4572_; lean_object* v_readmeFile_4573_; uint8_t v_reservoir_4574_; lean_object* v_enableArtifactCache_x3f_4575_; lean_object* v_restoreAllArtifacts_x3f_4576_; uint8_t v_libPrefixOnWindows_4577_; uint8_t v_allowImportAll_4578_; lean_object* v_builtinLint_x3f_4579_; lean_object* v_checks_4580_; uint8_t v_fixedToolchain_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4589_; 
v_toWorkspaceConfig_4546_ = lean_ctor_get(v_cfg_4545_, 0);
v_toLeanConfig_4547_ = lean_ctor_get(v_cfg_4545_, 1);
v_bootstrap_4548_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29);
v_extraDepTargets_4549_ = lean_ctor_get(v_cfg_4545_, 2);
v_precompileModules_4550_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4551_ = lean_ctor_get(v_cfg_4545_, 3);
v_srcDir_4552_ = lean_ctor_get(v_cfg_4545_, 4);
v_buildDir_4553_ = lean_ctor_get(v_cfg_4545_, 5);
v_leanLibDir_4554_ = lean_ctor_get(v_cfg_4545_, 6);
v_nativeLibDir_4555_ = lean_ctor_get(v_cfg_4545_, 7);
v_binDir_4556_ = lean_ctor_get(v_cfg_4545_, 8);
v_irDir_4557_ = lean_ctor_get(v_cfg_4545_, 9);
v_releaseRepo_4558_ = lean_ctor_get(v_cfg_4545_, 10);
v_buildArchive_4559_ = lean_ctor_get(v_cfg_4545_, 11);
v_preferReleaseBuild_4560_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4561_ = lean_ctor_get(v_cfg_4545_, 12);
v_testDriver_4562_ = lean_ctor_get(v_cfg_4545_, 13);
v_testDriverArgs_4563_ = lean_ctor_get(v_cfg_4545_, 14);
v_lintDriver_4564_ = lean_ctor_get(v_cfg_4545_, 15);
v_lintDriverArgs_4565_ = lean_ctor_get(v_cfg_4545_, 16);
v_version_4566_ = lean_ctor_get(v_cfg_4545_, 17);
v_versionTags_4567_ = lean_ctor_get(v_cfg_4545_, 18);
v_description_4568_ = lean_ctor_get(v_cfg_4545_, 19);
v_keywords_4569_ = lean_ctor_get(v_cfg_4545_, 20);
v_homepage_4570_ = lean_ctor_get(v_cfg_4545_, 21);
v_license_4571_ = lean_ctor_get(v_cfg_4545_, 22);
v_licenseFiles_4572_ = lean_ctor_get(v_cfg_4545_, 23);
v_readmeFile_4573_ = lean_ctor_get(v_cfg_4545_, 24);
v_reservoir_4574_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4575_ = lean_ctor_get(v_cfg_4545_, 25);
v_restoreAllArtifacts_x3f_4576_ = lean_ctor_get(v_cfg_4545_, 26);
v_libPrefixOnWindows_4577_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29 + 4);
v_allowImportAll_4578_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4579_ = lean_ctor_get(v_cfg_4545_, 27);
v_checks_4580_ = lean_ctor_get(v_cfg_4545_, 28);
v_fixedToolchain_4581_ = lean_ctor_get_uint8(v_cfg_4545_, sizeof(void*)*29 + 6);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_cfg_4545_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4583_ = v_cfg_4545_;
v_isShared_4584_ = v_isSharedCheck_4589_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_checks_4580_);
lean_inc(v_builtinLint_x3f_4579_);
lean_inc(v_restoreAllArtifacts_x3f_4576_);
lean_inc(v_enableArtifactCache_x3f_4575_);
lean_inc(v_readmeFile_4573_);
lean_inc(v_licenseFiles_4572_);
lean_inc(v_license_4571_);
lean_inc(v_homepage_4570_);
lean_inc(v_keywords_4569_);
lean_inc(v_description_4568_);
lean_inc(v_versionTags_4567_);
lean_inc(v_version_4566_);
lean_inc(v_lintDriverArgs_4565_);
lean_inc(v_lintDriver_4564_);
lean_inc(v_testDriverArgs_4563_);
lean_inc(v_testDriver_4562_);
lean_inc(v_downloadCacheService_x3f_4561_);
lean_inc(v_buildArchive_4559_);
lean_inc(v_releaseRepo_4558_);
lean_inc(v_irDir_4557_);
lean_inc(v_binDir_4556_);
lean_inc(v_nativeLibDir_4555_);
lean_inc(v_leanLibDir_4554_);
lean_inc(v_buildDir_4553_);
lean_inc(v_srcDir_4552_);
lean_inc(v_moreGlobalServerArgs_4551_);
lean_inc(v_extraDepTargets_4549_);
lean_inc(v_toLeanConfig_4547_);
lean_inc(v_toWorkspaceConfig_4546_);
lean_dec(v_cfg_4545_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4589_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4585_ = lean_apply_1(v_f_4544_, v_toWorkspaceConfig_4546_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4585_);
v___x_4587_ = v___x_4583_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v_toLeanConfig_4547_);
lean_ctor_set(v_reuseFailAlloc_4588_, 2, v_extraDepTargets_4549_);
lean_ctor_set(v_reuseFailAlloc_4588_, 3, v_moreGlobalServerArgs_4551_);
lean_ctor_set(v_reuseFailAlloc_4588_, 4, v_srcDir_4552_);
lean_ctor_set(v_reuseFailAlloc_4588_, 5, v_buildDir_4553_);
lean_ctor_set(v_reuseFailAlloc_4588_, 6, v_leanLibDir_4554_);
lean_ctor_set(v_reuseFailAlloc_4588_, 7, v_nativeLibDir_4555_);
lean_ctor_set(v_reuseFailAlloc_4588_, 8, v_binDir_4556_);
lean_ctor_set(v_reuseFailAlloc_4588_, 9, v_irDir_4557_);
lean_ctor_set(v_reuseFailAlloc_4588_, 10, v_releaseRepo_4558_);
lean_ctor_set(v_reuseFailAlloc_4588_, 11, v_buildArchive_4559_);
lean_ctor_set(v_reuseFailAlloc_4588_, 12, v_downloadCacheService_x3f_4561_);
lean_ctor_set(v_reuseFailAlloc_4588_, 13, v_testDriver_4562_);
lean_ctor_set(v_reuseFailAlloc_4588_, 14, v_testDriverArgs_4563_);
lean_ctor_set(v_reuseFailAlloc_4588_, 15, v_lintDriver_4564_);
lean_ctor_set(v_reuseFailAlloc_4588_, 16, v_lintDriverArgs_4565_);
lean_ctor_set(v_reuseFailAlloc_4588_, 17, v_version_4566_);
lean_ctor_set(v_reuseFailAlloc_4588_, 18, v_versionTags_4567_);
lean_ctor_set(v_reuseFailAlloc_4588_, 19, v_description_4568_);
lean_ctor_set(v_reuseFailAlloc_4588_, 20, v_keywords_4569_);
lean_ctor_set(v_reuseFailAlloc_4588_, 21, v_homepage_4570_);
lean_ctor_set(v_reuseFailAlloc_4588_, 22, v_license_4571_);
lean_ctor_set(v_reuseFailAlloc_4588_, 23, v_licenseFiles_4572_);
lean_ctor_set(v_reuseFailAlloc_4588_, 24, v_readmeFile_4573_);
lean_ctor_set(v_reuseFailAlloc_4588_, 25, v_enableArtifactCache_x3f_4575_);
lean_ctor_set(v_reuseFailAlloc_4588_, 26, v_restoreAllArtifacts_x3f_4576_);
lean_ctor_set(v_reuseFailAlloc_4588_, 27, v_builtinLint_x3f_4579_);
lean_ctor_set(v_reuseFailAlloc_4588_, 28, v_checks_4580_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29, v_bootstrap_4548_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29 + 1, v_precompileModules_4550_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4560_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29 + 3, v_reservoir_4574_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4577_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29 + 5, v_allowImportAll_4578_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*29 + 6, v_fixedToolchain_4581_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(lean_object* v_x_4590_){
_start:
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Lake_defaultPackagesDir;
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3___boxed(lean_object* v_x_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___lam__3(v_x_4592_);
lean_dec_ref(v_x_4592_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg(){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = ((lean_object*)(l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___closed__4));
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg___boxed(lean_object* v___dummy_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
return v_res_4606_;
}
}
static lean_object* _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lake_PackageConfig_toWorkspaceConfig___proj___redArg();
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj(lean_object* v_p_4608_, lean_object* v_n_4609_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig___proj___boxed(lean_object* v_p_4611_, lean_object* v_n_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lake_PackageConfig_toWorkspaceConfig___proj(v_p_4611_, v_n_4612_);
lean_dec(v_n_4612_);
lean_dec(v_p_4611_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___redArg();
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(lean_object* v_p_4618_, lean_object* v_n_4619_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_obj_once(&l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0, &l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toWorkspaceConfig___proj___closed__0);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent___boxed(lean_object* v_p_4621_, lean_object* v_n_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Lake_PackageConfig_toWorkspaceConfig_instConfigParent(v_p_4621_, v_n_4622_);
lean_dec(v_n_4622_);
lean_dec(v_p_4621_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(lean_object* v_cfg_4624_){
_start:
{
lean_object* v_toLeanConfig_4625_; 
v_toLeanConfig_4625_ = lean_ctor_get(v_cfg_4624_, 1);
lean_inc_ref(v_toLeanConfig_4625_);
return v_toLeanConfig_4625_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0___boxed(lean_object* v_cfg_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__0(v_cfg_4626_);
lean_dec_ref(v_cfg_4626_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__1(lean_object* v_val_4628_, lean_object* v_cfg_4629_){
_start:
{
lean_object* v_toWorkspaceConfig_4630_; uint8_t v_bootstrap_4631_; lean_object* v_extraDepTargets_4632_; uint8_t v_precompileModules_4633_; lean_object* v_moreGlobalServerArgs_4634_; lean_object* v_srcDir_4635_; lean_object* v_buildDir_4636_; lean_object* v_leanLibDir_4637_; lean_object* v_nativeLibDir_4638_; lean_object* v_binDir_4639_; lean_object* v_irDir_4640_; lean_object* v_releaseRepo_4641_; lean_object* v_buildArchive_4642_; uint8_t v_preferReleaseBuild_4643_; lean_object* v_downloadCacheService_x3f_4644_; lean_object* v_testDriver_4645_; lean_object* v_testDriverArgs_4646_; lean_object* v_lintDriver_4647_; lean_object* v_lintDriverArgs_4648_; lean_object* v_version_4649_; lean_object* v_versionTags_4650_; lean_object* v_description_4651_; lean_object* v_keywords_4652_; lean_object* v_homepage_4653_; lean_object* v_license_4654_; lean_object* v_licenseFiles_4655_; lean_object* v_readmeFile_4656_; uint8_t v_reservoir_4657_; lean_object* v_enableArtifactCache_x3f_4658_; lean_object* v_restoreAllArtifacts_x3f_4659_; uint8_t v_libPrefixOnWindows_4660_; uint8_t v_allowImportAll_4661_; lean_object* v_builtinLint_x3f_4662_; lean_object* v_checks_4663_; uint8_t v_fixedToolchain_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
v_toWorkspaceConfig_4630_ = lean_ctor_get(v_cfg_4629_, 0);
v_bootstrap_4631_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29);
v_extraDepTargets_4632_ = lean_ctor_get(v_cfg_4629_, 2);
v_precompileModules_4633_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4634_ = lean_ctor_get(v_cfg_4629_, 3);
v_srcDir_4635_ = lean_ctor_get(v_cfg_4629_, 4);
v_buildDir_4636_ = lean_ctor_get(v_cfg_4629_, 5);
v_leanLibDir_4637_ = lean_ctor_get(v_cfg_4629_, 6);
v_nativeLibDir_4638_ = lean_ctor_get(v_cfg_4629_, 7);
v_binDir_4639_ = lean_ctor_get(v_cfg_4629_, 8);
v_irDir_4640_ = lean_ctor_get(v_cfg_4629_, 9);
v_releaseRepo_4641_ = lean_ctor_get(v_cfg_4629_, 10);
v_buildArchive_4642_ = lean_ctor_get(v_cfg_4629_, 11);
v_preferReleaseBuild_4643_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4644_ = lean_ctor_get(v_cfg_4629_, 12);
v_testDriver_4645_ = lean_ctor_get(v_cfg_4629_, 13);
v_testDriverArgs_4646_ = lean_ctor_get(v_cfg_4629_, 14);
v_lintDriver_4647_ = lean_ctor_get(v_cfg_4629_, 15);
v_lintDriverArgs_4648_ = lean_ctor_get(v_cfg_4629_, 16);
v_version_4649_ = lean_ctor_get(v_cfg_4629_, 17);
v_versionTags_4650_ = lean_ctor_get(v_cfg_4629_, 18);
v_description_4651_ = lean_ctor_get(v_cfg_4629_, 19);
v_keywords_4652_ = lean_ctor_get(v_cfg_4629_, 20);
v_homepage_4653_ = lean_ctor_get(v_cfg_4629_, 21);
v_license_4654_ = lean_ctor_get(v_cfg_4629_, 22);
v_licenseFiles_4655_ = lean_ctor_get(v_cfg_4629_, 23);
v_readmeFile_4656_ = lean_ctor_get(v_cfg_4629_, 24);
v_reservoir_4657_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4658_ = lean_ctor_get(v_cfg_4629_, 25);
v_restoreAllArtifacts_x3f_4659_ = lean_ctor_get(v_cfg_4629_, 26);
v_libPrefixOnWindows_4660_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29 + 4);
v_allowImportAll_4661_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4662_ = lean_ctor_get(v_cfg_4629_, 27);
v_checks_4663_ = lean_ctor_get(v_cfg_4629_, 28);
v_fixedToolchain_4664_ = lean_ctor_get_uint8(v_cfg_4629_, sizeof(void*)*29 + 6);
v_isSharedCheck_4671_ = !lean_is_exclusive(v_cfg_4629_);
if (v_isSharedCheck_4671_ == 0)
{
lean_object* v_unused_4672_; 
v_unused_4672_ = lean_ctor_get(v_cfg_4629_, 1);
lean_dec(v_unused_4672_);
v___x_4666_ = v_cfg_4629_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_checks_4663_);
lean_inc(v_builtinLint_x3f_4662_);
lean_inc(v_restoreAllArtifacts_x3f_4659_);
lean_inc(v_enableArtifactCache_x3f_4658_);
lean_inc(v_readmeFile_4656_);
lean_inc(v_licenseFiles_4655_);
lean_inc(v_license_4654_);
lean_inc(v_homepage_4653_);
lean_inc(v_keywords_4652_);
lean_inc(v_description_4651_);
lean_inc(v_versionTags_4650_);
lean_inc(v_version_4649_);
lean_inc(v_lintDriverArgs_4648_);
lean_inc(v_lintDriver_4647_);
lean_inc(v_testDriverArgs_4646_);
lean_inc(v_testDriver_4645_);
lean_inc(v_downloadCacheService_x3f_4644_);
lean_inc(v_buildArchive_4642_);
lean_inc(v_releaseRepo_4641_);
lean_inc(v_irDir_4640_);
lean_inc(v_binDir_4639_);
lean_inc(v_nativeLibDir_4638_);
lean_inc(v_leanLibDir_4637_);
lean_inc(v_buildDir_4636_);
lean_inc(v_srcDir_4635_);
lean_inc(v_moreGlobalServerArgs_4634_);
lean_inc(v_extraDepTargets_4632_);
lean_inc(v_toWorkspaceConfig_4630_);
lean_dec(v_cfg_4629_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 1, v_val_4628_);
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_toWorkspaceConfig_4630_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_val_4628_);
lean_ctor_set(v_reuseFailAlloc_4670_, 2, v_extraDepTargets_4632_);
lean_ctor_set(v_reuseFailAlloc_4670_, 3, v_moreGlobalServerArgs_4634_);
lean_ctor_set(v_reuseFailAlloc_4670_, 4, v_srcDir_4635_);
lean_ctor_set(v_reuseFailAlloc_4670_, 5, v_buildDir_4636_);
lean_ctor_set(v_reuseFailAlloc_4670_, 6, v_leanLibDir_4637_);
lean_ctor_set(v_reuseFailAlloc_4670_, 7, v_nativeLibDir_4638_);
lean_ctor_set(v_reuseFailAlloc_4670_, 8, v_binDir_4639_);
lean_ctor_set(v_reuseFailAlloc_4670_, 9, v_irDir_4640_);
lean_ctor_set(v_reuseFailAlloc_4670_, 10, v_releaseRepo_4641_);
lean_ctor_set(v_reuseFailAlloc_4670_, 11, v_buildArchive_4642_);
lean_ctor_set(v_reuseFailAlloc_4670_, 12, v_downloadCacheService_x3f_4644_);
lean_ctor_set(v_reuseFailAlloc_4670_, 13, v_testDriver_4645_);
lean_ctor_set(v_reuseFailAlloc_4670_, 14, v_testDriverArgs_4646_);
lean_ctor_set(v_reuseFailAlloc_4670_, 15, v_lintDriver_4647_);
lean_ctor_set(v_reuseFailAlloc_4670_, 16, v_lintDriverArgs_4648_);
lean_ctor_set(v_reuseFailAlloc_4670_, 17, v_version_4649_);
lean_ctor_set(v_reuseFailAlloc_4670_, 18, v_versionTags_4650_);
lean_ctor_set(v_reuseFailAlloc_4670_, 19, v_description_4651_);
lean_ctor_set(v_reuseFailAlloc_4670_, 20, v_keywords_4652_);
lean_ctor_set(v_reuseFailAlloc_4670_, 21, v_homepage_4653_);
lean_ctor_set(v_reuseFailAlloc_4670_, 22, v_license_4654_);
lean_ctor_set(v_reuseFailAlloc_4670_, 23, v_licenseFiles_4655_);
lean_ctor_set(v_reuseFailAlloc_4670_, 24, v_readmeFile_4656_);
lean_ctor_set(v_reuseFailAlloc_4670_, 25, v_enableArtifactCache_x3f_4658_);
lean_ctor_set(v_reuseFailAlloc_4670_, 26, v_restoreAllArtifacts_x3f_4659_);
lean_ctor_set(v_reuseFailAlloc_4670_, 27, v_builtinLint_x3f_4662_);
lean_ctor_set(v_reuseFailAlloc_4670_, 28, v_checks_4663_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29, v_bootstrap_4631_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29 + 1, v_precompileModules_4633_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4643_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29 + 3, v_reservoir_4657_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4660_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29 + 5, v_allowImportAll_4661_);
lean_ctor_set_uint8(v_reuseFailAlloc_4670_, sizeof(void*)*29 + 6, v_fixedToolchain_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__2(lean_object* v_f_4673_, lean_object* v_cfg_4674_){
_start:
{
lean_object* v_toWorkspaceConfig_4675_; lean_object* v_toLeanConfig_4676_; uint8_t v_bootstrap_4677_; lean_object* v_extraDepTargets_4678_; uint8_t v_precompileModules_4679_; lean_object* v_moreGlobalServerArgs_4680_; lean_object* v_srcDir_4681_; lean_object* v_buildDir_4682_; lean_object* v_leanLibDir_4683_; lean_object* v_nativeLibDir_4684_; lean_object* v_binDir_4685_; lean_object* v_irDir_4686_; lean_object* v_releaseRepo_4687_; lean_object* v_buildArchive_4688_; uint8_t v_preferReleaseBuild_4689_; lean_object* v_downloadCacheService_x3f_4690_; lean_object* v_testDriver_4691_; lean_object* v_testDriverArgs_4692_; lean_object* v_lintDriver_4693_; lean_object* v_lintDriverArgs_4694_; lean_object* v_version_4695_; lean_object* v_versionTags_4696_; lean_object* v_description_4697_; lean_object* v_keywords_4698_; lean_object* v_homepage_4699_; lean_object* v_license_4700_; lean_object* v_licenseFiles_4701_; lean_object* v_readmeFile_4702_; uint8_t v_reservoir_4703_; lean_object* v_enableArtifactCache_x3f_4704_; lean_object* v_restoreAllArtifacts_x3f_4705_; uint8_t v_libPrefixOnWindows_4706_; uint8_t v_allowImportAll_4707_; lean_object* v_builtinLint_x3f_4708_; lean_object* v_checks_4709_; uint8_t v_fixedToolchain_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4718_; 
v_toWorkspaceConfig_4675_ = lean_ctor_get(v_cfg_4674_, 0);
v_toLeanConfig_4676_ = lean_ctor_get(v_cfg_4674_, 1);
v_bootstrap_4677_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29);
v_extraDepTargets_4678_ = lean_ctor_get(v_cfg_4674_, 2);
v_precompileModules_4679_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29 + 1);
v_moreGlobalServerArgs_4680_ = lean_ctor_get(v_cfg_4674_, 3);
v_srcDir_4681_ = lean_ctor_get(v_cfg_4674_, 4);
v_buildDir_4682_ = lean_ctor_get(v_cfg_4674_, 5);
v_leanLibDir_4683_ = lean_ctor_get(v_cfg_4674_, 6);
v_nativeLibDir_4684_ = lean_ctor_get(v_cfg_4674_, 7);
v_binDir_4685_ = lean_ctor_get(v_cfg_4674_, 8);
v_irDir_4686_ = lean_ctor_get(v_cfg_4674_, 9);
v_releaseRepo_4687_ = lean_ctor_get(v_cfg_4674_, 10);
v_buildArchive_4688_ = lean_ctor_get(v_cfg_4674_, 11);
v_preferReleaseBuild_4689_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_4690_ = lean_ctor_get(v_cfg_4674_, 12);
v_testDriver_4691_ = lean_ctor_get(v_cfg_4674_, 13);
v_testDriverArgs_4692_ = lean_ctor_get(v_cfg_4674_, 14);
v_lintDriver_4693_ = lean_ctor_get(v_cfg_4674_, 15);
v_lintDriverArgs_4694_ = lean_ctor_get(v_cfg_4674_, 16);
v_version_4695_ = lean_ctor_get(v_cfg_4674_, 17);
v_versionTags_4696_ = lean_ctor_get(v_cfg_4674_, 18);
v_description_4697_ = lean_ctor_get(v_cfg_4674_, 19);
v_keywords_4698_ = lean_ctor_get(v_cfg_4674_, 20);
v_homepage_4699_ = lean_ctor_get(v_cfg_4674_, 21);
v_license_4700_ = lean_ctor_get(v_cfg_4674_, 22);
v_licenseFiles_4701_ = lean_ctor_get(v_cfg_4674_, 23);
v_readmeFile_4702_ = lean_ctor_get(v_cfg_4674_, 24);
v_reservoir_4703_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29 + 3);
v_enableArtifactCache_x3f_4704_ = lean_ctor_get(v_cfg_4674_, 25);
v_restoreAllArtifacts_x3f_4705_ = lean_ctor_get(v_cfg_4674_, 26);
v_libPrefixOnWindows_4706_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29 + 4);
v_allowImportAll_4707_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29 + 5);
v_builtinLint_x3f_4708_ = lean_ctor_get(v_cfg_4674_, 27);
v_checks_4709_ = lean_ctor_get(v_cfg_4674_, 28);
v_fixedToolchain_4710_ = lean_ctor_get_uint8(v_cfg_4674_, sizeof(void*)*29 + 6);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_cfg_4674_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4712_ = v_cfg_4674_;
v_isShared_4713_ = v_isSharedCheck_4718_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_checks_4709_);
lean_inc(v_builtinLint_x3f_4708_);
lean_inc(v_restoreAllArtifacts_x3f_4705_);
lean_inc(v_enableArtifactCache_x3f_4704_);
lean_inc(v_readmeFile_4702_);
lean_inc(v_licenseFiles_4701_);
lean_inc(v_license_4700_);
lean_inc(v_homepage_4699_);
lean_inc(v_keywords_4698_);
lean_inc(v_description_4697_);
lean_inc(v_versionTags_4696_);
lean_inc(v_version_4695_);
lean_inc(v_lintDriverArgs_4694_);
lean_inc(v_lintDriver_4693_);
lean_inc(v_testDriverArgs_4692_);
lean_inc(v_testDriver_4691_);
lean_inc(v_downloadCacheService_x3f_4690_);
lean_inc(v_buildArchive_4688_);
lean_inc(v_releaseRepo_4687_);
lean_inc(v_irDir_4686_);
lean_inc(v_binDir_4685_);
lean_inc(v_nativeLibDir_4684_);
lean_inc(v_leanLibDir_4683_);
lean_inc(v_buildDir_4682_);
lean_inc(v_srcDir_4681_);
lean_inc(v_moreGlobalServerArgs_4680_);
lean_inc(v_extraDepTargets_4678_);
lean_inc(v_toLeanConfig_4676_);
lean_inc(v_toWorkspaceConfig_4675_);
lean_dec(v_cfg_4674_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4718_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4714_; lean_object* v___x_4716_; 
v___x_4714_ = lean_apply_1(v_f_4673_, v_toLeanConfig_4676_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 1, v___x_4714_);
v___x_4716_ = v___x_4712_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_toWorkspaceConfig_4675_);
lean_ctor_set(v_reuseFailAlloc_4717_, 1, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4717_, 2, v_extraDepTargets_4678_);
lean_ctor_set(v_reuseFailAlloc_4717_, 3, v_moreGlobalServerArgs_4680_);
lean_ctor_set(v_reuseFailAlloc_4717_, 4, v_srcDir_4681_);
lean_ctor_set(v_reuseFailAlloc_4717_, 5, v_buildDir_4682_);
lean_ctor_set(v_reuseFailAlloc_4717_, 6, v_leanLibDir_4683_);
lean_ctor_set(v_reuseFailAlloc_4717_, 7, v_nativeLibDir_4684_);
lean_ctor_set(v_reuseFailAlloc_4717_, 8, v_binDir_4685_);
lean_ctor_set(v_reuseFailAlloc_4717_, 9, v_irDir_4686_);
lean_ctor_set(v_reuseFailAlloc_4717_, 10, v_releaseRepo_4687_);
lean_ctor_set(v_reuseFailAlloc_4717_, 11, v_buildArchive_4688_);
lean_ctor_set(v_reuseFailAlloc_4717_, 12, v_downloadCacheService_x3f_4690_);
lean_ctor_set(v_reuseFailAlloc_4717_, 13, v_testDriver_4691_);
lean_ctor_set(v_reuseFailAlloc_4717_, 14, v_testDriverArgs_4692_);
lean_ctor_set(v_reuseFailAlloc_4717_, 15, v_lintDriver_4693_);
lean_ctor_set(v_reuseFailAlloc_4717_, 16, v_lintDriverArgs_4694_);
lean_ctor_set(v_reuseFailAlloc_4717_, 17, v_version_4695_);
lean_ctor_set(v_reuseFailAlloc_4717_, 18, v_versionTags_4696_);
lean_ctor_set(v_reuseFailAlloc_4717_, 19, v_description_4697_);
lean_ctor_set(v_reuseFailAlloc_4717_, 20, v_keywords_4698_);
lean_ctor_set(v_reuseFailAlloc_4717_, 21, v_homepage_4699_);
lean_ctor_set(v_reuseFailAlloc_4717_, 22, v_license_4700_);
lean_ctor_set(v_reuseFailAlloc_4717_, 23, v_licenseFiles_4701_);
lean_ctor_set(v_reuseFailAlloc_4717_, 24, v_readmeFile_4702_);
lean_ctor_set(v_reuseFailAlloc_4717_, 25, v_enableArtifactCache_x3f_4704_);
lean_ctor_set(v_reuseFailAlloc_4717_, 26, v_restoreAllArtifacts_x3f_4705_);
lean_ctor_set(v_reuseFailAlloc_4717_, 27, v_builtinLint_x3f_4708_);
lean_ctor_set(v_reuseFailAlloc_4717_, 28, v_checks_4709_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29, v_bootstrap_4677_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29 + 1, v_precompileModules_4679_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29 + 2, v_preferReleaseBuild_4689_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29 + 3, v_reservoir_4703_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29 + 4, v_libPrefixOnWindows_4706_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29 + 5, v_allowImportAll_4707_);
lean_ctor_set_uint8(v_reuseFailAlloc_4717_, sizeof(void*)*29 + 6, v_fixedToolchain_4710_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(lean_object* v_x_4727_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___boxed(lean_object* v_x_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3(v_x_4729_);
lean_dec_ref(v_x_4729_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg(){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___closed__4));
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___redArg___boxed(lean_object* v___dummy_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
return v_res_4743_;
}
}
static lean_object* _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0(void){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l_Lake_PackageConfig_toLeanConfig___proj___redArg();
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj(lean_object* v_p_4745_, lean_object* v_n_4746_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig___proj___boxed(lean_object* v_p_4748_, lean_object* v_n_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_Lake_PackageConfig_toLeanConfig___proj(v_p_4748_, v_n_4749_);
lean_dec(v_n_4749_);
lean_dec(v_p_4748_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg(){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg___boxed(lean_object* v___dummy_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent___redArg();
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent(lean_object* v_p_4755_, lean_object* v_n_4756_){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = lean_obj_once(&l_Lake_PackageConfig_toLeanConfig___proj___closed__0, &l_Lake_PackageConfig_toLeanConfig___proj___closed__0_once, _init_l_Lake_PackageConfig_toLeanConfig___proj___closed__0);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_toLeanConfig_instConfigParent___boxed(lean_object* v_p_4758_, lean_object* v_n_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Lake_PackageConfig_toLeanConfig_instConfigParent(v_p_4758_, v_n_4759_);
lean_dec(v_n_4759_);
lean_dec(v_p_4758_);
return v_res_4760_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4770_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__3));
v___x_4771_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__0));
v___x_4772_ = lean_array_push(v___x_4771_, v___x_4770_);
return v___x_4772_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4780_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__7));
v___x_4781_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__4, &l_Lake_PackageConfig___fields___closed__4_once, _init_l_Lake_PackageConfig___fields___closed__4);
v___x_4782_ = lean_array_push(v___x_4781_, v___x_4780_);
return v___x_4782_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4790_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__11));
v___x_4791_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__8, &l_Lake_PackageConfig___fields___closed__8_once, _init_l_Lake_PackageConfig___fields___closed__8);
v___x_4792_ = lean_array_push(v___x_4791_, v___x_4790_);
return v___x_4792_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4800_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__15));
v___x_4801_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__12, &l_Lake_PackageConfig___fields___closed__12_once, _init_l_Lake_PackageConfig___fields___closed__12);
v___x_4802_ = lean_array_push(v___x_4801_, v___x_4800_);
return v___x_4802_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4810_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__19));
v___x_4811_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__16, &l_Lake_PackageConfig___fields___closed__16_once, _init_l_Lake_PackageConfig___fields___closed__16);
v___x_4812_ = lean_array_push(v___x_4811_, v___x_4810_);
return v___x_4812_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4820_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__23));
v___x_4821_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__20, &l_Lake_PackageConfig___fields___closed__20_once, _init_l_Lake_PackageConfig___fields___closed__20);
v___x_4822_ = lean_array_push(v___x_4821_, v___x_4820_);
return v___x_4822_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__28(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4830_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__27));
v___x_4831_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__24, &l_Lake_PackageConfig___fields___closed__24_once, _init_l_Lake_PackageConfig___fields___closed__24);
v___x_4832_ = lean_array_push(v___x_4831_, v___x_4830_);
return v___x_4832_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__32(void){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__31));
v___x_4841_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__28, &l_Lake_PackageConfig___fields___closed__28_once, _init_l_Lake_PackageConfig___fields___closed__28);
v___x_4842_ = lean_array_push(v___x_4841_, v___x_4840_);
return v___x_4842_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4850_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__35));
v___x_4851_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__32, &l_Lake_PackageConfig___fields___closed__32_once, _init_l_Lake_PackageConfig___fields___closed__32);
v___x_4852_ = lean_array_push(v___x_4851_, v___x_4850_);
return v___x_4852_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__40(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4860_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__39));
v___x_4861_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__36, &l_Lake_PackageConfig___fields___closed__36_once, _init_l_Lake_PackageConfig___fields___closed__36);
v___x_4862_ = lean_array_push(v___x_4861_, v___x_4860_);
return v___x_4862_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__44(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4870_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__43));
v___x_4871_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__40, &l_Lake_PackageConfig___fields___closed__40_once, _init_l_Lake_PackageConfig___fields___closed__40);
v___x_4872_ = lean_array_push(v___x_4871_, v___x_4870_);
return v___x_4872_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4880_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__47));
v___x_4881_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__44, &l_Lake_PackageConfig___fields___closed__44_once, _init_l_Lake_PackageConfig___fields___closed__44);
v___x_4882_ = lean_array_push(v___x_4881_, v___x_4880_);
return v___x_4882_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__52(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4890_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__51));
v___x_4891_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__48, &l_Lake_PackageConfig___fields___closed__48_once, _init_l_Lake_PackageConfig___fields___closed__48);
v___x_4892_ = lean_array_push(v___x_4891_, v___x_4890_);
return v___x_4892_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__56(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4900_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__55));
v___x_4901_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__52, &l_Lake_PackageConfig___fields___closed__52_once, _init_l_Lake_PackageConfig___fields___closed__52);
v___x_4902_ = lean_array_push(v___x_4901_, v___x_4900_);
return v___x_4902_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__60(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__59));
v___x_4911_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__56, &l_Lake_PackageConfig___fields___closed__56_once, _init_l_Lake_PackageConfig___fields___closed__56);
v___x_4912_ = lean_array_push(v___x_4911_, v___x_4910_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__64(void){
_start:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4920_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__63));
v___x_4921_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__60, &l_Lake_PackageConfig___fields___closed__60_once, _init_l_Lake_PackageConfig___fields___closed__60);
v___x_4922_ = lean_array_push(v___x_4921_, v___x_4920_);
return v___x_4922_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__70(void){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4934_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__69));
v___x_4935_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__64, &l_Lake_PackageConfig___fields___closed__64_once, _init_l_Lake_PackageConfig___fields___closed__64);
v___x_4936_ = lean_array_push(v___x_4935_, v___x_4934_);
return v___x_4936_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__72(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4940_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__71));
v___x_4941_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__70, &l_Lake_PackageConfig___fields___closed__70_once, _init_l_Lake_PackageConfig___fields___closed__70);
v___x_4942_ = lean_array_push(v___x_4941_, v___x_4940_);
return v___x_4942_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__76(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4950_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__75));
v___x_4951_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__72, &l_Lake_PackageConfig___fields___closed__72_once, _init_l_Lake_PackageConfig___fields___closed__72);
v___x_4952_ = lean_array_push(v___x_4951_, v___x_4950_);
return v___x_4952_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__80(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4960_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__79));
v___x_4961_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__76, &l_Lake_PackageConfig___fields___closed__76_once, _init_l_Lake_PackageConfig___fields___closed__76);
v___x_4962_ = lean_array_push(v___x_4961_, v___x_4960_);
return v___x_4962_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__84(void){
_start:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4970_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__83));
v___x_4971_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__80, &l_Lake_PackageConfig___fields___closed__80_once, _init_l_Lake_PackageConfig___fields___closed__80);
v___x_4972_ = lean_array_push(v___x_4971_, v___x_4970_);
return v___x_4972_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__88(void){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4980_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__87));
v___x_4981_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__84, &l_Lake_PackageConfig___fields___closed__84_once, _init_l_Lake_PackageConfig___fields___closed__84);
v___x_4982_ = lean_array_push(v___x_4981_, v___x_4980_);
return v___x_4982_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__92(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__91));
v___x_4991_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__88, &l_Lake_PackageConfig___fields___closed__88_once, _init_l_Lake_PackageConfig___fields___closed__88);
v___x_4992_ = lean_array_push(v___x_4991_, v___x_4990_);
return v___x_4992_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__96(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__95));
v___x_5001_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__92, &l_Lake_PackageConfig___fields___closed__92_once, _init_l_Lake_PackageConfig___fields___closed__92);
v___x_5002_ = lean_array_push(v___x_5001_, v___x_5000_);
return v___x_5002_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__100(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__99));
v___x_5011_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__96, &l_Lake_PackageConfig___fields___closed__96_once, _init_l_Lake_PackageConfig___fields___closed__96);
v___x_5012_ = lean_array_push(v___x_5011_, v___x_5010_);
return v___x_5012_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__104(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5020_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__103));
v___x_5021_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__100, &l_Lake_PackageConfig___fields___closed__100_once, _init_l_Lake_PackageConfig___fields___closed__100);
v___x_5022_ = lean_array_push(v___x_5021_, v___x_5020_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__108(void){
_start:
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5030_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__107));
v___x_5031_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__104, &l_Lake_PackageConfig___fields___closed__104_once, _init_l_Lake_PackageConfig___fields___closed__104);
v___x_5032_ = lean_array_push(v___x_5031_, v___x_5030_);
return v___x_5032_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__112(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5040_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__111));
v___x_5041_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__108, &l_Lake_PackageConfig___fields___closed__108_once, _init_l_Lake_PackageConfig___fields___closed__108);
v___x_5042_ = lean_array_push(v___x_5041_, v___x_5040_);
return v___x_5042_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__116(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5050_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__115));
v___x_5051_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__112, &l_Lake_PackageConfig___fields___closed__112_once, _init_l_Lake_PackageConfig___fields___closed__112);
v___x_5052_ = lean_array_push(v___x_5051_, v___x_5050_);
return v___x_5052_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__120(void){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5060_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__119));
v___x_5061_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__116, &l_Lake_PackageConfig___fields___closed__116_once, _init_l_Lake_PackageConfig___fields___closed__116);
v___x_5062_ = lean_array_push(v___x_5061_, v___x_5060_);
return v___x_5062_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__124(void){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5070_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__123));
v___x_5071_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__120, &l_Lake_PackageConfig___fields___closed__120_once, _init_l_Lake_PackageConfig___fields___closed__120);
v___x_5072_ = lean_array_push(v___x_5071_, v___x_5070_);
return v___x_5072_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__128(void){
_start:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5080_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__127));
v___x_5081_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__124, &l_Lake_PackageConfig___fields___closed__124_once, _init_l_Lake_PackageConfig___fields___closed__124);
v___x_5082_ = lean_array_push(v___x_5081_, v___x_5080_);
return v___x_5082_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__134(void){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5094_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__133));
v___x_5095_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__128, &l_Lake_PackageConfig___fields___closed__128_once, _init_l_Lake_PackageConfig___fields___closed__128);
v___x_5096_ = lean_array_push(v___x_5095_, v___x_5094_);
return v___x_5096_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__136(void){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5100_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__135));
v___x_5101_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__134, &l_Lake_PackageConfig___fields___closed__134_once, _init_l_Lake_PackageConfig___fields___closed__134);
v___x_5102_ = lean_array_push(v___x_5101_, v___x_5100_);
return v___x_5102_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__142(void){
_start:
{
lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5114_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__141));
v___x_5115_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__136, &l_Lake_PackageConfig___fields___closed__136_once, _init_l_Lake_PackageConfig___fields___closed__136);
v___x_5116_ = lean_array_push(v___x_5115_, v___x_5114_);
return v___x_5116_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__144(void){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5120_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__143));
v___x_5121_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__142, &l_Lake_PackageConfig___fields___closed__142_once, _init_l_Lake_PackageConfig___fields___closed__142);
v___x_5122_ = lean_array_push(v___x_5121_, v___x_5120_);
return v___x_5122_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__148(void){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5130_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__147));
v___x_5131_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__144, &l_Lake_PackageConfig___fields___closed__144_once, _init_l_Lake_PackageConfig___fields___closed__144);
v___x_5132_ = lean_array_push(v___x_5131_, v___x_5130_);
return v___x_5132_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__152(void){
_start:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5140_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__151));
v___x_5141_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__148, &l_Lake_PackageConfig___fields___closed__148_once, _init_l_Lake_PackageConfig___fields___closed__148);
v___x_5142_ = lean_array_push(v___x_5141_, v___x_5140_);
return v___x_5142_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__158(void){
_start:
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v___x_5154_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__157));
v___x_5155_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__152, &l_Lake_PackageConfig___fields___closed__152_once, _init_l_Lake_PackageConfig___fields___closed__152);
v___x_5156_ = lean_array_push(v___x_5155_, v___x_5154_);
return v___x_5156_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__160(void){
_start:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5160_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__159));
v___x_5161_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__158, &l_Lake_PackageConfig___fields___closed__158_once, _init_l_Lake_PackageConfig___fields___closed__158);
v___x_5162_ = lean_array_push(v___x_5161_, v___x_5160_);
return v___x_5162_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__164(void){
_start:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5170_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__163));
v___x_5171_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__160, &l_Lake_PackageConfig___fields___closed__160_once, _init_l_Lake_PackageConfig___fields___closed__160);
v___x_5172_ = lean_array_push(v___x_5171_, v___x_5170_);
return v___x_5172_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__168(void){
_start:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
v___x_5180_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__167));
v___x_5181_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__164, &l_Lake_PackageConfig___fields___closed__164_once, _init_l_Lake_PackageConfig___fields___closed__164);
v___x_5182_ = lean_array_push(v___x_5181_, v___x_5180_);
return v___x_5182_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__169(void){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5183_ = l_Lake_WorkspaceConfig___fields;
v___x_5184_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__168, &l_Lake_PackageConfig___fields___closed__168_once, _init_l_Lake_PackageConfig___fields___closed__168);
v___x_5185_ = l_Array_append___redArg(v___x_5184_, v___x_5183_);
return v___x_5185_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__173(void){
_start:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5193_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__172));
v___x_5194_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__169, &l_Lake_PackageConfig___fields___closed__169_once, _init_l_Lake_PackageConfig___fields___closed__169);
v___x_5195_ = lean_array_push(v___x_5194_, v___x_5193_);
return v___x_5195_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__174(void){
_start:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5196_ = l_Lake_LeanConfig___fields;
v___x_5197_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__173, &l_Lake_PackageConfig___fields___closed__173_once, _init_l_Lake_PackageConfig___fields___closed__173);
v___x_5198_ = l_Array_append___redArg(v___x_5197_, v___x_5196_);
return v___x_5198_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields___closed__178(void){
_start:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5206_ = ((lean_object*)(l_Lake_PackageConfig___fields___closed__177));
v___x_5207_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__174, &l_Lake_PackageConfig___fields___closed__174_once, _init_l_Lake_PackageConfig___fields___closed__174);
v___x_5208_ = lean_array_push(v___x_5207_, v___x_5206_);
return v___x_5208_;
}
}
static lean_object* _init_l_Lake_PackageConfig___fields(void){
_start:
{
lean_object* v___x_5209_; 
v___x_5209_ = lean_obj_once(&l_Lake_PackageConfig___fields___closed__178, &l_Lake_PackageConfig___fields___closed__178_once, _init_l_Lake_PackageConfig___fields___closed__178);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg(){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l_Lake_PackageConfig___fields;
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___redArg___boxed(lean_object* v___dummy_5212_){
_start:
{
lean_object* v_res_5213_; 
v_res_5213_ = l_Lake_PackageConfig_instConfigFields___redArg();
return v_res_5213_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields(lean_object* v_p_5214_, lean_object* v_n_5215_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l_Lake_PackageConfig___fields;
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigFields___boxed(lean_object* v_p_5217_, lean_object* v_n_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Lake_PackageConfig_instConfigFields(v_p_5217_, v_n_5218_);
lean_dec(v_n_5218_);
lean_dec(v_p_5217_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instConfigInfo___lam__0(lean_object* v_x1_5220_, lean_object* v_x2_5221_){
_start:
{
lean_object* v_name_5222_; lean_object* v___x_5223_; 
v_name_5222_ = lean_ctor_get(v_x2_5221_, 0);
lean_inc(v_name_5222_);
v___x_5223_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5222_, v_x2_5221_, v_x1_5220_);
return v___x_5223_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5224_ = l_Lake_PackageConfig___fields;
v___x_5225_ = lean_array_get_size(v___x_5224_);
return v___x_5225_;
}
}
static uint8_t _init_l_Lake_PackageConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5245_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5246_ = lean_unsigned_to_nat(0u);
v___x_5247_ = lean_nat_dec_lt(v___x_5246_, v___x_5245_);
return v___x_5247_;
}
}
static size_t _init_l_Lake_PackageConfig_instConfigInfo___closed__13(void){
_start:
{
lean_object* v___x_5249_; size_t v___x_5250_; 
v___x_5249_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__0, &l_Lake_PackageConfig_instConfigInfo___closed__0_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__0);
v___x_5250_ = lean_usize_of_nat(v___x_5249_);
return v___x_5250_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_5251_; size_t v___x_5252_; size_t v___x_5253_; lean_object* v___x_5254_; lean_object* v___f_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5251_ = lean_box(1);
v___x_5252_ = lean_usize_once(&l_Lake_PackageConfig_instConfigInfo___closed__13, &l_Lake_PackageConfig_instConfigInfo___closed__13_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__13);
v___x_5253_ = ((size_t)0ULL);
v___x_5254_ = l_Lake_PackageConfig___fields;
v___f_5255_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__12));
v___x_5256_ = ((lean_object*)(l_Lake_PackageConfig_instConfigInfo___closed__10));
v___x_5257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5256_, v___f_5255_, v___x_5254_, v___x_5253_, v___x_5252_, v___x_5251_);
return v___x_5257_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instConfigInfo(void){
_start:
{
lean_object* v___x_5258_; lean_object* v___y_5260_; lean_object* v___x_5263_; uint8_t v___x_5264_; 
v___x_5258_ = l_Lake_PackageConfig___fields;
v___x_5263_ = lean_box(1);
v___x_5264_ = lean_uint8_once(&l_Lake_PackageConfig_instConfigInfo___closed__11, &l_Lake_PackageConfig_instConfigInfo___closed__11_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__11);
if (v___x_5264_ == 0)
{
v___y_5260_ = v___x_5263_;
goto v___jp_5259_;
}
else
{
lean_object* v___x_5265_; 
v___x_5265_ = lean_obj_once(&l_Lake_PackageConfig_instConfigInfo___closed__14, &l_Lake_PackageConfig_instConfigInfo___closed__14_once, _init_l_Lake_PackageConfig_instConfigInfo___closed__14);
v___y_5260_ = v___x_5265_;
goto v___jp_5259_;
}
v___jp_5259_:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5261_ = lean_unsigned_to_nat(2u);
lean_inc(v___y_5260_);
v___x_5262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5258_);
lean_ctor_set(v___x_5262_, 1, v___y_5260_);
lean_ctor_set(v___x_5262_, 2, v___x_5261_);
return v___x_5262_;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0(void){
_start:
{
uint8_t v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; uint8_t v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5266_ = 1;
v___x_5267_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__7));
v___x_5268_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__6));
v___x_5269_ = l_Lake_defaultVersionTags;
v___x_5270_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__4));
v___x_5271_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__2));
v___x_5272_ = lean_box(0);
v___x_5273_ = l_Lake_defaultIrDir;
v___x_5274_ = l_Lake_defaultBinDir;
v___x_5275_ = l_Lake_defaultNativeLibDir;
v___x_5276_ = l_Lake_defaultLeanLibDir;
v___x_5277_ = l_Lake_defaultBuildDir;
v___x_5278_ = ((lean_object*)(l_Lake_instInhabitedPackageConfig_default___redArg___closed__1));
v___x_5279_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__0));
v___x_5280_ = 0;
v___x_5281_ = ((lean_object*)(l_Lake_PackageConfig_toLeanConfig___proj___redArg___lam__3___closed__1));
v___x_5282_ = l_Lake_defaultPackagesDir;
v___x_5283_ = lean_alloc_ctor(0, 29, 7);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
lean_ctor_set(v___x_5283_, 1, v___x_5281_);
lean_ctor_set(v___x_5283_, 2, v___x_5279_);
lean_ctor_set(v___x_5283_, 3, v___x_5279_);
lean_ctor_set(v___x_5283_, 4, v___x_5278_);
lean_ctor_set(v___x_5283_, 5, v___x_5277_);
lean_ctor_set(v___x_5283_, 6, v___x_5276_);
lean_ctor_set(v___x_5283_, 7, v___x_5275_);
lean_ctor_set(v___x_5283_, 8, v___x_5274_);
lean_ctor_set(v___x_5283_, 9, v___x_5273_);
lean_ctor_set(v___x_5283_, 10, v___x_5272_);
lean_ctor_set(v___x_5283_, 11, v___x_5272_);
lean_ctor_set(v___x_5283_, 12, v___x_5272_);
lean_ctor_set(v___x_5283_, 13, v___x_5271_);
lean_ctor_set(v___x_5283_, 14, v___x_5279_);
lean_ctor_set(v___x_5283_, 15, v___x_5271_);
lean_ctor_set(v___x_5283_, 16, v___x_5279_);
lean_ctor_set(v___x_5283_, 17, v___x_5270_);
lean_ctor_set(v___x_5283_, 18, v___x_5269_);
lean_ctor_set(v___x_5283_, 19, v___x_5271_);
lean_ctor_set(v___x_5283_, 20, v___x_5279_);
lean_ctor_set(v___x_5283_, 21, v___x_5271_);
lean_ctor_set(v___x_5283_, 22, v___x_5271_);
lean_ctor_set(v___x_5283_, 23, v___x_5268_);
lean_ctor_set(v___x_5283_, 24, v___x_5267_);
lean_ctor_set(v___x_5283_, 25, v___x_5272_);
lean_ctor_set(v___x_5283_, 26, v___x_5272_);
lean_ctor_set(v___x_5283_, 27, v___x_5272_);
lean_ctor_set(v___x_5283_, 28, v___x_5279_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29, v___x_5280_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29 + 1, v___x_5280_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29 + 2, v___x_5280_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29 + 3, v___x_5266_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29 + 4, v___x_5280_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29 + 5, v___x_5280_);
lean_ctor_set_uint8(v___x_5283_, sizeof(void*)*29 + 6, v___x_5280_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0, &l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___redArg___closed__0);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___redArg___boxed(lean_object* v___dummy_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
return v_res_5287_;
}
}
static lean_object* _init_l_Lake_PackageConfig_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_5288_; 
v___x_5288_ = l_Lake_PackageConfig_instEmptyCollection___redArg();
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection(lean_object* v_p_5289_, lean_object* v_n_5290_){
_start:
{
lean_object* v___x_5291_; 
v___x_5291_ = lean_obj_once(&l_Lake_PackageConfig_instEmptyCollection___closed__0, &l_Lake_PackageConfig_instEmptyCollection___closed__0_once, _init_l_Lake_PackageConfig_instEmptyCollection___closed__0);
return v___x_5291_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_instEmptyCollection___boxed(lean_object* v_p_5292_, lean_object* v_n_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lake_PackageConfig_instEmptyCollection(v_p_5292_, v_n_5293_);
lean_dec(v_n_5293_);
lean_dec(v_p_5292_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg(lean_object* v_n_5295_){
_start:
{
lean_inc(v_n_5295_);
return v_n_5295_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___redArg___boxed(lean_object* v_n_5296_){
_start:
{
lean_object* v_res_5297_; 
v_res_5297_ = l_Lake_PackageConfig_origName___redArg(v_n_5296_);
lean_dec(v_n_5296_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName(lean_object* v_p_5298_, lean_object* v_n_5299_, lean_object* v_x_5300_){
_start:
{
lean_inc(v_n_5299_);
return v_n_5299_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_origName___boxed(lean_object* v_p_5301_, lean_object* v_n_5302_, lean_object* v_x_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Lake_PackageConfig_origName(v_p_5301_, v_n_5302_, v_x_5303_);
lean_dec_ref(v_x_5303_);
lean_dec(v_n_5302_);
lean_dec(v_p_5301_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name(lean_object* v_self_5312_){
_start:
{
lean_object* v_keyName_5313_; 
v_keyName_5313_ = lean_ctor_get(v_self_5312_, 1);
lean_inc(v_keyName_5313_);
return v_keyName_5313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_name___boxed(lean_object* v_self_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Lake_PackageDecl_name(v_self_5314_);
lean_dec_ref(v_self_5314_);
return v_res_5315_;
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
